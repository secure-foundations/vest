#!/usr/bin/env python3
"""Summarize Criterion measurements collected by the Vest benchmarks.

Criterion remains the source of truth: this script reads its ``new`` estimates
under ``target/criterion`` without rerunning anything. Microformats are shown as
Vest-versus-hand-written latency comparisons. Real formats are shown as elapsed
time, byte throughput, and throughput relative to Vest.
"""

from __future__ import annotations

import argparse
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

MICROFORMATS = [
    ("flat", "flat struct, fixed + length-prefixed fields"),
    ("table", "[entry; @count], counted repetition"),
    ("nest", "eight header/footer layers around a payload"),
    ("tlv", "[u8; @len] >>= choose(@tag), tagged union"),
    ("varint", "btc_varint count and lengths"),
    ("bits", "bit-packed header plus byte-aligned body"),
    ("bounded_list", "[u8; @len] >>= Vec<item>"),
    ("tail_list", "Tail >>= Vec<item>"),
]
MICROFORMAT_NAMES = {name for name, _ in MICROFORMATS}
REAL_SUITES = ("tls", "bitcoin", "cms", "cbor")
REAL_IMPLEMENTATIONS = {
    "tls": {"vest", "rustls"},
    "bitcoin": {"vest", "rust-bitcoin"},
    "cms": {"vest", "rasn-cms", "rustcrypto-cms", "cryptographic-message-syntax"},
    "cbor": {"vest", "ciborium", "cbor4ii", "minicbor-serde"},
}
# Workloads of families whose groups have changed, in report order. Criterion
# retains removed groups on disk, such as the synthetic `tls/parse`.
REAL_WORKLOADS = {
    "tls": [
        "client_hello",
        "server_hello",
        "encrypted_extensions",
        "certificate",
        "certificate_verify",
        "finished",
        "new_session_ticket",
    ],
}
DEFAULT_ROOT = Path(__file__).resolve().parent.parent / "target" / "criterion"


@dataclass(frozen=True)
class Measurement:
    group: str
    implementation: str
    mean_ns: float
    lower_ns: float
    upper_ns: float
    confidence: float
    bytes_per_iteration: int | None

    def mib_per_second(self, nanoseconds: float) -> float:
        assert self.bytes_per_iteration is not None
        return self.bytes_per_iteration * 1e9 / nanoseconds / (1024 * 1024)


def load_measurements(root: Path) -> list[Measurement]:
    measurements = []
    if not root.is_dir():
        return measurements

    for estimates_path in root.glob("**/new/estimates.json"):
        benchmark_path = estimates_path.with_name("benchmark.json")
        if not benchmark_path.is_file():
            continue
        with estimates_path.open(encoding="utf-8") as estimates_file:
            estimates = json.load(estimates_file)
        with benchmark_path.open(encoding="utf-8") as benchmark_file:
            benchmark = json.load(benchmark_file)

        mean = estimates["mean"]
        interval = mean["confidence_interval"]
        throughput = benchmark.get("throughput") or {}
        measurements.append(
            Measurement(
                group=benchmark["group_id"],
                implementation=benchmark["function_id"],
                mean_ns=mean["point_estimate"],
                lower_ns=interval["lower_bound"],
                upper_ns=interval["upper_bound"],
                confidence=interval["confidence_level"],
                bytes_per_iteration=throughput.get("Bytes"),
            )
        )
    return measurements


def format_duration(nanoseconds: float) -> str:
    if nanoseconds < 1_000:
        return f"{nanoseconds:.1f} ns"
    if nanoseconds < 1_000_000:
        return f"{nanoseconds / 1_000:.1f} us"
    if nanoseconds < 1_000_000_000:
        return f"{nanoseconds / 1_000_000:.2f} ms"
    return f"{nanoseconds / 1_000_000_000:.2f} s"


def print_microformats(measurements: Iterable[Measurement], selected: set[str]) -> bool:
    by_key = {
        (measurement.group, measurement.implementation.casefold()): measurement
        for measurement in measurements
    }
    formats = [
        (name, description)
        for name, description in MICROFORMATS
        if not selected or "formats" in selected or name in selected
    ]
    printed = False
    for operation in ("parse", "serialize"):
        rows = []
        for name, description in formats:
            vest = by_key.get((f"{name}/{operation}", "vest"))
            hand = by_key.get((f"{name}/{operation}", "hand"))
            if vest is not None and hand is not None:
                rows.append((name, vest, hand, description))
        if not rows:
            continue

        printed = True
        print(
            f"\n--- microformats: {operation} (time per corpus pass; lower is better) ---"
        )
        print(
            f"{'format':<15}{'Vest mean [95% CI]':>31}{'hand mean [95% CI]':>31}"
            f"{'Vest/hand':>12}   what it isolates"
        )
        for name, vest, hand, description in rows:
            confidence = vest.confidence * 100
            vest_estimate = (
                f"{format_duration(vest.mean_ns)} "
                f"[{format_duration(vest.lower_ns)}, {format_duration(vest.upper_ns)}]"
            )
            # All current benchmarks use 95%; keep the heading compact while
            # making a future Criterion configuration change visible.
            if abs(confidence - 95) > 0.01:
                vest_estimate += f" ({confidence:g}%)"
            hand_estimate = (
                f"{format_duration(hand.mean_ns)} "
                f"[{format_duration(hand.lower_ns)}, {format_duration(hand.upper_ns)}]"
            )
            print(
                f"{name:<15}{vest_estimate:>31}{hand_estimate:>31}"
                f"{vest.mean_ns / hand.mean_ns:>11.2f}x   {description}"
            )
    return printed


def real_group_parts(group: str) -> tuple[str, str, str] | None:
    parts = group.split("/")
    if (
        len(parts) < 2
        or parts[0] not in REAL_SUITES
        or parts[-1] not in ("parse", "serialize")
    ):
        return None
    workload = "/".join(parts[1:-1]) or "default"
    return parts[0], workload, parts[-1]


def workload_rank(suite: str, workload: str) -> int:
    order = REAL_WORKLOADS.get(suite, [])
    return order.index(workload) if workload in order else len(order)


def print_real_formats(measurements: Iterable[Measurement], selected: set[str]) -> bool:
    groups: dict[tuple[str, str, str], list[Measurement]] = {}
    for measurement in measurements:
        parts = real_group_parts(measurement.group)
        if parts is None or measurement.bytes_per_iteration is None:
            continue
        suite, workload, _ = parts
        if selected and suite not in selected:
            continue
        if suite in REAL_WORKLOADS and workload not in REAL_WORKLOADS[suite]:
            continue
        # Criterion retains removed benchmark functions on disk. Restrict each
        # family to its current implementations so superseded baselines do not
        # silently reappear in a later report.
        if measurement.implementation.casefold() not in REAL_IMPLEMENTATIONS[suite]:
            continue
        groups.setdefault(parts, []).append(measurement)

    printed = False
    suite_order = {name: index for index, name in enumerate(REAL_SUITES)}
    operation_order = {"parse": 0, "serialize": 1}
    for (suite, workload, operation), rows in sorted(
        groups.items(),
        key=lambda item: (
            suite_order[item[0][0]],
            workload_rank(item[0][0], item[0][1]),
            item[0][1],
            operation_order[item[0][2]],
        ),
    ):
        vest = next(
            (row for row in rows if row.implementation.casefold() == "vest"), None
        )
        # An interrupted Criterion run may leave only one side of a comparison.
        if vest is None or len(rows) < 2:
            continue
        printed = True
        confidence = vest.confidence * 100
        print(
            f"\n--- {suite}: {workload} {operation} "
            f"(MiB/s; higher is better, {confidence:g}% CI) ---"
        )
        print(
            f"{'implementation':<32}{'mean time':>13}{'MiB/s [CI]':>29}{'vs Vest':>11}"
        )
        rows.sort(
            key=lambda row: (
                row.implementation.casefold() != "vest",
                row.implementation.casefold(),
            )
        )
        vest_throughput = vest.mib_per_second(vest.mean_ns)
        for row in rows:
            throughput = row.mib_per_second(row.mean_ns)
            # Time and throughput are inversely related, so the throughput CI
            # bounds use the opposite time bounds.
            throughput_low = row.mib_per_second(row.upper_ns)
            throughput_high = row.mib_per_second(row.lower_ns)
            throughput_estimate = (
                f"{throughput:.1f} [{throughput_low:.1f}, {throughput_high:.1f}]"
            )
            print(
                f"{row.implementation:<32}{format_duration(row.mean_ns):>13}"
                f"{throughput_estimate:>29}{throughput / vest_throughput:>10.2f}x"
            )
    return printed


def parse_args() -> argparse.Namespace:
    choices = ["formats", *[name for name, _ in MICROFORMATS], *REAL_SUITES]
    parser = argparse.ArgumentParser(
        description="print stored Criterion results without rerunning benchmarks"
    )
    parser.add_argument(
        "targets",
        nargs="*",
        choices=choices,
        help="limit the report to a benchmark family or individual microformat",
    )
    parser.add_argument(
        "--criterion-dir",
        type=Path,
        default=Path(os.environ.get("VEST_BENCH_CRITERION_DIR", DEFAULT_ROOT)),
        help="Criterion output directory (default: repository target/criterion)",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    measurements = load_measurements(args.criterion_dir)
    if not measurements:
        raise SystemExit(
            f"no Criterion measurements found under {args.criterion_dir}; "
            "run `make -C vest_bench bench` first"
        )

    selected = set(args.targets)
    want_microformats = not selected or bool(
        selected & (MICROFORMAT_NAMES | {"formats"})
    )
    want_real_formats = not selected or bool(selected & set(REAL_SUITES))
    printed = False
    if want_microformats:
        printed |= print_microformats(measurements, selected)
    if want_real_formats:
        printed |= print_real_formats(measurements, selected)
    if not printed:
        requested = ", ".join(args.targets) if args.targets else "the requested targets"
        raise SystemExit(
            f"no measured results found for {requested}; Criterion smoke tests (`--test`) "
            "validate setup but do not record timing estimates"
        )
    print()


if __name__ == "__main__":
    main()
