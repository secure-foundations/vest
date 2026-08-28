#!/usr/bin/env python3
"""Summarize the generic CBOR Criterion output."""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path


LINE = re.compile(
    r"^test generic_cbor/(parse|serialize)/(VPS|ciborium|cbor4ii|minicbor-serde) "
    r"\.\.\. bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$",
    re.M,
)
REAL_LINE = re.compile(
    r"^test real_cose_cbor/(parse|serialize)/(VPS|ciborium) "
    r"\.\.\. bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$",
    re.M,
)
CORPUS_BYTES = 108864
CORPUS_VALUES = 1536


def throughput_sizes(stdout: Path) -> dict[str, int]:
    path = stdout.with_name("throughput.tsv")
    if not path.exists():
        return {}
    with path.open(newline="") as f:
        return {row["group"]: int(row["bytes"]) for row in csv.DictReader(f, delimiter="\t")}


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    runs = sorted((root / "results/raw/runtime/cbor").glob("*/stdout.log"))
    if not runs:
        print("No CBOR runtime result found.")
        return
    rows = []
    exact_sizes = throughput_sizes(runs[-1])
    for operation, system, ns, std_dev in LINE.findall(runs[-1].read_text()):
        nanos = int(ns)
        size = exact_sizes.get(f"generic_cbor/{operation}", CORPUS_BYTES)
        rows.append({
            "operation": operation,
            "system": system,
            "nanoseconds": nanos,
            "std_dev_nanoseconds": int(std_dev),
            "values": CORPUS_VALUES,
            "bytes": size,
            "mib_per_second": size / (nanos / 1e9) / (1024 * 1024),
        })
    if len(rows) != 8:
        raise ValueError(f"expected 8 CBOR rows, found {len(rows)}")
    by_operation = {(r["operation"], r["system"]): r for r in rows}
    for r in rows:
        vps = by_operation[(r["operation"], "VPS")]
        r["relative_to_vps"] = vps["nanoseconds"] / r["nanoseconds"]
    out = root / "results/derived"
    (out / "cbor_runtime.json").write_text(json.dumps(rows, indent=2) + "\n")
    with (out / "cbor_runtime.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys(), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    lines = [
        "# Generic CBOR runtime", "",
        f"Common corpus: {CORPUS_VALUES} values, {CORPUS_BYTES} encoded bytes. It includes "
        "over-wide integers, fragmented byte/text strings, and recursively indefinite "
        "arrays/maps; serialization normalizes the logical values.", "",
        "| Operation | Implementation | Time | MiB/s | Throughput relative to VPS |",
        "|---|---|---:|---:|---:|",
    ]
    for r in rows:
        lines.append(
            f'| {r["operation"]} | {r["system"]} | {r["nanoseconds"] / 1e3:.2f} ± '
            f'{r["std_dev_nanoseconds"] / 1e3:.2f} µs | '
            f'{r["mib_per_second"]:.1f} | {r["relative_to_vps"]:.2f}× |'
        )
    report = "\n".join(lines) + "\n"
    real_runs = sorted((root / "results/raw/runtime/cbor-real").glob("*/stdout.log"))
    if real_runs:
        real_rows = []
        exact_sizes = throughput_sizes(real_runs[-1])
        for operation, system, ns, std_dev in REAL_LINE.findall(real_runs[-1].read_text()):
            nanos = int(ns)
            size = exact_sizes.get(f"real_cose_cbor/{operation}", 3997)
            real_rows.append({
                "operation": operation, "system": system, "nanoseconds": nanos,
                "std_dev_nanoseconds": int(std_dev), "values": 49, "bytes": size,
                "mib_per_second": size / (nanos / 1e9) / (1024 * 1024),
            })
        if len(real_rows) != 4:
            raise ValueError(f"expected 4 real CBOR rows, found {len(real_rows)}")
        real_vps = {r["operation"]: r for r in real_rows if r["system"] == "VPS"}
        for r in real_rows:
            r["relative_to_vps"] = real_vps[r["operation"]]["nanoseconds"] / r["nanoseconds"]
        (out / "cbor_real_runtime.json").write_text(json.dumps(real_rows, indent=2) + "\n")
        with (out / "cbor_real_runtime.csv").open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=real_rows[0].keys(), lineterminator="\n")
            writer.writeheader()
            writer.writerows(real_rows)
        real_lines = [
            "", "## COSE Working Group protocol corpus", "",
            "49 complete COSE messages, 3,997 encoded bytes. cbor4ii and "
            "minicbor-serde are omitted because their Serde-to-`ciborium::Value` path "
            "rejects semantic tags used by 44 messages.", "",
            "| Operation | Implementation | Time | MiB/s | Throughput relative to VPS |",
            "|---|---|---:|---:|---:|",
        ]
        for r in real_rows:
            real_lines.append(
                f'| {r["operation"]} | {r["system"]} | {r["nanoseconds"] / 1e3:.2f} ± '
                f'{r["std_dev_nanoseconds"] / 1e3:.2f} µs | '
                f'{r["mib_per_second"]:.1f} | {r["relative_to_vps"]:.2f}× |'
            )
        report += "\n".join(real_lines) + "\n"
    (out / "cbor_runtime.md").write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
