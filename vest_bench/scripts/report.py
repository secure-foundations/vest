#!/usr/bin/env python3
"""Report one recorded benchmark run; never silently mix cached measurements."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import statistics
import sys
from dataclasses import dataclass

from common import MICROFORMATS, POLICY, RESULTS, SUITES, external_corpus_matches, fingerprint


@dataclass(frozen=True)
class Measurement:
    group: str
    implementation: str
    median_ns: float
    lower_ns: float
    upper_ns: float
    confidence: float
    bytes_per_iteration: int | None
    samples: tuple[float, ...]
    items: int | None = None

    @property
    def id(self) -> str:
        return f"{self.group}/{self.implementation}"

    def mib_per_second(self, nanoseconds: float) -> float:
        if self.bytes_per_iteration is None:
            raise ValueError(f"missing byte throughput for {self.id}")
        return self.bytes_per_iteration * 1e9 / nanoseconds / 2**20


def load_measurements(directory: Path, manifest: dict | None = None) -> list[Measurement]:
    recorded = {m["id"]: m for m in manifest["measurements"]} if manifest else None
    found = {}
    for path in sorted(directory.glob("**/new/estimates.json")):
        benchmark_path = path.with_name("benchmark.json")
        if not benchmark_path.is_file():
            raise ValueError(f"missing benchmark metadata: {path}")
        benchmark = json.loads(benchmark_path.read_text())
        group, implementation = benchmark["group_id"], benchmark["function_id"]
        identity = f"{group}/{implementation}"
        if recorded is not None:
            if identity not in recorded:
                raise ValueError(f"unrecorded measurements in run: {identity}")
            for name, expected in recorded[identity]["files"].items():
                file = directory / name
                if not file.is_file() or hashlib.sha256(file.read_bytes()).hexdigest() != expected:
                    raise ValueError(f"modified or stale measurement: {file}")
        if identity in found:
            raise ValueError(f"duplicate measurement: {identity}")
        estimate = json.loads(path.read_text())["median"]
        interval = estimate["confidence_interval"]
        sample = json.loads(path.with_name("sample.json").read_text())
        if len(sample["iters"]) != len(sample["times"]) or not sample["iters"]:
            raise ValueError(f"invalid samples: {identity}")
        if any(n <= 0 for n in sample["iters"]):
            raise ValueError(f"non-positive iteration count: {identity}")
        samples = tuple(t / n for t, n in zip(sample["times"], sample["iters"]))
        if any(not math.isfinite(s) or s <= 0 for s in samples):
            raise ValueError(f"non-positive or non-finite samples: {identity}")
        if recorded is not None and len(samples) != manifest["settings"]["samples"]:
            raise ValueError(f"wrong sample count: {identity}")
        corpus = recorded[identity].get("corpus", {}) if recorded else {}
        byte_count = (benchmark.get("throughput") or {}).get("Bytes")
        if byte_count is None:
            print(f"WARNING: {identity} has no byte throughput; reporting latency only", file=sys.stderr)
        if corpus and corpus["bytes"] != byte_count:
            raise ValueError(f"corpus byte count disagrees with Criterion: {identity}")
        found[identity] = Measurement(
            group, implementation, estimate["point_estimate"], interval["lower_bound"],
            interval["upper_bound"], interval["confidence_level"], byte_count, samples, corpus.get("items"),
        )
    if recorded is not None and found.keys() != recorded.keys():
        raise ValueError(f"missing measurements: {recorded.keys() - found.keys()}")
    return list(found.values())


def quantile(values: list[float], probability: float) -> float:
    index = (len(values) - 1) * probability
    low = int(index)
    high = min(low + 1, len(values) - 1)
    return values[low] + (values[high] - values[low]) * (index - low)


def ratio_interval(vest: Measurement, baseline: Measurement, resamples: int = 2000) -> tuple[float, float, float]:
    """Independent bootstrap of the ratio of median throughputs.

    Samples are not paired: implementations run in different processes. The
    interval describes sampling noise, not cross-run or thermal variance.
    """
    if vest.bytes_per_iteration != baseline.bytes_per_iteration:
        raise ValueError(f"unequal byte workloads: {vest.id}, {baseline.id}")
    if vest.items is not None and baseline.items is not None and vest.items != baseline.items:
        raise ValueError(f"unequal item workloads: {vest.id}, {baseline.id}")
    point = baseline.median_ns / vest.median_ns
    rng = random.Random(hashlib.sha256((vest.id + baseline.id).encode()).digest())
    boot = sorted(
        statistics.median(rng.choices(baseline.samples, k=len(baseline.samples))) /
        statistics.median(rng.choices(vest.samples, k=len(vest.samples)))
        for _ in range(resamples)
    )
    return point, quantile(boot, 0.025), quantile(boot, 0.975)


def selected_group(group: str, targets: set[str]) -> bool:
    suite = group.split("/")[0]
    return not targets or suite in targets or ("formats" in targets and suite in MICROFORMATS)


def format_duration(ns: float) -> str:
    if ns < 1000:
        return f"{ns:.1f} ns"
    if ns < 1e6:
        return f"{ns / 1000:.2f} µs"
    if ns < 1e9:
        return f"{ns / 1e6:.2f} ms"
    return f"{ns / 1e9:.2f} s"


def markdown_tables(measurements: list[Measurement], manifest: dict, targets: set[str]) -> str:
    groups = {}
    for m in measurements:
        if selected_group(m.group, targets):
            groups.setdefault(m.group, []).append(m)
    lines = []
    for group, rows in sorted(groups.items()):
        vest = next((m for m in rows if m.implementation.casefold() == "vest"), None)
        if vest is None:
            raise ValueError(f"no Vest measurement for {group}")
        rows.sort(key=lambda m: (m.implementation.casefold() != "vest", m.implementation.casefold()))
        lines += [
            f"### {group}", "",
            "| Implementation | Median per corpus pass [CI] | MiB/s [CI] | Vest/baseline [95% CI] | ns/item |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
        for m in rows:
            duration = f"{format_duration(m.median_ns)} [{format_duration(m.lower_ns)}–{format_duration(m.upper_ns)}]"
            throughput = "—" if m.bytes_per_iteration is None else (
                f"{m.mib_per_second(m.median_ns):,.1f} [{m.mib_per_second(m.upper_ns):,.1f}–{m.mib_per_second(m.lower_ns):,.1f}]"
            )
            ratio = "—" if m is vest else "{:.2f}× [{:.2f}–{:.2f}]".format(*ratio_interval(vest, m))
            per_item = f"{m.median_ns / m.items:,.1f}" if m.items else "—"
            lines.append(f"| {m.implementation} | {duration} | {throughput} | {ratio} | {per_item} |")
        lines.append("")
    if manifest.get("allocations"):
        lines += [
            "### Untimed allocation audit", "",
            "Counts are per corpus pass, excluding harness output storage and final result destruction.",
            "Requested bytes sum allocation sizes and reallocations' new sizes, not peak live memory.", "",
            "| Benchmark | Allocations | Reallocations | Requested bytes | Deallocations inside codec |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
        for identity, count in sorted(manifest["allocations"].items()):
            if selected_group(identity.rsplit("/", 1)[0], targets):
                lines.append(f"| {identity} | {count['allocations']} | {count['reallocations']} | {count['requested_bytes']} | {count['deallocations']} |")
    return "\n".join(lines)


def load_run(directory: Path, allow_stale: bool = False) -> dict:
    manifest = json.loads((directory / "run.json").read_text())
    if manifest["policy"] != POLICY:
        raise ValueError("run uses a different timing policy")
    if manifest["status"] != "complete":
        raise ValueError("run did not complete; refusing partial comparisons")
    if len(set(manifest["jobs"])) != len(manifest["jobs"]):
        raise ValueError("duplicate jobs in manifest")
    if set(manifest["jobs"]) != {m["id"] for m in manifest["measurements"]}:
        raise ValueError("manifest contains missing or unexpected jobs")
    if len(manifest["measurements"]) != len(manifest["jobs"]):
        raise ValueError("duplicate measurements in manifest")
    if manifest.get("allocations") and set(manifest["allocations"]) != set(manifest["jobs"]):
        raise ValueError("incomplete allocation audit")
    if manifest["fingerprint"] != fingerprint():
        if not allow_stale:
            raise ValueError("sources/corpora differ from this run; rerun or use --allow-stale explicitly")
        print("WARNING: reporting a historical source/corpus version", file=sys.stderr)
    if not external_corpus_matches(manifest.get("external_corpus")):
        if not allow_stale:
            raise ValueError("external corpus differs from this run")
        print("WARNING: external corpus no longer matches this historical run", file=sys.stderr)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", choices=[*SUITES, *MICROFORMATS])
    parser.add_argument("--run", type=Path, help="recorded run directory (default: latest completed run)")
    parser.add_argument("--allow-stale", action="store_true", help="explicitly report a historical source/corpus version")
    parser.add_argument("--criterion-dir", type=Path, help="inspect untracked legacy data, with an explicit warning")
    args = parser.parse_args()
    try:
        if args.criterion_dir:
            if args.run:
                raise ValueError("--run and --criterion-dir are mutually exclusive")
            print("WARNING: untracked data; run identity, completeness, and source version are unknown", file=sys.stderr)
            manifest = {}
            measurements = load_measurements(args.criterion_dir)
        else:
            directory = args.run
            if directory is None:
                directory = Path(json.loads((RESULTS / "latest.json").read_text())["run"])
                if not directory.is_absolute():
                    directory = RESULTS / directory
            manifest = load_run(directory, args.allow_stale)
            print(f"Run: {directory}\nCommit: {manifest['commit']}\nMachine: {manifest['machine']}\nAllocator: {manifest['allocator']}")
            print(f"Coverage: {len(manifest['jobs'])} measurements; targets: {', '.join(manifest['targets'])}")
            if manifest.get("quick"):
                print("WARNING: quick validation run; not publication-quality measurements")
            measurements = load_measurements(directory / "criterion", manifest)
        if not measurements:
            raise ValueError("no measurements found; run make bench first")
        result = markdown_tables(measurements, manifest, set(args.targets))
        if not result:
            raise ValueError("no results for the selected targets in this run")
        print("\nMedian time/throughput and Criterion confidence intervals. Vest/baseline > 1 means Vest is faster.")
        print("Ratio intervals use independent resampling; they do not include between-run variance.\n")
        print(result)
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        raise SystemExit(f"{error}; use make bench to create a complete, current run") from error


if __name__ == "__main__":
    main()
