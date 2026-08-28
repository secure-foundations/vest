#!/usr/bin/env python3
"""Derive the Vest/VPS runtime table from Criterion's bencher output."""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path


LINE = re.compile(
    r"^test vest_vps/(bitcoin|tls)/(parse|serialize)/(Vest|VPS) \.\.\. "
    r"bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$",
    re.M,
)


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    runs = sorted((root / "results/raw/runtime/vest-vps").glob("*/stdout.log"))
    if not runs:
        print("No Vest/VPS runtime result found.")
        return
    text = runs[-1].read_text()
    throughput_file = runs[-1].with_name("throughput.tsv")
    exact_sizes = {}
    if throughput_file.exists():
        with throughput_file.open(newline="") as f:
            exact_sizes = {row["group"]: int(row["bytes"]) for row in csv.DictReader(f, delimiter="\t")}
    # Retained runs include exact byte denominators. These fallbacks are used
    # only for older logs that predate throughput.tsv.
    corpus_bytes = {"bitcoin": 705_062_422, "tls": 74_915}
    rows = []
    for domain, operation, system, ns, std_dev in LINE.findall(text):
        nanos = int(ns)
        size = exact_sizes.get(f"vest_vps/{domain}/{operation}", corpus_bytes[domain])
        rows.append({
            "domain": domain,
            "operation": operation,
            "system": system,
            "nanoseconds": nanos,
            "std_dev_nanoseconds": int(std_dev),
            "corpus_bytes": size,
            "mib_per_second": size / (nanos / 1e9) / (1024 * 1024),
        })
    if len(rows) != 8:
        raise ValueError(f"expected 8 benchmark rows in {runs[-1]}, found {len(rows)}")
    lookup = {(r["domain"], r["operation"], r["system"]): r for r in rows}
    for r in rows:
        other = lookup[(r["domain"], r["operation"], "Vest")]
        r["speedup_over_vest"] = other["nanoseconds"] / r["nanoseconds"]

    out = root / "results/derived"
    (out / "vest_vps_runtime.json").write_text(json.dumps(rows, indent=2) + "\n")
    with (out / "vest_vps_runtime.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys(), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    lines = [
        "# Vest versus VPS runtime", "",
        "Output buffers and parsed values are prepared outside the timed region.", "",
        "| Format | Operation | System | Time | MiB/s | Speedup over Vest |",
        "|---|---|---|---:|---:|---:|",
    ]
    for r in rows:
        unit = (
            f'{r["nanoseconds"] / 1e6:.2f} ± {r["std_dev_nanoseconds"] / 1e6:.2f} ms'
            if r["nanoseconds"] >= 1_000_000 else
            f'{r["nanoseconds"] / 1e3:.2f} ± {r["std_dev_nanoseconds"] / 1e3:.2f} µs'
        )
        domain = "TLS" if r["domain"] == "tls" else r["domain"].title()
        lines.append(
            f'| {domain} | {r["operation"]} | {r["system"]} | {unit} | '
            f'{r["mib_per_second"]:.1f} | {r["speedup_over_vest"]:.2f}× |'
        )
    report = "\n".join(lines) + "\n"
    (out / "vest_vps_runtime.md").write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
