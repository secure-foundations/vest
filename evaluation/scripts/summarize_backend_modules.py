#!/usr/bin/env python3
"""Aggregate VPS backend Verus timing by top-level subsystem."""

from __future__ import annotations

import csv
import json
from collections import defaultdict
from pathlib import Path


def area(module: str) -> str:
    first = module.split("::", 1)[0]
    return first if first in {"core", "combinators", "primitives", "asn1", "cbor"} else "library_root"


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    logs = sorted((root / "results/raw/backend-verify").glob("*/stdout.log"))
    if not logs:
        print("No backend verification log found.")
        return
    report = json.loads(logs[-1].read_text())
    totals: dict[str, dict[str, float]] = defaultdict(lambda: {"verify_cpu_ms": 0, "smt_cpu_ms": 0, "modules": 0})
    for item in report["times-ms"]["total-verify-module-times"]:
        bucket = totals[area(item["module"])]
        bucket["verify_cpu_ms"] += item["time"]
        bucket["modules"] += 1
    for item in report["times-ms"]["smt"]["smt-run-module-times"]:
        totals[area(item["module"])]["smt_cpu_ms"] += item["time-micros"] / 1000
    rows = []
    for name in ["core", "combinators", "primitives", "asn1", "cbor", "library_root"]:
        data = totals[name]
        rows.append({
            "area": name,
            "verified_modules": int(data["modules"]),
            "verification_cpu_seconds": data["verify_cpu_ms"] / 1000,
            "smt_cpu_seconds": data["smt_cpu_ms"] / 1000,
        })
    out = root / "results/derived"
    (out / "backend_module_times.json").write_text(json.dumps(rows, indent=2) + "\n")
    with (out / "backend_module_times.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    lines = [
        "# VPS backend verification by subsystem", "",
        "Times are aggregate CPU time across 10 workers; module counts include generated proof/spec submodules.", "",
        "| Area | Verified modules | Verification CPU (s) | SMT CPU (s) |",
        "|---|---:|---:|---:|",
    ]
    for r in rows:
        lines.append(
            f'| {r["area"]} | {r["verified_modules"]} | '
            f'{r["verification_cpu_seconds"]:.2f} | {r["smt_cpu_seconds"]:.2f} |'
        )
    text = "\n".join(lines) + "\n"
    (out / "backend_module_times.md").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()

