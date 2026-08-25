#!/usr/bin/env python3
"""Combine the newest successful/failure boundary runs into scalability tables."""

from __future__ import annotations

import csv
import json
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    latest: dict[tuple[str, str, int], tuple[Path, dict]] = {}
    for path in sorted((root / "results/raw/scalability").glob("*/**/metadata.json")):
        data = json.loads(path.read_text())
        if data.get("size") == 0 or data.get("kind") not in {"depth", "struct", "choice"}:
            continue
        key = (data["kind"], data["system"], data["size"])
        latest[key] = (path, data)
    rows = []
    for key in sorted(latest, key=lambda k: ({"depth": 0, "struct": 1, "choice": 2}[k[0]], k[2], k[1])):
        path, data = latest[key]
        rows.append({
            "kind": data["kind"],
            "size": data["size"],
            "system": data["system"],
            "generated_sloc": data.get("generated_sloc"),
            "verified_vcs": data.get("verified_vcs"),
            "verus_seconds": data.get("verus_total_seconds"),
            "rust_seconds": data.get("rust_seconds"),
            "verification_wall_seconds": data.get("verification_wall_seconds"),
            "smt_cpu_seconds": data.get("smt_cpu_seconds"),
            "result": "pass" if data.get("verify_exit_code") == 0 else str(data.get("verify_exit_code")),
            "raw_metadata": str(path.relative_to(root)),
        })
    out = root / "results/derived"
    (out / "scalability.json").write_text(json.dumps(rows, indent=2) + "\n")
    if rows:
        with (out / "scalability.csv").open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
    lines = [
        "# Vest versus VPS scalability", "",
        "Measurements use a warm shared target cache, 10 workers, a 300 s limit, and Rust recursion limit 512.", "",
        "| Shape | Size | System | Generated SLOC | VCs | Verus (s) | Rust (s) | Verify wall (s) | SMT CPU (s) | Result |",
        "|---|---:|---|---:|---:|---:|---:|---:|---:|---|",
    ]
    for r in rows:
        def number(name: str) -> str:
            value = r[name]
            return "–" if value is None else f"{value:.2f}"
        lines.append(
            f'| {r["kind"]} | {r["size"]} | {r["system"]} | {r["generated_sloc"] or "–"} | '
            f'{r["verified_vcs"] or "–"} | {number("verus_seconds")} | {number("rust_seconds")} | '
            f'{number("verification_wall_seconds")} | {number("smt_cpu_seconds")} | {r["result"]} |'
        )
    report = "\n".join(lines) + "\n"
    (out / "scalability.md").write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()

