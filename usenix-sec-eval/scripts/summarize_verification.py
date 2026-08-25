#!/usr/bin/env python3
"""Summarize Verus JSON logs without discarding their timing breakdown."""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path


def newest_logs(eval_root: Path) -> list[tuple[str, Path, Path | None]]:
    logs: list[tuple[str, Path, Path | None]] = []
    backend_runs = sorted((eval_root / "results/raw/backend-verify").glob("*/stdout.log"))
    if backend_runs:
        logs.append(("VPS backend", backend_runs[-1], None))
    verification = eval_root / "results/raw/verification"
    selected = {
        "vest-bitcoin": "Vest Bitcoin",
        "vps-bitcoin-isolated": "VPS Bitcoin",
        "vest-tls": "Vest TLS",
        "vps-tls-isolated": "VPS TLS",
    }
    if verification.exists():
        for directory, display in selected.items():
            label = verification / directory
            runs = sorted(label.glob("*/stdout.log"))
            if runs:
                logs.append((display, runs[-1], runs[-1].with_name("metadata.json")))
    return logs


def row(label: str, log: Path, metadata: Path | None) -> dict[str, object]:
    contents = log.read_text()
    first_report = contents.find("{")
    if first_report < 0:
        raise ValueError(f"no Verus JSON report in {log}")
    contents = contents[first_report:]
    decoder = json.JSONDecoder()
    reports = []
    offset = 0
    while offset < len(contents):
        while offset < len(contents) and contents[offset].isspace():
            offset += 1
        if offset < len(contents):
            report, offset = decoder.raw_decode(contents, offset)
            reports.append(report)
    if len(reports) != 1:
        raise ValueError(f"expected one Verus report in {log}, found {len(reports)}")
    report = reports[0]
    times = report["times-ms"]
    verification = report["verification-results"]
    wall = None
    if metadata and metadata.exists():
        wall = json.loads(metadata.read_text())["wall_seconds"]
    elif (stderr := log.with_name("stderr.log")).exists():
        match = re.search(r"^real ([0-9.]+)$", stderr.read_text(), re.M)
        if match:
            wall = float(match.group(1))
    return {
        "label": label,
        "verified_vcs": verification["verified"],
        "errors": verification["errors"],
        "wall_seconds": wall,
        "verus_total_seconds": times["total"] / 1000,
        "rust_seconds": times["rust"]["total"] / 1000,
        "verification_wall_seconds": times["verification"]["total"] / 1000,
        "verification_cpu_seconds": times["total-verify"] / 1000,
        "smt_cpu_seconds": times["smt"]["total"] / 1000,
        "threads": times["num-threads"],
        "verus_version": report["verus"]["version"],
        "log": str(log.relative_to(log.parents[4])),
    }


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    rows = [row(*entry) for entry in newest_logs(root)]
    out = root / "results/derived"
    out.mkdir(exist_ok=True)
    (out / "verification.json").write_text(json.dumps(rows, indent=2) + "\n")
    if rows:
        with (out / "verification.csv").open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
    lines = [
        "# Verification summary", "",
        "| Target | VCs | Errors | Wall (s) | Rust (s) | Verify wall (s) | Verify CPU (s) | SMT CPU (s) |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for r in rows:
        wall = "–" if r["wall_seconds"] is None else f'{r["wall_seconds"]:.2f}'
        lines.append(
            f'| {r["label"]} | {r["verified_vcs"]} | {r["errors"]} | {wall} | '
            f'{r["rust_seconds"]:.2f} | {r["verification_wall_seconds"]:.2f} | '
            f'{r["verification_cpu_seconds"]:.2f} | {r["smt_cpu_seconds"]:.2f} |'
        )
    text = "\n".join(lines) + "\n"
    (out / "verification.md").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
