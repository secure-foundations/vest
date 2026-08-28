#!/usr/bin/env python3
"""Render runtime bars with Criterion's estimated timing standard deviation."""

from __future__ import annotations

import json
import math
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
os.environ.setdefault("MPLCONFIGDIR", str(ROOT / "results/.matplotlib"))
os.environ.setdefault("XDG_CACHE_HOME", str(ROOT / "results/.cache"))
os.environ.setdefault("MPLBACKEND", "Agg")

import matplotlib.pyplot as plt


def panels(rows: list[dict], default_domain: str) -> list[tuple[str, list[dict]]]:
    grouped: dict[tuple[str, str], list[dict]] = {}
    for row in rows:
        key = (row.get("domain", default_domain), row["operation"])
        grouped.setdefault(key, []).append(row)
    return [(f"{domain} — {operation}", group) for (domain, operation), group in grouped.items()]


def plot(source: Path, destination: Path, default_domain: str) -> None:
    groups = panels(json.loads(source.read_text()), default_domain)
    columns = min(3, len(groups))
    rows = math.ceil(len(groups) / columns)
    fig, axes = plt.subplots(rows, columns, figsize=(4.1 * columns, 3.2 * rows), squeeze=False)
    for axis, (title, measurements) in zip(axes.flat, groups):
        labels = [row["system"] for row in measurements]
        rates = [row["mib_per_second"] for row in measurements]
        # Criterion's bencher report prints the median point estimate and the
        # bootstrap standard-deviation point estimate. Transform t ± sigma
        # through throughput = bytes/t; the resulting errors are asymmetric.
        lower_errors = []
        upper_errors = []
        for row in measurements:
            median = row["nanoseconds"]
            std_dev = row["std_dev_nanoseconds"]
            rate = row["mib_per_second"]
            lower_rate = rate * median / (median + std_dev)
            upper_rate = rate * median / max(1, median - std_dev)
            lower_errors.append(rate - lower_rate)
            upper_errors.append(upper_rate - rate)
        errors = [lower_errors, upper_errors]
        axis.bar(labels, rates, yerr=errors, capsize=3, color="#4472c4", alpha=0.9)
        axis.set_title(title, fontsize=9)
        axis.set_ylabel("MiB/s")
        axis.tick_params(axis="x", labelrotation=35, labelsize=8)
        axis.grid(axis="y", alpha=0.25)
    for axis in list(axes.flat)[len(groups):]:
        axis.remove()
    fig.tight_layout()
    fig.savefig(destination, bbox_inches="tight")
    plt.close(fig)


def main() -> None:
    root = ROOT
    derived = root / "results/derived"
    figures = root / "results/figures"
    figures.mkdir(exist_ok=True)
    for stem, domain in [
        ("vest_vps_runtime", "Vest/VPS"),
        ("asn1_cms_runtime", "ASN.1/CMS"),
        ("cbor_runtime", "CBOR"),
    ]:
        source = derived / f"{stem}.json"
        if source.exists():
            plot(source, figures / f"{stem}.pdf", domain)


if __name__ == "__main__":
    main()
