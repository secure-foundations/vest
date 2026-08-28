#!/usr/bin/env python3
"""Summarize ASN.1 record and CMS ContentInfo runtime results."""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path


ASN1 = re.compile(
    r"^test asn1_(der|ber_common|ber_comprehensive|ber)/(parse|serialize)/"
    r"(VPS|rasn|RustCrypto-der|RustCrypto-ber) "
    r"\.\.\. bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$", re.M,
)
CMS = re.compile(
    r"^test cms_content_info/(parse|serialize)/(VPS|rasn-cms|RustCrypto-cms|cryptographic-message-syntax) "
    r"\.\.\. bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$", re.M,
)
CMS_REAL = re.compile(
    r"^test cms_corpus/(pkits|dss-cades|rfc4134|combined)/(parse|serialize)/"
    r"(VPS|rasn-cms|RustCrypto-cms) "
    r"\.\.\. bench:\s+([0-9]+) ns/iter \(\+/- ([0-9]+)\)$", re.M,
)


def newest(root: Path, domain: str) -> Path | None:
    runs = sorted((root / f"results/raw/runtime/{domain}").glob("*/stdout.log"))
    return runs[-1] if runs else None


def throughput_sizes(stdout: Path) -> dict[str, int]:
    path = stdout.with_name("throughput.tsv")
    if not path.exists():
        return {}
    with path.open(newline="") as f:
        return {row["group"]: int(row["bytes"]) for row in csv.DictReader(f, delimiter="\t")}


def asn1_corpus_sizes(stdout: Path) -> dict[str, int]:
    stderr = stdout.with_name("stderr.log").read_text()
    patterns = {
        "der": r"ASN\.1 DER corpus: \d+ values, (\d+) bytes",
        "ber_common": r"ASN\.1 BER common corpus: \d+ values, (\d+) bytes",
        "ber_comprehensive": r"ASN\.1 BER comprehensive corpus: \d+ values, (\d+) bytes",
    }
    return {name: int(re.search(pattern, stderr).group(1)) for name, pattern in patterns.items()}


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    rows = []
    asn1 = newest(root, "asn1")
    if asn1:
        corpus_sizes = asn1_corpus_sizes(asn1)
        exact_sizes = throughput_sizes(asn1)
        for rules, operation, system, ns, std_dev in ASN1.findall(asn1.read_text()):
            corpus_key = "ber_comprehensive" if rules == "ber" else rules
            group = {
                ("der", "parse"): "asn1_der/parse",
                ("der", "serialize"): "asn1_der/serialize",
                ("ber_common", "parse"): "asn1_ber_common/parse",
                ("ber_comprehensive", "parse"): "asn1_ber_comprehensive/parse",
                ("ber", "serialize"): "asn1_ber/serialize",
            }[(rules, operation)]
            corpus = exact_sizes.get(group, corpus_sizes[corpus_key])
            nanos = int(ns)
            domain = {
                "der": "ASN.1 DER",
                "ber_common": "ASN.1 BER common",
                "ber_comprehensive": "ASN.1 BER comprehensive",
                "ber": "ASN.1 BER normalized output",
            }[rules]
            rows.append({
                "domain": domain, "operation": operation, "system": system,
                "nanoseconds": nanos, "std_dev_nanoseconds": int(std_dev),
                "values": 1024, "bytes": corpus,
                "mib_per_second": corpus / (nanos / 1e9) / (1024 * 1024),
            })
    cms = newest(root, "cms")
    if cms:
        exact_sizes = throughput_sizes(cms)
        for operation, system, ns, std_dev in CMS.findall(cms.read_text()):
            nanos = int(ns)
            size = exact_sizes.get(f"cms_content_info/{operation}", 282954)
            rows.append({
                "domain": "CMS ContentInfo DER", "operation": operation, "system": system,
                "nanoseconds": nanos, "std_dev_nanoseconds": int(std_dev),
                "values": 1024, "bytes": size,
                "mib_per_second": size / (nanos / 1e9) / (1024 * 1024),
            })
    cms_real = newest(root, "cms-real")
    if cms_real:
        stderr = cms_real.with_name("stderr.log").read_text()
        corpus_meta = {
            name: (int(values), int(size))
            for name, values, size in re.findall(
                r"CMS (pkits|dss-cades|rfc4134|combined) corpus: (\d+) values, (\d+) bytes", stderr
            )
        }
        labels = {"pkits": "CMS NIST PKITS", "dss-cades": "CMS EC DSS CAdES",
                  "rfc4134": "CMS RFC 4134", "combined": "CMS combined real corpus"}
        throughput_file = cms_real.with_name("throughput.tsv")
        throughput = {}
        if throughput_file.exists():
            with throughput_file.open(newline="") as f:
                for row in csv.DictReader(f, delimiter="\t"):
                    throughput[(row["corpus"], row["operation"])] = int(row["bytes"])
        for corpus, operation, system, ns, std_dev in CMS_REAL.findall(cms_real.read_text()):
            nanos = int(ns)
            values, input_size = corpus_meta[corpus]
            size = throughput.get((corpus, operation), input_size)
            rows.append({
                "domain": labels[corpus], "operation": operation, "system": system,
                "nanoseconds": nanos, "std_dev_nanoseconds": int(std_dev),
                "values": values, "bytes": size,
                "mib_per_second": size / (nanos / 1e9) / (1024 * 1024),
            })
    if not rows:
        print("No ASN.1/CMS runtime results found.")
        return
    vps = {(r["domain"], r["operation"]): r for r in rows if r["system"] == "VPS"}
    for r in rows:
        r["relative_to_vps"] = vps[(r["domain"], r["operation"])]["nanoseconds"] / r["nanoseconds"]
    out = root / "results/derived"
    (out / "asn1_cms_runtime.json").write_text(json.dumps(rows, indent=2) + "\n")
    with (out / "asn1_cms_runtime.csv").open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=rows[0].keys(), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    lines = [
        "# ASN.1 and CMS runtime", "",
        "ASN.1 uses 1,024 typed records. The common BER corpus is accepted by all "
        "three parsers; the comprehensive corpus additionally exercises legal forms "
        "that RustCrypto's deliberately restricted BER decoder rejects. BER "
        "serialization reports normalized definite output. Synthetic CMS uses 1,024 `id-data` "
        "ContentInfo values. The real CMS rows use three independently attributed "
        "SignedData corpora: official NIST PKITS S/MIME cases, European Commission "
        "DSS CAdES fixtures, and RFC 4134 examples. Each row uses the exact common "
        "input intersection accepted by all three implementations. The combined rows "
        "are directly sampled over the concatenation of all three strata.", "",
        "| Domain | Operation | Implementation | Time | MiB/s | Throughput relative to VPS |",
        "|---|---|---|---:|---:|---:|",
    ]
    for r in rows:
        lines.append(
            f'| {r["domain"]} | {r["operation"]} | {r["system"]} | '
            f'{r["nanoseconds"] / 1e3:.2f} ± {r["std_dev_nanoseconds"] / 1e3:.2f} µs | {r["mib_per_second"]:.1f} | '
            f'{r["relative_to_vps"]:.2f}× |'
        )
    report = "\n".join(lines) + "\n"
    (out / "asn1_cms_runtime.md").write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
