#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/asn1/$STAMP"
mkdir -p "$OUT"
{
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "command=cargo bench --bench asn1_record -- --noplot --output-format bencher"
} > "$OUT/metadata.txt"
cd "$ROOT/harnesses/asn1-runtime"
/usr/bin/time -p cargo bench --bench asn1_record -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"
"$ROOT/scripts/record_criterion_throughput.sh" "$ROOT/harnesses/asn1-runtime/target/criterion" "$OUT/throughput.tsv" "asn1_"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"
cat "$OUT/stdout.log"
echo "Raw ASN.1 runtime artifacts: $OUT"
