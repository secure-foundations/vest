#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/cbor/$STAMP"
mkdir -p "$OUT"
{
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "command=cargo bench --bench generic_cbor -- --noplot --output-format bencher"
} > "$OUT/metadata.txt"
cd "$ROOT/harnesses/cbor-runtime"
/usr/bin/time -p cargo bench --bench generic_cbor -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"
"$ROOT/scripts/record_criterion_throughput.sh" "$ROOT/harnesses/cbor-runtime/target/criterion" "$OUT/throughput.tsv" "generic_cbor/"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"
cat "$OUT/stdout.log"
echo "Raw CBOR runtime artifacts: $OUT"
