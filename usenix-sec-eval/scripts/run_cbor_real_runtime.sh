#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/cbor-real/$STAMP"
mkdir -p "$OUT"
{
    echo "revision=$(git -C "$ROOT/.." rev-parse HEAD)"
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "source=cose-wg/Examples@53c9d634333bb4f529d78f5980fffa2667ee2c12"
    echo "command=cargo bench --bench real_cose -- --noplot --output-format bencher"
} > "$OUT/metadata.txt"
cd "$ROOT/harnesses/cbor-runtime"
/usr/bin/time -p cargo bench --bench real_cose -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"
"$ROOT/scripts/record_criterion_throughput.sh" "$ROOT/harnesses/cbor-runtime/target/criterion" "$OUT/throughput.tsv" "real_cose_cbor/"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"
cat "$OUT/stdout.log"
echo "Raw real CBOR runtime artifacts: $OUT"
