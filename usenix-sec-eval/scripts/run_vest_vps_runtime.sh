#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/vest-vps/$STAMP"
mkdir -p "$OUT"

{
    echo "revision=$(git -C "$ROOT/.." rev-parse HEAD)"
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "command=cargo bench --bench vest_vps -- --noplot --output-format bencher"
} > "$OUT/metadata.txt"

cd "$ROOT/harnesses/vest-vps-runtime"
/usr/bin/time -p cargo bench --bench vest_vps -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"
"$ROOT/scripts/record_criterion_throughput.sh" "$ROOT/harnesses/vest-vps-runtime/target/criterion" "$OUT/throughput.tsv" "vest_vps/"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"

cat "$OUT/stdout.log"
cat "$OUT/stderr.log"
echo "Raw runtime artifacts: $OUT"
