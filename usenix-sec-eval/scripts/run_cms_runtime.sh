#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/cms/$STAMP"
mkdir -p "$OUT"
{
    echo "revision=$(git -C "$ROOT/.." rev-parse HEAD)"
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "command=cargo bench --bench cms_content_info -- --noplot --output-format bencher"
} > "$OUT/metadata.txt"
cd "$ROOT/harnesses/asn1-runtime"
/usr/bin/time -p cargo bench --bench cms_content_info -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"
"$ROOT/scripts/record_criterion_throughput.sh" "$ROOT/harnesses/asn1-runtime/target/criterion" "$OUT/throughput.tsv" "cms_content_info/"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"
cat "$OUT/stdout.log"
echo "Raw CMS runtime artifacts: $OUT"
