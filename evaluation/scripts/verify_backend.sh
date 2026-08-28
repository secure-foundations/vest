#!/bin/sh
set -eu

THREADS=${1:-10}
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
CRATE="$ROOT/../vps-lib"
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUTDIR="$ROOT/results/raw/backend-verify/$STAMP"
mkdir -p "$OUTDIR"

touch "$CRATE/src/lib.rs"

{
    echo "command=cargo verus verify --fwd-verus-args-to roots -- --time-expanded --output-json --num-threads $THREADS"
    echo "threads=$THREADS"
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
} > "$OUTDIR/metadata.txt"

cd "$CRATE"
/usr/bin/time -p cargo verus verify --fwd-verus-args-to roots -- \
    --time-expanded --output-json --num-threads "$THREADS" \
    > "$OUTDIR/stdout.log" 2> "$OUTDIR/stderr.log"

echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUTDIR/metadata.txt"
cat "$OUTDIR/stderr.log"
echo "Raw verification artifacts: $OUTDIR"
