#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
STAMP=$(date -u '+%Y%m%dT%H%M%SZ')
OUT="$ROOT/results/raw/runtime/cms-real/$STAMP"
mkdir -p "$OUT"
{
    echo "started_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "command=cargo bench --bench cms_real_signed_data -- --noplot --output-format bencher"
    find "$ROOT/corpora/cms" -name MANIFEST.tsv | sort | while IFS= read -r manifest; do
        shasum -a 256 "$manifest"
    done
} > "$OUT/metadata.txt"
cd "$ROOT/harnesses/asn1-runtime"
/usr/bin/time -p cargo bench --bench cms_real_signed_data -- --noplot --output-format bencher \
    > "$OUT/stdout.log" 2> "$OUT/stderr.log"

# Bencher output contains only time. Preserve Criterion's exact per-operation
# throughput denominator as a first-class raw artifact; BER normalization can
# make serialized output slightly shorter than the parsed input.
{
    printf 'corpus\toperation\tbytes\n'
    find "$ROOT/harnesses/asn1-runtime/target/criterion" -path '*/VPS/new/benchmark.json' -type f | sort |
        while IFS= read -r benchmark; do
            json=$(cat "$benchmark")
            group=$(printf '%s\n' "$json" | sed -E 's/.*"group_id":"([^"]+)".*/\1/')
            case "$group" in
                cms_corpus/*/parse|cms_corpus/*/serialize)
                    corpus=$(printf '%s\n' "$group" | cut -d/ -f2)
                    operation=$(printf '%s\n' "$group" | cut -d/ -f3)
                    bytes=$(printf '%s\n' "$json" | sed -E 's/.*"throughput":\{"Bytes":([0-9]+)\}.*/\1/')
                    printf '%s\t%s\t%s\n' "$corpus" "$operation" "$bytes"
                    ;;
            esac
        done
} > "$OUT/throughput.tsv"
echo "finished_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')" >> "$OUT/metadata.txt"
cat "$OUT/stdout.log"
echo "Raw real CMS runtime artifacts: $OUT"
