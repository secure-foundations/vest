#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
OUT="$ROOT/results/raw/machine-info.txt"
mkdir -p "$(dirname "$OUT")"

{
    echo "timestamp_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "vest_revision=$(git -C "$ROOT/.." rev-parse HEAD)"
    echo "vest_dirty=$(test -n "$(git -C "$ROOT/.." status --porcelain)" && echo true || echo false)"
    echo "uname=$(uname -a)"
    if command -v sysctl >/dev/null 2>&1; then
        echo "cpu=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || true)"
        echo "logical_cpus=$(sysctl -n hw.logicalcpu 2>/dev/null || true)"
        echo "memory_bytes=$(sysctl -n hw.memsize 2>/dev/null || true)"
    fi
    if command -v system_profiler >/dev/null 2>&1; then
        system_profiler SPHardwareDataType 2>/dev/null \
            | sed -n -e 's/^[[:space:]]*Model Identifier: /model_identifier=/p' \
                     -e 's/^[[:space:]]*Chip: /chip=/p' \
                     -e 's/^[[:space:]]*Total Number of Cores: /cores=/p' \
                     -e 's/^[[:space:]]*Memory: /memory=/p'
    fi
    echo "rustc=$(rustc --version)"
    echo "cargo=$(cargo --version)"
    echo "verus_metadata_begin"
    verus --version --output-json 2>&1
    echo "verus_metadata_end"
} > "$OUT"

cat "$OUT"
