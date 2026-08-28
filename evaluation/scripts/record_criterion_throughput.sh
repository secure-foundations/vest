#!/bin/sh
set -eu

CRITERION=$1
OUT=$2
PREFIX=$3

{
    printf 'group\tbytes\n'
    find "$CRITERION" -path '*/VPS/new/benchmark.json' -type f | sort |
        while IFS= read -r benchmark; do
            json=$(cat "$benchmark")
            group=$(printf '%s\n' "$json" | sed -E 's/.*"group_id":"([^"]+)".*/\1/')
            bytes=$(printf '%s\n' "$json" | sed -nE 's/.*"throughput":\{"Bytes":([0-9]+)\}.*/\1/p')
            if [ -n "$bytes" ] && [ "${group#"$PREFIX"}" != "$group" ]; then
                printf '%s\t%s\n' "$group" "$bytes"
            fi
        done
} > "$OUT"
