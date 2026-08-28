#!/bin/sh
set -eu

THREADS=${1:-10}
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
REPO="$ROOT/.."
RUN="$ROOT/scripts/run_verification.py"

cmp "$REPO/vest-dsl-vps/test/src/bitcoin.rs" "$ROOT/harnesses/vps-bitcoin-verify/src/bitcoin.rs" || {
    echo "isolated VPS Bitcoin fixture is stale; copy the regenerated bitcoin.rs first" >&2
    exit 1
}
cmp "$REPO/vest-dsl-vps/test/src/tls.rs" "$ROOT/harnesses/vps-tls-verify/src/tls.rs" || {
    echo "isolated VPS TLS fixture is stale; copy the regenerated tls.rs first" >&2
    exit 1
}

python3 "$RUN" vest-bitcoin "$REPO/baselines/vest-dsl/bitcoin" --module vest_bitcoin --threads "$THREADS"
python3 "$RUN" vps-bitcoin "$ROOT/harnesses/vps-bitcoin-verify" --module bitcoin --threads "$THREADS"
python3 "$RUN" vest-tls "$REPO/baselines/vest-dsl/tls" --module tls_combinators --threads "$THREADS"
python3 "$RUN" vps-tls "$ROOT/harnesses/vps-tls-verify" --module tls --threads "$THREADS"
