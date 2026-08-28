#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
REPO=$(CDPATH= cd -- "$ROOT/.." && pwd)
OUT="$ROOT/results/raw/artifact-manifest.txt"

hash_file() {
    rel=$1
    if [ -f "$REPO/$rel" ]; then
        hash=$(shasum -a 256 "$REPO/$rel" | awk '{print $1}')
        printf '%s  %s\n' "$hash" "$rel"
    fi
}

{
    echo "generated_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "vstd_versions:"
    sed -n '/vstd[[:space:]]*=/p' "$REPO/baselines/vest-lib/Cargo.toml"
    sed -n '/vstd[[:space:]]*=/p' "$REPO/vps-lib/Cargo.toml"
    echo "sha256:"
    hash_file baselines/vest-lib/Cargo.toml
    hash_file baselines/vest-dsl/tls/Cargo.toml
    hash_file baselines/vest-dsl/bitcoin/Cargo.toml
    hash_file vest-dsl-vps/test/Cargo.toml
    hash_file vest-dsl-vps/test/src/tls.vest
    hash_file vest-dsl-vps/test/src/bitcoin.vest
    hash_file vest-dsl-vps/test/bench_data/tls/tranco_handshakes.rs
    hash_file evaluation/harnesses/vps-bitcoin-verify/src/bitcoin.rs
    hash_file evaluation/harnesses/vps-tls-verify/src/tls.rs
    hash_file evaluation/schemas/runtime-record.asn1
    hash_file vps-asn1/rfcs/CMS-RFC5652-Curated.asn1
    hash_file evaluation/harnesses/vest-vps-runtime/Cargo.lock
    hash_file evaluation/harnesses/vest-vps-runtime/benches/vest_vps.rs
    hash_file evaluation/harnesses/cbor-runtime/Cargo.lock
    hash_file evaluation/harnesses/cbor-runtime/benches/generic_cbor.rs
    hash_file evaluation/harnesses/asn1-runtime/Cargo.lock
    hash_file evaluation/harnesses/asn1-runtime/benches/asn1_record.rs
    hash_file evaluation/harnesses/asn1-runtime/benches/cms_content_info.rs
    hash_file evaluation/harnesses/asn1-runtime/benches/cms_real_signed_data.rs
    hash_file evaluation/harnesses/cbor-runtime/benches/real_cose.rs
    find "$ROOT/corpora" -type f | sort | while IFS= read -r file; do
        rel=${file#"$REPO/"}
        hash=$(shasum -a 256 "$file" | awk '{print $1}')
        printf '%s  %s\n' "$hash" "$rel"
    done
} > "$OUT"

cat "$OUT"
