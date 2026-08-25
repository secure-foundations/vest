#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
REPO="$ROOT/.."
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
    echo "revision=$(git -C "$REPO" rev-parse HEAD)"
    echo "dirty=$(test -n "$(git -C "$REPO" status --porcelain)" && echo true || echo false)"
    echo "vstd_versions:"
    sed -n '/vstd[[:space:]]*=/p' "$REPO/vest/Cargo.toml"
    sed -n '/vstd[[:space:]]*=/p' "$REPO/vest_lib2/Cargo.toml"
    echo "sha256:"
    hash_file vest/Cargo.toml
    hash_file vest-dsl/tls/Cargo.toml
    hash_file vest-dsl/bitcoin/Cargo.toml
    hash_file vest2/test/Cargo.toml
    hash_file vest2/test/src/tls.vest
    hash_file vest2/test/src/bitcoin.vest
    hash_file usenix-sec-eval/harnesses/vps-bitcoin-verify/src/bitcoin.rs
    hash_file usenix-sec-eval/harnesses/vps-tls-verify/src/tls.rs
    hash_file usenix-sec-eval/schemas/runtime-record.asn1
    hash_file vestasn1/rfcs/CMS-RFC5652-Curated.asn1
    hash_file usenix-sec-eval/harnesses/vest-vps-runtime/Cargo.lock
    hash_file usenix-sec-eval/harnesses/vest-vps-runtime/benches/vest_vps.rs
    hash_file usenix-sec-eval/harnesses/cbor-runtime/Cargo.lock
    hash_file usenix-sec-eval/harnesses/cbor-runtime/benches/generic_cbor.rs
    hash_file usenix-sec-eval/harnesses/asn1-runtime/Cargo.lock
    hash_file usenix-sec-eval/harnesses/asn1-runtime/benches/asn1_record.rs
    hash_file usenix-sec-eval/harnesses/asn1-runtime/benches/cms_content_info.rs
    hash_file usenix-sec-eval/harnesses/asn1-runtime/benches/cms_real_signed_data.rs
    hash_file usenix-sec-eval/harnesses/cbor-runtime/benches/real_cose.rs
    find "$ROOT/corpora" -type f | sort | while IFS= read -r file; do
        rel=${file#"$REPO/"}
        hash=$(shasum -a 256 "$file" | awk '{print $1}')
        printf '%s  %s\n' "$hash" "$rel"
    done
} > "$OUT"

cat "$OUT"
