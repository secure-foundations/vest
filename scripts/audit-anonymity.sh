#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"

failed=false

check() {
    description=$1
    pattern=$2
    if git grep -n -I -i -E "$pattern" -- . \
        ':(exclude)scripts/audit-anonymity.sh' \
        ':(exclude)baselines/vest-dsl/Cargo.lock'; then
        echo "anonymity audit failed: $description" >&2
        failed=true
    fi
}

check "local filesystem identity" '(/Users/|/home/[^/<[:space:]]+/|Research/repos/)'
check "first-party identity or organization" '(secure[- ]foundations|github\.com/secure-foundations|yicai)'
check "pre-anonymization crate names" '(^|[^[:alnum:]_])(vest_lib2|vest2|vestasn1|usenix-sec-eval)([^[:alnum:]_]|$)'
check "recorded source-tree Git state" '^(vest_revision|vest_dirty|repo_revision|repo_dirty|git_dirty|revision=)'

if [ "$failed" = true ]; then
    exit 1
fi

echo "Anonymity audit passed."
