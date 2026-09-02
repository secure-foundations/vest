#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
required_mdbook="mdbook v0.5.4"

if ! command -v mdbook >/dev/null 2>&1; then
  echo "error: mdbook is not installed" >&2
  echo "install it with: cargo install mdbook --version 0.5.4 --locked" >&2
  exit 1
fi

installed_mdbook="$(mdbook --version)"
if [[ "$installed_mdbook" != "$required_mdbook" ]]; then
  echo "error: expected $required_mdbook, found $installed_mdbook" >&2
  exit 1
fi

mdbook build "$repo_root"
touch "$repo_root/docs/.nojekyll"

