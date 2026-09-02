#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

"$repo_root/scripts/build-guide.sh"
(
  cd "$repo_root/vest_lib"
  ./doc.sh --strict
)

rustdoc_paths=(
  .lock
  crates.js
  help.html
  search.index
  settings.html
  src
  src-files.js
  static.files
  trait.impl
  type.impl
  vest_lib
)

for path in "${rustdoc_paths[@]}"; do
  rm -rf "$repo_root/docs/$path"
done
cp -R "$repo_root/vest_lib/doc/." "$repo_root/docs/"
touch "$repo_root/docs/.nojekyll"

