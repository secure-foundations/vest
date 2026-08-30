#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
version="$(tr -d '[:space:]' < "$repo_root/verus-version.txt")"
install_dir="${VERUS_INSTALL_DIR:-$repo_root/.verus}"

if [[ -x "$install_dir/verus" && -f "$install_dir/version.json" ]]; then
  installed_version="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["verus"]["version"])' "$install_dir/version.json")"
  if [[ "$installed_version" == "$version" ]]; then
    toolchain="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["verus"]["toolchain"])' "$install_dir/version.json")"
    rustup toolchain install "$toolchain"
    echo "Verus ${version} is already installed in $install_dir"
    exit 0
  fi
fi

case "$(uname -s):$(uname -m)" in
  Darwin:arm64) asset="arm64-macos" ;;
  Darwin:x86_64) asset="x86-macos" ;;
  Linux:x86_64) asset="x86-linux" ;;
  *)
    echo "No prebuilt Verus release is available for $(uname -s) $(uname -m)." >&2
    exit 1
    ;;
esac

archive="verus-${version}-${asset}.zip"
url="https://github.com/verus-lang/verus/releases/download/release/${version}/${archive}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

echo "Downloading Verus ${version} for ${asset}..."
curl -fL --retry 5 --retry-delay 2 --retry-all-errors \
  "$url" -o "$tmp_dir/verus.zip"
unzip -q "$tmp_dir/verus.zip" -d "$tmp_dir/unpack"

release_dir="$(find "$tmp_dir/unpack" -mindepth 1 -maxdepth 2 -type f -name verus -print -quit)"
if [[ -z "$release_dir" ]]; then
  echo "The Verus archive did not contain the expected executable." >&2
  exit 1
fi
release_dir="$(dirname "$release_dir")"

rm -rf "$install_dir"
mv "$release_dir" "$install_dir"

if [[ "$(uname -s)" == Darwin && -f "$install_dir/macos_allow_gatekeeper.sh" ]]; then
  bash "$install_dir/macos_allow_gatekeeper.sh" || true
fi

toolchain="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["verus"]["toolchain"])' "$install_dir/version.json")"
rustup toolchain install "$toolchain"

echo "Installed Verus ${version} in $install_dir"
echo "Add it to this shell with: export PATH=\"$install_dir:\$PATH\""
