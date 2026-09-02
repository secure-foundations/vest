#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
install_dir="${VERUS_INSTALL_DIR:-$repo_root/.verus}"
release_metadata="$repo_root/verus.json"

if [[ -z "$install_dir" || "$install_dir" == "/" || "$install_dir" == "." ]]; then
  echo "Refusing unsafe VERUS_INSTALL_DIR: ${install_dir:-<empty>}" >&2
  exit 1
fi
if [[ ! -r "$release_metadata" ]]; then
  echo "Missing Verus release metadata: $release_metadata" >&2
  exit 1
fi

version="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["version"])' "$release_metadata")"
expected_commit="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["commit"])' "$release_metadata")"
expected_rust="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["rust"])' "$release_metadata")"
if [[ ! "$version" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]]; then
  echo "Invalid Verus version in $release_metadata: $version" >&2
  exit 1
fi
if [[ ! "$expected_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo "Invalid Verus commit in $release_metadata: $expected_commit" >&2
  exit 1
fi
if [[ ! "$expected_rust" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "Invalid Rust version in $release_metadata: $expected_rust" >&2
  exit 1
fi

metadata_field() {
  python3 -c \
    'import json, sys; print(json.load(open(sys.argv[1]))["verus"][sys.argv[2]])' \
    "$1/version.json" "$2"
}

complete_install() {
  local dir="$1"
  [[ -x "$dir/verus" ]] &&
    [[ -x "$dir/cargo-verus" ]] &&
    [[ -x "$dir/z3" ]] &&
    [[ -f "$dir/version.json" ]] &&
    [[ "$(metadata_field "$dir" version 2>/dev/null)" == "$version" ]] &&
    [[ "$(metadata_field "$dir" commit 2>/dev/null)" == "$expected_commit" ]]
}

valid_install() {
  local dir="$1"
  complete_install "$dir" &&
    [[ -f "$dir/.vest-archive-sha256" ]] &&
    [[ "$(tr -d '[:space:]' < "$dir/.vest-archive-sha256")" == "$expected_checksum" ]]
}

install_toolchain() {
  local toolchain
  toolchain="$(metadata_field "$1" toolchain)"
  if [[ ! "$toolchain" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]]; then
    echo "The Verus metadata names an invalid Rust toolchain: $toolchain" >&2
    return 1
  fi
  if [[ "$toolchain" != "$expected_rust" && "$toolchain" != "$expected_rust-"* ]]; then
    echo "Verus requires $toolchain, but $release_metadata records Rust $expected_rust." >&2
    return 1
  fi
  if ! rustup run "$toolchain" rustc --version >/dev/null 2>&1; then
    rustup toolchain install "$toolchain" --profile minimal
  fi
}

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
expected_checksum="$(python3 -c \
  'import json, sys; print(json.load(open(sys.argv[1]))["artifacts"][sys.argv[2]]["sha256"])' \
  "$release_metadata" "$asset" 2>/dev/null || true)"
if [[ ! "$expected_checksum" =~ ^[0-9a-f]{64}$ ]]; then
  echo "No valid SHA-256 checksum is recorded for $archive." >&2
  exit 1
fi

if valid_install "$install_dir"; then
  install_toolchain "$install_dir"
  echo "Verus ${version} is already installed in $install_dir"
  exit 0
fi

url="https://github.com/verus-lang/verus/releases/download/release/${version}/${archive}"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

echo "Downloading Verus ${version} for ${asset}..."
curl --proto '=https' --tlsv1.2 --fail --location \
  --retry 5 --retry-delay 2 --retry-all-errors \
  "$url" -o "$tmp_dir/verus.zip"

actual_checksum="$(shasum -a 256 "$tmp_dir/verus.zip" | awk '{ print $1 }')"
if [[ "$actual_checksum" != "$expected_checksum" ]]; then
  echo "SHA-256 mismatch for $archive." >&2
  echo "Expected: $expected_checksum" >&2
  echo "Actual:   $actual_checksum" >&2
  exit 1
fi

unzip -q "$tmp_dir/verus.zip" -d "$tmp_dir/unpack"

release_dir="$(find "$tmp_dir/unpack" -mindepth 1 -maxdepth 2 -type f -name verus -print -quit)"
if [[ -z "$release_dir" ]]; then
  echo "The Verus archive did not contain the expected executable." >&2
  exit 1
fi
release_dir="$(dirname "$release_dir")"

if ! complete_install "$release_dir"; then
  echo "The downloaded archive is incomplete or does not match Verus ${version}." >&2
  exit 1
fi
printf '%s\n' "$expected_checksum" > "$release_dir/.vest-archive-sha256"

mkdir -p "$(dirname "$install_dir")"
rm -rf "$install_dir"
mv "$release_dir" "$install_dir"

if [[ "$(uname -s)" == Darwin && -f "$install_dir/macos_allow_gatekeeper.sh" ]]; then
  bash "$install_dir/macos_allow_gatekeeper.sh" || true
fi

install_toolchain "$install_dir"

echo "Installed Verus ${version} in $install_dir"
echo "Add it to this shell with: export PATH=\"$install_dir:\$PATH\""
