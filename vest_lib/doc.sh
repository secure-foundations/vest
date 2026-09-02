#!/usr/bin/env bash
set -euo pipefail

rustdoc_lints=()
if [[ "${1:-}" == "--strict" ]]; then
    # Rust's ordinary style lints do not understand all Verus expressions and
    # can suggest precedence-changing rewrites. Strict documentation mode is
    # therefore limited to diagnostics that describe the published docs.
    rustdoc_lints=(
        -D rustdoc::broken_intra_doc_links
        -D rustdoc::invalid_codeblock_attributes
    )
fi

if [[ -n "${VERUS_BIN_DIR:-}" ]]; then
    verus_bin_dir="$VERUS_BIN_DIR"
elif command -v verus >/dev/null 2>&1; then
    verus_bin_dir="$(cd "$(dirname "$(command -v verus)")" && pwd)"
else
    echo "error: verus is not on PATH and VERUS_BIN_DIR is not set" >&2
    exit 1
fi

if [[ -n "${VERUSDOC_BIN:-}" ]]; then
    verusdoc_bin="$VERUSDOC_BIN"
elif [[ -n "${VERUS:-}" && -x "$VERUS/target/debug/verusdoc" ]]; then
    verusdoc_bin="$VERUS/target/debug/verusdoc"
else
    echo "error: set VERUSDOC_BIN to a verusdoc executable" >&2
    echo "build it from the matching Verus source with: cargo build -p verusdoc" >&2
    exit 1
fi

version_json="$verus_bin_dir/version.json"
if [[ ! -f "$version_json" ]]; then
    echo "error: $verus_bin_dir does not look like a Verus release directory" >&2
    exit 1
fi

toolchain="$(python3 -c 'import json, sys; print(json.load(open(sys.argv[1]))["verus"]["toolchain"])' "$version_json")"
if ! rustup toolchain list | cut -d' ' -f1 | grep -Fxq "$toolchain"; then
    rustup toolchain install "$toolchain"
fi

case "$(uname -s)" in
    Darwin) dynamic_library_extension=dylib ;;
    Linux) dynamic_library_extension=so ;;
    *) echo "error: unsupported platform $(uname -s)" >&2; exit 1 ;;
esac

echo "Generating vest_lib documentation with Verus toolchain $toolchain..."
rm -rf doc
RUSTC_BOOTSTRAP=1 \
VERUSDOC=1 \
VERUS_Z3_PATH="$verus_bin_dir/z3" \
rustup run "$toolchain" rustdoc \
    --crate-name vest_lib \
    --crate-type lib \
    --edition=2021 \
    --out-dir doc \
    -L "dependency=$verus_bin_dir" \
    --extern "vstd=$verus_bin_dir/libvstd.rlib" \
    --extern "verus_builtin=$verus_bin_dir/libverus_builtin.rlib" \
    --extern "verus_builtin_macros=$verus_bin_dir/libverus_builtin_macros.$dynamic_library_extension" \
    --extern "verus_state_machines_macros=$verus_bin_dir/libverus_state_machines_macros.$dynamic_library_extension" \
    --cfg verus_keep_ghost \
    --cfg verus_keep_ghost_body \
    --cfg 'feature="std"' \
    --cfg 'feature="alloc"' \
    -Zcrate-attr='feature(stmt_expr_attributes)' \
    -Zcrate-attr='feature(negative_impls)' \
    -Zcrate-attr='feature(register_tool)' \
    -Zcrate-attr='feature(rustc_attrs)' \
    -Zcrate-attr='feature(unboxed_closures)' \
    -Zcrate-attr='feature(never_type)' \
    -Zcrate-attr='register_tool(verus)' \
    -Zcrate-attr='register_tool(verifier)' \
    -Zcrate-attr='register_tool(verusfmt)' \
    -Zcrate-attr='allow(internal_features)' \
    -Zcrate-attr='allow(unused_braces)' \
    -Zproc-macro-backtrace \
    ${rustdoc_lints[@]+"${rustdoc_lints[@]}"} \
    src/lib.rs

echo "Post-processing documentation with verusdoc..."
"$verusdoc_bin"
echo "Documentation generated at vest_lib/doc/vest_lib/index.html"
