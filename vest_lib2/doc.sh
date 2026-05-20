#! /bin/bash

set -e

RUSTDOC=""
if [ "x$1" = "x--strict" ]; then
    RUSTDOC="-D warnings"
fi

if [ -z "$VERUS" ]; then
    echo "Error: \$VERUS environment variable is not set." 1>&2
    echo "Please set it to the Verus source directory, e.g.:" 1>&2
    echo "  export VERUS=/path/to/verus/source" 1>&2
    exit 1
fi

# Detect the rustc version that vstd was compiled with, so we use the matching rustdoc
VSTD_RUSTC_VERSION=$(strings "$VERUS/target-verus/debug/libvstd.rlib" | grep -o 'rustc version [0-9.]*' | head -1 | sed 's/rustc version //')
if [ -n "$VSTD_RUSTC_VERSION" ]; then
    echo "Detected vstd compiled with rustc $VSTD_RUSTC_VERSION"
    VERUS_TOOLCHAIN="$VSTD_RUSTC_VERSION"
else
    # Fall back to rust-toolchain.toml
    TOOLCHAIN_FILE="$VERUS/../rust-toolchain.toml"
    if [ -f "$TOOLCHAIN_FILE" ]; then
        VERUS_TOOLCHAIN=$(grep 'channel' "$TOOLCHAIN_FILE" | sed 's/.*"\(.*\)".*/\1/')
        echo "Using Verus Rust toolchain from rust-toolchain.toml: $VERUS_TOOLCHAIN"
    else
        echo "Warning: Could not detect Verus rustc version, using default rustdoc" 1>&2
        VERUS_TOOLCHAIN=""
    fi
fi

case $(uname -m) in
  x86_64)
    ARCH=x86_64
    ;;
  arm64)
    ARCH=aarch64
    ;;
  *)
    echo "Unknown architecture $(uname -m)" 1>&2
    exit 1
    ;;
esac

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

# Use rustup run with the detected toolchain if available, otherwise plain rustdoc
if [ -n "$VERUS_TOOLCHAIN" ]; then
    RUSTDOC_CMD="rustup run $VERUS_TOOLCHAIN rustdoc"
else
    RUSTDOC_CMD="rustdoc"
fi

echo "Running rustdoc for vest-plus..."
RUSTC_BOOTSTRAP=1 eval ""VERUSDOC=1 VERUS_Z3_PATH="$(pwd)/z3"  $RUSTDOC_CMD \
  --crate-name vest_plus \
  -L dependency=$VERUS/target-verus/debug \
  -L dependency=$VERUS/target/debug/deps \
  --extern vstd=$VERUS/target-verus/debug/libvstd.rlib \
  --extern verus_builtin=$VERUS/target-verus/debug/libverus_builtin.rlib \
  --extern verus_builtin_macros=$VERUS/target-verus/debug/libverus_builtin_macros.$DYN_LIB_EXT \
  --extern verus_state_machines_macros=$VERUS/target-verus/debug/libverus_state_machines_macros.$DYN_LIB_EXT \
  --edition=2021 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature=\"std\"' \
  --cfg 'feature=\"alloc\"' \
  -Zcrate-attr=feature\\\(stmt_expr_attributes\\\) \
  -Zcrate-attr=feature\\\(negative_impls\\\) \
  -Zcrate-attr=feature\\\(register_tool\\\) \
  -Zcrate-attr=feature\\\(rustc_attrs\\\) \
  -Zcrate-attr=feature\\\(unboxed_closures\\\) \
  -Zcrate-attr=feature\\\(never_type\\\) \
  -Zcrate-attr=register_tool\\\(verus\\\) \
  -Zcrate-attr=register_tool\\\(verifier\\\) \
  -Zcrate-attr=register_tool\\\(verusfmt\\\) \
  -Zcrate-attr=allow\\\(internal_features\\\) \
  -Zcrate-attr=allow\\\(unused_braces\\\) \
  -Zproc-macro-backtrace \
  $RUSTDOC \
  ./src/lib.rs""

echo "Running post-processor..."
$VERUS/target/debug/verusdoc

echo "Documentation generated at ./doc/vest_plus/index.html"
