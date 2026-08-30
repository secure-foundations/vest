//! ASN.1 schema parser and Rust code generator
//!
//! This library parses ASN.1 module definitions and generates Rust code
//! using the `synta` library's derive macros.
//!
//! # Quick start
//!
//! ```no_run
//! use synta_codegen::{parse, generate};
//!
//! let schema = r#"
//!     Certificate DEFINITIONS ::= BEGIN
//!         Certificate ::= SEQUENCE {
//!             version INTEGER,
//!             serialNumber INTEGER
//!         }
//!     END
//! "#;
//!
//! let module = parse(schema).unwrap();
//! let rust_code = generate(&module).unwrap();
//! println!("{}", rust_code);
//! ```
//!
//! # Configuration
//!
//! [`generate_with_config`] accepts a [`CodeGenConfig`] that controls several
//! aspects of the emitted code.
//!
//! ## Owned vs. borrowed string types
//!
//! By default all ASN.1 string and binary types (`OCTET STRING`, `BIT STRING`,
//! `UTF8String`, `PrintableString`, `IA5String`) are generated as **owned**
//! heap-allocating types (`OctetString`, `BitString`, …).  This is convenient
//! when constructing structs programmatically.
//!
//! For parse-only workloads (e.g. X.509 certificate inspection) you can switch
//! to **zero-copy borrowed** types (`OctetStringRef<'a>`, `BitStringRef<'a>`,
//! …) that borrow directly from the input buffer.  Structs that contain these
//! fields automatically gain a `'a` lifetime parameter.
//!
//! ```no_run
//! use synta_codegen::{parse, generate_with_config, CodeGenConfig, StringTypeMode};
//!
//! let schema = r#"
//!     Msg DEFINITIONS ::= BEGIN
//!         Msg ::= SEQUENCE {
//!             payload OCTET STRING,
//!             label   UTF8String
//!         }
//!     END
//! "#;
//!
//! let module = parse(schema).unwrap();
//! let config = CodeGenConfig {
//!     string_type_mode: StringTypeMode::Borrowed,
//!     ..Default::default()
//! };
//! // Emits:
//! //   pub struct Msg<'a> {
//! //       pub payload: OctetStringRef<'a>,
//! //       pub label: Utf8StringRef<'a>,
//! //   }
//! let rust_code = generate_with_config(&module, config).unwrap();
//! println!("{}", rust_code);
//! ```
//!
//! String types that have no zero-copy variant (`TeletexString`, `BmpString`,
//! `UniversalString`, `GeneralString`, `NumericString`, `VisibleString`) are
//! always emitted as owned types regardless of [`StringTypeMode`].
//!
//! Named bit strings (`BIT STRING { flag(0), … }`) are always emitted as
//! owned `BitString` because they are decoded into a concrete bit-field type.
//!
//! ## Derive macro gating
//!
//! By default every `Asn1Sequence` / `Asn1Set` / `Asn1Choice` derive and its
//! associated `asn1(…)` helper attributes are wrapped in
//! `#[cfg_attr(feature = "derive", …)]`.  This lets the consuming crate make
//! `synta-derive` an **optional** dependency controlled by a Cargo feature:
//!
//! ```toml
//! # Cargo.toml of the consuming crate (default behaviour)
//! [dependencies]
//! synta-derive = { version = "0.1", optional = true }
//!
//! [features]
//! derive = ["dep:synta-derive"]
//! ```
//!
//! Third-party crates that **always** depend on `synta-derive` and do not want
//! to expose a `derive` Cargo feature can use [`DeriveMode::Always`]:
//!
//! ```no_run
//! use synta_codegen::{parse, generate_with_config, CodeGenConfig, DeriveMode};
//!
//! let schema = r#"
//!     Msg DEFINITIONS ::= BEGIN
//!         Msg ::= SEQUENCE { id INTEGER }
//!     END
//! "#;
//!
//! let module = parse(schema).unwrap();
//! let config = CodeGenConfig {
//!     derive_mode: DeriveMode::Always,
//!     ..Default::default()
//! };
//! // Emits:
//! //   #[derive(Debug, Clone, PartialEq)]
//! //   #[derive(Asn1Sequence)]          ← no cfg_attr wrapper
//! //   pub struct Msg { pub id: Integer }
//! let rust_code = generate_with_config(&module, config).unwrap();
//! println!("{}", rust_code);
//! ```
//!
//! If the crate uses a feature name other than `"derive"`, pass it via
//! [`DeriveMode::Custom`]:
//!
//! ```no_run
//! use synta_codegen::{parse, generate_with_config, CodeGenConfig, DeriveMode};
//!
//! # let schema = "Msg DEFINITIONS ::= BEGIN Msg ::= SEQUENCE { id INTEGER } END";
//! # let module = parse(schema).unwrap();
//! let config = CodeGenConfig {
//!     derive_mode: DeriveMode::Custom("asn1-derive".to_string()),
//!     ..Default::default()
//! };
//! // Emits:
//! //   #[cfg_attr(feature = "asn1-derive", derive(Asn1Sequence))]
//! let rust_code = generate_with_config(&module, config).unwrap();
//! println!("{}", rust_code);
//! ```
//!
//! ## Import path prefix
//!
//! Use [`CodeGenConfig::with_crate_imports`], [`CodeGenConfig::with_super_imports`],
//! or [`CodeGenConfig::with_custom_prefix`] to emit `use` statements instead of
//! the default comment-only import annotations.
//!
//! ## Constrained INTEGER type selection
//!
//! When a top-level `INTEGER` type carries a value-range constraint (e.g.
//! `INTEGER (0..100)`), synta-codegen generates a newtype whose inner field is
//! the **smallest native Rust integer primitive** that covers the declared range,
//! rather than the arbitrary-precision `Integer` type:
//!
//! - Lower bound ≥ 0 → unsigned: `u8` (≤255), `u16` (≤65535), `u32` (≤4294967295), `u64`.
//! - Lower bound < 0 → signed: `i8`, `i16`, `i32`, `i64`.
//! - Unconstrained bounds (`MIN`/`MAX`, named values) → `i64`.
//!
//! Using a primitive type means the generated struct automatically derives
//! `Copy`, `PartialOrd`, and `Ord`, and avoids heap allocation.  For example,
//! `Percentage ::= INTEGER (0..100)` produces:
//!
//! ```text
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
//! pub struct Percentage(u8);
//!
//! impl Percentage {
//!     pub fn new(value: u8) -> Result<Self, &'static str> { ... }
//!     pub const fn new_unchecked(value: u8) -> Self { Percentage(value) }
//!     pub const fn get(&self) -> u8 { self.0 }
//!     pub fn into_inner(self) -> u8 { self.0 }
//! }
//! ```
//!
//! The equivalent C generation uses `uint8_t` / `uint16_t` / `uint32_t` /
//! `uint64_t` for non-negative ranges and `int8_t` / `int16_t` / `int32_t` /
//! `int64_t` for signed ranges.

pub mod ast;
pub mod c_cmake_codegen;
pub mod c_codegen;
pub mod c_impl_codegen;
pub mod c_meson_codegen;
pub mod codegen;
pub mod import_graph;
pub mod naming;
pub mod parser;

pub use ast::{Definition, Module, Type};
pub use c_cmake_codegen::{generate_cmake, CMakeConfig};
pub use c_codegen::{generate_c, generate_c_with_config, CCodeGenConfig};
pub use c_impl_codegen::{generate_c_impl, CImplConfig, PatternMode};
pub use c_meson_codegen::{generate_meson, MesonConfig};
pub use codegen::{generate, generate_with_config, CodeGenConfig, DeriveMode, StringTypeMode};
pub use import_graph::{detect_cycles, topological_order, ImportCycle};
pub use naming::module_file_stem;
pub use parser::{parse, ParseError};

/// Locate the `asn1/` schema directory containing the ASN.1 schemas.
///
/// Call this from a build script (`build.rs`) to obtain the path to the shared
/// ASN.1 schema files that ship with the `synta` package.  Three layouts are
/// checked in order:
///
/// 1. **Crate-local** — `<CARGO_MANIFEST_DIR>/asn1/` exists inside the calling
///    crate itself.  Handles self-contained crates that bundle their own schemas.
///
/// 2. **Workspace build** — the calling crate sits one level below the
///    workspace root where `asn1/` lives.  `../asn1` relative to
///    `CARGO_MANIFEST_DIR` is returned.
///
/// 3. **crates.io / registry build** — falls back to `cargo metadata` to find
///    the source location of the `synta` package and returns its `asn1/`
///    subdirectory.  The `synta` package is identified by its manifest
///    directory name: `"synta"` (workspace root) or `"synta-X.Y.Z"` (crates.io
///    registry entry, recognised by `"synta-"` followed by an ASCII digit).
///
/// # Panics
///
/// Panics if none of the three layouts yields a valid `asn1/` directory.
pub fn find_asn1_dir() -> std::path::PathBuf {
    let manifest_dir =
        std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect(
            "CARGO_MANIFEST_DIR not set — find_asn1_dir() must be called from a build script",
        ));

    // 1. Crate-local: asn1/ ships inside the calling crate itself.
    let local = manifest_dir.join("asn1");
    if local.is_dir() {
        return local;
    }

    // 2. Workspace: asn1/ is one level above the calling crate.
    let workspace = manifest_dir.join("../asn1");
    if workspace.is_dir() {
        return workspace;
    }

    // 3. crates.io / registry: use `cargo metadata` to locate the synta
    //    package and return its bundled asn1/ directory.
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    if let Some(asn1) = find_asn1_via_cargo_metadata(&cargo, &manifest_dir) {
        return asn1;
    }

    panic!(
        "Cannot locate the synta asn1/ schema directory.\n\
         Tried: {m}/asn1 (crate-local), ../asn1 (workspace), \
         and `cargo metadata` (crates.io).\n\
         CARGO_MANIFEST_DIR = {m:?}",
        m = manifest_dir.display()
    );
}

/// Use `cargo metadata` to find the `asn1/` directory inside the `synta`
/// package source tree.
///
/// Scans every `manifest_path` value in the metadata JSON and identifies the
/// `synta` package by the name of its containing directory: `"synta"` (when
/// the workspace root happens to be in a directory named `synta`) or
/// `"synta-X.Y.Z"` (the standard crates.io registry layout).
fn find_asn1_via_cargo_metadata(
    cargo: &str,
    manifest_dir: &std::path::Path,
) -> Option<std::path::PathBuf> {
    let output = std::process::Command::new(cargo)
        .args(["metadata", "--format-version=1", "--manifest-path"])
        .arg(manifest_dir.join("Cargo.toml"))
        .output()
        .ok()?;

    if !output.status.success() {
        return None;
    }

    let json = String::from_utf8(output.stdout).ok()?;

    // Cargo emits compact JSON; each manifest_path value appears as:
    //   "manifest_path":"/absolute/path/to/Cargo.toml"
    // We scan every occurrence and select the one whose parent directory is
    // named "synta" or "synta-<version>" (digit after the hyphen).
    let mp_prefix = r#""manifest_path":""#;
    let mut rest = json.as_str();
    while let Some(pos) = rest.find(mp_prefix) {
        let after = &rest[pos + mp_prefix.len()..];
        if let Some(end) = after.find('"') {
            // Unescape JSON backslash sequences (relevant on Windows).
            let path_str = after[..end].replace("\\\\", "\\").replace("\\/", "/");
            let manifest = std::path::PathBuf::from(&path_str);
            if let Some(dir) = manifest.parent() {
                let dir_name = dir.file_name().unwrap_or_default().to_string_lossy();
                let is_synta = dir_name == "synta"
                    || (dir_name.starts_with("synta-")
                        && dir_name["synta-".len()..]
                            .chars()
                            .next()
                            .is_some_and(|c| c.is_ascii_digit()));
                if is_synta {
                    let asn1 = dir.join("asn1");
                    if asn1.is_dir() {
                        return Some(asn1);
                    }
                }
            }
            rest = &rest[pos + mp_prefix.len() + end + 1..];
        } else {
            break;
        }
    }

    None
}

/// Parse ASN.1 schema and generate Rust code in one step
pub fn parse_and_generate(input: &str) -> Result<String, Box<dyn std::error::Error>> {
    let module = parse(input)?;
    let code = generate(&module)?;
    Ok(code)
}

/// Parse ASN.1 schema and generate C header in one step
pub fn parse_and_generate_c(input: &str) -> Result<String, Box<dyn std::error::Error>> {
    let module = parse(input)?;
    let code = generate_c(&module)?;
    Ok(code)
}

/// Parse ASN.1 schema and generate C implementation in one step
pub fn parse_and_generate_c_impl(
    input: &str,
    header_file: &str,
) -> Result<String, Box<dyn std::error::Error>> {
    let module = parse(input)?;
    let config = CImplConfig {
        header_file: header_file.to_string(),
        arena_mode: false,
        pattern_mode: Default::default(),
        with_containing: false,
    };
    let code = generate_c_impl(&module, config)?;
    Ok(code)
}
