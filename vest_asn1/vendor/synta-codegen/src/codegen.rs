//! Rust code generator from ASN.1 AST

use crate::ast::*;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

/// Controls whether string and binary ASN.1 types are generated as owned
/// heap-allocating types or as zero-copy borrowed references.
///
/// The following ASN.1 types have both an owned form and a zero-copy `Ref`
/// variant and are therefore affected by this setting:
///
/// | ASN.1 type        | Owned (`Owned` mode)  | Borrowed (`Borrowed` mode) |
/// |-------------------|-----------------------|----------------------------|
/// | `OCTET STRING`    | `OctetString`         | `OctetStringRef<'a>`       |
/// | `BIT STRING`      | `BitString`           | `BitStringRef<'a>`         |
/// | `UTF8String`      | `Utf8String`          | `Utf8StringRef<'a>`        |
/// | `PrintableString` | `PrintableString`     | `PrintableStringRef<'a>`   |
/// | `IA5String`       | `IA5String`           | `IA5StringRef<'a>`         |
///
/// Types that have **no** zero-copy variant (`TeletexString`, `BmpString`,
/// `UniversalString`, `GeneralString`, `NumericString`, `VisibleString`) are
/// always emitted as owned types regardless of this setting.
///
/// Named bit strings (`BIT STRING { flag(0), … }`) are always emitted as
/// owned `BitString` regardless of this setting because they are decoded into
/// a concrete bit-field type.
///
/// - [`StringTypeMode::Owned`] (default): heap-allocates on decode; convenient
///   for constructing structs from scratch (e.g. in tests or protocol message
///   builders).
/// - [`StringTypeMode::Borrowed`]: borrows directly from the input buffer;
///   optimal for parse-only workloads such as X.509 certificate inspection.
///   Every struct that contains these fields (directly or transitively) gains a
///   `'a` lifetime parameter.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum StringTypeMode {
    /// Generate owned, heap-allocating types (`OctetString`, `BitString`, …).
    /// No lifetime parameter is added to generated structs.
    #[default]
    Owned,
    /// Generate zero-copy borrowed types (`OctetStringRef<'a>`, `BitStringRef<'a>`, …)
    /// that borrow from the decoder's input buffer.
    /// Structs containing these fields acquire a `'a` lifetime parameter.
    Borrowed,
}

/// Controls how derive macros for ASN.1 types are emitted in generated code.
///
/// The generated code uses `synta_derive` proc-macros (`Asn1Sequence`,
/// `Asn1Choice`, `Asn1Set`) as well as helper attributes (`asn1(tag(…))`,
/// `asn1(optional)`, `asn1(rawder)`).  By default these are wrapped in
/// `#[cfg_attr(feature = "derive", …)]` so that the consuming crate can make
/// `synta-derive` an optional dependency.  Third-party crates that always
/// depend on `synta-derive` can use [`DeriveMode::Always`] to emit the
/// attributes unconditionally, removing the need to declare a `derive`
/// Cargo feature.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum DeriveMode {
    /// Emit `#[cfg_attr(feature = "derive", derive(Asn1Sequence))]` (default).
    ///
    /// Derive macros and their helper attributes are gated behind a `derive`
    /// Cargo feature.  The consuming crate must declare
    /// `[features] derive = ["dep:synta-derive"]` (or similar) in its
    /// `Cargo.toml`.
    #[default]
    FeatureGated,
    /// Emit `#[derive(Asn1Sequence)]` unconditionally — no feature gate.
    ///
    /// Use this when the consuming crate always depends on `synta-derive`
    /// and does not want to expose a `derive` Cargo feature.
    Always,
    /// Emit `#[cfg_attr(feature = "<name>", derive(Asn1Sequence))]` with a
    /// custom feature name instead of `"derive"`.
    ///
    /// Useful when the consuming crate exposes its own feature name for
    /// derive support (e.g. `"asn1-derive"` or `"full"`).
    Custom(String),
}

/// Configuration options for code generation
#[derive(Debug, Clone, Default)]
pub struct CodeGenConfig {
    /// Module path prefix for imports (e.g., "crate", "super", or custom path)
    /// If None, imports are only documented in comments
    pub module_path_prefix: Option<String>,
    /// Emit `core::convert::TryFrom` instead of `std::convert::TryFrom`.
    /// Use this when generating code for `#![no_std]` environments.
    pub use_core: bool,
    /// Set of imported type names that should be skipped during code generation
    /// Types in this set are assumed to come from external modules
    pub skip_imported_types: std::collections::HashSet<String>,
    /// Map of imported type names to their lifetime requirements
    /// Key: type name, Value: lifetime parameter (e.g., "'a")
    /// If a type is not in this map, it's assumed to not require a lifetime
    pub imported_type_lifetimes: std::collections::HashMap<String, String>,
    /// Controls whether string/binary ASN.1 types (`OCTET STRING`, `BIT STRING`,
    /// `UTF8String`, `PrintableString`, `IA5String`) are generated as owned
    /// heap-allocating types or as zero-copy borrowed `Ref` variants.
    /// Defaults to [`StringTypeMode::Owned`].
    pub string_type_mode: StringTypeMode,
    /// When `true`, `ANY` and `ANY DEFINED BY` fields are generated as
    /// `RawDer<'a>` (zero-copy raw TLV capture) instead of `Element<'a>`.
    ///
    /// Use this for schemas where every open-typed field should be stored as raw
    /// bytes for lazy decoding rather than eagerly parsed into an `Element` tree.
    /// The generated type aliases and struct fields are then `RawDer<'a>`, which
    /// implements both `Decode<'a>` (reads any TLV) and `DecodeImplicit<'a>`
    /// (captures the value bytes of an IMPLICIT-tagged field).
    ///
    /// Defaults to `false`.
    pub any_as_raw_der: bool,
    /// Controls how derive macros (`Asn1Sequence`, `Asn1Choice`, `Asn1Set`)
    /// and their helper attributes are emitted.
    ///
    /// Defaults to [`DeriveMode::FeatureGated`], which wraps every derive
    /// annotation in `#[cfg_attr(feature = "derive", …)]`.  Set to
    /// [`DeriveMode::Always`] to emit them unconditionally, which removes the
    /// need for the consuming crate to declare a `derive` Cargo feature.
    pub derive_mode: DeriveMode,
    /// Set of field names (after `to_snake_case` conversion) that should be
    /// emitted as `RawDer<'a>` regardless of their ASN.1 type.
    ///
    /// Use this to defer decoding of expensive fields — such as `issuer`,
    /// `subject`, and `extensions` in an X.509 `TBSCertificate` — until the
    /// caller explicitly requests them.  The field is stored as a zero-copy
    /// TLV capture that can be decoded lazily.
    ///
    /// Fields listed here are always emitted with the `'a` lifetime, which
    /// is propagated to the enclosing struct declaration automatically.
    ///
    /// Defaults to an empty set (no override).
    pub raw_der_fields: std::collections::HashSet<String>,
    /// Set of type names that are known `CHOICE` types, even when they are
    /// defined in an imported (external) schema that is not available to this
    /// codegen invocation.
    ///
    /// Per ASN.1 X.680 §31.2.7, `IMPLICIT` tagging cannot be applied to
    /// `CHOICE` types; such tags must be treated as `EXPLICIT`.  When the
    /// `CHOICE` definition lives in another schema file the codegen cannot
    /// detect the tag-promotion requirement automatically.  Adding the type
    /// name here extends `resolves_to_choice()` so that imported `CHOICE`
    /// types are still promoted correctly.
    ///
    /// Example: `config.known_choice_types.insert("GeneralName".into());`
    ///
    /// Defaults to an empty set.
    pub known_choice_types: std::collections::HashSet<String>,
}

impl CodeGenConfig {
    /// Add a type that requires a lifetime parameter when imported
    pub fn with_lifetime(
        mut self,
        type_name: impl Into<String>,
        lifetime: impl Into<String>,
    ) -> Self {
        self.imported_type_lifetimes
            .insert(type_name.into(), lifetime.into());
        self
    }

    /// Configure common X.509 types that require lifetimes
    /// This also marks which types should be skipped (imported from external crates)
    /// vs which types should be generated locally
    pub fn with_x509_lifetimes(mut self) -> Self {
        // Types that are actually exported from synta-certificate and should be skipped
        let skip_types = vec![
            "AlgorithmIdentifier",
            "SubjectPublicKeyInfo",
            "TBSCertificate",
            "Certificate",
            "Validity", // Doesn't need lifetime but is imported
        ];

        // Imported types that need lifetime parameters (NOT locally-generated types)
        let types_with_lifetimes = vec![
            "AlgorithmIdentifier",
            "SubjectPublicKeyInfo",
            "TBSCertificate",
            "Certificate",
            // Note: Name and Extension are NOT in this list because they're defined
            // locally without lifetimes to match the auto-generated X.509 code
        ];

        for type_name in skip_types {
            self.skip_imported_types.insert(type_name.to_string());
        }

        for type_name in types_with_lifetimes {
            self.imported_type_lifetimes
                .insert(type_name.to_string(), "'a".to_string());
        }

        self
    }
}

impl CodeGenConfig {
    /// Create config with crate-relative imports
    pub fn with_crate_imports() -> Self {
        Self {
            module_path_prefix: Some("crate".to_string()),
            ..Default::default()
        }
    }

    /// Create config with super-relative imports
    pub fn with_super_imports() -> Self {
        Self {
            module_path_prefix: Some("super".to_string()),
            ..Default::default()
        }
    }

    /// Create config with custom module path prefix
    pub fn with_custom_prefix(prefix: impl Into<String>) -> Self {
        Self {
            module_path_prefix: Some(prefix.into()),
            ..Default::default()
        }
    }
}

/// Check if a name is a Rust keyword and needs escaping
fn is_rust_keyword(s: &str) -> bool {
    matches!(
        s,
        "as" | "break"
            | "const"
            | "continue"
            | "crate"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "Self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "async"
            | "await"
            | "dyn"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
            | "try"
    )
}

/// Escape a Rust identifier if it's a keyword
fn escape_rust_keyword(s: String) -> String {
    if is_rust_keyword(&s) {
        format!("r#{}", s)
    } else {
        s
    }
}

/// Convert ASN.1 identifier to Rust snake_case
fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut prev_lower = false;

    for (i, ch) in s.chars().enumerate() {
        if ch == '-' {
            result.push('_');
            prev_lower = false;
        } else if ch.is_uppercase() {
            if i > 0 && prev_lower {
                result.push('_');
            }
            result.push(ch.to_ascii_lowercase());
            prev_lower = false;
        } else {
            result.push(ch);
            prev_lower = ch.is_lowercase();
        }
    }

    escape_rust_keyword(result)
}

/// Convert ASN.1 identifier to Rust PascalCase.
///
/// Each hyphen-separated segment is capitalised independently.  If a segment
/// consists entirely of uppercase letters (and optional digits / other
/// non-letter characters), the non-first letter characters are lowercased so
/// that e.g. `KDC-REQ` becomes `KdcReq` rather than `KDCREQ`.  Mixed-case
/// segments such as `Kerberos` or `SafeBody` are left unchanged (only the
/// first character is forced to uppercase).
fn to_pascal_case(s: &str) -> String {
    s.split('-').map(pascal_segment).collect()
}

/// Capitalise one hyphen-separated segment for use in a PascalCase identifier.
fn pascal_segment(seg: &str) -> String {
    if seg.is_empty() {
        return String::new();
    }
    // A segment is "all-caps" when every *letter* character is uppercase.
    // Digits and other non-letter characters are neutral.
    let all_caps = seg.chars().all(|c| !c.is_alphabetic() || c.is_uppercase());
    let mut out = String::with_capacity(seg.len());
    for (i, c) in seg.chars().enumerate() {
        if i == 0 {
            out.push(c.to_ascii_uppercase());
        } else if all_caps && c.is_alphabetic() {
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

/// Convert ASN.1 identifier to Rust SCREAMING_SNAKE_CASE for constants
fn to_screaming_snake_case(s: &str) -> String {
    let mut result = String::new();
    let mut prev_lower = false;

    for (i, ch) in s.chars().enumerate() {
        if ch == '-' {
            result.push('_');
            prev_lower = false;
        } else if ch.is_ascii_uppercase() {
            if i > 0 && prev_lower {
                result.push('_');
            }
            result.push(ch);
            prev_lower = false;
        } else {
            result.push(ch.to_ascii_uppercase());
            prev_lower = true;
        }
    }

    result
}

/// Convert ASN.1 module name to Rust module name (snake_case)
fn module_name_to_rust(s: &str) -> String {
    // Delegate to to_snake_case so that Rust keywords are properly escaped
    // and the conversion logic stays in one place.
    to_snake_case(s)
}

/// Code generator
pub struct CodeGenerator {
    output: String,
    config: CodeGenConfig,
    pattern_counter: usize, // Counter for generating unique pattern names
    imported_types: HashSet<String>, // Set of imported type names for lifetime tracking
    types_with_lifetimes: HashSet<String>, // Set of type names that have been generated with <'a>
    type_definitions: HashMap<String, Type>, // Map of type names to their definitions for inlining
}

impl CodeGenerator {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            config: CodeGenConfig::default(),
            pattern_counter: 0,
            imported_types: HashSet::new(),
            types_with_lifetimes: HashSet::new(),
            type_definitions: HashMap::new(),
        }
    }

    pub fn with_config(config: CodeGenConfig) -> Self {
        Self {
            output: String::new(),
            config,
            pattern_counter: 0,
            imported_types: HashSet::new(),
            types_with_lifetimes: HashSet::new(),
            type_definitions: HashMap::new(),
        }
    }

    /// Return the crate path for `TryFrom`.
    ///
    /// Always returns `"core"` — `core::convert::TryFrom` is available in both
    /// `std` and `no_std` targets and is identical to `std::convert::TryFrom`.
    /// The `use_core` config field is retained for API compatibility.
    fn try_from_path(&self) -> &'static str {
        "core"
    }

    /// Return the Cargo feature name used to gate derive annotations, or `None`
    /// when [`DeriveMode::Always`] is active (no gating needed).
    fn derive_feature_name(&self) -> Option<&str> {
        match &self.config.derive_mode {
            DeriveMode::Always => None,
            DeriveMode::FeatureGated => Some("derive"),
            DeriveMode::Custom(name) => Some(name.as_str()),
        }
    }

    /// Format a top-level derive-gated attribute.
    ///
    /// - `Always` → `#[ATTR]`
    /// - `FeatureGated` → `#[cfg_attr(feature = "derive", ATTR)]`
    /// - `Custom(n)` → `#[cfg_attr(feature = "n", ATTR)]`
    fn derive_cfg_attr(&self, attr: &str) -> String {
        match self.derive_feature_name() {
            None => format!("#[{}]", attr),
            Some(feat) => format!("#[cfg_attr(feature = \"{}\", {})]", feat, attr),
        }
    }

    /// Format a field-level (4-space-indented) derive-gated attribute.
    fn field_derive_cfg_attr(&self, attr: &str) -> String {
        match self.derive_feature_name() {
            None => format!("    #[{}]", attr),
            Some(feat) => format!("    #[cfg_attr(feature = \"{}\", {})]", feat, attr),
        }
    }

    /// Check if module contains any PATTERN constraints
    fn has_pattern_constraints(&self, module: &Module) -> bool {
        for def in &module.definitions {
            if self.type_has_pattern(&def.ty) {
                return true;
            }
        }
        false
    }

    /// Check if a type contains PATTERN constraints
    fn type_has_pattern(&self, ty: &Type) -> bool {
        match ty {
            Type::Constrained {
                constraint,
                base_type,
            } => {
                if let ConstraintSpec::Subtype(subtype) = &constraint.spec {
                    if self.constraint_has_pattern(subtype) {
                        return true;
                    }
                }
                self.type_has_pattern(base_type)
            }
            Type::Sequence(fields) | Type::Set(fields) => {
                fields.iter().any(|f| self.type_has_pattern(&f.ty))
            }
            Type::Choice(variants) => variants.iter().any(|v| self.type_has_pattern(&v.ty)),
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => self.type_has_pattern(inner),
            Type::Tagged { inner, .. } => self.type_has_pattern(inner),
            _ => false,
        }
    }

    /// Check if a constraint contains PATTERN
    fn constraint_has_pattern(&self, constraint: &SubtypeConstraint) -> bool {
        match constraint {
            SubtypeConstraint::Pattern(_) => true,
            SubtypeConstraint::SizeConstraint(inner)
            | SubtypeConstraint::InnerType(inner)
            | SubtypeConstraint::Complement(inner) => self.constraint_has_pattern(inner),
            SubtypeConstraint::Union(elements) | SubtypeConstraint::Intersection(elements) => {
                elements.iter().any(|e| self.constraint_has_pattern(e))
            }
            _ => false,
        }
    }

    /// Generate Rust code from a module
    pub fn generate_module(&mut self, module: &Module) -> Result<String, std::fmt::Error> {
        // File header
        writeln!(
            &mut self.output,
            "// Auto-generated from ASN.1 module: {}",
            module.name
        )?;
        writeln!(&mut self.output)?;

        // Document exports if present
        if !module.exports.is_empty() {
            writeln!(&mut self.output, "// EXPORTS:")?;
            for export in &module.exports {
                writeln!(&mut self.output, "//   {}", export)?;
            }
            writeln!(&mut self.output)?;
        }

        // Document imports if present
        if !module.imports.is_empty() {
            writeln!(&mut self.output, "// IMPORTS:")?;
            for import in &module.imports {
                write!(&mut self.output, "//   ")?;
                for (i, symbol) in import.symbols.iter().enumerate() {
                    if i > 0 {
                        write!(&mut self.output, ", ")?;
                    }
                    write!(&mut self.output, "{}", symbol)?;
                }
                writeln!(&mut self.output, " FROM {}", import.module_name)?;
            }
            writeln!(&mut self.output)?;
        }

        // Standard synta imports.  The #[allow(unused_imports)] attributes
        // suppress clippy warnings for imports that are only needed when the
        // `derive` feature is active or when specific ASN.1 constructs are used.
        writeln!(&mut self.output, "#[allow(unused_imports)]")?;
        writeln!(&mut self.output, "use synta::types::string::*;")?;
        // All primitive, tagged, and constructed types are re-exported at the
        // synta crate root.  Encoder / Decoder are needed for the Encode /
        // Decode forwarding impls on constrained types.
        writeln!(&mut self.output, "#[allow(unused_imports)]")?;
        writeln!(
            &mut self.output,
            "use synta::{{Encode, Decode, Tagged, Encoder, Decoder, \
             GeneralizedTime, ObjectIdentifier, RelativeOid, UtcTime, \
             Integer, Boolean, Enumerated, Null, Real, \
             ExplicitTag, ImplicitTag, Element, RawDer, SetOf}};"
        )?;
        let derive_feat = self.derive_feature_name().map(str::to_owned);
        if let Some(feat) = derive_feat {
            writeln!(&mut self.output, "#[cfg(feature = \"{feat}\")]")?;
        }
        writeln!(&mut self.output, "#[allow(unused_imports)]")?;
        writeln!(
            &mut self.output,
            "use synta_derive::{{Asn1Sequence, Asn1Choice, Asn1Set}};"
        )?;

        // Add regex imports if module contains PATTERN constraints
        if self.has_pattern_constraints(module) {
            writeln!(&mut self.output, "#[cfg(feature = \"regex\")]")?;
            writeln!(&mut self.output, "use regex::Regex;")?;
            writeln!(&mut self.output, "#[cfg(feature = \"regex\")]")?;
            writeln!(&mut self.output, "use once_cell::sync::Lazy;")?;
        }
        writeln!(&mut self.output)?;

        // Generate use statements for imported types if module_path_prefix is configured
        if let Some(ref prefix) = self.config.module_path_prefix {
            if !module.imports.is_empty() {
                for import in &module.imports {
                    let module_path = module_name_to_rust(&import.module_name);
                    write!(&mut self.output, "use {}::{}", prefix, module_path)?;

                    if import.symbols.len() == 1 {
                        writeln!(&mut self.output, "::{};", import.symbols[0])?;
                    } else {
                        write!(&mut self.output, "::{{")?;
                        for (i, symbol) in import.symbols.iter().enumerate() {
                            if i > 0 {
                                write!(&mut self.output, ", ")?;
                            }
                            write!(&mut self.output, "{}", symbol)?;
                        }
                        writeln!(&mut self.output, "}};")?;
                    }
                }
                writeln!(&mut self.output)?;
            }
        }

        // Build set of all imported type names (for lifetime tracking)
        self.imported_types = module
            .imports
            .iter()
            .flat_map(|import| import.symbols.iter())
            .cloned()
            .collect();

        // Generate value assignments (constants)
        if !module.values.is_empty() {
            writeln!(
                &mut self.output,
                "// ============================================================================"
            )?;
            writeln!(&mut self.output, "// Constants")?;
            writeln!(
                &mut self.output,
                "// ============================================================================\n"
            )?;

            // Build OID registry for resolving named references
            let oid_registry = self.build_oid_registry(&module.values);

            for value_assignment in &module.values {
                self.generate_value_assignment(value_assignment, &oid_registry)?;
            }
            writeln!(&mut self.output)?;
        }

        // PASS 0: Build type definitions map for inlining
        for def in &module.definitions {
            let type_name = to_pascal_case(&def.name);
            self.type_definitions.insert(type_name, def.ty.clone());
        }

        // PASS 1: Pre-scan all definitions to determine which types need lifetimes
        // This is needed to handle forward references
        self.prescan_types_for_lifetimes(&module.definitions);

        // PASS 2: Generate each definition, skipping types that are in skip_imported_types
        for def in &module.definitions {
            // Skip this definition if it's in the skip list (external import)
            if self.config.skip_imported_types.contains(&def.name) {
                continue;
            }

            self.generate_definition(def)?;
            writeln!(&mut self.output)?;
        }

        Ok(self.output.clone())
    }

    fn generate_definition(&mut self, def: &Definition) -> Result<(), std::fmt::Error> {
        let type_name = to_pascal_case(&def.name);

        match &def.ty {
            Type::Sequence(fields) => {
                self.generate_sequence_type(&type_name, fields)?;
            }
            Type::Set(fields) => {
                self.generate_set_type(&type_name, fields)?;
            }
            Type::Choice(variants) => {
                self.generate_choice_type(&type_name, variants)?;
            }
            Type::SequenceOf(inner, size_constraint) => {
                self.generate_sequence_of_type(&type_name, inner, size_constraint.as_ref())?;
            }
            Type::SetOf(inner, size_constraint) => {
                self.generate_set_of_type(&type_name, inner, size_constraint.as_ref())?;
            }
            // X.680 constrained types - generate validated newtypes
            Type::Constrained {
                base_type,
                constraint,
            } => {
                match (base_type.as_ref(), &constraint.spec) {
                    (
                        Type::Integer(_, named_numbers),
                        ConstraintSpec::Subtype(subtype_constraint),
                    ) => {
                        self.generate_constrained_integer(&type_name, subtype_constraint)?;

                        // Generate named constants if present
                        if !named_numbers.is_empty() {
                            let prim = Self::constrained_integer_rust_type(subtype_constraint);
                            writeln!(&mut self.output)?;
                            writeln!(&mut self.output, "impl {} {{", type_name)?;

                            for named_number in named_numbers {
                                let const_name = to_screaming_snake_case(&named_number.name);
                                writeln!(
                                    &mut self.output,
                                    "    pub const {}: {} = {};",
                                    const_name, prim, named_number.value
                                )?;
                            }

                            writeln!(&mut self.output, "}}")?;
                        }
                    }
                    (Type::IA5String(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "IA5String",
                            subtype_constraint,
                        )?;
                    }
                    (Type::PrintableString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "PrintableString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::Utf8String(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "Utf8String",
                            subtype_constraint,
                        )?;
                    }
                    (Type::TeletexString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "TeletexString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::UniversalString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "UniversalString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::BmpString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "BmpString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::GeneralString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "GeneralString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::NumericString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "NumericString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::VisibleString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "VisibleString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::OctetString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "OctetString",
                            subtype_constraint,
                        )?;
                    }
                    (
                        Type::BitString(_),
                        ConstraintSpec::Subtype(SubtypeConstraint::NamedBitList(named_bits)),
                    ) => {
                        // Named bit list without size constraint: type alias + bit constants
                        writeln!(&mut self.output, "pub type {} = BitString;", type_name)?;
                        self.generate_named_bit_constants(&type_name, named_bits)?;
                    }
                    (
                        Type::BitString(_),
                        ConstraintSpec::Subtype(SubtypeConstraint::Intersection(constraints)),
                    ) if constraints
                        .iter()
                        .any(|c| matches!(c, SubtypeConstraint::NamedBitList(_))) =>
                    {
                        // Named bit list with size constraint: constrained newtype + bit constants
                        let size_con = constraints
                            .iter()
                            .find(|c| matches!(c, SubtypeConstraint::SizeConstraint(_)));
                        let named_bits_opt = constraints.iter().find_map(|c| {
                            if let SubtypeConstraint::NamedBitList(bits) = c {
                                Some(bits)
                            } else {
                                None
                            }
                        });

                        if let Some(size_con) = size_con {
                            self.generate_constrained_string(&type_name, "BitString", size_con)?;
                        } else {
                            writeln!(&mut self.output, "pub type {} = BitString;", type_name)?;
                        }

                        if let Some(named_bits) = named_bits_opt {
                            self.generate_named_bit_constants(&type_name, named_bits)?;
                        }
                    }
                    (Type::BitString(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        self.generate_constrained_string(
                            &type_name,
                            "BitString",
                            subtype_constraint,
                        )?;
                    }
                    (Type::TypeRef(_), ConstraintSpec::Subtype(subtype_constraint)) => {
                        // Subtype definition: NewType ::= BaseType (constraint)
                        self.generate_subtype(&type_name, base_type, subtype_constraint)?;
                    }
                    _ => {
                        // For unsupported constraint types, fall back to type alias with comment
                        writeln!(
                            &mut self.output,
                            "// Constrained type (validation not yet implemented)"
                        )?;
                        let rust_type = self.rust_type(base_type);
                        self.generate_type_alias(&type_name, &rust_type, base_type)?;
                    }
                }
            }
            Type::Integer(_, named_numbers) if !named_numbers.is_empty() => {
                // INTEGER with named values - generate type alias and module-level constants.
                // Module-level consts avoid the orphan-rule restriction on impl blocks for
                // type aliases of foreign types, and allow `const` without Integer::from().
                writeln!(&mut self.output, "pub type {} = Integer;", type_name)?;
                self.generate_named_integer_constants(&type_name, named_numbers)?;
            }
            Type::Integer(Some(constraint), _) => {
                // Legacy constraint - type alias with constraint comment
                let constraint_str = self.format_value_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
                writeln!(&mut self.output, "pub type {} = Integer;", type_name)?;
            }
            Type::OctetString(Some(constraint))
            | Type::BitString(Some(constraint))
            | Type::Utf8String(Some(constraint))
            | Type::PrintableString(Some(constraint))
            | Type::IA5String(Some(constraint))
            | Type::TeletexString(Some(constraint))
            | Type::UniversalString(Some(constraint))
            | Type::BmpString(Some(constraint))
            | Type::GeneralString(Some(constraint))
            | Type::NumericString(Some(constraint))
            | Type::VisibleString(Some(constraint)) => {
                // Legacy constraint - type alias with size constraint comment
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
                let rust_type = self.rust_type(&def.ty);
                self.generate_type_alias(&type_name, &rust_type, &def.ty)?;
            }
            Type::Enumerated(named_values) => {
                self.generate_enumerated_type(&type_name, named_values)?;
            }
            Type::Tagged { tag, inner } => {
                // Top-level tagged type: emit a doc comment then generate the inner type
                let class_str = match tag.class {
                    TagClass::Application => "APPLICATION",
                    TagClass::Universal => "UNIVERSAL",
                    TagClass::Private => "PRIVATE",
                    TagClass::ContextSpecific => "CONTEXT",
                };
                let tagging_str = match tag.tagging {
                    Tagging::Explicit => "EXPLICIT",
                    Tagging::Implicit => "IMPLICIT",
                };
                writeln!(
                    &mut self.output,
                    "/// [{} {}] {} outer tag",
                    class_str, tag.number, tagging_str
                )?;
                // Generate the inner type under the same name
                let inner_def = Definition {
                    name: def.name.clone(),
                    ty: *inner.clone(),
                };
                self.generate_definition(&inner_def)?;
            }
            Type::Class(fields) => {
                // ASN.1 Information Object Classes (X.681 §9) have no DER encoding.
                // Emit a structured comment block so the schema is self-documenting
                // but do not generate any Rust type.
                writeln!(
                    &mut self.output,
                    "// ASN.1 Information Object Class: {} (no Rust type generated)",
                    type_name
                )?;
                if !fields.is_empty() {
                    write!(&mut self.output, "// Fields:")?;
                    for field in fields {
                        write!(&mut self.output, " &{}", field.name)?;
                        if field.unique {
                            write!(&mut self.output, " UNIQUE")?;
                        }
                        if field.optional {
                            write!(&mut self.output, " OPTIONAL")?;
                        }
                        write!(&mut self.output, ";")?;
                    }
                    writeln!(&mut self.output)?;
                }
            }
            _ => {
                // Type alias
                let rust_type = self.rust_type(&def.ty);
                self.generate_type_alias(&type_name, &rust_type, &def.ty)?;
            }
        }

        Ok(())
    }

    fn format_value_constraint(&self, constraint: &ValueConstraint) -> String {
        match constraint {
            ValueConstraint::Single(val) => format!("value = {}", val),
            ValueConstraint::Range(min, max) => {
                let min_str = min
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "MIN".to_string());
                let max_str = max
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "MAX".to_string());
                format!("{}..{}", min_str, max_str)
            }
        }
    }

    fn format_size_constraint(&self, constraint: &SizeConstraint) -> String {
        match constraint {
            SizeConstraint::Fixed(size) => format!("SIZE ({})", size),
            SizeConstraint::Range(min, max) => {
                let min_str = min
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "0".to_string());
                let max_str = max
                    .map(|v| v.to_string())
                    .unwrap_or_else(|| "MAX".to_string());
                format!("SIZE ({}..{})", min_str, max_str)
            }
        }
    }

    /// Return the smallest Rust primitive integer type whose range covers all
    /// values permitted by `constraint`.
    ///
    /// When the lower bound is ≥ 0 (non-negative), unsigned types are preferred
    /// because they cover twice the range of the same-width signed type:
    /// `u8` (0..=255), `u16` (0..=65535), `u32` (0..=4294967295), `u64`.
    ///
    /// When the lower bound is negative, the smallest signed type that fits both
    /// bounds is chosen: `i8`, `i16`, `i32`, `i64`.
    ///
    /// Falls back to `i64` / `u64` when either bound is `MIN`, `MAX`, a named
    /// value (not a literal), or the constraint is not a simple value/range.
    fn constrained_integer_rust_type(constraint: &SubtypeConstraint) -> &'static str {
        let (lo, hi) = match constraint {
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => (*n, *n),
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(lo),
                max: ConstraintValue::Integer(hi),
            } => (*lo, *hi),
            _ => return "i64",
        };
        if lo >= 0 {
            // Non-negative range — use the smallest unsigned type.
            if hi <= u8::MAX as i64 {
                "u8"
            } else if hi <= u16::MAX as i64 {
                "u16"
            } else if hi <= u32::MAX as i64 {
                "u32"
            } else {
                "u64"
            }
        } else {
            // Range includes negative values — use signed types.
            if lo >= i8::MIN as i64 && hi <= i8::MAX as i64 {
                "i8"
            } else if lo >= i16::MIN as i64 && hi <= i16::MAX as i64 {
                "i16"
            } else if lo >= i32::MIN as i64 && hi <= i32::MAX as i64 {
                "i32"
            } else {
                "i64"
            }
        }
    }

    /// Generate validation code for a constraint value
    fn generate_constraint_value_check(&self, var: &str, value: &ConstraintValue) -> String {
        match value {
            ConstraintValue::Integer(n) => format!("{} == {}", var, n),
            ConstraintValue::Min => "true /* MIN */".to_string(),
            ConstraintValue::Max => "true /* MAX */".to_string(),
            ConstraintValue::NamedValue(name) => format!("{} == {} /* named value */", var, name),
        }
    }

    /// Generate validation code for a subtype constraint
    fn generate_constraint_validation(&self, var: &str, constraint: &SubtypeConstraint) -> String {
        match constraint {
            SubtypeConstraint::SingleValue(val) => self.generate_constraint_value_check(var, val),
            SubtypeConstraint::ValueRange { min, max } => {
                // Use RangeInclusive::contains when both bounds are concrete integers
                // to avoid clippy's manual_range_contains warning.
                if let (ConstraintValue::Integer(lo), ConstraintValue::Integer(hi)) = (min, max) {
                    return format!("({}..={}).contains(&{})", lo, hi, var);
                }
                let mut parts: Vec<String> = Vec::new();
                match min {
                    ConstraintValue::Integer(n) => parts.push(format!("{} >= {}", var, n)),
                    ConstraintValue::Min => {}
                    ConstraintValue::NamedValue(name) => parts.push(format!("{} >= {}", var, name)),
                    ConstraintValue::Max => parts.push(format!("{} <= i64::MAX", var)),
                }
                match max {
                    ConstraintValue::Integer(n) => parts.push(format!("{} <= {}", var, n)),
                    ConstraintValue::Max => {}
                    ConstraintValue::NamedValue(name) => parts.push(format!("{} <= {}", var, name)),
                    ConstraintValue::Min => parts.push(format!("{} >= i64::MIN", var)),
                }
                if parts.is_empty() {
                    "true".to_string()
                } else {
                    format!("({})", parts.join(" && "))
                }
            }
            SubtypeConstraint::Union(elements) => {
                let checks: Vec<String> = elements
                    .iter()
                    .map(|e| self.generate_constraint_validation(var, e))
                    .collect();
                format!("({})", checks.join(" || "))
            }
            SubtypeConstraint::Intersection(elements) => {
                let checks: Vec<String> = elements
                    .iter()
                    .map(|e| self.generate_constraint_validation(var, e))
                    .collect();
                format!("({})", checks.join(" && "))
            }
            SubtypeConstraint::Complement(inner) => {
                let inner_check = self.generate_constraint_validation(var, inner);
                format!("!({})", inner_check)
            }
            _ => "true /* unsupported constraint */".to_string(),
        }
    }

    /// Generate a human-readable constraint description for error messages
    fn generate_constraint_description(&self, constraint: &SubtypeConstraint) -> String {
        match constraint {
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => {
                format!("must equal {}", n)
            }
            SubtypeConstraint::ValueRange { min, max } => {
                let min_str = match min {
                    ConstraintValue::Integer(n) => n.to_string(),
                    ConstraintValue::Min => "MIN".to_string(),
                    ConstraintValue::NamedValue(n) => n.clone(),
                    ConstraintValue::Max => "MAX".to_string(),
                };
                let max_str = match max {
                    ConstraintValue::Integer(n) => n.to_string(),
                    ConstraintValue::Max => "MAX".to_string(),
                    ConstraintValue::NamedValue(n) => n.clone(),
                    ConstraintValue::Min => "MIN".to_string(),
                };
                format!("must be in range {}..{}", min_str, max_str)
            }
            SubtypeConstraint::Union(elements) => {
                let descriptions: Vec<String> = elements
                    .iter()
                    .map(|e| self.generate_constraint_description(e))
                    .collect();
                format!("must satisfy one of: {}", descriptions.join(", "))
            }
            SubtypeConstraint::Complement(inner) => {
                format!(
                    "must not be {}",
                    self.generate_constraint_description(inner)
                )
            }
            _ => "must satisfy constraint".to_string(),
        }
    }

    /// Generate a proper Rust enum for an ENUMERATED type
    fn generate_enumerated_type(
        &mut self,
        name: &str,
        named_values: &[NamedNumber],
    ) -> Result<(), std::fmt::Error> {
        writeln!(&mut self.output, "/// ENUMERATED")?;
        writeln!(
            &mut self.output,
            "#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]"
        )?;
        writeln!(&mut self.output, "#[repr(i64)]")?;
        writeln!(&mut self.output, "pub enum {} {{", name)?;

        for nv in named_values {
            let variant_name = to_pascal_case(&nv.name);
            writeln!(&mut self.output, "    {} = {},", variant_name, nv.value)?;
        }

        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // TryFrom<Integer> implementation
        let try_from_path = self.try_from_path();
        writeln!(
            &mut self.output,
            "impl {}::convert::TryFrom<Integer> for {} {{",
            try_from_path, name
        )?;
        writeln!(&mut self.output, "    type Error = &'static str;")?;
        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "    fn try_from(value: Integer) -> Result<Self, Self::Error> {{"
        )?;
        writeln!(
            &mut self.output,
            "        let discriminant = value.as_i64().map_err(|_| \"ENUMERATED value out of i64 range\")?;"
        )?;
        writeln!(&mut self.output, "        match discriminant {{")?;

        for nv in named_values {
            let variant_name = to_pascal_case(&nv.name);
            writeln!(
                &mut self.output,
                "            {} => Ok({}::{}),",
                nv.value, name, variant_name
            )?;
        }

        writeln!(
            &mut self.output,
            "            _ => Err(\"unknown ENUMERATED value\"),"
        )?;
        writeln!(&mut self.output, "        }}")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // From<T> for Integer
        writeln!(&mut self.output, "impl From<{}> for Integer {{", name)?;
        writeln!(&mut self.output, "    fn from(value: {}) -> Self {{", name)?;
        writeln!(&mut self.output, "        Integer::from(value as i64)")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // Encode / Decode / Tagged forwarding impls.
        // ENUMERATED (tag 10) is encoded identically to INTEGER (tag 2) but
        // with a different universal tag number.
        writeln!(&mut self.output, "impl Encode for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn encode(&self, encoder: &mut Encoder) -> synta::Result<()> {{"
        )?;
        writeln!(
            &mut self.output,
            "        let as_int = Integer::from(*self as i64);"
        )?;
        writeln!(
            &mut self.output,
            "        let tag = synta::Tag::universal(synta::tag::TAG_ENUMERATED);"
        )?;
        writeln!(&mut self.output, "        encoder.write_tag(tag)?;")?;
        writeln!(
            &mut self.output,
            "        encoder.write_length(as_int.as_bytes().len())?;"
        )?;
        writeln!(
            &mut self.output,
            "        encoder.write_bytes(as_int.as_bytes());"
        )?;
        writeln!(&mut self.output, "        Ok(())")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(
            &mut self.output,
            "    fn encoded_len(&self) -> synta::Result<usize> {{"
        )?;
        writeln!(
            &mut self.output,
            "        let as_int = Integer::from(*self as i64);"
        )?;
        writeln!(&mut self.output, "        let tag_len = 1usize;")?;
        writeln!(
            &mut self.output,
            "        let length = as_int.as_bytes().len();"
        )?;
        writeln!(
            &mut self.output,
            "        let length_len = synta::Length::Definite(length).encoded_len()?;"
        )?;
        writeln!(
            &mut self.output,
            "        Ok(tag_len + length_len + length)"
        )?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl<'a> Decode<'a> for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn decode(decoder: &mut Decoder<'a>) -> synta::Result<Self> {{"
        )?;
        writeln!(&mut self.output, "        let tag = decoder.read_tag()?;")?;
        writeln!(
            &mut self.output,
            "        let expected = synta::Tag::universal(synta::tag::TAG_ENUMERATED);"
        )?;
        writeln!(&mut self.output, "        if tag != expected {{")?;
        writeln!(
            &mut self.output,
            "            return Err(synta::Error::UnexpectedTag {{"
        )?;
        writeln!(
            &mut self.output,
            "                position: decoder.position(),"
        )?;
        writeln!(&mut self.output, "                expected,")?;
        writeln!(&mut self.output, "                actual: tag,")?;
        writeln!(&mut self.output, "            }});")?;
        writeln!(&mut self.output, "        }}")?;
        writeln!(
            &mut self.output,
            "        let length = decoder.read_length()?;"
        )?;
        writeln!(&mut self.output, "        let len = length.definite()?;")?;
        writeln!(
            &mut self.output,
            "        let bytes = decoder.read_bytes(len)?;"
        )?;
        writeln!(
            &mut self.output,
            "        let integer = Integer::from_bytes(bytes);"
        )?;
        writeln!(
            &mut self.output,
            "        core::convert::TryFrom::try_from(integer)\
             .map_err(|_| synta::Error::LengthOverflow)"
        )?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl Tagged for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn tag() -> synta::Tag {{ synta::Tag::universal(synta::tag::TAG_ENUMERATED) }}"
        )?;
        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, false)?;

        Ok(())
    }

    /// Generate named bit position constants for a BIT STRING type
    fn generate_named_bit_constants(
        &mut self,
        name: &str,
        named_bits: &[NamedNumber],
    ) -> Result<(), std::fmt::Error> {
        if named_bits.is_empty() {
            return Ok(());
        }

        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "// Named bit positions for {} (defined as module-level constants to avoid orphan rule issues)",
            name
        )?;

        for bit in named_bits {
            let const_name = to_screaming_snake_case(&bit.name);
            let full_const_name = format!("{}_{}", to_screaming_snake_case(name), const_name);
            writeln!(
                &mut self.output,
                "/// Bit position for `{}` in {}",
                bit.name, name
            )?;
            writeln!(
                &mut self.output,
                "pub const {}: usize = {};",
                full_const_name, bit.value
            )?;
        }

        Ok(())
    }

    /// Generate module-level named-value constants for an unconstrained INTEGER type.
    ///
    /// Uses `i64` literals rather than `Integer::from()` (which is not `const`)
    /// and avoids `impl TypeAlias { … }` which the orphan rule disallows for
    /// type aliases of foreign types.
    fn generate_named_integer_constants(
        &mut self,
        name: &str,
        named_numbers: &[NamedNumber],
    ) -> Result<(), std::fmt::Error> {
        if named_numbers.is_empty() {
            return Ok(());
        }

        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "// Named values for {} (defined as module-level constants to avoid orphan rule issues)",
            name
        )?;

        for num in named_numbers {
            let const_name = to_screaming_snake_case(&num.name);
            let full_const_name = format!("{}_{}", to_screaming_snake_case(name), const_name);
            writeln!(
                &mut self.output,
                "/// Named value `{}` for {}",
                num.name, name
            )?;
            writeln!(
                &mut self.output,
                "pub const {}: i64 = {};",
                full_const_name, num.value
            )?;
        }

        Ok(())
    }

    /// Generate a validated newtype for a constrained INTEGER.
    ///
    /// Picks the smallest Rust primitive integer that fits the constraint range.
    /// When the lower bound is ≥ 0, an unsigned type is chosen (`u8`, `u16`,
    /// `u32`, `u64`); when the lower bound is negative, a signed type is chosen
    /// (`i8`, `i16`, `i32`, `i64`).  Unconstrained bounds fall back to `i64`.
    /// Using a native primitive gives the generated struct `Copy`, `PartialOrd`,
    /// and `Ord` for free and avoids the heap allocation that the
    /// arbitrary-precision `Integer` type would incur.
    fn generate_constrained_integer(
        &mut self,
        name: &str,
        constraint: &SubtypeConstraint,
    ) -> Result<(), std::fmt::Error> {
        let prim = Self::constrained_integer_rust_type(constraint);

        // Generate documentation with constraint info
        let constraint_display = self.format_constraint_display(constraint);
        writeln!(&mut self.output, "/// INTEGER ({})", constraint_display)?;
        writeln!(
            &mut self.output,
            "#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]"
        )?;
        writeln!(&mut self.output, "pub struct {}({});", name, prim)?;
        writeln!(&mut self.output)?;

        // Generate constructor with validation
        writeln!(&mut self.output, "impl {} {{", name)?;
        writeln!(
            &mut self.output,
            "    /// Create a new {} with validation",
            name
        )?;
        writeln!(
            &mut self.output,
            "    pub fn new(value: {}) -> Result<Self, &'static str> {{",
            prim
        )?;

        let validation = self.generate_constraint_validation("value", constraint);
        let description = self.generate_constraint_description(constraint);

        writeln!(&mut self.output, "        if {} {{", validation)?;
        writeln!(&mut self.output, "            Ok({}(value))", name)?;
        writeln!(&mut self.output, "        }} else {{")?;
        writeln!(&mut self.output, "            Err(\"{}\")", description)?;
        writeln!(&mut self.output, "        }}")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Unchecked constructor for when you know the value is valid
        writeln!(
            &mut self.output,
            "    /// Create without validation (use with caution)"
        )?;
        writeln!(
            &mut self.output,
            "    pub const fn new_unchecked(value: {}) -> Self {{",
            prim
        )?;
        writeln!(&mut self.output, "        {}(value)", name)?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Getter — returns by value since primitives are Copy
        writeln!(&mut self.output, "    /// Get the inner value")?;
        writeln!(
            &mut self.output,
            "    pub const fn get(&self) -> {} {{",
            prim
        )?;
        writeln!(&mut self.output, "        self.0")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Into inner
        writeln!(
            &mut self.output,
            "    /// Consume and return the inner value"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn into_inner(self) -> {} {{",
            prim
        )?;
        writeln!(&mut self.output, "        self.0")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // TryFrom<Integer> — decode path: wire Integer → native primitive → validated newtype.
        // Use the native as_{prim}() method: a single fallible step that handles both
        // the i64/u64 sign check and the narrowing conversion in one call.
        let as_method = format!("as_{}", prim);
        let try_from_path = self.try_from_path();
        writeln!(
            &mut self.output,
            "impl {}::convert::TryFrom<Integer> for {} {{",
            try_from_path, name
        )?;
        writeln!(&mut self.output, "    type Error = &'static str;")?;
        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "    fn try_from(value: Integer) -> Result<Self, Self::Error> {{"
        )?;
        writeln!(
            &mut self.output,
            "        let n = value.{as_method}().map_err(|_| \"integer value out of {prim} range\")?;"
        )?;
        writeln!(&mut self.output, "        Self::new(n)")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // Encode / Decode / Tagged forwarding impls — required so that this
        // type can appear as a field in #[derive(Asn1Sequence)] structs.
        // Encode: Integer::from(self.0) — uses the From<{prim}> impl directly.
        writeln!(&mut self.output, "impl Encode for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn encode(&self, encoder: &mut Encoder) -> synta::Result<()> {{"
        )?;
        writeln!(
            &mut self.output,
            "        Integer::from(self.0).encode(encoder)"
        )?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(
            &mut self.output,
            "    fn encoded_len(&self) -> synta::Result<usize> {{"
        )?;
        writeln!(
            &mut self.output,
            "        Integer::from(self.0).encoded_len()"
        )?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // Decode: wire Integer → as_{prim}() → new() — single narrowing step.
        writeln!(&mut self.output, "impl<'a> Decode<'a> for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn decode(decoder: &mut Decoder<'a>) -> synta::Result<Self> {{"
        )?;
        writeln!(
            &mut self.output,
            "        Integer::decode(decoder).and_then(|v| {{"
        )?;
        writeln!(
            &mut self.output,
            "            let n = v.{as_method}().map_err(|_| synta::Error::LengthOverflow)?;"
        )?;
        writeln!(
            &mut self.output,
            "            Self::new(n).map_err(|_| synta::Error::LengthOverflow)"
        )?;
        writeln!(&mut self.output, "        }})")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl Tagged for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn tag() -> synta::Tag {{ Integer::tag() }}"
        )?;
        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, false)?;

        Ok(())
    }

    /// Generate a validated newtype for a constrained string type
    fn generate_constrained_string(
        &mut self,
        name: &str,
        base_type: &str,
        constraint: &SubtypeConstraint,
    ) -> Result<(), std::fmt::Error> {
        // Generate documentation with constraint info
        let constraint_display = self.format_constraint_display(constraint);
        writeln!(
            &mut self.output,
            "/// {} ({})",
            base_type, constraint_display
        )?;
        writeln!(&mut self.output, "#[derive(Debug, Clone, PartialEq, Eq)]")?;
        writeln!(&mut self.output, "pub struct {}({});", name, base_type)?;
        writeln!(&mut self.output)?;

        // Generate constructor with validation
        writeln!(&mut self.output, "impl {} {{", name)?;
        writeln!(
            &mut self.output,
            "    /// Create a new {} with validation",
            name
        )?;
        writeln!(
            &mut self.output,
            "    pub fn new(value: {}) -> Result<Self, &'static str> {{",
            base_type
        )?;

        // Generate validation based on constraint type
        let validation_code = self.generate_string_validation("value", base_type, constraint);
        writeln!(&mut self.output, "{}", validation_code)?;

        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Unchecked constructor
        writeln!(
            &mut self.output,
            "    /// Create without validation (use with caution)"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn new_unchecked(value: {}) -> Self {{",
            base_type
        )?;
        writeln!(&mut self.output, "        {}(value)", name)?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Getter
        writeln!(
            &mut self.output,
            "    /// Get a reference to the inner value"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn get(&self) -> &{} {{",
            base_type
        )?;
        writeln!(&mut self.output, "        &self.0")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // As str for string types
        if base_type != "OctetString" && base_type != "BitString" {
            writeln!(&mut self.output, "    /// Get the string value")?;
            writeln!(&mut self.output, "    pub fn as_str(&self) -> &str {{")?;
            writeln!(&mut self.output, "        self.0.as_str()")?;
            writeln!(&mut self.output, "    }}")?;
            writeln!(&mut self.output)?;
        }

        // Into inner
        writeln!(
            &mut self.output,
            "    /// Consume and return the inner value"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn into_inner(self) -> {} {{",
            base_type
        )?;
        writeln!(&mut self.output, "        self.0")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // TryFrom implementation
        let try_from_path = self.try_from_path();
        writeln!(
            &mut self.output,
            "impl {}::convert::TryFrom<{}> for {} {{",
            try_from_path, base_type, name
        )?;
        writeln!(&mut self.output, "    type Error = &'static str;")?;
        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "    fn try_from(value: {}) -> Result<Self, Self::Error> {{",
            base_type
        )?;
        writeln!(&mut self.output, "        Self::new(value)")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // Encode / Decode / Tagged forwarding impls — required so that this
        // type can appear as a field in #[derive(Asn1Sequence)] structs.
        writeln!(&mut self.output, "impl Encode for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn encode(&self, encoder: &mut Encoder) -> synta::Result<()> {{"
        )?;
        writeln!(&mut self.output, "        self.0.encode(encoder)")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(
            &mut self.output,
            "    fn encoded_len(&self) -> synta::Result<usize> {{"
        )?;
        writeln!(&mut self.output, "        self.0.encoded_len()")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl<'a> Decode<'a> for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn decode(decoder: &mut Decoder<'a>) -> synta::Result<Self> {{"
        )?;
        writeln!(
            &mut self.output,
            "        {}::decode(decoder).and_then(|v| {{",
            base_type
        )?;
        writeln!(
            &mut self.output,
            "            Self::new(v).map_err(|_| synta::Error::LengthOverflow)"
        )?;
        writeln!(&mut self.output, "        }})")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl Tagged for {} {{", name)?;
        writeln!(
            &mut self.output,
            "    fn tag() -> synta::Tag {{ {}::tag() }}",
            base_type
        )?;
        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, false)?;

        Ok(())
    }

    /// Generate validation code for string constraints
    fn generate_string_validation(
        &mut self,
        var: &str,
        base_type: &str,
        constraint: &SubtypeConstraint,
    ) -> String {
        match constraint {
            SubtypeConstraint::SizeConstraint(inner) => {
                // SIZE constraint - validate length
                self.generate_size_validation(var, base_type, inner)
            }
            SubtypeConstraint::PermittedAlphabet(ranges) => {
                // FROM constraint - validate characters
                self.generate_alphabet_validation(var, ranges)
            }
            SubtypeConstraint::Pattern(pattern) => {
                // PATTERN constraint - regex validation
                self.generate_pattern_validation(var, pattern)
            }
            SubtypeConstraint::ContainedSubtype(ty) => {
                // CONTAINING constraint - optionally validate that the bytes contain a valid encoded value
                self.generate_containing_validation(var, ty)
            }
            SubtypeConstraint::Intersection(constraints) => {
                // Combined constraints - validate all of them
                self.generate_intersection_string_validation(var, base_type, constraints)
            }
            _ => {
                // Unsupported constraint
                format!(
                    "        Ok({}({}))",
                    self.get_struct_name_from_var(var),
                    var
                )
            }
        }
    }

    /// Generate validation for intersection of string constraints
    /// This generates sequential validation: check each constraint in order
    fn generate_intersection_string_validation(
        &self,
        var: &str,
        base_type: &str,
        constraints: &[SubtypeConstraint],
    ) -> String {
        let struct_name = self.get_struct_name_from_var(var);

        // Separate size and alphabet constraints
        let size_constraint = constraints.iter().find_map(|c| {
            if let SubtypeConstraint::SizeConstraint(inner) = c {
                Some(inner.as_ref())
            } else {
                None
            }
        });

        let alphabet_constraint = constraints.iter().find_map(|c| {
            if let SubtypeConstraint::PermittedAlphabet(ranges) = c {
                Some(ranges)
            } else {
                None
            }
        });

        // Generate combined validation
        match (size_constraint, alphabet_constraint) {
            (Some(size), Some(alphabet)) => {
                // Both SIZE and FROM - validate both
                let length_expr = if base_type == "BitString" {
                    format!("{}.bit_len()", var)
                } else if base_type == "OctetString" {
                    format!("{}.as_bytes().len()", var)
                } else {
                    format!("{}.as_str().len()", var)
                };

                // Generate size check condition (None = no check needed)
                let size_check: Option<String> = match size {
                    SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => {
                        Some(format!("{} == {}", length_expr, n))
                    }
                    SubtypeConstraint::ValueRange { min, max } => {
                        let mut parts: Vec<String> = Vec::new();
                        if let ConstraintValue::Integer(n) = min {
                            if *n == 1 && base_type != "BitString" {
                                let obj = length_expr.trim_end_matches(".len()");
                                parts.push(format!("!{}.is_empty()", obj));
                            } else {
                                parts.push(format!("{} >= {}", length_expr, n));
                            }
                        }
                        if let ConstraintValue::Integer(n) = max {
                            parts.push(format!("{} <= {}", length_expr, n));
                        }
                        if parts.is_empty() {
                            None
                        } else {
                            Some(parts.join(" && "))
                        }
                    }
                    _ => None,
                };

                // Generate alphabet check condition
                let range_checks: Vec<String> = alphabet
                    .iter()
                    .map(|r| {
                        if r.min == r.max {
                            format!("ch == '{}'", r.min)
                        } else {
                            format!("(ch >= '{}' && ch <= '{}')", r.min, r.max)
                        }
                    })
                    .collect();
                let alphabet_check = range_checks.join(" || ");

                // Generate error messages
                let size_error = match size {
                    SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => {
                        format!("length must equal {}", n)
                    }
                    SubtypeConstraint::ValueRange { min, max } => {
                        let min_str = match min {
                            ConstraintValue::Integer(n) => n.to_string(),
                            _ => "MIN".to_string(),
                        };
                        let max_str = match max {
                            ConstraintValue::Integer(n) => n.to_string(),
                            _ => "MAX".to_string(),
                        };
                        format!("length must be in range {}..{}", min_str, max_str)
                    }
                    _ => "invalid length".to_string(),
                };

                let ranges_display: Vec<String> = alphabet
                    .iter()
                    .map(|r| {
                        if r.min == r.max {
                            format!("'{}'", r.min)
                        } else {
                            format!("'{}'..'{}'", r.min, r.max)
                        }
                    })
                    .collect();
                let alphabet_error =
                    format!("characters must be from: {}", ranges_display.join(", "));

                // Generate validation code
                let size_check_block = if let Some(cond) = size_check {
                    format!(
                        "        // Check SIZE constraint\n        if !({}) {{\n            return Err(\"{}\");\n        }}\n",
                        cond, size_error
                    )
                } else {
                    String::new()
                };
                format!(
                    "{}        // Check FROM constraint\n        for ch in {}.as_str().chars() {{\n            if !({}) {{\n                return Err(\"{}\");\n            }}\n        }}\n        Ok({}({}))",
                    size_check_block, var, alphabet_check, alphabet_error, struct_name, var
                )
            }
            (Some(size), None) => {
                // Only SIZE
                self.generate_size_validation(var, base_type, size)
            }
            (None, Some(alphabet)) => {
                // Only FROM
                self.generate_alphabet_validation(var, alphabet)
            }
            (None, None) => {
                // No recognized constraints
                format!("        Ok({}({}))", struct_name, var)
            }
        }
    }

    /// Generate size constraint validation for strings
    fn generate_size_validation(
        &self,
        var: &str,
        base_type: &str,
        size_constraint: &SubtypeConstraint,
    ) -> String {
        let length_expr = if base_type == "BitString" {
            // BitString::bit_len() returns the number of bits (not bytes)
            format!("{}.bit_len()", var)
        } else if base_type == "OctetString" {
            format!("{}.as_bytes().len()", var)
        } else {
            format!("{}.as_str().len()", var)
        };

        let struct_name = self.get_struct_name_from_var(var);

        match size_constraint {
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => {
                format!(
                    "        if {} == {} {{\n            Ok({}({}))\n        }} else {{\n            Err(\"length must equal {}\")\n        }}",
                    length_expr, n, struct_name, var, n
                )
            }
            SubtypeConstraint::ValueRange { min, max } => {
                let mut checks: Vec<String> = Vec::new();
                if let ConstraintValue::Integer(n) = min {
                    if *n == 1 && base_type != "BitString" {
                        let obj = length_expr.trim_end_matches(".len()");
                        checks.push(format!("!{}.is_empty()", obj));
                    } else {
                        checks.push(format!("{} >= {}", length_expr, n));
                    }
                }
                if let ConstraintValue::Integer(n) = max {
                    checks.push(format!("{} <= {}", length_expr, n));
                }

                let min_str = match min {
                    ConstraintValue::Integer(n) => n.to_string(),
                    _ => "0".to_string(),
                };
                let max_str = match max {
                    ConstraintValue::Integer(n) => n.to_string(),
                    _ => "MAX".to_string(),
                };

                if checks.is_empty() {
                    // Unbounded range — all lengths accepted; no check needed.
                    format!("        Ok({}({}))", struct_name, var)
                } else {
                    format!(
                        "        if {} {{\n            Ok({}({}))\n        }} else {{\n            Err(\"length must be in range {}..{}\")\n        }}",
                        checks.join(" && "), struct_name, var, min_str, max_str
                    )
                }
            }
            _ => format!("        Ok({}({}))", struct_name, var),
        }
    }

    /// Generate permitted alphabet validation
    fn generate_alphabet_validation(&self, var: &str, ranges: &[CharRange]) -> String {
        let struct_name = self.get_struct_name_from_var(var);

        // Generate character range checks
        let range_checks: Vec<String> = ranges
            .iter()
            .map(|r| {
                if r.min == r.max {
                    format!("ch == '{}'", r.min)
                } else {
                    format!("(ch >= '{}' && ch <= '{}')", r.min, r.max)
                }
            })
            .collect();

        let check_expr = range_checks.join(" || ");

        let ranges_display: Vec<String> = ranges
            .iter()
            .map(|r| {
                if r.min == r.max {
                    format!("'{}'", r.min)
                } else {
                    format!("'{}'..'{}'", r.min, r.max)
                }
            })
            .collect();

        format!(
            "        for ch in {}.as_str().chars() {{\n            if !({}) {{\n                return Err(\"characters must be from: {}\");\n            }}\n        }}\n        Ok({}({}))",
            var, check_expr, ranges_display.join(", "), struct_name, var
        )
    }

    /// Generate pattern (regex) validation
    fn generate_pattern_validation(&mut self, var: &str, pattern: &str) -> String {
        let struct_name = self.get_struct_name_from_var(var);

        // Generate unique pattern variable name
        let pattern_name = format!("PATTERN_{}", self.pattern_counter);
        self.pattern_counter += 1;

        // Generate regex validation with feature flag
        let mut result = String::new();

        // Generate static regex pattern with feature flag
        result.push_str(&format!(
            "        #[cfg(feature = \"regex\")]\n        {{\n            static {}: Lazy<Regex> = Lazy::new(|| Regex::new(r\"{}\").unwrap());\n",
            pattern_name, pattern.replace("\"", "\\\"")
        ));

        // Generate validation check
        result.push_str(&format!(
            "            if !{}.is_match({}.as_ref()) {{\n",
            pattern_name, var
        ));
        result.push_str(&format!(
            "                return Err(format!(\"value does not match pattern: {}\"));\n",
            pattern.replace("\"", "\\\"")
        ));
        result.push_str("            }\n        }\n");

        // Generate placeholder for when regex feature is disabled
        result.push_str("        #[cfg(not(feature = \"regex\"))]\n");
        result.push_str(&format!(
            "        // Pattern validation disabled (requires 'regex' feature): {}\n",
            pattern
        ));

        result.push_str(&format!("        Ok({}({}))", struct_name, var));

        result
    }

    fn generate_containing_validation(&self, var: &str, contained_type: &Type) -> String {
        let struct_name = self.get_struct_name_from_var(var);
        let type_name = self.rust_type(contained_type);

        let mut result = String::new();

        // Generate validation with feature flag
        result.push_str("        #[cfg(feature = \"validate_containing\")]\n");
        result.push_str("        {\n");
        result.push_str("            use synta::der::Decoder;\n");
        result.push_str(&format!(
            "            // Validate that {} contains a valid DER-encoded {}\n",
            var, type_name
        ));
        result.push_str(&format!("            let bytes = {}.as_ref();\n", var));
        result.push_str(
            "            let mut decoder = Decoder::new(bytes, synta::Encoding::Der)?;\n",
        );
        result.push_str(&format!(
            "            let _decoded: {} = decoder.decode().map_err(|e| {{\n",
            type_name
        ));
        result.push_str(&format!(
            "                format!(\"invalid {} in CONTAINING constraint: {{}}\", e)\n",
            type_name
        ));
        result.push_str("            })?;\n");
        result.push_str("            // Optionally verify complete consumption\n");
        result.push_str("            if !decoder.is_empty() {\n");
        result.push_str(&format!("                return Err(\"trailing bytes after {} in CONTAINING constraint\".into());\n", type_name));
        result.push_str("            }\n");
        result.push_str("        }\n");

        // Generate placeholder for when validate_containing feature is disabled
        result.push_str("        #[cfg(not(feature = \"validate_containing\"))]\n");
        result.push_str(&format!(
            "        // CONTAINING validation disabled (requires 'validate_containing' feature): {}\n",
            type_name
        ));

        result.push_str(&format!("        Ok({}({}))", struct_name, var));

        result
    }

    /// Helper to extract struct name from variable name
    fn get_struct_name_from_var(&self, _var: &str) -> String {
        // This is a simplified version - in real code, we'd need context
        // For now, just return "Self"
        "Self".to_string()
    }

    /// Format constraint for display in comments
    fn format_constraint_display(&self, constraint: &SubtypeConstraint) -> String {
        match constraint {
            SubtypeConstraint::SingleValue(val) => match val {
                ConstraintValue::Integer(n) => n.to_string(),
                ConstraintValue::NamedValue(name) => name.clone(),
                ConstraintValue::Min => "MIN".to_string(),
                ConstraintValue::Max => "MAX".to_string(),
            },
            SubtypeConstraint::ValueRange { min, max } => {
                let min_str = match min {
                    ConstraintValue::Integer(n) => n.to_string(),
                    ConstraintValue::Min => "MIN".to_string(),
                    ConstraintValue::Max => "MAX".to_string(),
                    ConstraintValue::NamedValue(n) => n.clone(),
                };
                let max_str = match max {
                    ConstraintValue::Integer(n) => n.to_string(),
                    ConstraintValue::Max => "MAX".to_string(),
                    ConstraintValue::Min => "MIN".to_string(),
                    ConstraintValue::NamedValue(n) => n.clone(),
                };
                format!("{}..{}", min_str, max_str)
            }
            SubtypeConstraint::Union(elements) => {
                let parts: Vec<String> = elements
                    .iter()
                    .map(|e| self.format_constraint_display(e))
                    .collect();
                parts.join(" | ")
            }
            SubtypeConstraint::Intersection(elements) => {
                let parts: Vec<String> = elements
                    .iter()
                    .map(|e| format!("({})", self.format_constraint_display(e)))
                    .collect();
                parts.join(" ^ ")
            }
            SubtypeConstraint::Complement(inner) => {
                format!("ALL EXCEPT {}", self.format_constraint_display(inner))
            }
            SubtypeConstraint::SizeConstraint(inner) => {
                format!("SIZE ({})", self.format_constraint_display(inner))
            }
            SubtypeConstraint::PermittedAlphabet(ranges) => {
                let range_strs: Vec<String> = ranges
                    .iter()
                    .map(|r| {
                        if r.min == r.max {
                            format!("\"{}\"", r.min)
                        } else {
                            format!("\"{}\"..\"{}\"", r.min, r.max)
                        }
                    })
                    .collect();
                format!("FROM ({})", range_strs.join(" | "))
            }
            SubtypeConstraint::Pattern(pattern) => {
                format!("PATTERN \"{}\"", pattern)
            }
            SubtypeConstraint::ContainedSubtype(ty) => {
                format!("CONTAINING {}", self.rust_type(ty))
            }
            SubtypeConstraint::InnerType(inner) => {
                format!("inner type: {}", self.format_constraint_display(inner))
            }
            SubtypeConstraint::NamedBitList(bits) => {
                let names: Vec<String> = bits
                    .iter()
                    .map(|b| format!("{}({})", b.name, b.value))
                    .collect();
                format!("{{ {} }}", names.join(", "))
            }
        }
    }

    fn generate_sequence_type(
        &mut self,
        name: &str,
        fields: &[SequenceField],
    ) -> Result<(), std::fmt::Error> {
        // PRE-PASS: for each field whose underlying type is an anonymous SEQUENCE,
        // SET, or CHOICE, generate a named Rust type *before* the struct header so
        // that the field can reference it by name.  Replace the anonymous body with
        // a TypeRef in the working field list so the rest of codegen stays unchanged.
        let mut effective_fields: Vec<SequenceField> = Vec::with_capacity(fields.len());
        for field in fields {
            if let Some(anon) = anonymous_inner_type(&field.ty) {
                let anon_name = format!("{}{}", name, to_pascal_case(&field.name));
                self.generate_definition(&Definition {
                    name: anon_name.clone(),
                    ty: anon.clone(),
                })?;
                writeln!(&mut self.output)?;
                let new_ty = match &field.ty {
                    Type::Tagged { tag, .. } => Type::Tagged {
                        tag: tag.clone(),
                        inner: Box::new(Type::TypeRef(anon_name)),
                    },
                    _ => Type::TypeRef(anon_name),
                };
                effective_fields.push(SequenceField {
                    name: field.name.clone(),
                    ty: new_ty,
                    optional: field.optional,
                    default: field.default.clone(),
                });
            } else {
                effective_fields.push(field.clone());
            }
        }
        let fields: &[SequenceField] = &effective_fields;

        // Derive Default when every field is optional with no explicit ASN.1 DEFAULT —
        // in that case all fields map to None, which is always the correct default.
        let all_optional = fields.iter().all(|f| f.optional && f.default.is_none());
        if all_optional {
            writeln!(
                &mut self.output,
                "#[derive(Debug, Clone, PartialEq, Default)]"
            )?;
        } else {
            writeln!(&mut self.output, "#[derive(Debug, Clone, PartialEq)]")?;
        }
        let attr = self.derive_cfg_attr("derive(Asn1Sequence)");
        writeln!(&mut self.output, "{}", attr)?;

        // Add lifetime parameter if any field needs it
        let needs_lifetime = self.sequence_needs_lifetime(fields);
        if needs_lifetime {
            writeln!(&mut self.output, "pub struct {}<'a> {{", name)?;
            // Track that this type has a lifetime
            self.types_with_lifetimes.insert(name.to_string());
        } else {
            writeln!(&mut self.output, "pub struct {} {{", name)?;
        }

        for field in fields {
            self.generate_field(field)?;
        }

        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, needs_lifetime)?;

        Ok(())
    }

    fn generate_set_type(
        &mut self,
        name: &str,
        fields: &[SequenceField],
    ) -> Result<(), std::fmt::Error> {
        // PRE-PASS: same anonymous-inner-type handling as generate_sequence_type.
        let mut effective_fields: Vec<SequenceField> = Vec::with_capacity(fields.len());
        for field in fields {
            if let Some(anon) = anonymous_inner_type(&field.ty) {
                let anon_name = format!("{}{}", name, to_pascal_case(&field.name));
                self.generate_definition(&Definition {
                    name: anon_name.clone(),
                    ty: anon.clone(),
                })?;
                writeln!(&mut self.output)?;
                let new_ty = match &field.ty {
                    Type::Tagged { tag, .. } => Type::Tagged {
                        tag: tag.clone(),
                        inner: Box::new(Type::TypeRef(anon_name)),
                    },
                    _ => Type::TypeRef(anon_name),
                };
                effective_fields.push(SequenceField {
                    name: field.name.clone(),
                    ty: new_ty,
                    optional: field.optional,
                    default: field.default.clone(),
                });
            } else {
                effective_fields.push(field.clone());
            }
        }
        let fields: &[SequenceField] = &effective_fields;

        writeln!(&mut self.output, "#[derive(Debug, Clone, PartialEq)]")?;
        let attr = self.derive_cfg_attr("derive(Asn1Set)");
        writeln!(&mut self.output, "{}", attr)?;

        // Add lifetime parameter if any field needs it
        let needs_lifetime = self.sequence_needs_lifetime(fields);
        if needs_lifetime {
            writeln!(&mut self.output, "pub struct {}<'a> {{", name)?;
            // Track that this type has a lifetime
            self.types_with_lifetimes.insert(name.to_string());
        } else {
            writeln!(&mut self.output, "pub struct {} {{", name)?;
        }

        for field in fields {
            self.generate_field(field)?;
        }

        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, needs_lifetime)?;

        Ok(())
    }

    fn generate_choice_type(
        &mut self,
        name: &str,
        variants: &[ChoiceVariant],
    ) -> Result<(), std::fmt::Error> {
        // PRE-PASS: for each variant whose underlying type is an anonymous SEQUENCE,
        // SET, or CHOICE, generate a named Rust type *before* the enum header so
        // that the variant can reference it by name.  Replace the anonymous body with
        // a TypeRef in the working variant list so the rest of codegen stays unchanged.
        let mut effective_variants: Vec<ChoiceVariant> = Vec::with_capacity(variants.len());
        for variant in variants {
            if let Some(anon) = anonymous_inner_type(&variant.ty) {
                let anon_name = format!("{}{}", name, to_pascal_case(&variant.name));
                self.generate_definition(&Definition {
                    name: anon_name.clone(),
                    ty: anon.clone(),
                })?;
                writeln!(&mut self.output)?;
                let new_ty = match &variant.ty {
                    Type::Tagged { tag, .. } => Type::Tagged {
                        tag: tag.clone(),
                        inner: Box::new(Type::TypeRef(anon_name)),
                    },
                    _ => Type::TypeRef(anon_name),
                };
                effective_variants.push(ChoiceVariant {
                    name: variant.name.clone(),
                    ty: new_ty,
                });
            } else {
                effective_variants.push(variant.clone());
            }
        }
        let variants: &[ChoiceVariant] = &effective_variants;

        writeln!(&mut self.output, "#[derive(Debug, Clone, PartialEq)]")?;
        let attr = self.derive_cfg_attr("derive(Asn1Choice)");
        writeln!(&mut self.output, "{}", attr)?;

        // Add lifetime parameter if any variant needs it
        let needs_lifetime = self.choice_needs_lifetime(variants);
        if needs_lifetime {
            writeln!(&mut self.output, "pub enum {}<'a> {{", name)?;
            // Track that this type has a lifetime
            self.types_with_lifetimes.insert(name.to_string());
        } else {
            writeln!(&mut self.output, "pub enum {} {{", name)?;
        }

        for variant in variants {
            let variant_name = to_pascal_case(&variant.name);

            // For IMPLICIT context-specific tagged variants, force owned string types.
            // IMPLICIT tags require TLV reconstruction during decode (the context tag
            // replaces the inner type's own tag), so borrowed string types cannot borrow
            // from the original input — the reconstruction buffer is a local allocation.
            let rust_type = if let Type::Tagged { tag, .. } = &variant.ty {
                if tag.class == TagClass::ContextSpecific && tag.tagging == Tagging::Implicit {
                    let saved = self.config.string_type_mode.clone();
                    self.config.string_type_mode = StringTypeMode::Owned;
                    let ty = self.inline_sequence_of_types(&variant.ty);
                    self.config.string_type_mode = saved;
                    ty
                } else {
                    self.inline_sequence_of_types(&variant.ty)
                }
            } else {
                self.inline_sequence_of_types(&variant.ty)
            };

            // If it's a tagged type, emit the attribute with the correct tagging mode
            if let Type::Tagged { tag, .. } = &variant.ty {
                match tag.class {
                    TagClass::ContextSpecific => {
                        let tagging_str = match tag.tagging {
                            Tagging::Explicit => "explicit",
                            Tagging::Implicit => "implicit",
                        };
                        let attr = self.field_derive_cfg_attr(&format!(
                            "asn1(tag({}, {}))",
                            tag.number, tagging_str
                        ));
                        writeln!(&mut self.output, "{}", attr)?;
                    }
                    TagClass::Application => {
                        writeln!(
                            &mut self.output,
                            "    // APPLICATION [{}] -- use asn1(application_tag) when supported",
                            tag.number
                        )?;
                        let attr = self
                            .field_derive_cfg_attr(&format!("asn1(tag({}, explicit))", tag.number));
                        writeln!(&mut self.output, "{}", attr)?;
                    }
                    TagClass::Universal => {
                        writeln!(&mut self.output, "    // UNIVERSAL [{}]", tag.number)?;
                    }
                    TagClass::Private => {
                        writeln!(&mut self.output, "    // PRIVATE [{}]", tag.number)?;
                    }
                }
            }

            writeln!(&mut self.output, "    {}({}),", variant_name, rust_type)?;
        }

        writeln!(&mut self.output, "}}")?;

        self.generate_format_asn1_impl(name, needs_lifetime)?;

        Ok(())
    }

    fn generate_sequence_of_type(
        &mut self,
        name: &str,
        inner: &Type,
        size_constraint: Option<&SizeConstraint>,
    ) -> Result<(), std::fmt::Error> {
        // Handle anonymous inner types: SEQUENCE OF SEQUENCE { ... } / SET { ... } / CHOICE { ... }
        // Generate a named element type so the collection has a concrete Rust type to reference.
        if matches!(inner, Type::Sequence(_) | Type::Set(_) | Type::Choice(_)) {
            let element_name = format!("{}Element", name);
            let element_def = Definition {
                name: element_name.clone(),
                ty: inner.clone(),
            };
            self.generate_definition(&element_def)?;
            writeln!(&mut self.output)?;
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            let rust_type = format!("Vec<{}>", element_name);
            // Construct the SequenceOf type for lifetime tracking
            let seq_of_type = Type::SequenceOf(Box::new(inner.clone()), size_constraint.cloned());
            self.generate_type_alias(name, &rust_type, &seq_of_type)?;
            return Ok(());
        }

        // Handle inner type constraints (Phase 3)
        if let Type::Constrained {
            base_type,
            constraint,
        } = inner
        {
            // Generate element newtype with constrained validation
            let element_name = format!("{}Element", name);

            // Generate the constrained element type
            match base_type.as_ref() {
                Type::Integer(_, _) => {
                    if let ConstraintSpec::Subtype(ref subtype) = constraint.spec {
                        self.generate_constrained_integer(&element_name, subtype)?;
                    }
                }
                Type::IA5String(_)
                | Type::Utf8String(_)
                | Type::PrintableString(_)
                | Type::TeletexString(_)
                | Type::UniversalString(_)
                | Type::BmpString(_)
                | Type::GeneralString(_)
                | Type::NumericString(_)
                | Type::VisibleString(_) => {
                    let base_type_str = self.rust_type(base_type);
                    if let ConstraintSpec::Subtype(ref subtype) = constraint.spec {
                        self.generate_constrained_string(&element_name, &base_type_str, subtype)?;
                    }
                }
                _ => {
                    // For other types, fall back to simple type alias
                    let inner_type = self.rust_type(inner);
                    writeln!(
                        &mut self.output,
                        "pub type {} = {};",
                        element_name, inner_type
                    )?;
                }
            }

            writeln!(&mut self.output)?;

            // Generate the collection type using the element type
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            writeln!(
                &mut self.output,
                "pub type {} = Vec<{}>;",
                name, element_name
            )?;
        } else {
            // No constraint on inner type - generate simple type alias
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            let inner_type = self.rust_type(inner);
            let rust_type = format!("Vec<{}>", inner_type);
            // Construct the SequenceOf/SetOf type for lifetime tracking
            let seq_of_type = Type::SequenceOf(Box::new(inner.clone()), size_constraint.cloned());
            self.generate_type_alias(name, &rust_type, &seq_of_type)?;
        }
        Ok(())
    }

    fn generate_set_of_type(
        &mut self,
        name: &str,
        inner: &Type,
        size_constraint: Option<&SizeConstraint>,
    ) -> Result<(), std::fmt::Error> {
        // Handle anonymous inner types: SET OF SEQUENCE { ... } / SET { ... } / CHOICE { ... }
        if matches!(inner, Type::Sequence(_) | Type::Set(_) | Type::Choice(_)) {
            let element_name = format!("{}Element", name);
            let element_def = Definition {
                name: element_name.clone(),
                ty: inner.clone(),
            };
            self.generate_definition(&element_def)?;
            writeln!(&mut self.output)?;
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            let rust_type = format!("SetOf<{}>", element_name);
            // Construct the SetOf type for lifetime tracking
            let seq_of_type = Type::SetOf(Box::new(inner.clone()), size_constraint.cloned());
            self.generate_type_alias(name, &rust_type, &seq_of_type)?;
            return Ok(());
        }

        // Handle inner type constraints (Phase 3) - same as SEQUENCE OF
        if let Type::Constrained {
            base_type,
            constraint,
        } = inner
        {
            // Generate element newtype with constrained validation
            let element_name = format!("{}Element", name);

            // Generate the constrained element type
            match base_type.as_ref() {
                Type::Integer(_, _) => {
                    if let ConstraintSpec::Subtype(ref subtype) = constraint.spec {
                        self.generate_constrained_integer(&element_name, subtype)?;
                    }
                }
                Type::IA5String(_)
                | Type::Utf8String(_)
                | Type::PrintableString(_)
                | Type::TeletexString(_)
                | Type::UniversalString(_)
                | Type::BmpString(_)
                | Type::GeneralString(_)
                | Type::NumericString(_)
                | Type::VisibleString(_) => {
                    let base_type_str = self.rust_type(base_type);
                    if let ConstraintSpec::Subtype(ref subtype) = constraint.spec {
                        self.generate_constrained_string(&element_name, &base_type_str, subtype)?;
                    }
                }
                _ => {
                    // For other types, fall back to simple type alias
                    let inner_type = self.rust_type(inner);
                    writeln!(
                        &mut self.output,
                        "pub type {} = {};",
                        element_name, inner_type
                    )?;
                }
            }

            writeln!(&mut self.output)?;

            // Generate the collection type using the element type
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            writeln!(
                &mut self.output,
                "pub type {} = SetOf<{}>;",
                name, element_name
            )?;
        } else {
            // No constraint on inner type - generate simple type alias
            if let Some(constraint) = size_constraint {
                let constraint_str = self.format_size_constraint(constraint);
                writeln!(&mut self.output, "// Constraint: {}", constraint_str)?;
            }
            let inner_type = self.rust_type(inner);
            let rust_type = format!("SetOf<{}>", inner_type);
            // Construct the SetOf type for lifetime tracking
            let seq_of_type = Type::SetOf(Box::new(inner.clone()), size_constraint.cloned());
            self.generate_type_alias(name, &rust_type, &seq_of_type)?;
        }
        Ok(())
    }

    /// Return `true` when `ty` resolves to `Type::Any` or `Type::AnyDefinedBy`,
    /// following up to one level of TypeRef indirection through `type_definitions`.
    fn resolves_to_any(&self, ty: &Type) -> bool {
        match ty {
            Type::Any | Type::AnyDefinedBy(_) => true,
            Type::TypeRef(name) => {
                let clean = name.trim_end_matches("{}");
                matches!(
                    self.type_definitions.get(clean),
                    Some(Type::Any) | Some(Type::AnyDefinedBy(_))
                )
            }
            _ => false,
        }
    }

    /// Return `true` when `ty` resolves to `Type::Choice`,
    /// following up to one level of TypeRef indirection through `type_definitions`
    /// or via the `config.known_choice_types` set (for imported types).
    ///
    /// Per ASN.1 X.680 §31.2.7, IMPLICIT tagging cannot be applied to CHOICE
    /// types; such tags must be treated as EXPLICIT.
    fn resolves_to_choice(&self, ty: &Type) -> bool {
        match ty {
            Type::Choice(_) => true,
            Type::TypeRef(name) => {
                let clean = name.trim_end_matches("{}");
                self.config.known_choice_types.contains(clean)
                    || matches!(self.type_definitions.get(clean), Some(Type::Choice(_)))
            }
            _ => false,
        }
    }

    fn generate_field(&mut self, field: &SequenceField) -> Result<(), std::fmt::Error> {
        let field_name = to_snake_case(&field.name);
        // Inline SEQUENCE OF and SET OF types to enable derive macro Vec<T<'a>> detection
        let rust_type = self.inline_sequence_of_types(&field.ty);

        // Add attribute for tagged fields
        if let Type::Tagged { tag, inner } = &field.ty {
            let tagging = match tag.tagging {
                Tagging::Explicit => "explicit",
                // ASN.1 X.680 §31.2.7: IMPLICIT tagging cannot be applied to CHOICE;
                // such a tag is automatically treated as EXPLICIT.
                // Note: IMPLICIT ANY is NOT promoted — the rawder mechanism handles
                // it specially via the any_as_raw_der config option.
                Tagging::Implicit if self.resolves_to_choice(inner) => "explicit",
                Tagging::Implicit => "implicit",
            };
            match tag.class {
                TagClass::ContextSpecific => {
                    let attr = self
                        .field_derive_cfg_attr(&format!("asn1(tag({}, {}))", tag.number, tagging));
                    writeln!(&mut self.output, "{}", attr)?;
                    // When any_as_raw_der = true, IMPLICIT-tagged ANY fields are emitted as
                    // RawDer<'a>.  The type alias (e.g. `CertificateSet<'a> = RawDer<'a>`) is
                    // opaque to the derive macro, which cannot detect that the aliased type is
                    // RawDer and therefore cannot select the correct encode path.  Emit a
                    // `rawder` marker attribute so the derive's encode path can use the direct
                    // content-write approach instead of the "encode then strip" approach.
                    if self.config.any_as_raw_der
                        && tag.tagging == Tagging::Implicit
                        && self.resolves_to_any(inner)
                    {
                        let rawder_attr = self.field_derive_cfg_attr("asn1(rawder)");
                        writeln!(&mut self.output, "{}", rawder_attr)?;
                    }
                }
                TagClass::Application => {
                    writeln!(
                        &mut self.output,
                        "    // APPLICATION [{} {}] -- use asn1(application_tag) when supported",
                        tag.number, tagging
                    )?;
                    let attr = self
                        .field_derive_cfg_attr(&format!("asn1(tag({}, {}))", tag.number, tagging));
                    writeln!(&mut self.output, "{}", attr)?;
                }
                TagClass::Universal => {
                    writeln!(
                        &mut self.output,
                        "    // UNIVERSAL [{}] {}",
                        tag.number, tagging
                    )?;
                }
                TagClass::Private => {
                    writeln!(
                        &mut self.output,
                        "    // PRIVATE [{}] {}",
                        tag.number, tagging
                    )?;
                }
            }
        }

        // Add optional attribute
        // Fields with DEFAULT values are implicitly optional in ASN.1
        if field.optional || field.default.is_some() {
            let attr = self.field_derive_cfg_attr("asn1(optional)");
            writeln!(&mut self.output, "{}", attr)?;
        }

        // Override with RawDer<'a> for fields listed in raw_der_fields.
        let rust_type = if self.config.raw_der_fields.contains(&field_name) {
            "RawDer<'a>".to_string()
        } else {
            rust_type
        };

        // Fields are Option<T> if explicitly OPTIONAL or have DEFAULT values
        let final_type = if field.optional || field.default.is_some() {
            format!("Option<{}>", rust_type)
        } else {
            rust_type
        };

        writeln!(&mut self.output, "    pub {}: {},", field_name, final_type)?;

        Ok(())
    }

    /// Generate a subtype definition (TypeRef with additional constraints)
    fn generate_subtype(
        &mut self,
        type_name: &str,
        base_type: &Type,
        constraint: &SubtypeConstraint,
    ) -> Result<(), std::fmt::Error> {
        let base_type_name = self.rust_type(base_type);
        let constraint_display = self.format_constraint_display(constraint);

        // Generate doc comment
        writeln!(
            &mut self.output,
            "/// {} ({})",
            base_type_name, constraint_display
        )?;

        // Generate newtype struct
        writeln!(
            &mut self.output,
            "#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]"
        )?;
        writeln!(
            &mut self.output,
            "pub struct {}({});",
            type_name, base_type_name
        )?;
        writeln!(&mut self.output)?;

        writeln!(&mut self.output, "impl {} {{", type_name)?;

        // Generate validation code
        // The approach: convert the base type to its underlying primitive, then validate
        let validation_code = self.generate_subtype_validation("val", constraint)?;

        writeln!(
            &mut self.output,
            "    /// Create a new {} with validation",
            type_name
        )?;
        writeln!(
            &mut self.output,
            "    pub fn new(value: {}) -> Result<Self, &'static str> {{",
            base_type_name
        )?;

        // Determine if this is an integer or string constraint
        let is_integer_constraint = matches!(
            constraint,
            SubtypeConstraint::SingleValue(_)
                | SubtypeConstraint::ValueRange { .. }
                | SubtypeConstraint::Union(_)
                | SubtypeConstraint::Intersection(_)
                | SubtypeConstraint::Complement(_)
        );

        let description = self.generate_constraint_description(constraint);

        if is_integer_constraint {
            writeln!(&mut self.output, "        let val = value.into_inner();")?;
            writeln!(&mut self.output, "        if {} {{", validation_code)?;
            writeln!(&mut self.output, "            Ok({}(value))", type_name)?;
            writeln!(&mut self.output, "        }} else {{")?;
            writeln!(&mut self.output, "            Err(\"{}\")", description)?;
            writeln!(&mut self.output, "        }}")?;
        } else {
            // String subtype - work with the string value directly
            let validation_code =
                self.generate_string_validation("value", &base_type_name, constraint);
            write!(&mut self.output, "{}", validation_code)?;
        }

        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Generate unchecked constructor
        writeln!(
            &mut self.output,
            "    /// Create without validation (use with caution)"
        )?;
        writeln!(
            &mut self.output,
            "    pub const fn new_unchecked(value: {}) -> Self {{",
            base_type_name
        )?;
        writeln!(&mut self.output, "        {}(value)", type_name)?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Generate get method
        writeln!(&mut self.output, "    /// Get the inner value")?;
        writeln!(
            &mut self.output,
            "    pub const fn get(&self) -> &{} {{",
            base_type_name
        )?;
        writeln!(&mut self.output, "        &self.0")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;

        // Generate into_inner method
        writeln!(
            &mut self.output,
            "    /// Consume and return the inner value"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn into_inner(self) -> {} {{",
            base_type_name
        )?;
        writeln!(&mut self.output, "        self.0")?;
        writeln!(&mut self.output, "    }}")?;

        writeln!(&mut self.output, "}}")?;
        writeln!(&mut self.output)?;

        // Generate TryFrom impl
        let try_from_path = self.try_from_path();
        writeln!(
            &mut self.output,
            "impl {}::convert::TryFrom<{}> for {} {{",
            try_from_path, base_type_name, type_name
        )?;
        writeln!(&mut self.output, "    type Error = &'static str;")?;
        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "    fn try_from(value: {}) -> Result<Self, Self::Error> {{",
            base_type_name
        )?;
        writeln!(&mut self.output, "        Self::new(value)")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;

        Ok(())
    }

    /// Generate validation code for subtype constraints
    fn generate_subtype_validation(
        &mut self,
        var: &str,
        constraint: &SubtypeConstraint,
    ) -> Result<String, std::fmt::Error> {
        // Delegate to generate_constraint_validation which works with i64
        // This assumes the base type can be converted to Integer
        Ok(self.generate_constraint_validation(var, constraint))
    }

    /// Emit `impl [<'a>] TypeName[<'a>] { pub fn to_der(...) pub fn format_asn1(...) }`
    /// after any generated struct/enum that implements `Encode`.
    ///
    /// `to_der` encodes `self` to DER bytes and returns a `synta::Result<Vec<u8>>`.
    /// `format_asn1` encodes `self` to DER and delegates to
    /// `synta::format_asn1_bytes`, which supports both raw hex and
    /// human-readable ASN.1 text output.
    fn generate_format_asn1_impl(
        &mut self,
        name: &str,
        has_lifetime: bool,
    ) -> Result<(), std::fmt::Error> {
        writeln!(&mut self.output)?;
        if has_lifetime {
            writeln!(&mut self.output, "impl<'a> {}<'a> {{", name)?;
        } else {
            writeln!(&mut self.output, "impl {} {{", name)?;
        }
        // from_der()
        if has_lifetime {
            writeln!(
                &mut self.output,
                "    /// Parse a DER-encoded `{}` from borrowed bytes.",
                name
            )?;
            writeln!(&mut self.output, "    ///")?;
            writeln!(
                &mut self.output,
                "    /// The returned value borrows from `data` for zero-copy fields."
            )?;
            writeln!(
                &mut self.output,
                "    pub fn from_der(data: &'a [u8]) -> synta::Result<Self> {{"
            )?;
        } else {
            writeln!(
                &mut self.output,
                "    /// Parse a DER-encoded `{}` from bytes.",
                name
            )?;
            writeln!(
                &mut self.output,
                "    pub fn from_der(data: &[u8]) -> synta::Result<Self> {{"
            )?;
        }
        writeln!(
            &mut self.output,
            "        synta::Decoder::new(data, synta::Encoding::Der).decode::<Self>()"
        )?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output)?;
        // to_der()
        writeln!(&mut self.output, "    /// Encode this value to DER bytes.")?;
        writeln!(&mut self.output, "    ///")?;
        writeln!(
            &mut self.output,
            "    /// Returns a [`synta::Result`] wrapping the DER-encoded bytes,"
        )?;
        writeln!(&mut self.output, "    /// or an error if encoding fails.")?;
        writeln!(
            &mut self.output,
            "    pub fn to_der(&self) -> synta::Result<Vec<u8>> {{"
        )?;
        writeln!(&mut self.output, "        use synta::Encode;")?;
        writeln!(
            &mut self.output,
            "        let mut encoder = synta::Encoder::new(synta::Encoding::Der);"
        )?;
        writeln!(&mut self.output, "        self.encode(&mut encoder)?;")?;
        writeln!(&mut self.output, "        encoder.finish()")?;
        writeln!(&mut self.output, "    }}")?;
        // format_asn1()
        writeln!(&mut self.output)?;
        writeln!(
            &mut self.output,
            "    /// Format the encoded DER bytes of this value."
        )?;
        writeln!(&mut self.output, "    ///")?;
        writeln!(
            &mut self.output,
            "    /// `mode` controls the output style:"
        )?;
        writeln!(
            &mut self.output,
            "    /// - [`synta::Asn1FormatMode::Hex`] — space-separated uppercase hex bytes"
        )?;
        writeln!(
            &mut self.output,
            "    /// - [`synta::Asn1FormatMode::Text`] — indented human-readable ASN.1 dump"
        )?;
        writeln!(
            &mut self.output,
            "    pub fn format_asn1(&self, mode: synta::Asn1FormatMode) -> String {{"
        )?;
        writeln!(&mut self.output, "        use synta::Encode;")?;
        writeln!(
            &mut self.output,
            "        let mut encoder = synta::Encoder::new(synta::Encoding::Der);"
        )?;
        writeln!(
            &mut self.output,
            "        if self.encode(&mut encoder).is_err() {{"
        )?;
        writeln!(
            &mut self.output,
            "            return String::from(\"<encode error>\");"
        )?;
        writeln!(&mut self.output, "        }}")?;
        writeln!(&mut self.output, "        match encoder.finish() {{")?;
        writeln!(
            &mut self.output,
            "            Ok(bytes) => synta::format_asn1_bytes(&bytes, mode),"
        )?;
        writeln!(
            &mut self.output,
            "            Err(_) => String::from(\"<encode error>\"),"
        )?;
        writeln!(&mut self.output, "        }}")?;
        writeln!(&mut self.output, "    }}")?;
        writeln!(&mut self.output, "}}")?;
        Ok(())
    }

    /// Return the Rust type name for an ASN.1 string type, respecting the
    /// configured [`StringTypeMode`].
    ///
    /// Types that have a zero-copy `Ref` variant (e.g. `OctetString` /
    /// `OctetStringRef<'a>`) use `borrowed` in [`StringTypeMode::Borrowed`]
    /// mode. Types that only have an owned form (e.g. `TeletexString`) are
    /// returned as-is regardless of mode.
    #[inline]
    fn string_rust_type(&self, owned: &str, borrowed: &str) -> String {
        match self.config.string_type_mode {
            StringTypeMode::Owned => owned.to_string(),
            StringTypeMode::Borrowed => format!("{}<'a>", borrowed),
        }
    }

    fn rust_type(&self, ty: &Type) -> String {
        match ty {
            Type::Integer(_, _) => "Integer".to_string(),
            Type::Enumerated(_) => "Enumerated".to_string(),
            Type::Real => "f64".to_string(),
            Type::Boolean => "Boolean".to_string(),
            // Types with both owned and zero-copy borrowed variants
            Type::OctetString(_) => self.string_rust_type("OctetString", "OctetStringRef"),
            Type::BitString(_) => self.string_rust_type("BitString", "BitStringRef"),
            Type::Utf8String(_) => self.string_rust_type("Utf8String", "Utf8StringRef"),
            Type::PrintableString(_) => {
                self.string_rust_type("PrintableString", "PrintableStringRef")
            }
            Type::IA5String(_) => self.string_rust_type("IA5String", "IA5StringRef"),
            Type::ObjectIdentifier => "ObjectIdentifier".to_string(),
            Type::RelativeOid => "RelativeOid".to_string(),
            Type::Null => "Null".to_string(),
            // Types without a Ref variant — always owned
            Type::TeletexString(_) => "TeletexString".to_string(),
            Type::UniversalString(_) => "UniversalString".to_string(),
            Type::BmpString(_) => "BmpString".to_string(),
            Type::GeneralString(_) => "GeneralString".to_string(),
            Type::NumericString(_) => "NumericString".to_string(),
            Type::VisibleString(_) => "VisibleString".to_string(),
            Type::UtcTime => "UtcTime".to_string(),
            Type::GeneralizedTime => "GeneralizedTime".to_string(),
            Type::TypeRef(name) => {
                let type_name = to_pascal_case(name);

                // Check if this type requires a specific lifetime parameter.
                // Applies to both explicitly imported types (IMPORTS section) and
                // bare TypeRefs that reference types from other schemas without a
                // formal IMPORTS declaration — `imported_types` membership is not
                // required for the lookup.
                if let Some(lifetime) = self.config.imported_type_lifetimes.get(name) {
                    return format!("{}<{}>", type_name, lifetime);
                }

                // Check if this is a locally-generated type that has a lifetime
                if self.types_with_lifetimes.contains(&type_name) {
                    return format!("{}<'a>", type_name);
                }

                type_name
            }
            Type::Class(_) => "/* class */".to_string(),
            Type::Sequence(_) => "/* nested sequence */".to_string(),
            Type::Set(_) => "/* nested set */".to_string(),
            Type::Choice(_) => "/* nested choice */".to_string(),
            Type::SequenceOf(inner, _) => format!("Vec<{}>", self.rust_type(inner)),
            Type::SetOf(inner, _) => format!("SetOf<{}>", self.rust_type(inner)),
            Type::Tagged { inner, .. } => self.rust_type(inner),
            Type::Constrained { base_type, .. } => self.rust_type(base_type),
            Type::Any => {
                if self.config.any_as_raw_der {
                    "RawDer<'a>".to_string()
                } else {
                    "Element<'a>".to_string()
                }
            }
            Type::AnyDefinedBy(_) => {
                if self.config.any_as_raw_der {
                    "RawDer<'a>".to_string()
                } else {
                    "Element<'a>".to_string()
                }
            }
        }
    }

    /// Return `true` when `ty` requires a `'a` lifetime parameter.
    ///
    /// This is `true` when any of the following apply:
    /// - The type is `OctetString`, `BitString`, `Utf8String`, `PrintableString`,
    ///   or `IA5String` and [`StringTypeMode::Borrowed`] is active.
    /// - The type is `ANY` / `ANY DEFINED BY` (always `Element<'a>`).
    /// - The type is a reference to an imported type whose lifetime was declared
    ///   via [`CodeGenConfig::imported_type_lifetimes`].
    /// - The type is a reference to a locally-generated type that was previously
    ///   determined to need a lifetime (fixed-point prescan).
    /// - The type is a `SEQUENCE OF`, `SET OF`, tagged, or constrained wrapper
    ///   around a type that needs a lifetime.
    fn type_needs_lifetime(&self, ty: &Type) -> bool {
        match ty {
            // Types with Ref variants: need lifetime in Borrowed mode
            Type::OctetString(_)
            | Type::BitString(_)
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_) => self.config.string_type_mode == StringTypeMode::Borrowed,
            Type::Any => true,             // Element<'a>
            Type::AnyDefinedBy(_) => true, // Element<'a>

            Type::TypeRef(name) => {
                let type_name = to_pascal_case(name);

                // Check if this type requires a lifetime parameter (from config).
                // Does not require the type to be in the IMPORTS section.
                if self.config.imported_type_lifetimes.contains_key(name) {
                    return true;
                }

                // Check if this is a locally-generated type that has a lifetime
                if self.types_with_lifetimes.contains(&type_name) {
                    return true;
                }

                false
            }
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => self.type_needs_lifetime(inner),
            Type::Tagged { inner, .. }
            | Type::Constrained {
                base_type: inner, ..
            } => self.type_needs_lifetime(inner),
            Type::Sequence(fields) => fields.iter().any(|f| self.type_needs_lifetime(&f.ty)),
            Type::Set(fields) => fields.iter().any(|f| self.type_needs_lifetime(&f.ty)),
            Type::Choice(variants) => variants.iter().any(|v| self.type_needs_lifetime(&v.ty)),
            _ => false,
        }
    }

    /// Check if a sequence type needs a lifetime parameter
    fn sequence_needs_lifetime(&self, fields: &[SequenceField]) -> bool {
        fields.iter().any(|field| {
            let field_name = to_snake_case(&field.name);
            self.config.raw_der_fields.contains(&field_name) || self.type_needs_lifetime(&field.ty)
        })
    }

    /// Check if a choice type needs a lifetime parameter
    fn choice_needs_lifetime(&self, variants: &[ChoiceVariant]) -> bool {
        // Delegate uniformly to type_needs_lifetime, which recurses through Tagged
        // wrappers (both Explicit and Implicit) to check the inner type.
        // The previous early-return for IMPLICIT context tags was incorrect: it
        // prevented lifetime propagation for e.g. `[0] V2Form` where V2Form<'a>
        // requires a lifetime even though the outer tag is IMPLICIT.
        variants
            .iter()
            .any(|variant| self.type_needs_lifetime(&variant.ty))
    }

    /// Generate a type alias declaration, adding lifetime parameter if needed
    fn generate_type_alias(
        &mut self,
        type_name: &str,
        rust_type: &str,
        asn1_type: &Type,
    ) -> Result<(), std::fmt::Error> {
        // Check if the type needs a lifetime by analyzing the ASN.1 type structure.
        // This is more reliable than checking the rust_type string, especially for
        // forward references where the RHS type may not yet be in types_with_lifetimes.
        let needs_lifetime = self.type_needs_lifetime(asn1_type);

        if needs_lifetime {
            writeln!(
                &mut self.output,
                "pub type {}<'a> = {};",
                type_name, rust_type
            )?;
            // Track that this type alias has a lifetime parameter so that
            // later references to it will include the lifetime
            self.types_with_lifetimes.insert(type_name.to_string());
        } else {
            writeln!(&mut self.output, "pub type {} = {};", type_name, rust_type)?;
        }
        Ok(())
    }

    /// Build OID registry from value assignments for resolving named references
    fn build_oid_registry(
        &self,
        values: &[crate::ast::ValueAssignment],
    ) -> std::collections::HashMap<String, Vec<u32>> {
        use std::collections::HashMap;
        let mut registry: HashMap<String, Vec<u32>> = HashMap::new();

        // Iterate multiple times to resolve dependencies
        let mut changed = true;
        while changed {
            changed = false;
            for value_assignment in values {
                if registry.contains_key(&value_assignment.name) {
                    continue;
                }

                if let crate::ast::Value::ObjectIdentifier(components) = &value_assignment.value {
                    let mut resolved = Vec::new();
                    let mut can_resolve = true;

                    for component in components {
                        match component {
                            crate::ast::OidComponent::Number(n) => {
                                resolved.push(*n);
                            }
                            crate::ast::OidComponent::NamedRef(name) => {
                                if let Some(base_oid) = registry.get(name) {
                                    resolved.extend_from_slice(base_oid);
                                } else {
                                    can_resolve = false;
                                    break;
                                }
                            }
                        }
                    }

                    if can_resolve {
                        registry.insert(value_assignment.name.clone(), resolved);
                        changed = true;
                    }
                }
            }
        }

        registry
    }

    /// Generate a value assignment as a constant
    fn generate_value_assignment(
        &mut self,
        value_assignment: &crate::ast::ValueAssignment,
        oid_registry: &std::collections::HashMap<String, Vec<u32>>,
    ) -> Result<(), std::fmt::Error> {
        let const_name = to_screaming_snake_case(&value_assignment.name);

        match &value_assignment.value {
            crate::ast::Value::ObjectIdentifier(_components) => {
                // Look up the resolved OID from the registry
                if let Some(oid_values) = oid_registry.get(&value_assignment.name) {
                    // Generate constant
                    write!(&mut self.output, "pub const {}: &[u32] = &[", const_name)?;
                    for (i, value) in oid_values.iter().enumerate() {
                        if i > 0 {
                            write!(&mut self.output, ", ")?;
                        }
                        write!(&mut self.output, "{}", value)?;
                    }
                    writeln!(&mut self.output, "];")?;
                } else {
                    // OID couldn't be fully resolved - skip it
                    writeln!(
                        &mut self.output,
                        "// Note: Could not resolve OID for {}",
                        value_assignment.name
                    )?;
                }
            }
            crate::ast::Value::Integer(n) => {
                writeln!(&mut self.output, "pub const {}: i64 = {};", const_name, n)?;
            }
            crate::ast::Value::Boolean(b) => {
                writeln!(&mut self.output, "pub const {}: bool = {};", const_name, b)?;
            }
            crate::ast::Value::String(s) => {
                writeln!(
                    &mut self.output,
                    "pub const {}: &str = \"{}\";",
                    const_name, s
                )?;
            }
            crate::ast::Value::Identifier(name) => {
                writeln!(
                    &mut self.output,
                    "pub const {}: i64 = {} as i64;",
                    const_name,
                    to_screaming_snake_case(name)
                )?;
            }
        }

        Ok(())
    }

    /// Pre-scan all type definitions to determine which need lifetimes
    /// This handles forward references by iterating until a fixed point
    fn prescan_types_for_lifetimes(&mut self, definitions: &[Definition]) {
        // Iterate until we reach a fixed point (no new types with lifetimes discovered)
        let mut changed = true;
        while changed {
            changed = false;

            for def in definitions {
                // Skip if already in the set or should be skipped
                let type_name = to_pascal_case(&def.name);
                if self.types_with_lifetimes.contains(&type_name) {
                    continue;
                }
                if self.config.skip_imported_types.contains(&def.name) {
                    continue;
                }

                // Check if this type needs a lifetime
                let needs_lifetime = match &def.ty {
                    Type::Sequence(fields) => self.sequence_needs_lifetime(fields),
                    Type::Set(fields) => self.sequence_needs_lifetime(fields),
                    Type::Choice(variants) => self.choice_needs_lifetime(variants),
                    // Special case: BitString/OctetString with NamedBitList generates owned types (no lifetime)
                    Type::Constrained {
                        base_type: _,
                        constraint,
                    } => match constraint.spec {
                        ConstraintSpec::Subtype(SubtypeConstraint::NamedBitList(_)) => false,
                        ConstraintSpec::Subtype(SubtypeConstraint::Intersection(
                            ref constraints,
                        )) if constraints
                            .iter()
                            .any(|c| matches!(c, SubtypeConstraint::NamedBitList(_))) =>
                        {
                            false
                        }
                        _ => self.type_needs_lifetime(&def.ty),
                    },
                    // For all other types, use the general type_needs_lifetime check
                    other => self.type_needs_lifetime(other),
                };

                if needs_lifetime {
                    self.types_with_lifetimes.insert(type_name);
                    changed = true;
                }
            }
        }
    }

    /// Recursively inline SEQUENCE OF and SET OF types for CHOICE variants and struct fields
    /// This enables the derive macro to detect Vec<T<'a>> patterns even when nested or tagged
    fn inline_sequence_of_types(&self, ty: &Type) -> String {
        match ty {
            Type::TypeRef(type_ref_name) => {
                let type_name = to_pascal_case(type_ref_name);
                if let Some(def_type) = self.type_definitions.get(&type_name) {
                    match def_type {
                        Type::SequenceOf(inner, _) => {
                            // Recursively inline the inner type in case it's also a SequenceOf/SetOf
                            let inner_rust_type = self.inline_sequence_of_types(inner);
                            format!("Vec<{}>", inner_rust_type)
                        }
                        Type::SetOf(inner, _) => {
                            // Recursively inline the inner type in case it's also a SetOf
                            let inner_rust_type = self.inline_sequence_of_types(inner);
                            format!("SetOf<{}>", inner_rust_type)
                        }
                        _ => self.rust_type(ty),
                    }
                } else {
                    self.rust_type(ty)
                }
            }
            // For tagged types, inline the inner type
            Type::Tagged { inner, .. } => self.inline_sequence_of_types(inner),
            // For constrained types, inline the base type
            Type::Constrained { base_type, .. } => self.inline_sequence_of_types(base_type),
            _ => self.rust_type(ty),
        }
    }
}

impl Default for CodeGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// Return the anonymous inner type if `ty` (after stripping exactly one layer
/// of `Tagged` or `Constrained`) is a bare SEQUENCE, SET, or CHOICE body.
///
/// Named `TypeRef`s are excluded — they are already concrete Rust types.
/// Only returns `Some` when the body is an *inline* anonymous structural type
/// that has not yet been given a name and cannot be referenced as-is.
fn anonymous_inner_type(ty: &Type) -> Option<&Type> {
    let candidate = match ty {
        Type::Tagged { inner, .. } => inner.as_ref(),
        Type::Constrained { base_type, .. } => base_type.as_ref(),
        other => other,
    };
    matches!(
        candidate,
        Type::Sequence(_) | Type::Set(_) | Type::Choice(_)
    )
    .then_some(candidate)
}

/// Generate Rust code from an ASN.1 module using default configuration.
///
/// All string and binary types are emitted as owned heap-allocating types
/// (e.g. `OctetString`, `BitString`).  Use [`generate_with_config`] together
/// with [`CodeGenConfig`] to customise the output (e.g. to switch to
/// zero-copy borrowed types via [`StringTypeMode::Borrowed`]).
pub fn generate(module: &Module) -> Result<String, std::fmt::Error> {
    let mut gen = CodeGenerator::new();
    gen.generate_module(module)
}

/// Generate Rust code from an ASN.1 module with custom configuration.
///
/// # Configuration options
///
/// - **`string_type_mode`** — choose between owned heap-allocating types
///   (`OctetString`, `BitString`, …) and zero-copy borrowed types
///   (`OctetStringRef<'a>`, `BitStringRef<'a>`, …).  See [`StringTypeMode`].
/// - **`module_path_prefix`** — emit `use <prefix>::<module>::Type;` statements
///   instead of comment-only import annotations.  See
///   [`CodeGenConfig::with_crate_imports`], [`CodeGenConfig::with_super_imports`],
///   [`CodeGenConfig::with_custom_prefix`].
/// - **`use_core`** — emit `core::convert::TryFrom` instead of
///   `std::convert::TryFrom` for `#![no_std]` environments.
/// - **`skip_imported_types`** / **`imported_type_lifetimes`** — fine-grained
///   control over which imported types are emitted and which carry a lifetime.
pub fn generate_with_config(
    module: &Module,
    config: CodeGenConfig,
) -> Result<String, std::fmt::Error> {
    let mut gen = CodeGenerator::with_config(config);
    gen.generate_module(module)
}
