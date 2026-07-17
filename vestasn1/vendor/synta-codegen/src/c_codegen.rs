//! C code generator using libcsynta API
//!
//! This module generates C code that uses the libcsynta C API to encode/decode
//! ASN.1 structures defined in an ASN.1 module.

use crate::ast::*;
use crate::naming::{module_file_stem, to_pascal_case, to_screaming_snake_case, to_snake_case};
use std::fmt::Write;

/// Configuration options for C code generation
#[derive(Debug, Clone, Default)]
pub struct CCodeGenConfig {
    /// Include path for synta.h (default: "synta.h")
    pub synta_header_path: Option<String>,
    /// Add static inline functions for common operations
    pub generate_helpers: bool,
    /// Generate SyntaArena type and _decode_arena() prototypes
    pub arena_mode: bool,
}

impl CCodeGenConfig {
    /// Create config with custom synta header path
    pub fn with_header_path(path: impl Into<String>) -> Self {
        Self {
            synta_header_path: Some(path.into()),
            generate_helpers: false,
            arena_mode: false,
        }
    }

    /// Enable generating helper functions
    pub fn with_helpers(mut self) -> Self {
        self.generate_helpers = true;
        self
    }

    /// Enable arena/bump allocator mode
    pub fn with_arena(mut self) -> Self {
        self.arena_mode = true;
        self
    }
}

// ── Anonymous inner type expansion ───────────────────────────────────────────
//
// When an ASN.1 SEQUENCE field or CHOICE variant contains an anonymous inline
// SEQUENCE / SET / CHOICE body, the Rust codegen extracts it into a named type
// before the enclosing type.  The C codegen must do the same: C unions cannot
// embed anonymous structs by value without a name, and the `void*` placeholder
// we previously emitted for CHOICE variants was not type-safe.
//
// `expand_anonymous_types()` rewrites the definition list so that every
// anonymous body becomes a named `Definition` inserted immediately before the
// parent.  The parent's field/variant type is replaced by a `TypeRef` to the
// new name.  The topological sort (`topo_order`) then handles ordering.

/// Strip the outermost `Tagged` / `Constrained` wrapper and return `Some(body)`
/// if the result is an anonymous inline SEQUENCE, SET, or CHOICE.
fn anonymous_inner_c(ty: &Type) -> Option<&Type> {
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

/// Re-wrap `inner` inside the outermost `Tagged` or `Constrained` layer of
/// `original` so that tag annotation comments are preserved in the C output.
fn rewrap_with_tag(original: &Type, inner: Type) -> Type {
    match original {
        Type::Tagged { tag, .. } => Type::Tagged {
            tag: tag.clone(),
            inner: Box::new(inner),
        },
        Type::Constrained { constraint, .. } => Type::Constrained {
            base_type: Box::new(inner),
            constraint: constraint.clone(),
        },
        _ => inner,
    }
}

/// Expand anonymous inner types in `fields`, pushing synthetic `Definition`s
/// into `synthetics` and replacing the inline body with a `TypeRef`.
fn expand_fields(
    fields: &[SequenceField],
    parent_name: &str,
    synthetics: &mut Vec<Definition>,
) -> Vec<SequenceField> {
    fields
        .iter()
        .map(|field| {
            if let Some(body) = anonymous_inner_c(&field.ty) {
                let syn_name = format!(
                    "{}{}",
                    to_pascal_case(parent_name),
                    to_pascal_case(&field.name)
                );
                let expanded_body = expand_type(body, &syn_name, synthetics);
                synthetics.push(Definition {
                    name: syn_name.clone(),
                    ty: expanded_body,
                });
                SequenceField {
                    name: field.name.clone(),
                    ty: rewrap_with_tag(&field.ty, Type::TypeRef(syn_name)),
                    optional: field.optional,
                    default: field.default.clone(),
                }
            } else {
                field.clone()
            }
        })
        .collect()
}

/// Expand anonymous inner types in `variants`, pushing synthetic `Definition`s
/// into `synthetics` and replacing the inline body with a `TypeRef`.
fn expand_variants(
    variants: &[ChoiceVariant],
    parent_name: &str,
    synthetics: &mut Vec<Definition>,
) -> Vec<ChoiceVariant> {
    variants
        .iter()
        .map(|variant| {
            if let Some(body) = anonymous_inner_c(&variant.ty) {
                let syn_name = format!(
                    "{}{}",
                    to_pascal_case(parent_name),
                    to_pascal_case(&variant.name)
                );
                let expanded_body = expand_type(body, &syn_name, synthetics);
                synthetics.push(Definition {
                    name: syn_name.clone(),
                    ty: expanded_body,
                });
                ChoiceVariant {
                    name: variant.name.clone(),
                    ty: rewrap_with_tag(&variant.ty, Type::TypeRef(syn_name)),
                }
            } else {
                variant.clone()
            }
        })
        .collect()
}

/// Recursively expand anonymous inline bodies found inside `ty`.
fn expand_type(ty: &Type, parent_name: &str, synthetics: &mut Vec<Definition>) -> Type {
    match ty {
        Type::Sequence(fields) => Type::Sequence(expand_fields(fields, parent_name, synthetics)),
        Type::Set(fields) => Type::Set(expand_fields(fields, parent_name, synthetics)),
        Type::Choice(variants) => Type::Choice(expand_variants(variants, parent_name, synthetics)),
        other => other.clone(),
    }
}

/// Expand all anonymous inline SEQUENCE / SET / CHOICE bodies in `defs` into
/// named synthetic definitions, returning an extended definition list.
///
/// Each synthetic definition is inserted immediately before the parent so that
/// `topo_order` will emit the helper struct before the struct that references
/// it.  The naming convention is `{ParentPascalCase}{FieldOrVariantPascalCase}`,
/// matching the Rust codegen convention.
fn expand_anonymous_types(defs: &[Definition]) -> Vec<Definition> {
    let mut result: Vec<Definition> = Vec::with_capacity(defs.len() * 2);
    for def in defs {
        let mut synthetics: Vec<Definition> = Vec::new();
        let expanded_ty = expand_type(&def.ty, &def.name, &mut synthetics);
        result.extend(synthetics);
        result.push(Definition {
            name: def.name.clone(),
            ty: expanded_ty,
        });
    }
    result
}

/// Generate C code from an ASN.1 module
pub fn generate_c(module: &Module) -> Result<String, Box<dyn std::error::Error>> {
    generate_c_with_config(module, CCodeGenConfig::default())
}

/// Generate C code with custom configuration
pub fn generate_c_with_config(
    module: &Module,
    config: CCodeGenConfig,
) -> Result<String, Box<dyn std::error::Error>> {
    // Expand anonymous inline SEQUENCE / SET / CHOICE bodies into named types
    // before any other processing so that forward declarations, topo-sort, and
    // encoder/decoder prototypes all see the fully-named definition list.
    let expanded_defs = expand_anonymous_types(&module.definitions);

    let mut output = String::new();

    // Header comment
    writeln!(
        &mut output,
        "/* Generated from ASN.1 module {} */",
        module.name
    )?;
    writeln!(&mut output, "/* DO NOT EDIT - auto-generated code */")?;
    writeln!(&mut output)?;

    // Include guards
    let guard_name = format!("{}_H", to_screaming_snake_case(&module.name));
    writeln!(&mut output, "#ifndef {}", guard_name)?;
    writeln!(&mut output, "#define {}", guard_name)?;
    writeln!(&mut output)?;

    // Includes
    writeln!(&mut output, "#include <stdint.h>")?;
    writeln!(&mut output, "#include <stdbool.h>")?;
    writeln!(&mut output, "#include <stdlib.h>")?;
    writeln!(&mut output, "#include <string.h>")?;
    if config.generate_helpers {
        writeln!(&mut output, "#include <stdio.h>")?;
    }
    let header_path = config.synta_header_path.as_deref().unwrap_or("synta.h");
    writeln!(&mut output, "#include \"{}\"", header_path)?;
    writeln!(&mut output)?;

    // Headers for imported modules — one #include per FROM clause
    if !module.imports.is_empty() {
        writeln!(&mut output, "/* Imported module headers */")?;
        for import in &module.imports {
            let stem = module_file_stem(&import.module_name);
            writeln!(&mut output, "#include \"{}.h\"", stem)?;
        }
        writeln!(&mut output)?;
    }

    // Arena/bump allocator support
    if config.arena_mode {
        writeln!(&mut output, "/* Arena/bump allocator support */")?;
        writeln!(&mut output)?;
        writeln!(&mut output, "#ifndef SYNTA_ARENA_MAX_HANDLES")?;
        writeln!(&mut output, "#define SYNTA_ARENA_MAX_HANDLES 256")?;
        writeln!(&mut output, "#endif")?;
        writeln!(&mut output)?;
        writeln!(&mut output, "typedef struct {{")?;
        writeln!(&mut output, "    void   *_ptrs[SYNTA_ARENA_MAX_HANDLES];")?;
        writeln!(
            &mut output,
            "    void  (*_fns[SYNTA_ARENA_MAX_HANDLES])(void*);"
        )?;
        writeln!(&mut output, "    size_t  _n;")?;
        writeln!(&mut output, "}} SyntaArena;")?;
        writeln!(&mut output)?;
        writeln!(
            &mut output,
            "static inline void synta_arena_init(SyntaArena *a) {{ a->_n = 0; }}"
        )?;
        writeln!(&mut output)?;
        writeln!(
            &mut output,
            "static inline int _synta_arena_track(SyntaArena *a, void *p, void (*fn)(void*)) {{"
        )?;
        writeln!(
            &mut output,
            "    if (!p || a->_n >= SYNTA_ARENA_MAX_HANDLES) return 0;"
        )?;
        writeln!(
            &mut output,
            "    a->_ptrs[a->_n] = p; a->_fns[a->_n] = fn; a->_n++; return 1;"
        )?;
        writeln!(&mut output, "}}")?;
        writeln!(&mut output)?;
        writeln!(
            &mut output,
            "static inline void synta_arena_free_all(SyntaArena *a) {{"
        )?;
        writeln!(
            &mut output,
            "    for (size_t i = 0; i < a->_n; i++) a->_fns[i](a->_ptrs[i]);"
        )?;
        writeln!(&mut output, "    a->_n = 0;")?;
        writeln!(&mut output, "}}")?;
        writeln!(&mut output)?;
    }

    writeln!(&mut output, "#ifdef __cplusplus")?;
    writeln!(&mut output, "extern \"C\" {{")?;
    writeln!(&mut output, "#endif")?;
    writeln!(&mut output)?;

    // BitString support type
    writeln!(&mut output, "/* BitString support */")?;
    writeln!(&mut output)?;
    writeln!(&mut output, "typedef struct {{")?;
    writeln!(&mut output, "    SyntaByteArray data;")?;
    writeln!(&mut output, "    uint8_t unused_bits;")?;
    writeln!(&mut output, "}} SyntaBitString;")?;
    writeln!(&mut output)?;

    // OID arrays and other value constants from the module's value assignments
    generate_value_constants(&mut output, module)?;

    // Forward declarations for complex types
    writeln!(&mut output, "/* Forward declarations */")?;
    writeln!(&mut output)?;
    for def in &expanded_defs {
        match &def.ty {
            Type::Sequence(_)
            | Type::Set(_)
            | Type::Choice(_)
            | Type::SequenceOf(_, _)
            | Type::SetOf(_, _) => {
                let c_name = to_pascal_case(&def.name);
                writeln!(&mut output, "typedef struct {} {};", c_name, c_name)?;
            }
            Type::Integer(_, named_numbers) if !named_numbers.is_empty() => {
                let c_name = to_pascal_case(&def.name);
                writeln!(&mut output, "typedef int64_t {};", c_name)?;
            }
            Type::Enumerated(_) => {
                let c_name = to_pascal_case(&def.name);
                writeln!(&mut output, "typedef enum {} {};", c_name, c_name)?;
            }
            _ => {}
        }
    }
    writeln!(&mut output)?;

    // Generate struct definitions in topological order so that embedded-value
    // fields are always fully defined before the struct that contains them.
    writeln!(&mut output, "/* Type definitions */")?;
    writeln!(&mut output)?;
    for idx in topo_order(&expanded_defs) {
        generate_type_definition(&mut output, &expanded_defs[idx], config.generate_helpers)?;
        writeln!(&mut output)?;
    }

    // Generate encoder/decoder function prototypes
    writeln!(&mut output, "/* Encoder/Decoder functions */")?;
    writeln!(&mut output)?;
    for def in &expanded_defs {
        generate_encoder_decoder_prototypes(&mut output, def, config.arena_mode)?;
        writeln!(&mut output)?;
    }

    // Generate helper functions if enabled
    if config.generate_helpers {
        writeln!(&mut output, "/* Helper functions */")?;
        writeln!(&mut output)?;
        for def in &expanded_defs {
            generate_helper_functions(&mut output, def)?;
            writeln!(&mut output)?;
        }
    }

    writeln!(&mut output, "#ifdef __cplusplus")?;
    writeln!(&mut output, "}}")?;
    writeln!(&mut output, "#endif")?;
    writeln!(&mut output)?;

    writeln!(&mut output, "#endif /* {} */", guard_name)?;

    Ok(output)
}

/// Collect types that must be fully defined (not just forward-declared) before
/// `ty` can be used as an embedded-value field.
fn value_deps_of_type(ty: &Type, deps: &mut Vec<String>) {
    match ty {
        Type::Sequence(fields) | Type::Set(fields) => {
            for field in fields {
                value_deps_of_field_type(&field.ty, deps);
            }
        }
        Type::Choice(variants) => {
            // Union members are embedded by value, so TypeRef variants (possibly
            // wrapped in a tag) create deps.
            for variant in variants {
                value_deps_of_field_type(&variant.ty, deps);
            }
        }
        // SequenceOf/SetOf store elements as pointers – only a forward decl needed.
        _ => {}
    }
}

/// Collect the concrete `TypeRef` names that a struct/union *field* depends
/// on by value (i.e., not through a pointer).
///
/// A `TypeRef` field is embedded by value in the generated C struct, so its
/// definition must appear before the enclosing struct.  Anonymous inline
/// SEQUENCE / SET fields are traversed recursively.  SEQUENCE OF / SET OF
/// fields are pointers and only need a forward declaration, so they are
/// ignored.  `Tagged` and `Constrained` wrappers are stripped to reach the
/// underlying type.
fn value_deps_of_field_type(ty: &Type, deps: &mut Vec<String>) {
    match ty {
        Type::TypeRef(name) => deps.push(name.clone()),
        // Inline anonymous struct/set: recurse
        Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
            for f in inner_fields {
                value_deps_of_field_type(&f.ty, deps);
            }
        }
        // Strip Tag/Constrained wrappers and check the real type
        Type::Tagged { inner, .. }
        | Type::Constrained {
            base_type: inner, ..
        } => {
            value_deps_of_field_type(inner, deps);
        }
        // SequenceOf/SetOf: pointer field, forward decl is enough
        _ => {}
    }
}

/// Return indices into `defs` in a topological order dictated by embedded-value
/// dependencies.  Falls back to the original position for any cycles.
fn topo_order(defs: &[Definition]) -> Vec<usize> {
    use std::collections::{HashMap, VecDeque};

    let index: HashMap<&str, usize> = defs
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();

    let mut in_degree = vec![0usize; defs.len()];
    // adj[j] = list of definition indices that depend on j
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); defs.len()];

    for (i, def) in defs.iter().enumerate() {
        let mut raw_deps = Vec::new();
        value_deps_of_type(&def.ty, &mut raw_deps);

        // Deduplicate and build edges
        let mut seen = std::collections::HashSet::new();
        for dep in raw_deps {
            if !seen.insert(dep.clone()) {
                continue;
            }
            if let Some(&j) = index.get(dep.as_str()) {
                if j != i && !adj[j].contains(&i) {
                    adj[j].push(i);
                    in_degree[i] += 1;
                }
            }
        }
    }

    // Kahn's algorithm (FIFO preserves relative order of equal-degree nodes)
    let mut queue: VecDeque<usize> = (0..defs.len()).filter(|&i| in_degree[i] == 0).collect();
    let mut result = Vec::with_capacity(defs.len());

    while let Some(i) = queue.pop_front() {
        result.push(i);
        for &j in &adj[i] {
            in_degree[j] -= 1;
            if in_degree[j] == 0 {
                queue.push_back(j);
            }
        }
    }

    // Append any nodes involved in cycles (shouldn't happen in valid ASN.1)
    for i in 0..defs.len() {
        if !result.contains(&i) {
            result.push(i);
        }
    }

    result
}

/// Format a constraint as a human-readable string for C comments.
fn format_c_constraint_display(constraint: &SubtypeConstraint) -> String {
    match constraint {
        SubtypeConstraint::SingleValue(val) => match val {
            ConstraintValue::Integer(n) => n.to_string(),
            ConstraintValue::Min => "MIN".to_string(),
            ConstraintValue::Max => "MAX".to_string(),
            ConstraintValue::NamedValue(name) => name.clone(),
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
            let parts: Vec<String> = elements.iter().map(format_c_constraint_display).collect();
            parts.join(" | ")
        }
        SubtypeConstraint::Intersection(elements) => {
            let parts: Vec<String> = elements
                .iter()
                .map(|e| format!("({})", format_c_constraint_display(e)))
                .collect();
            parts.join(" ^ ")
        }
        SubtypeConstraint::Complement(inner) => {
            format!("ALL EXCEPT {}", format_c_constraint_display(inner))
        }
        SubtypeConstraint::SizeConstraint(inner) => {
            format!("SIZE ({})", format_c_constraint_display(inner))
        }
        SubtypeConstraint::Pattern(p) => format!("PATTERN \"{}\"", p),
        SubtypeConstraint::PermittedAlphabet(ranges) => {
            let parts: Vec<String> = ranges
                .iter()
                .map(|r| {
                    if r.min == r.max {
                        format!("\"{}\"", r.min)
                    } else {
                        format!("\"{}\"..\"{}\"", r.min, r.max)
                    }
                })
                .collect();
            format!("FROM ({})", parts.join(" | "))
        }
        _ => "constraint".to_string(),
    }
}

/// Return the smallest C integer type whose range covers all values permitted
/// by `constraint`.
///
/// When the lower bound is ≥ 0 (non-negative), unsigned types are preferred:
/// `uint8_t` (0..=255), `uint16_t` (0..=65535), `uint32_t` (0..=4294967295),
/// `uint64_t`.
///
/// When the lower bound is negative, the smallest signed type that fits both
/// bounds is chosen: `int8_t`, `int16_t`, `int32_t`, `int64_t`.
///
/// Falls back to `int64_t` / `uint64_t` when either bound is `MIN`, `MAX`, a
/// named value, or the constraint is not a simple value/range.
fn constrained_integer_c_type(constraint: &SubtypeConstraint) -> &'static str {
    let (lo, hi) = match constraint {
        SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) => (*n, *n),
        SubtypeConstraint::ValueRange {
            min: ConstraintValue::Integer(lo),
            max: ConstraintValue::Integer(hi),
        } => (*lo, *hi),
        _ => return "int64_t",
    };
    if lo >= 0 {
        if hi <= u8::MAX as i64 {
            "uint8_t"
        } else if hi <= u16::MAX as i64 {
            "uint16_t"
        } else if hi <= u32::MAX as i64 {
            "uint32_t"
        } else {
            "uint64_t"
        }
    } else if lo >= i8::MIN as i64 && hi <= i8::MAX as i64 {
        "int8_t"
    } else if lo >= i16::MIN as i64 && hi <= i16::MAX as i64 {
        "int16_t"
    } else if lo >= i32::MIN as i64 && hi <= i32::MAX as i64 {
        "int32_t"
    } else {
        "int64_t"
    }
}

/// Generate a C boolean expression checking whether `var` (a C integer lvalue
/// of type `c_type`) satisfies `constraint`.
///
/// When `c_type` is an unsigned integer type (`uint8_t` etc.), lower bounds
/// that are ≤ 0 are omitted because unsigned variables can never be negative —
/// emitting `v >= 0` for a `uint8_t` would always be true and trigger compiler
/// warnings.
///
/// Returns `"1"` when no bounds can be violated (e.g., unconstrained `MIN..MAX`),
/// and `"1 /* unsupported constraint */"` for constraint kinds not yet handled.
fn generate_c_constraint_check(var: &str, constraint: &SubtypeConstraint, c_type: &str) -> String {
    let is_unsigned = c_type.starts_with("uint");
    match constraint {
        SubtypeConstraint::SingleValue(val) => match val {
            ConstraintValue::Integer(n) => format!("{} == {}LL", var, n),
            ConstraintValue::Min => format!("{} == INT64_MIN", var),
            ConstraintValue::Max => format!("{} == INT64_MAX", var),
            ConstraintValue::NamedValue(name) => format!("{} == {}", var, name),
        },
        SubtypeConstraint::ValueRange { min, max } => {
            let mut parts: Vec<String> = Vec::new();
            match min {
                // For unsigned types a lower bound of ≤ 0 is trivially satisfied.
                ConstraintValue::Integer(n) if is_unsigned && *n <= 0 => {}
                ConstraintValue::Integer(n) => parts.push(format!("{} >= {}LL", var, n)),
                ConstraintValue::Min => {}
                ConstraintValue::Max => parts.push(format!("{} >= INT64_MAX", var)),
                ConstraintValue::NamedValue(name) => parts.push(format!("{} >= {}", var, name)),
            }
            match max {
                ConstraintValue::Integer(n) => parts.push(format!("{} <= {}LL", var, n)),
                ConstraintValue::Max => {}
                ConstraintValue::Min => parts.push(format!("{} <= INT64_MIN", var)),
                ConstraintValue::NamedValue(name) => parts.push(format!("{} <= {}", var, name)),
            }
            if parts.is_empty() {
                "1".to_string()
            } else {
                format!("({})", parts.join(" && "))
            }
        }
        SubtypeConstraint::Union(elements) => {
            let checks: Vec<String> = elements
                .iter()
                .map(|e| generate_c_constraint_check(var, e, c_type))
                .collect();
            format!("({})", checks.join(" || "))
        }
        SubtypeConstraint::Intersection(elements) => {
            let checks: Vec<String> = elements
                .iter()
                .map(|e| generate_c_constraint_check(var, e, c_type))
                .collect();
            format!("({})", checks.join(" && "))
        }
        SubtypeConstraint::Complement(inner) => {
            let inner_check = generate_c_constraint_check(var, inner, c_type);
            format!("!({})", inner_check)
        }
        _ => "1 /* unsupported constraint */".to_string(),
    }
}

/// Generate the C typedef and `static inline` helpers for a top-level constrained INTEGER.
///
/// The storage type is the smallest C integer type that fits the constraint
/// range.  When the lower bound is ≥ 0, an unsigned type is chosen
/// (`uint8_t` / `uint16_t` / `uint32_t` / `uint64_t`); when the lower bound
/// is negative, a signed type is chosen (`int8_t` / `int16_t` / `int32_t` /
/// `int64_t`).  Unconstrained bounds fall back to `int64_t`.
///
/// For unsigned storage types, lower-bound checks that are trivially true
/// (i.e. the bound is ≤ 0) are omitted from the generated validation expression
/// to avoid compiler warnings about always-true comparisons.
///
/// Emits, in order:
/// 1. `typedef struct { uintN_t value; } FooType;`  (or `intN_t` for signed)
/// 2. `bool foo_type_new(uintN_t v, FooType *out)` — validated constructor
/// 3. `FooType foo_type_new_unchecked(uintN_t v)` — unchecked constructor
/// 4. `uintN_t foo_type_get(const FooType *self)` — value accessor
/// 5. `bool foo_type_validate(const FooType *self)` — re-validate
///
/// Optionally also emits `#define` constants for any named numbers.
fn generate_constrained_integer_c(
    output: &mut String,
    name: &str,
    constraint: &SubtypeConstraint,
    named_numbers: &[NamedNumber],
) -> Result<(), Box<dyn std::error::Error>> {
    let c_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let c_type = constrained_integer_c_type(constraint);
    let display = format_c_constraint_display(constraint);
    let check = generate_c_constraint_check("v", constraint, c_type);

    // Struct typedef
    writeln!(output, "/* INTEGER ({}) */", display)?;
    writeln!(output, "typedef struct {{ {} value; }} {};", c_type, c_name)?;
    writeln!(output)?;

    // Named-value constants (e.g. from MsgType ::= INTEGER (10..19) { AS_REQ(10), ... })
    if !named_numbers.is_empty() {
        writeln!(output, "/* Named values for {} */", c_name)?;
        for nn in named_numbers {
            let const_name = to_screaming_snake_case(&nn.name);
            writeln!(
                output,
                "#define {}_{} (({}){})",
                c_name, const_name, c_type, nn.value
            )?;
        }
        writeln!(output)?;
    }

    // _new() — validated constructor
    writeln!(
        output,
        "/** Create {}: validates INTEGER ({}). Returns false if out of range. */",
        c_name, display
    )?;
    writeln!(
        output,
        "static inline bool {}_new({} v, {}* out) {{",
        fn_prefix, c_type, c_name
    )?;
    writeln!(output, "    if (!({check})) return false;", check = check)?;
    writeln!(output, "    out->value = v;")?;
    writeln!(output, "    return true;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _new_unchecked() — bypass validation
    writeln!(
        output,
        "/** Create {} without validation (use with caution). */",
        c_name
    )?;
    writeln!(
        output,
        "static inline {} {}_new_unchecked({} v) {{",
        c_name, fn_prefix, c_type
    )?;
    writeln!(output, "    {} out; out.value = v; return out;", c_name)?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _get() — value accessor
    writeln!(
        output,
        "/** Get the inner {} value of {}. */",
        c_type, c_name
    )?;
    writeln!(
        output,
        "static inline {} {}_get(const {}* self) {{ return self->value; }}",
        c_type, fn_prefix, c_name
    )?;
    writeln!(output)?;

    // _validate() — re-validate a value already stored in the struct
    writeln!(
        output,
        "/** Check that {} satisfies INTEGER ({}). */",
        c_name, display
    )?;
    writeln!(
        output,
        "static inline bool {}_validate(const {}* self) {{",
        fn_prefix, c_name
    )?;
    writeln!(output, "    {} v = self->value;", c_type)?;
    writeln!(output, "    return {check};", check = check)?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Return the ASN.1 base-type name used in generated comments for string types.
fn string_base_type_name(ty: &Type) -> &'static str {
    match ty {
        Type::IA5String(_) => "IA5String",
        Type::PrintableString(_) => "PrintableString",
        Type::Utf8String(_) => "UTF8String",
        Type::OctetString(_) => "OCTET STRING",
        Type::BitString(_) => "BIT STRING",
        _ => "STRING",
    }
}

/// Generate a C boolean expression checking a `uint32_t` length variable against
/// a SIZE sub-constraint.
///
/// For a `MIN..MAX` or `0..MAX` range all `uint32_t` values satisfy the bound, so
/// those bounds are omitted and `"1"` is returned when no check remains.
fn generate_c_length_check(len_var: &str, size_constraint: &SubtypeConstraint) -> String {
    match size_constraint {
        SubtypeConstraint::SingleValue(val) => match val {
            ConstraintValue::Integer(n) => format!("{} == {}U", len_var, n),
            ConstraintValue::Min | ConstraintValue::Max => "1".to_string(),
            ConstraintValue::NamedValue(name) => format!("{} == {}", len_var, name),
        },
        SubtypeConstraint::ValueRange { min, max } => {
            let mut parts: Vec<String> = Vec::new();
            match min {
                ConstraintValue::Integer(n) if *n > 0 => {
                    parts.push(format!("{} >= {}U", len_var, n));
                }
                // 0 or MIN: always true for uint32_t, skip
                ConstraintValue::Integer(_) | ConstraintValue::Min => {}
                ConstraintValue::Max => parts.push(format!("{} >= UINT32_MAX", len_var)),
                ConstraintValue::NamedValue(name) => {
                    parts.push(format!("{} >= {}", len_var, name));
                }
            }
            match max {
                ConstraintValue::Integer(n) => parts.push(format!("{} <= {}U", len_var, n)),
                ConstraintValue::Max => {}
                ConstraintValue::Min => parts.push(format!("{} == 0", len_var)),
                ConstraintValue::NamedValue(name) => {
                    parts.push(format!("{} <= {}", len_var, name));
                }
            }
            if parts.is_empty() {
                "1".to_string()
            } else {
                format!("({})", parts.join(" && "))
            }
        }
        SubtypeConstraint::Union(elements) => {
            let checks: Vec<String> = elements
                .iter()
                .map(|e| generate_c_length_check(len_var, e))
                .collect();
            format!("({})", checks.join(" || "))
        }
        SubtypeConstraint::Intersection(elements) => {
            let checks: Vec<String> = elements
                .iter()
                .map(|e| generate_c_length_check(len_var, e))
                .collect();
            format!("({})", checks.join(" && "))
        }
        SubtypeConstraint::Complement(inner) => {
            let inner_check = generate_c_length_check(len_var, inner);
            format!("!({})", inner_check)
        }
        _ => "1 /* unsupported size constraint */".to_string(),
    }
}

/// Format a char as a C character literal (ASCII printable or `\xNN` escape).
pub(crate) fn format_c_char_literal(c: char) -> String {
    if c == '\'' || c == '\\' {
        format!("'\\{}'", c)
    } else if c.is_ascii() && (c as u8) >= 0x20 && (c as u8) < 0x7f {
        format!("'{}'", c)
    } else {
        format!("'\\x{:02x}'", c as u32)
    }
}

/// Generate the C boolean sub-expression for a single `FROM` alphabet range set.
///
/// Returns an expression over the local variable `_c` (type `unsigned char`)
/// that is true when `_c` falls within one of the permitted character ranges.
pub(crate) fn generate_c_alphabet_expr(ranges: &[CharRange]) -> String {
    if ranges.is_empty() {
        return "1 /* no alphabet constraint */".to_string();
    }
    let parts: Vec<String> = ranges
        .iter()
        .map(|r| {
            if r.min == r.max {
                format!("_c == {}", format_c_char_literal(r.min))
            } else {
                format!(
                    "(_c >= {} && _c <= {})",
                    format_c_char_literal(r.min),
                    format_c_char_literal(r.max)
                )
            }
        })
        .collect();
    parts.join(" || ")
}

/// Emit C validation statements for a string subtype constraint into `out`.
///
/// * `indent`     — indentation prefix for each emitted line.
/// * `len_var`    — name of the already-declared `uint32_t` length variable.
/// * `value_expr` — C expression of type `SyntaByteArray` (e.g. `"value"` or `"self->value"`).
fn emit_c_string_validation_stmts(
    out: &mut String,
    indent: &str,
    constraint: &SubtypeConstraint,
    len_var: &str,
    value_expr: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    match constraint {
        SubtypeConstraint::SizeConstraint(inner) => {
            let check = generate_c_length_check(len_var, inner);
            writeln!(
                out,
                "{}if (!({check})) return false;",
                indent,
                check = check
            )?;
        }
        SubtypeConstraint::PermittedAlphabet(ranges) => {
            let alpha_expr = generate_c_alphabet_expr(ranges);
            writeln!(out, "{}{{", indent)?;
            writeln!(out, "{}    uint32_t _i;", indent)?;
            writeln!(
                out,
                "{}    const unsigned char *_ap = (const unsigned char *){}.data;",
                indent, value_expr
            )?;
            writeln!(out, "{}    bool _ok = true;", indent)?;
            writeln!(
                out,
                "{}    for (_i = 0; _i < {lv} && _ok; _i++) {{",
                indent,
                lv = len_var
            )?;
            writeln!(out, "{}        unsigned char _c = _ap[_i];", indent)?;
            writeln!(out, "{}        _ok = {alpha};", indent, alpha = alpha_expr)?;
            writeln!(out, "{}    }}", indent)?;
            writeln!(out, "{}    if (!_ok) return false;", indent)?;
            writeln!(out, "{}}}", indent)?;
        }
        SubtypeConstraint::Pattern(p) => {
            writeln!(
                out,
                "{}/* PATTERN constraint \"{}\" not enforced at runtime; use --with-regex or --with-pcre with --impl (single-file) or --emit impl/both (multi-file) to enable */",
                indent, p
            )?;
        }
        SubtypeConstraint::ContainedSubtype(_ty) => {
            writeln!(
                out,
                "{}/* CONTAINING constraint not enforced at runtime; use --with-containing with --impl (single-file) or --emit impl/both (multi-file) to enable */",
                indent
            )?;
        }
        SubtypeConstraint::Intersection(parts) => {
            for part in parts {
                emit_c_string_validation_stmts(out, indent, part, len_var, value_expr)?;
            }
        }
        SubtypeConstraint::Union(_) => {
            writeln!(
                out,
                "{}/* Union constraint: complex, treated as unchecked */",
                indent
            )?;
        }
        SubtypeConstraint::Complement(_) => {
            writeln!(
                out,
                "{}/* Complement constraint: complex, treated as unchecked */",
                indent
            )?;
        }
        _ => {
            writeln!(out, "{}/* unsupported constraint: skipped */", indent)?;
        }
    }
    Ok(())
}

/// Generate a typedef and named bit constants for a BIT STRING with a `NamedBitList` constraint.
///
/// Emits, in order:
/// 1. `typedef SyntaBitString TypeName;`
/// 2. `#define TYPE_NAME_BITNAME_BIT  N` for every named bit (values aligned)
/// 3. (with helpers) `#define TYPE_NAME_IS_SET / _SET / _CLEAR` helper macros
///    that forward to `synta_bitstring_is_set / _set / _clear` from `synta.h`.
fn generate_named_bit_string_c(
    output: &mut String,
    name: &str,
    bits: &[NamedNumber],
    generate_helpers: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    // Prefix for #define names: derive from the raw ASN.1 identifier so that
    // hyphenated names like "kdc-options" produce "KDC_OPTIONS".
    let prefix = to_screaming_snake_case(name);

    writeln!(output, "/* {} — BIT STRING with named bits */", struct_name)?;
    writeln!(output, "typedef SyntaBitString {};", struct_name)?;

    if bits.is_empty() {
        return Ok(());
    }

    writeln!(output)?;
    writeln!(output, "/* Named bit positions for {} */", struct_name)?;

    // Collect macro names for alignment.
    let macro_names: Vec<String> = bits
        .iter()
        .map(|b| {
            let bit_upper = to_snake_case(&b.name).to_uppercase();
            format!("{prefix}_{bit_upper}_BIT")
        })
        .collect();
    let max_len = macro_names.iter().map(|s| s.len()).max().unwrap_or(0);

    for (bit, macro_name) in bits.iter().zip(&macro_names) {
        writeln!(
            output,
            "#define {macro_name:width$} {val}",
            width = max_len,
            val = bit.value
        )?;
    }

    if generate_helpers {
        writeln!(output)?;
        writeln!(output, "/* Bit-operation helpers for {} */", struct_name)?;
        writeln!(
            output,
            "/* (requires synta_bitstring_is_set/set/clear from synta.h) */"
        )?;
        let is_set = format!("{prefix}_IS_SET(bs, bit)");
        let set = format!("{prefix}_SET(bs, bit)");
        let clear = format!("{prefix}_CLEAR(bs, bit)");
        let helper_max = [is_set.len(), set.len(), clear.len()]
            .iter()
            .copied()
            .max()
            .unwrap_or(0);
        writeln!(
            output,
            "#define {is_set:width$} synta_bitstring_is_set(&(bs).data, (bit))",
            width = helper_max
        )?;
        writeln!(
            output,
            "#define {set:width$} synta_bitstring_set(&(bs).data, (bit))",
            width = helper_max
        )?;
        writeln!(
            output,
            "#define {clear:width$} synta_bitstring_clear(&(bs).data, (bit))",
            width = helper_max
        )?;
    }

    Ok(())
}

/// Generate the C typedef and `static inline` helpers for a top-level constrained string type.
///
/// Emits, in order:
/// 1. `typedef struct { SyntaByteArray value; } FooType;`
/// 2. `bool foo_type_new(SyntaByteArray value, FooType *out)` — validated constructor
/// 3. `FooType foo_type_new_unchecked(SyntaByteArray value)` — unchecked constructor
/// 4. `SyntaByteArray foo_type_get(const FooType *self)` — borrowed value (owned cleared)
/// 5. `bool foo_type_validate(const FooType *self)` — re-validate stored value
/// 6. `void foo_type_free(FooType *self)` — free buffer if owned
fn generate_constrained_string_c(
    output: &mut String,
    name: &str,
    base_type_str: &str,
    constraint: &SubtypeConstraint,
) -> Result<(), Box<dyn std::error::Error>> {
    let c_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let display = format_c_constraint_display(constraint);

    // Struct typedef
    writeln!(output, "/* {} ({}) */", base_type_str, display)?;
    writeln!(
        output,
        "typedef struct {{ SyntaByteArray value; }} {};",
        c_name
    )?;
    writeln!(output)?;

    // _new() — validated constructor
    writeln!(
        output,
        "/** Create {c}: validates {bt} ({d}). Returns false if constraint violated. */",
        c = c_name,
        bt = base_type_str,
        d = display
    )?;
    writeln!(
        output,
        "static inline bool {fn}_new(SyntaByteArray value, {c}* out) {{",
        fn = fn_prefix,
        c = c_name
    )?;
    writeln!(output, "    uint32_t _len = value.len;")?;
    emit_c_string_validation_stmts(output, "    ", constraint, "_len", "value")?;
    writeln!(output, "    out->value = value;")?;
    writeln!(output, "    return true;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _new_unchecked() — bypass validation
    writeln!(
        output,
        "/** Create {} without validation (use with caution). */",
        c_name
    )?;
    writeln!(
        output,
        "static inline {c} {fn}_new_unchecked(SyntaByteArray value) {{",
        c = c_name,
        fn = fn_prefix
    )?;
    writeln!(
        output,
        "    {c} out; out.value = value; return out;",
        c = c_name
    )?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _get() — borrowed accessor (ownership cleared to prevent double-free)
    writeln!(
        output,
        "/** Get a borrowed view of the {} value (owned flag cleared). */",
        c_name
    )?;
    writeln!(
        output,
        "static inline SyntaByteArray {fn}_get(const {c}* self) {{",
        fn = fn_prefix,
        c = c_name
    )?;
    writeln!(
        output,
        "    SyntaByteArray r = self->value; r.owned = 0; return r;"
    )?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _validate() — re-validate the stored value
    writeln!(
        output,
        "/** Check that {} satisfies {} ({}). */",
        c_name, base_type_str, display
    )?;
    writeln!(
        output,
        "static inline bool {fn}_validate(const {c}* self) {{",
        fn = fn_prefix,
        c = c_name
    )?;
    writeln!(output, "    uint32_t _len = self->value.len;")?;
    emit_c_string_validation_stmts(output, "    ", constraint, "_len", "self->value")?;
    writeln!(output, "    return true;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // _free() — release owned buffer
    writeln!(
        output,
        "/** Free {} if its value buffer is owned. */",
        c_name
    )?;
    writeln!(
        output,
        "static inline void {fn}_free({c}* self) {{",
        fn = fn_prefix,
        c = c_name
    )?;
    writeln!(
        output,
        "    if (self->value.owned != 0) {{ synta_byte_array_free(&self->value); self->value.owned = 0; }}"
    )?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate a type definition (struct, enum, typedef)
fn generate_type_definition(
    output: &mut String,
    def: &Definition,
    generate_helpers: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    match &def.ty {
        Type::Sequence(fields) | Type::Set(fields) => {
            generate_sequence_struct(output, &def.name, fields)?;
        }
        Type::Choice(variants) => {
            generate_choice_struct(output, &def.name, variants)?;
        }
        Type::Integer(_, named_numbers) if !named_numbers.is_empty() => {
            generate_defines_for_integer(output, &def.name, named_numbers)?;
        }
        Type::Enumerated(named_values) => {
            generate_enum_for_integer(output, &def.name, named_values)?;
        }
        Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
            // Generate a struct with count and array for SEQUENCE OF / SET OF.
            // The typedef was already emitted in the forward-declarations section,
            // so use plain struct syntax here.
            let struct_name = to_pascal_case(&def.name);
            let elem_type = get_c_type(inner);
            writeln!(output, "struct {} {{", struct_name)?;
            writeln!(output, "    size_t count;")?;
            writeln!(output, "    {}* items;", elem_type)?;
            writeln!(output, "}};")?;
        }
        Type::Constrained {
            base_type,
            constraint,
        } => {
            match (base_type.as_ref(), &constraint.spec) {
                (Type::Integer(_, named_numbers), ConstraintSpec::Subtype(subtype)) => {
                    generate_constrained_integer_c(output, &def.name, subtype, named_numbers)?;
                }
                // BIT STRING with named bits — must come before the general string arm.
                (
                    Type::BitString(_),
                    ConstraintSpec::Subtype(SubtypeConstraint::NamedBitList(bits)),
                ) => {
                    generate_named_bit_string_c(output, &def.name, bits, generate_helpers)?;
                }
                // BIT STRING { bits } (SIZE N..MAX) — the parser produces
                // Intersection([NamedBitList(bits), SizeConstraint(...)]).
                // Extract the named bits and treat this as a named-bit string;
                // the SIZE component is advisory information carried inline in
                // the ASN.1 schema and does not change the C representation.
                (
                    Type::BitString(_),
                    ConstraintSpec::Subtype(SubtypeConstraint::Intersection(parts)),
                ) if parts
                    .iter()
                    .any(|p| matches!(p, SubtypeConstraint::NamedBitList(_))) =>
                {
                    let bits = parts
                        .iter()
                        .find_map(|p| {
                            if let SubtypeConstraint::NamedBitList(b) = p {
                                Some(b.as_slice())
                            } else {
                                None
                            }
                        })
                        .unwrap_or(&[]);
                    generate_named_bit_string_c(output, &def.name, bits, generate_helpers)?;
                }
                (
                    Type::IA5String(_)
                    | Type::PrintableString(_)
                    | Type::Utf8String(_)
                    | Type::OctetString(_)
                    | Type::BitString(_),
                    ConstraintSpec::Subtype(subtype),
                ) => {
                    let base_name = string_base_type_name(base_type);
                    generate_constrained_string_c(output, &def.name, base_name, subtype)?;
                }
                _ => {
                    // Other constrained types — emit a bare typedef.
                    let c_name = to_pascal_case(&def.name);
                    let base_c_type = get_c_type(base_type);
                    writeln!(
                        output,
                        "/* Constrained type: constraint validation not yet implemented */"
                    )?;
                    writeln!(output, "typedef {} {};", base_c_type, c_name)?;
                }
            }
        }
        Type::TypeRef(_) => {
            // Type alias - just a typedef
            let c_name = to_pascal_case(&def.name);
            let base_type = get_c_type(&def.ty);
            writeln!(output, "typedef {} {};", base_type, c_name)?;
        }
        _ => {
            // Simple type alias
            let c_name = to_pascal_case(&def.name);
            let base_type = get_c_type(&def.ty);
            writeln!(output, "typedef {} {};", base_type, c_name)?;
        }
    }
    Ok(())
}

/// Return an inline C comment for a tag annotation, e.g. `"[0] EXPLICIT"` or
/// `"[APPLICATION 1] IMPLICIT"`, if the outermost layer of `ty` is `Tagged`.
/// Returns `None` for all other types.
fn tag_annotation_comment(ty: &Type) -> Option<String> {
    if let Type::Tagged {
        tag: tag_info,
        inner,
    } = ty
    {
        let cls = match tag_info.class {
            TagClass::Universal => format!("UNIVERSAL {}", tag_info.number),
            TagClass::Application => format!("APPLICATION {}", tag_info.number),
            TagClass::ContextSpecific => tag_info.number.to_string(),
            TagClass::Private => format!("PRIVATE {}", tag_info.number),
        };
        // ASN.1 X.680 §31.2.7: IMPLICIT tagging cannot be applied to CHOICE or ANY types;
        // such a tag is automatically treated as EXPLICIT.
        let inner_is_choice_or_any = matches!(
            inner.as_ref(),
            Type::Choice(_) | Type::Any | Type::AnyDefinedBy(_)
        );
        let mode = match tag_info.tagging {
            Tagging::Explicit => "EXPLICIT",
            Tagging::Implicit if inner_is_choice_or_any => "EXPLICIT",
            Tagging::Implicit => "IMPLICIT",
        };
        Some(format!("[{}] {}", cls, mode))
    } else {
        None
    }
}

/// Generate a struct definition for SEQUENCE type
fn generate_sequence_struct(
    output: &mut String,
    name: &str,
    fields: &[SequenceField],
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    writeln!(output, "struct {} {{", struct_name)?;

    for field in fields {
        // Skip NULL fields as they don't have data
        if matches!(field.ty, Type::Null) {
            continue;
        }

        let field_name = to_snake_case(&field.name);

        // Handle inline SEQUENCE/SET types
        match &field.ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                // Generate inline anonymous struct
                if field.optional {
                    writeln!(output, "    bool has_{};", field_name)?;
                }
                writeln!(output, "    struct {{")?;
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }
                    let inner_name = to_snake_case(&inner_field.name);
                    let inner_type = get_c_type_for_field(&inner_field.ty);
                    if inner_field.optional {
                        writeln!(output, "        bool has_{};", inner_name)?;
                        writeln!(output, "        {} {};", inner_type, inner_name)?;
                    } else {
                        writeln!(output, "        {} {};", inner_type, inner_name)?;
                    }
                }
                writeln!(output, "    }} {};", field_name)?;
            }
            _ => {
                let field_type = get_c_type_for_field(&field.ty);
                let tag_note = tag_annotation_comment(&field.ty);

                // For SEQUENCE OF / SET OF, generate length field
                if matches!(field.ty, Type::SequenceOf(_, _) | Type::SetOf(_, _)) {
                    writeln!(output, "    size_t {}_count;", field_name)?;
                    writeln!(output, "    {} {};", field_type, field_name)?;
                } else if field.optional {
                    writeln!(output, "    bool has_{};", field_name)?;
                    if let Some(ref tn) = tag_note {
                        writeln!(output, "    {} {}; /* {} */", field_type, field_name, tn)?;
                    } else {
                        writeln!(output, "    {} {};", field_type, field_name)?;
                    }
                } else if let Some(ref dv) = field.default {
                    if let Some(ref tn) = tag_note {
                        writeln!(
                            output,
                            "    {} {}; /* {} DEFAULT {} */",
                            field_type, field_name, tn, dv
                        )?;
                    } else {
                        writeln!(
                            output,
                            "    {} {}; /* DEFAULT {} */",
                            field_type, field_name, dv
                        )?;
                    }
                } else if let Some(ref tn) = tag_note {
                    writeln!(output, "    {} {}; /* {} */", field_type, field_name, tn)?;
                } else {
                    writeln!(output, "    {} {};", field_type, field_name)?;
                }
            }
        }
    }

    writeln!(output, "}};")?;
    Ok(())
}

/// Get C type for a field (handles embedded structs differently)
fn get_c_type_for_field(ty: &Type) -> String {
    match ty {
        Type::TypeRef(name) => to_pascal_case(name),
        Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
            // Array types - use pointer with length
            format!("{}*", get_c_type(inner))
        }
        _ => get_c_type(ty),
    }
}

/// Generate a struct definition for CHOICE type
fn generate_choice_struct(
    output: &mut String,
    name: &str,
    variants: &[ChoiceVariant],
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let tag_enum_name = format!("{}Tag", struct_name);

    // Generate tag enum
    writeln!(output, "typedef enum {} {{", tag_enum_name)?;
    for (i, variant) in variants.iter().enumerate() {
        let variant_name = to_pascal_case(&variant.name);
        let comma = if i < variants.len() - 1 { "," } else { "" };
        writeln!(output, "    {}_{}{}", tag_enum_name, variant_name, comma)?;
    }
    writeln!(output, "}} {};", tag_enum_name)?;
    writeln!(output)?;

    // Generate choice struct
    writeln!(output, "struct {} {{", struct_name)?;
    writeln!(output, "    {} tag;", tag_enum_name)?;
    writeln!(output, "    union {{")?;

    for variant in variants {
        // Skip NULL types as they don't have data
        if matches!(variant.ty, Type::Null) {
            continue;
        }

        let variant_name = to_snake_case(&variant.name);
        // After expand_anonymous_types() all inline SEQUENCE/SET bodies should have
        // been replaced by TypeRefs. If we still see a bare Sequence/Set here, the
        // expansion is incomplete — emit a C #error so the compiler catches it
        // immediately instead of silently producing type-unsafe void* code.
        if matches!(peel_type(&variant.ty), Type::Sequence(_) | Type::Set(_)) {
            debug_assert!(
                false,
                "CHOICE variant '{}' still has an inline Sequence/Set after \
                 expand_anonymous_types(); the expansion is incomplete",
                variant.name
            );
            writeln!(
                output,
                "        /* ERROR: inline SEQUENCE/SET variant '{}' was not expanded — \
                 run expand_anonymous_types() before generate_c() */",
                variant_name
            )?;
            writeln!(
                output,
                "        #error \"codegen bug: unexpanded inline SEQUENCE/SET in CHOICE variant '{}'\",",
                variant_name
            )?;
        } else {
            let variant_type = get_c_type_for_field(&variant.ty);
            writeln!(output, "        {} {};", variant_type, variant_name)?;
        }
    }

    writeln!(output, "    }} value;")?;
    writeln!(output, "}};")?;
    Ok(())
}

/// Generate enum for INTEGER with named numbers
fn generate_enum_for_integer(
    output: &mut String,
    name: &str,
    named_numbers: &[NamedNumber],
) -> Result<(), Box<dyn std::error::Error>> {
    let enum_name = to_pascal_case(name);
    writeln!(output, "enum {} {{", enum_name)?;

    for (i, nn) in named_numbers.iter().enumerate() {
        let variant_name = to_screaming_snake_case(&nn.name);
        let comma = if i < named_numbers.len() - 1 { "," } else { "" };
        writeln!(
            output,
            "    {}_{} = {}{}",
            enum_name, variant_name, nn.value, comma
        )?;
    }

    writeln!(output, "}};")?;
    Ok(())
}

/// Generate `#define` constants for an unconstrained INTEGER with named numbers.
///
/// # Why `int64_t`?
///
/// ASN.1 INTEGER is an unbounded type.  Named numbers (`{ tcp(6), udp(17) }`)
/// are symbolic labels for specific values; the actual DER-encoded value on
/// the wire may be any valid INTEGER, not just the listed names.  Using
/// `int64_t` matches what the runtime's `synta_integer_to_i64` returns, so
/// the decode/encode round-trip is correct over the full representable range
/// without truncation.
///
/// If a bounded representation is required, the schema should carry an
/// explicit size constraint (`INTEGER (0..65535)`), which causes the
/// constrained-integer path (`generate_constrained_integer_c`) to be taken
/// instead — that path wraps the value in a validated newtype struct.
///
/// # Output
///
/// The forward-declarations section already emits `typedef int64_t TypeName;`.
/// This function emits the accompanying preprocessor constants:
///
/// ```c
/// /* Named integer values for Protocol */
/// #define PROTOCOL_TCP  ((int64_t)6)
/// #define PROTOCOL_UDP  ((int64_t)17)
/// ```
///
/// Macro names are padded to the same length for visual alignment.
fn generate_defines_for_integer(
    output: &mut String,
    name: &str,
    named_numbers: &[NamedNumber],
) -> Result<(), Box<dyn std::error::Error>> {
    let type_name = to_pascal_case(name);
    let prefix = to_screaming_snake_case(name);

    writeln!(output, "/* Named integer values for {} */", type_name)?;

    // Pre-compute macro names to allow padding for alignment.
    let macro_names: Vec<String> = named_numbers
        .iter()
        .map(|nn| format!("{}_{}", prefix, to_snake_case(&nn.name).to_uppercase()))
        .collect();
    let max_len = macro_names.iter().map(|s| s.len()).max().unwrap_or(0);

    for (nn, macro_name) in named_numbers.iter().zip(&macro_names) {
        writeln!(
            output,
            "#define {:width$} ((int64_t){})",
            macro_name,
            nn.value,
            width = max_len
        )?;
    }

    Ok(())
}

/// Generate encoder/decoder function prototypes
fn generate_encoder_decoder_prototypes(
    output: &mut String,
    def: &Definition,
    arena_mode: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let c_name = to_pascal_case(&def.name);
    let fn_prefix = to_snake_case(&def.name);

    // Decoder prototype
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, {}* out);",
        fn_prefix, c_name
    )?;

    // Arena decoder prototype
    if arena_mode {
        writeln!(
            output,
            "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, {}* out);",
            fn_prefix, c_name
        )?;
    }

    // Encoder prototype
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const {}* value);",
        fn_prefix, c_name
    )?;

    // Free function for complex types
    match &def.ty {
        Type::Sequence(_)
        | Type::Set(_)
        | Type::Choice(_)
        | Type::SequenceOf(_, _)
        | Type::SetOf(_, _) => {
            writeln!(output, "void {}_free({}* value);", fn_prefix, c_name)?;
        }
        _ => {}
    }

    // Default constructor for sequences where every field is OPTIONAL or has a DEFAULT
    if let Type::Sequence(fields) | Type::Set(fields) = peel_type(&def.ty) {
        if fields.iter().all(|f| f.optional || f.default.is_some()) {
            writeln!(output, "{} {}_default(void);", c_name, fn_prefix)?;
        }
    }

    Ok(())
}

/// Generate helper functions (init, validate, print) for a definition.
fn generate_helper_functions(
    output: &mut String,
    def: &Definition,
) -> Result<(), Box<dyn std::error::Error>> {
    let c_name = to_pascal_case(&def.name);
    let fn_prefix = to_snake_case(&def.name);

    match &def.ty {
        Type::Sequence(fields) | Type::Set(fields) => {
            generate_init_helper(output, &c_name, &fn_prefix)?;
            writeln!(output)?;
            generate_validate_sequence(output, &c_name, &fn_prefix, fields)?;
            writeln!(output)?;
            generate_print_sequence(output, &c_name, &fn_prefix, fields)?;
        }
        Type::Choice(variants) => {
            generate_validate_choice(output, &c_name, &fn_prefix, variants)?;
            writeln!(output)?;
            generate_print_choice(output, &c_name, &fn_prefix, variants)?;
        }
        Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
            generate_init_helper(output, &c_name, &fn_prefix)?;
            writeln!(output)?;
            generate_validate_array(output, &c_name, &fn_prefix)?;
            writeln!(output)?;
            generate_print_array(output, &c_name, &fn_prefix, inner)?;
        }
        _ => {}
    }

    Ok(())
}

/// Emit a `static inline void <prefix>_init(<Name>* value)` zero-initialiser.
///
/// Uses `memset` to zero the entire struct so that optional `has_*` flags
/// start as `false` and all pointer fields start as `NULL`.
fn generate_init_helper(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(
        output,
        "static inline void {}_init({}* value) {{",
        fn_prefix, c_name
    )?;
    writeln!(output, "    if (value != NULL) {{")?;
    writeln!(output, "        memset(value, 0, sizeof({}));", c_name)?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit a `static inline SyntaErrorCode <prefix>_validate(const <Name>* value)`
/// helper for a SEQUENCE or SET struct.
///
/// Required pointer fields are checked for non-`NULL`; optional pointer fields
/// are only checked when their `has_*` flag is `true`.  `NULL` fields return
/// `SyntaErrorCode_InvalidArgument`; value types (BOOLEAN, REAL, C enums, etc.)
/// are not checked.  Returns `SyntaErrorCode_Success` when all checks pass.
fn generate_validate_sequence(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
    fields: &[SequenceField],
) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(
        output,
        "static inline SyntaErrorCode {}_validate(const {}* value) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) return SyntaErrorCode_NullPointer;"
    )?;
    for field in fields {
        if matches!(field.ty, Type::Null) {
            continue;
        }
        let field_name = to_snake_case(&field.name);
        if is_pointer_c_type(&field.ty) {
            if field.optional {
                writeln!(
                    output,
                    "    if (value->has_{name} && value->{name} == NULL) return SyntaErrorCode_InvalidArgument;",
                    name = field_name
                )?;
            } else {
                writeln!(
                    output,
                    "    if (value->{} == NULL) return SyntaErrorCode_InvalidArgument;",
                    field_name
                )?;
            }
        }
    }
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit a `static inline void <prefix>_print(const <Name>* value, FILE* stream)`
/// debugging helper for a SEQUENCE or SET struct.
///
/// Prints each field name and value via `fprintf`.  Optional absent fields are
/// printed as `(absent)`.  Requires `<stdio.h>`, which is included automatically
/// when `generate_helpers` is enabled in [`CCodeGenConfig`].
fn generate_print_sequence(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
    fields: &[SequenceField],
) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(
        output,
        "static inline void {}_print(const {}* value, FILE* stream) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) {{ fprintf(stream, \"{}(null)\\n\"); return; }}",
        c_name
    )?;
    writeln!(output, "    fprintf(stream, \"{}{{\\n\");", c_name)?;
    for field in fields {
        if matches!(field.ty, Type::Null) {
            continue;
        }
        let field_name = to_snake_case(&field.name);
        write_sequence_field_print(output, &field_name, &field.ty, field.optional)?;
    }
    writeln!(output, "    fprintf(stream, \"}}\\n\");")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit the fprintf statement(s) for one field inside a SEQUENCE print helper.
fn write_sequence_field_print(
    output: &mut String,
    field_name: &str,
    ty: &Type,
    optional: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let base = peel_type(ty);

    // SequenceOf/SetOf store a count field separately; no has_ flag even when optional.
    if matches!(base, Type::SequenceOf(_, _) | Type::SetOf(_, _)) {
        write_field_value_print(
            output,
            field_name,
            base,
            &format!("value->{}", field_name),
            "    ",
        )?;
        return Ok(());
    }

    if optional {
        writeln!(output, "    if (value->has_{}) {{", field_name)?;
        write_field_value_print(
            output,
            field_name,
            base,
            &format!("value->{}", field_name),
            "        ",
        )?;
        writeln!(output, "    }} else {{")?;
        writeln!(
            output,
            "        fprintf(stream, \"  {}: (absent)\\n\");",
            field_name
        )?;
        writeln!(output, "    }}")?;
    } else {
        write_field_value_print(
            output,
            field_name,
            base,
            &format!("value->{}", field_name),
            "    ",
        )?;
    }
    Ok(())
}

/// Emit a fprintf statement for a single field value (type already peeled of Tagged/Constrained).
fn write_field_value_print(
    output: &mut String,
    field_name: &str,
    ty: &Type,
    field_expr: &str,
    indent: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    match ty {
        Type::Boolean => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: %s\\n\", {} ? \"true\" : \"false\");",
                indent, field_name, field_expr
            )?;
        }
        Type::Real => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: %g\\n\", {});",
                indent, field_name, field_expr
            )?;
        }
        Type::OctetString(_)
        | Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::UtcTime
        | Type::GeneralizedTime
        | Type::Any
        | Type::AnyDefinedBy(_) => {
            writeln!(output, "{}if ({} != NULL)", indent, field_expr)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: <string(%zu bytes)>\\n\", synta_octet_string_len({}));",
                indent, field_name, field_expr
            )?;
            writeln!(output, "{}else", indent)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: NULL\\n\");",
                indent, field_name
            )?;
        }
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(output, "{}if ({} != NULL)", indent, field_expr)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: <integer>\\n\");",
                indent, field_name
            )?;
            writeln!(output, "{}else", indent)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: NULL\\n\");",
                indent, field_name
            )?;
        }
        Type::ObjectIdentifier => {
            writeln!(output, "{}if ({} != NULL)", indent, field_expr)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: <oid>\\n\");",
                indent, field_name
            )?;
            writeln!(output, "{}else", indent)?;
        }
        Type::RelativeOid => {
            writeln!(output, "{}if ({} != NULL)", indent, field_expr)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: <relative-oid>\\n\");",
                indent, field_name
            )?;
            writeln!(output, "{}else", indent)?;
            writeln!(
                output,
                "{}    fprintf(stream, \"  {}: NULL\\n\");",
                indent, field_name
            )?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: <bit-string(%u bytes)>\\n\", (unsigned int){}.data.len);",
                indent, field_name, field_expr
            )?;
        }
        Type::TypeRef(name) => {
            let type_name = to_pascal_case(name);
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: <{}>\\n\");",
                indent, field_name, type_name
            )?;
        }
        Type::Sequence(_) | Type::Set(_) => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: <struct>\\n\");",
                indent, field_name
            )?;
        }
        Type::SequenceOf(_, _) | Type::SetOf(_, _) => {
            // field_expr is "value->field_name"; the count field is "value->field_name_count"
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: [%zu elements]\\n\", {}_count);",
                indent, field_name, field_expr
            )?;
        }
        Type::Choice(_) => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: <choice>\\n\");",
                indent, field_name
            )?;
        }
        Type::Null => {}
        // Tagged/Constrained are already peeled by the caller.
        _ => {
            writeln!(
                output,
                "{}fprintf(stream, \"  {}: <value>\\n\");",
                indent, field_name
            )?;
        }
    }
    Ok(())
}

/// Emit a `static inline SyntaErrorCode <prefix>_validate(const <Name>* value)`
/// helper for a CHOICE type.
///
/// Validates the discriminant tag via a `switch` statement.  Any tag value
/// not listed in the CHOICE returns `SyntaErrorCode_InvalidEncoding`, preventing
/// access to the union through an unrecognised tag.
fn generate_validate_choice(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
    variants: &[ChoiceVariant],
) -> Result<(), Box<dyn std::error::Error>> {
    let tag_enum = format!("{}Tag", c_name);
    writeln!(
        output,
        "static inline SyntaErrorCode {}_validate(const {}* value) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) return SyntaErrorCode_NullPointer;"
    )?;
    writeln!(output, "    switch (value->tag) {{")?;
    for variant in variants {
        let variant_name = to_pascal_case(&variant.name);
        writeln!(output, "        case {}_{}: break;", tag_enum, variant_name)?;
    }
    writeln!(
        output,
        "        default: return SyntaErrorCode_InvalidEncoding;"
    )?;
    writeln!(output, "    }}")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit a `static inline void <prefix>_print(const <Name>* value, FILE* stream)`
/// debugging helper for a CHOICE type.
///
/// Prints the active variant name via a `switch` on the discriminant tag.
/// Unknown tags are printed as `<unknown tag>`.
fn generate_print_choice(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
    variants: &[ChoiceVariant],
) -> Result<(), Box<dyn std::error::Error>> {
    let tag_enum = format!("{}Tag", c_name);
    writeln!(
        output,
        "static inline void {}_print(const {}* value, FILE* stream) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) {{ fprintf(stream, \"{}(null)\\n\"); return; }}",
        c_name
    )?;
    writeln!(output, "    switch (value->tag) {{")?;
    for variant in variants {
        let variant_name = to_pascal_case(&variant.name);
        let variant_field = to_snake_case(&variant.name);
        writeln!(output, "        case {}_{}:", tag_enum, variant_name)?;
        writeln!(
            output,
            "            fprintf(stream, \"{}{{ {} }}\\n\");",
            c_name, variant_field
        )?;
        writeln!(output, "            break;")?;
    }
    writeln!(output, "        default:")?;
    writeln!(
        output,
        "            fprintf(stream, \"{}{{ <unknown tag> }}\\n\");",
        c_name
    )?;
    writeln!(output, "            break;")?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit a `static inline SyntaErrorCode <prefix>_validate(const <Name>* value)`
/// helper for a SEQUENCE OF / SET OF type.
///
/// Checks that `items` is non-`NULL` whenever `count` is non-zero, guarding
/// against an inconsistent `{count: n, items: NULL}` state that would cause
/// undefined behaviour when the array is iterated.
fn generate_validate_array(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(
        output,
        "static inline SyntaErrorCode {}_validate(const {}* value) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) return SyntaErrorCode_NullPointer;"
    )?;
    writeln!(
        output,
        "    if (value->count > 0 && value->items == NULL) return SyntaErrorCode_InvalidArgument;"
    )?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Emit a `static inline void <prefix>_print(const <Name>* value, FILE* stream)`
/// debugging helper for a SEQUENCE OF / SET OF type.
///
/// Prints the element count.  Individual element values are not printed
/// because the element type may itself require a recursive print call; callers
/// that need per-element output should iterate and call the element's own
/// `_print` helper.
fn generate_print_array(
    output: &mut String,
    c_name: &str,
    fn_prefix: &str,
    _inner: &Type,
) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(
        output,
        "static inline void {}_print(const {}* value, FILE* stream) {{",
        fn_prefix, c_name
    )?;
    writeln!(
        output,
        "    if (value == NULL) {{ fprintf(stream, \"{}(null)\\n\"); return; }}",
        c_name
    )?;
    writeln!(
        output,
        "    fprintf(stream, \"{}[%zu]\\n\", value->count);",
        c_name
    )?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Build a resolved OID registry from the module's value assignments.
///
/// OIDs that reference other named OIDs (e.g. `id-ori-kem ::= { id-ori 3 }`)
/// are resolved iteratively to a flat `Vec<u32>` of arc components.  Unresolvable
/// references (imported OID names not present in `values`) are left out of the
/// registry and generate a comment in the output instead.
fn build_c_oid_registry(values: &[ValueAssignment]) -> std::collections::HashMap<String, Vec<u32>> {
    use std::collections::HashMap;
    let mut registry: HashMap<String, Vec<u32>> = HashMap::new();

    let mut changed = true;
    while changed {
        changed = false;
        for va in values {
            if registry.contains_key(&va.name) {
                continue;
            }
            if let Value::ObjectIdentifier(components) = &va.value {
                let mut resolved = Vec::new();
                let mut can_resolve = true;
                for component in components {
                    match component {
                        OidComponent::Number(n) => resolved.push(*n),
                        OidComponent::NamedRef(name) => {
                            if let Some(base) = registry.get(name) {
                                resolved.extend_from_slice(base);
                            } else {
                                can_resolve = false;
                                break;
                            }
                        }
                    }
                }
                if can_resolve {
                    registry.insert(va.name.clone(), resolved);
                    changed = true;
                }
            }
        }
    }
    registry
}

/// Escape a string value for use as a C string literal (double-quoted).
///
/// Replaces backslashes (`\`) and double-quotes (`"`) with their C escape
/// sequences.  Other non-ASCII bytes are emitted as `\xNN` hex escapes.
fn escape_c_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_ascii() && (c as u8) >= 0x20 && (c as u8) < 0x7f => out.push(c),
            c => {
                for byte in c.to_string().as_bytes() {
                    out.push_str(&format!("\\x{:02x}", byte));
                }
            }
        }
    }
    out
}

/// Emit C constant definitions for all value assignments in the module.
///
/// | ASN.1 value type  | C output                                                 |
/// |-------------------|----------------------------------------------------------|
/// | OBJECT IDENTIFIER | `static const uint32_t NAME[] = {...};`                  |
/// |                   | `#define NAME_LEN n`                                     |
/// | INTEGER           | `#define NAME ((int64_t)n)`                              |
/// | BOOLEAN           | `#define NAME (true)` / `#define NAME (false)`           |
/// | String            | `#define NAME "text"`                                    |
///
/// OID values that reference other named OIDs in the same module are resolved
/// to their full arc component sequence before being emitted.  References that
/// cannot be resolved (e.g. imported OID names) produce a comment instead.
fn generate_value_constants(
    output: &mut String,
    module: &Module,
) -> Result<(), Box<dyn std::error::Error>> {
    if module.values.is_empty() {
        return Ok(());
    }

    writeln!(output, "/* Value constants */")?;
    writeln!(output)?;

    let oid_registry = build_c_oid_registry(&module.values);

    for va in &module.values {
        let c_name = to_screaming_snake_case(&va.name);
        match &va.value {
            Value::ObjectIdentifier(_) => {
                if let Some(arcs) = oid_registry.get(&va.name) {
                    write!(output, "static const uint32_t {}[] = {{", c_name)?;
                    for (i, n) in arcs.iter().enumerate() {
                        if i > 0 {
                            write!(output, ", ")?;
                        }
                        write!(output, "{}", n)?;
                    }
                    writeln!(output, "}};")?;
                    writeln!(output, "#define {}_LEN {}", c_name, arcs.len())?;
                    writeln!(output)?;
                } else {
                    writeln!(
                        output,
                        "/* OID {} could not be fully resolved (unresolved named reference) */",
                        va.name
                    )?;
                    writeln!(output)?;
                }
            }
            Value::Integer(n) => {
                writeln!(output, "#define {} ((int64_t){})", c_name, n)?;
                writeln!(output)?;
            }
            Value::Boolean(b) => {
                writeln!(
                    output,
                    "#define {} ({})",
                    c_name,
                    if *b { "true" } else { "false" }
                )?;
                writeln!(output)?;
            }
            Value::String(s) => {
                writeln!(output, "#define {} \"{}\"", c_name, escape_c_string(s))?;
                writeln!(output)?;
            }
            Value::Identifier(name) => {
                writeln!(output, "#define {} {}", c_name, to_screaming_snake_case(name))?;
                writeln!(output)?;
            }
        }
    }

    Ok(())
}

/// Strip `Tagged` and `Constrained` wrappers to reach the underlying base type.
fn peel_type(ty: &Type) -> &Type {
    match ty {
        Type::Tagged { inner, .. }
        | Type::Constrained {
            base_type: inner, ..
        } => peel_type(inner),
        _ => ty,
    }
}

/// Return true if `ty` maps to a C pointer (requires a NULL-check in validate helpers).
fn is_pointer_c_type(ty: &Type) -> bool {
    matches!(
        peel_type(ty),
        Type::Integer(_, _)
            | Type::Enumerated(_)
            | Type::OctetString(_)
            | Type::ObjectIdentifier
            | Type::RelativeOid
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::UtcTime
            | Type::GeneralizedTime
            | Type::Any
            | Type::AnyDefinedBy(_)
    )
}

/// Get the C type for an ASN.1 type
pub(crate) fn get_c_type(ty: &Type) -> String {
    match ty {
        Type::Integer(_, _) => "SyntaInteger*".to_string(),
        Type::Enumerated(_) => "SyntaInteger*".to_string(),
        Type::Real => "double".to_string(),
        Type::Boolean => "bool".to_string(),
        Type::OctetString(_) => "SyntaOctetString*".to_string(),
        Type::BitString(_) => "SyntaBitString".to_string(),
        Type::ObjectIdentifier => "SyntaObjectIdentifier*".to_string(),
        Type::RelativeOid => "SyntaRelativeOid*".to_string(),
        Type::Null => "void".to_string(),
        Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::TeletexString(_)
        | Type::UniversalString(_)
        | Type::BmpString(_)
        | Type::GeneralString(_)
        | Type::NumericString(_)
        | Type::VisibleString(_) => {
            "SyntaOctetString*".to_string() // Use OctetString for strings (FFI may not have typed strings yet)
        }
        Type::UtcTime | Type::GeneralizedTime => "SyntaOctetString*".to_string(), // Use OctetString for now (FFI may not have Time yet)
        Type::Sequence(_) | Type::Set(_) => "struct /* complex type */".to_string(),
        Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
            format!("{}*", get_c_type(inner))
        }
        Type::Choice(_) => "union /* choice */".to_string(),
        Type::TypeRef(name) => to_pascal_case(name),
        Type::Tagged { inner, .. } => get_c_type(inner),
        Type::Constrained { base_type, .. } => get_c_type(base_type),
        Type::Any => "SyntaOctetString*".to_string(), // ANY is encoded as OCTET STRING
        Type::AnyDefinedBy(_) => "SyntaOctetString*".to_string(), // ANY DEFINED BY also as OCTET STRING
        Type::Class(_) => "void /* class */".to_string(),         // IOC class — no C type
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_simple_sequence() {
        let module = Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "SimpleSeq".to_string(),
                ty: Type::Sequence(vec![
                    SequenceField {
                        name: "version".to_string(),
                        ty: Type::Integer(None, vec![]),
                        optional: false,
                        default: None,
                    },
                    SequenceField {
                        name: "serialNumber".to_string(),
                        ty: Type::Integer(None, vec![]),
                        optional: false,
                        default: None,
                    },
                ]),
            }],
        };

        let result = generate_c(&module).unwrap();
        assert!(result.contains("typedef struct SimpleSeq"));
        assert!(result.contains("SyntaInteger* version;"));
        assert!(result.contains("SyntaInteger* serial_number;"));
        assert!(result.contains("simple_seq_decode"));
        assert!(result.contains("simple_seq_encode"));
    }

    #[test]
    fn test_generate_choice() {
        let module = Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "MyChoice".to_string(),
                ty: Type::Choice(vec![
                    ChoiceVariant {
                        name: "intVal".to_string(),
                        ty: Type::Integer(None, vec![]),
                    },
                    ChoiceVariant {
                        name: "boolVal".to_string(),
                        ty: Type::Boolean,
                    },
                ]),
            }],
        };

        let result = generate_c(&module).unwrap();
        assert!(result.contains("typedef enum MyChoiceTag"));
        assert!(result.contains("typedef struct MyChoice"));
        assert!(result.contains("MyChoiceTag tag;"));
        assert!(result.contains("union {"));
    }

    #[test]
    fn test_generate_helpers() {
        let module = Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![
                Definition {
                    name: "SimpleSeq".to_string(),
                    ty: Type::Sequence(vec![
                        SequenceField {
                            name: "version".to_string(),
                            ty: Type::Integer(None, vec![]),
                            optional: false,
                            default: None,
                        },
                        SequenceField {
                            name: "flag".to_string(),
                            ty: Type::Boolean,
                            optional: true,
                            default: None,
                        },
                    ]),
                },
                Definition {
                    name: "MyChoice".to_string(),
                    ty: Type::Choice(vec![
                        ChoiceVariant {
                            name: "intVal".to_string(),
                            ty: Type::Integer(None, vec![]),
                        },
                        ChoiceVariant {
                            name: "boolVal".to_string(),
                            ty: Type::Boolean,
                        },
                    ]),
                },
            ],
        };

        let config = CCodeGenConfig {
            generate_helpers: true,
            ..Default::default()
        };
        let result = generate_c_with_config(&module, config).unwrap();

        // stdio.h included when helpers are on
        assert!(result.contains("#include <stdio.h>"));

        // _init for SEQUENCE
        assert!(result.contains("simple_seq_init"));
        // _validate for SEQUENCE
        assert!(result.contains("simple_seq_validate"));
        assert!(result.contains("SyntaErrorCode_NullPointer"));
        // required integer field null-check
        assert!(result.contains("value->version == NULL"));
        // optional boolean field — no null check (not a pointer type)
        assert!(!result.contains("value->flag == NULL"));
        // _print for SEQUENCE
        assert!(result.contains("simple_seq_print"));
        assert!(result.contains("FILE* stream"));

        // _validate for CHOICE
        assert!(result.contains("my_choice_validate"));
        assert!(result.contains("MyChoiceTag_IntVal"));
        assert!(result.contains("SyntaErrorCode_InvalidEncoding"));
        // _print for CHOICE
        assert!(result.contains("my_choice_print"));
    }

    #[test]
    fn test_generate_named_integer() {
        let module = Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "Protocol".to_string(),
                ty: Type::Integer(
                    None,
                    vec![
                        NamedNumber {
                            name: "tcp".to_string(),
                            value: 6,
                        },
                        NamedNumber {
                            name: "udp".to_string(),
                            value: 17,
                        },
                    ],
                ),
            }],
        };

        let result = generate_c(&module).unwrap();
        // Forward declaration uses int64_t, not enum
        assert!(result.contains("typedef int64_t Protocol;"));
        // Named constants as #define macros
        assert!(result.contains("#define PROTOCOL_TCP"));
        assert!(result.contains("((int64_t)6)"));
        assert!(result.contains("#define PROTOCOL_UDP"));
        assert!(result.contains("((int64_t)17)"));
        // No C enum should be generated
        assert!(!result.contains("enum Protocol {"));
    }

    // -----------------------------------------------------------------------
    // Constrained INTEGER tests
    // -----------------------------------------------------------------------

    fn make_constrained_integer_module(
        type_name: &str,
        constraint: SubtypeConstraint,
        named_numbers: Vec<NamedNumber>,
    ) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: type_name.to_string(),
                ty: Type::Constrained {
                    base_type: Box::new(Type::Integer(None, named_numbers)),
                    constraint: Constraint {
                        spec: ConstraintSpec::Subtype(constraint),
                        exception: None,
                    },
                },
            }],
        }
    }

    #[test]
    fn test_constrained_integer_value_range() {
        // Int32 ::= INTEGER (-2147483648..2147483647)
        let module = make_constrained_integer_module(
            "Int32",
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(-2147483648),
                max: ConstraintValue::Integer(2147483647),
            },
            vec![],
        );
        let result = generate_c(&module).unwrap();

        // Struct typedef — range fits int32_t so int32_t is chosen
        assert!(
            result.contains("typedef struct { int32_t value; } Int32;"),
            "missing struct typedef:\n{}",
            result
        );
        // Range displayed in comment
        assert!(result.contains("INTEGER (-2147483648..2147483647)"));
        // _new validated constructor
        assert!(result.contains("int32_new(int32_t v, Int32* out)"));
        assert!(result.contains("v >= -2147483648LL") && result.contains("v <= 2147483647LL"));
        // _new_unchecked
        assert!(result.contains("int32_new_unchecked(int32_t v)"));
        // _get accessor
        assert!(result.contains("int32_get(const Int32* self)"));
        // _validate
        assert!(result.contains("int32_validate(const Int32* self)"));
        // decode / encode prototypes
        assert!(result.contains("int32_decode(SyntaDecoder*"));
        assert!(result.contains("int32_encode(SyntaEncoder*"));
        // no _free (plain struct, no heap allocation)
        assert!(!result.contains("int32_free"));
    }

    #[test]
    fn test_constrained_integer_single_value() {
        // PvNo ::= INTEGER (5)
        let module = make_constrained_integer_module(
            "PvNo",
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(5)),
            vec![],
        );
        let result = generate_c(&module).unwrap();

        // Single value 5 ≥ 0 → uint8_t
        assert!(result.contains("typedef struct { uint8_t value; } PvNo;"));
        assert!(result.contains("INTEGER (5)"));
        assert!(result.contains("v == 5LL"));
        assert!(result.contains("pv_no_new(uint8_t v, PvNo* out)"));
        assert!(result.contains("pv_no_validate(const PvNo* self)"));
    }

    #[test]
    fn test_constrained_integer_min_max_unconstrained() {
        // UncheckedInt ::= INTEGER (MIN..MAX)  — all int64_t values valid
        let module = make_constrained_integer_module(
            "UncheckedInt",
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Min,
                max: ConstraintValue::Max,
            },
            vec![],
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("typedef struct { int64_t value; } UncheckedInt;"));
        // Check expression must be "1" (always true) — no bound to check
        assert!(result.contains("return 1;"));
        // The if(!()) guard must also evaluate to if(!(1)) which is always false, so
        // _new always succeeds.
        assert!(result.contains("if (!(1)) return false;"));
    }

    #[test]
    fn test_constrained_integer_half_open_range() {
        // NonNegInt ::= INTEGER (0..MAX)
        let module = make_constrained_integer_module(
            "NonNegInt",
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(0),
                max: ConstraintValue::Max,
            },
            vec![],
        );
        let result = generate_c(&module).unwrap();

        // Only a lower bound should be generated (no upper bound for MAX)
        assert!(result.contains("v >= 0LL"));
        assert!(!result.contains("v <= INT64_MAX"));
    }

    #[test]
    fn test_constrained_integer_union() {
        // SmallOrLarge ::= INTEGER (0..10 | 100..200)
        let module = make_constrained_integer_module(
            "SmallOrLarge",
            SubtypeConstraint::Union(vec![
                SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(0),
                    max: ConstraintValue::Integer(10),
                },
                SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(100),
                    max: ConstraintValue::Integer(200),
                },
            ]),
            vec![],
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("typedef struct { int64_t value; } SmallOrLarge;"));
        // Union operator
        assert!(result.contains("||"));
        assert!(result.contains("v >= 0LL") && result.contains("v <= 10LL"));
        assert!(result.contains("v >= 100LL") && result.contains("v <= 200LL"));
    }

    #[test]
    fn test_constrained_integer_complement() {
        // NotZero ::= INTEGER (ALL EXCEPT 0)
        let module = make_constrained_integer_module(
            "NotZero",
            SubtypeConstraint::Complement(Box::new(SubtypeConstraint::SingleValue(
                ConstraintValue::Integer(0),
            ))),
            vec![],
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("typedef struct { int64_t value; } NotZero;"));
        assert!(result.contains("!(v == 0LL)"));
    }

    #[test]
    fn test_constrained_integer_with_named_numbers() {
        // MsgType ::= INTEGER (0..30) — with named constants
        let module = make_constrained_integer_module(
            "MsgType",
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(0),
                max: ConstraintValue::Integer(30),
            },
            vec![
                NamedNumber {
                    name: "asReq".to_string(),
                    value: 10,
                },
                NamedNumber {
                    name: "asRep".to_string(),
                    value: 11,
                },
            ],
        );
        let result = generate_c(&module).unwrap();

        // Range 0..30 ≥ 0 → uint8_t
        assert!(result.contains("typedef struct { uint8_t value; } MsgType;"));
        // Named constants emitted as typed #define macros
        assert!(result.contains("#define MsgType_AS_REQ ((uint8_t)10)"));
        assert!(result.contains("#define MsgType_AS_REP ((uint8_t)11)"));
        // Still has validation helpers
        assert!(result.contains("msg_type_new(uint8_t v, MsgType* out)"));
        assert!(result.contains("msg_type_validate(const MsgType* self)"));
    }

    #[test]
    fn test_format_c_constraint_display() {
        assert_eq!(
            format_c_constraint_display(&SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(-128),
                max: ConstraintValue::Integer(127),
            }),
            "-128..127"
        );
        assert_eq!(
            format_c_constraint_display(&SubtypeConstraint::SingleValue(ConstraintValue::Integer(
                42
            ))),
            "42"
        );
        assert_eq!(
            format_c_constraint_display(&SubtypeConstraint::ValueRange {
                min: ConstraintValue::Min,
                max: ConstraintValue::Max,
            }),
            "MIN..MAX"
        );
    }

    #[test]
    fn test_generate_c_constraint_check() {
        // Concrete range, signed type — both bounds emitted
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(0),
                    max: ConstraintValue::Integer(100),
                },
                "int64_t",
            ),
            "(val >= 0LL && val <= 100LL)"
        );
        // Same range, unsigned type — lower bound 0 is trivially satisfied; omitted
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(0),
                    max: ConstraintValue::Integer(100),
                },
                "uint8_t",
            ),
            "(val <= 100LL)"
        );
        // Single value — unsigned does not change equality check
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::SingleValue(ConstraintValue::Integer(5)),
                "int64_t",
            ),
            "val == 5LL"
        );
        // MIN..MAX — always true regardless of type
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Min,
                    max: ConstraintValue::Max,
                },
                "int64_t",
            ),
            "1"
        );
        // Half-open (lower-bounded only), signed — keep the check
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(0),
                    max: ConstraintValue::Max,
                },
                "int64_t",
            ),
            "(val >= 0LL)"
        );
        // Complement
        assert_eq!(
            generate_c_constraint_check(
                "val",
                &SubtypeConstraint::Complement(Box::new(SubtypeConstraint::SingleValue(
                    ConstraintValue::Integer(0)
                ))),
                "int64_t",
            ),
            "!(val == 0LL)"
        );
    }

    // -----------------------------------------------------------------------
    // Constrained string tests
    // -----------------------------------------------------------------------

    fn make_constrained_string_module(
        type_name: &str,
        base_ty: Type,
        constraint: SubtypeConstraint,
    ) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: type_name.to_string(),
                ty: Type::Constrained {
                    base_type: Box::new(base_ty),
                    constraint: Constraint {
                        spec: ConstraintSpec::Subtype(constraint),
                        exception: None,
                    },
                },
            }],
        }
    }

    #[test]
    fn test_constrained_string_size_only() {
        // Realm ::= IA5String (SIZE (1..MAX))
        let module = make_constrained_string_module(
            "Realm",
            Type::IA5String(None),
            SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(1),
                max: ConstraintValue::Max,
            })),
        );
        let result = generate_c(&module).unwrap();

        // Struct typedef
        assert!(
            result.contains("typedef struct { SyntaByteArray value; } Realm;"),
            "missing struct typedef:\n{}",
            result
        );
        // Comment shows base type and constraint
        assert!(result.contains("/* IA5String (SIZE (1..MAX)) */"));
        // _new validated constructor
        assert!(result.contains("realm_new(SyntaByteArray value, Realm* out)"));
        assert!(result.contains("uint32_t _len = value.len;"));
        assert!(result.contains("_len >= 1U"));
        // _new_unchecked
        assert!(result.contains("realm_new_unchecked(SyntaByteArray value)"));
        // _get accessor
        assert!(result.contains("realm_get(const Realm* self)"));
        assert!(result.contains("r.owned = 0"));
        // _validate
        assert!(result.contains("realm_validate(const Realm* self)"));
        assert!(result.contains("uint32_t _len = self->value.len;"));
        // _free
        assert!(result.contains("realm_free(Realm* self)"));
        assert!(result.contains("synta_byte_array_free"));
        // decode / encode prototypes
        assert!(result.contains("realm_decode(SyntaDecoder*"));
        assert!(result.contains("realm_encode(SyntaEncoder*"));
    }

    #[test]
    fn test_constrained_string_size_exact() {
        // FixedTag ::= OCTET STRING (SIZE (4))
        let module = make_constrained_string_module(
            "FixedTag",
            Type::OctetString(None),
            SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::SingleValue(
                ConstraintValue::Integer(4),
            ))),
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("/* OCTET STRING (SIZE (4)) */"));
        assert!(result.contains("typedef struct { SyntaByteArray value; } FixedTag;"));
        assert!(result.contains("_len == 4U"));
        assert!(result.contains("fixed_tag_new(SyntaByteArray value, FixedTag* out)"));
        assert!(result.contains("fixed_tag_validate(const FixedTag* self)"));
        assert!(result.contains("fixed_tag_free(FixedTag* self)"));
    }

    #[test]
    fn test_constrained_string_size_zero_min() {
        // OptStr ::= IA5String (SIZE (0..255))  — no lower bound check needed (uint32_t >= 0 always)
        let module = make_constrained_string_module(
            "OptStr",
            Type::IA5String(None),
            SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(0),
                max: ConstraintValue::Integer(255),
            })),
        );
        let result = generate_c(&module).unwrap();

        // Upper bound present
        assert!(result.contains("_len <= 255U"));
        // Lower bound 0 is always true for uint32_t — must NOT be emitted
        assert!(!result.contains("_len >= 0U"));
    }

    #[test]
    fn test_constrained_string_min_max_size() {
        // AnyStr ::= IA5String (SIZE (MIN..MAX)) — always valid
        let module = make_constrained_string_module(
            "AnyStr",
            Type::IA5String(None),
            SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                min: ConstraintValue::Min,
                max: ConstraintValue::Max,
            })),
        );
        let result = generate_c(&module).unwrap();

        // Should produce "if (!(1)) return false;" — always passes
        assert!(result.contains("if (!(1)) return false;"));
    }

    #[test]
    fn test_constrained_string_alphabet_only() {
        // DigitStr ::= IA5String (FROM ("0".."9"))
        let module = make_constrained_string_module(
            "DigitStr",
            Type::IA5String(None),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: '0', max: '9' }]),
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("/* IA5String (FROM (\"0\"..\"9\")) */"));
        // Alphabet loop structure
        assert!(result.contains("const unsigned char *_ap ="));
        assert!(result.contains("unsigned char _c = _ap[_i]"));
        assert!(result.contains("_ok = (_c >= '0' && _c <= '9')"));
        assert!(result.contains("if (!_ok) return false;"));
    }

    #[test]
    fn test_constrained_string_alphabet_single_char() {
        // SingleChar ::= IA5String (FROM ("x"))
        let module = make_constrained_string_module(
            "SingleChar",
            Type::IA5String(None),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'x', max: 'x' }]),
        );
        let result = generate_c(&module).unwrap();
        // Single char uses == not range
        assert!(result.contains("_ok = _c == 'x'"));
    }

    #[test]
    fn test_constrained_string_size_and_alphabet() {
        // VisStr ::= PrintableString (SIZE (1..64) FROM ("A".."Z" | "a".."z"))
        let module = make_constrained_string_module(
            "VisStr",
            Type::PrintableString(None),
            SubtypeConstraint::Intersection(vec![
                SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(1),
                    max: ConstraintValue::Integer(64),
                })),
                SubtypeConstraint::PermittedAlphabet(vec![
                    CharRange { min: 'A', max: 'Z' },
                    CharRange { min: 'a', max: 'z' },
                ]),
            ]),
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("/* PrintableString"));
        // SIZE check first
        assert!(result.contains("_len >= 1U") && result.contains("_len <= 64U"));
        // Alphabet check
        assert!(result.contains("(_c >= 'A' && _c <= 'Z') || (_c >= 'a' && _c <= 'z')"));
        // _validate also has both checks
        assert!(result.contains("uint32_t _len = self->value.len;"));
    }

    #[test]
    fn test_constrained_string_pattern_placeholder() {
        // PatStr ::= IA5String (PATTERN "[0-9]+")
        let module = make_constrained_string_module(
            "PatStr",
            Type::IA5String(None),
            SubtypeConstraint::Pattern("[0-9]+".to_string()),
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("PATTERN constraint \"[0-9]+\" not enforced at runtime"));
        // Still emits the struct and helpers
        assert!(result.contains("typedef struct { SyntaByteArray value; } PatStr;"));
        assert!(result.contains("pat_str_new(SyntaByteArray value, PatStr* out)"));
    }

    #[test]
    fn test_constrained_utf8string() {
        // Label ::= UTF8String (SIZE (1..255))
        let module = make_constrained_string_module(
            "Label",
            Type::Utf8String(None),
            SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(1),
                max: ConstraintValue::Integer(255),
            })),
        );
        let result = generate_c(&module).unwrap();

        assert!(result.contains("/* UTF8String (SIZE (1..255)) */"));
        assert!(result.contains("typedef struct { SyntaByteArray value; } Label;"));
        assert!(result.contains("label_new(SyntaByteArray value, Label* out)"));
        assert!(result.contains("label_free(Label* self)"));
    }

    #[test]
    fn test_generate_c_length_check() {
        // Exact length
        assert_eq!(
            generate_c_length_check(
                "_len",
                &SubtypeConstraint::SingleValue(ConstraintValue::Integer(4))
            ),
            "_len == 4U"
        );
        // Range 1..MAX — only lower bound
        assert_eq!(
            generate_c_length_check(
                "_len",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(1),
                    max: ConstraintValue::Max,
                }
            ),
            "(_len >= 1U)"
        );
        // Range 0..256 — lower bound 0 omitted
        assert_eq!(
            generate_c_length_check(
                "_len",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(0),
                    max: ConstraintValue::Integer(256),
                }
            ),
            "(_len <= 256U)"
        );
        // MIN..MAX — always true
        assert_eq!(
            generate_c_length_check(
                "_len",
                &SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Min,
                    max: ConstraintValue::Max,
                }
            ),
            "1"
        );
    }

    #[test]
    fn test_format_c_char_literal() {
        assert_eq!(format_c_char_literal('A'), "'A'");
        assert_eq!(format_c_char_literal('0'), "'0'");
        assert_eq!(format_c_char_literal('\''), "'\\''");
        assert_eq!(format_c_char_literal('\\'), "'\\\\'");
        assert_eq!(format_c_char_literal('\x01'), "'\\x01'");
    }

    // -----------------------------------------------------------------------
    // Named-bit BIT STRING constants — Task 7
    // -----------------------------------------------------------------------

    fn make_named_bit_module(name: &str, bits: Vec<NamedNumber>) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: name.to_string(),
                ty: Type::Constrained {
                    base_type: Box::new(Type::BitString(None)),
                    constraint: Constraint {
                        spec: ConstraintSpec::Subtype(SubtypeConstraint::NamedBitList(bits)),
                        exception: None,
                    },
                },
            }],
        }
    }

    #[test]
    fn test_named_bit_string_typedef_and_defines() {
        // TicketFlags ::= BIT STRING { reserved(0), forwardable(1), proxiable(3) }
        let module = make_named_bit_module(
            "TicketFlags",
            vec![
                NamedNumber {
                    name: "reserved".to_string(),
                    value: 0,
                },
                NamedNumber {
                    name: "forwardable".to_string(),
                    value: 1,
                },
                NamedNumber {
                    name: "proxiable".to_string(),
                    value: 3,
                },
            ],
        );
        let result = generate_c(&module).unwrap();

        // Typedef
        assert!(
            result.contains("typedef SyntaBitString TicketFlags;"),
            "typedef present"
        );
        // Named bit defines: prefix is TICKET_FLAGS (snake_case of TicketFlags)
        assert!(
            result.contains("TICKET_FLAGS_RESERVED_BIT"),
            "reserved bit define"
        );
        assert!(
            result.contains("TICKET_FLAGS_FORWARDABLE_BIT"),
            "forwardable bit define"
        );
        assert!(
            result.contains("TICKET_FLAGS_PROXIABLE_BIT"),
            "proxiable bit define"
        );
        // Values
        assert!(
            result.contains("TICKET_FLAGS_RESERVED_BIT") && result.contains(" 0"),
            "value 0 present"
        );
        assert!(result.contains(" 1"), "value 1 present");
        assert!(result.contains(" 3"), "value 3 present");
        // No helper macros without --with-helpers
        assert!(!result.contains("IS_SET"), "no IS_SET without helpers");
    }

    #[test]
    fn test_named_bit_string_hyphenated_name() {
        // kdc-options ::= BIT STRING { reserved(0), forwardable(1) }
        let module = make_named_bit_module(
            "kdc-options",
            vec![
                NamedNumber {
                    name: "reserved".to_string(),
                    value: 0,
                },
                NamedNumber {
                    name: "forwardable".to_string(),
                    value: 1,
                },
            ],
        );
        let result = generate_c(&module).unwrap();
        // Hyphenated name → PascalCase typedef, SCREAMING prefix with underscore
        assert!(
            result.contains("typedef SyntaBitString KdcOptions;"),
            "typedef with PascalCase"
        );
        assert!(
            result.contains("KDC_OPTIONS_RESERVED_BIT"),
            "hyphenated prefix uses underscore"
        );
        assert!(
            result.contains("KDC_OPTIONS_FORWARDABLE_BIT"),
            "forwardable bit define"
        );
    }

    #[test]
    fn test_named_bit_string_camel_case_bit_name() {
        // digitalSignature(0) bit name should become DIGITAL_SIGNATURE
        let module = make_named_bit_module(
            "KeyUsage",
            vec![
                NamedNumber {
                    name: "digitalSignature".to_string(),
                    value: 0,
                },
                NamedNumber {
                    name: "nonRepudiation".to_string(),
                    value: 1,
                },
            ],
        );
        let result = generate_c(&module).unwrap();
        // KeyUsage → KEY_USAGE prefix; camelCase bit names → SCREAMING_SNAKE
        assert!(
            result.contains("KEY_USAGE_DIGITAL_SIGNATURE_BIT"),
            "camelCase bit → SCREAMING_SNAKE"
        );
        assert!(
            result.contains("KEY_USAGE_NON_REPUDIATION_BIT"),
            "nonRepudiation bit"
        );
    }

    #[test]
    fn test_named_bit_string_with_helpers() {
        let module = make_named_bit_module(
            "TicketFlags",
            vec![NamedNumber {
                name: "forwardable".to_string(),
                value: 1,
            }],
        );
        let config = CCodeGenConfig {
            generate_helpers: true,
            ..Default::default()
        };
        let result = generate_c_with_config(&module, config).unwrap();
        // Helper macros present (prefix TICKET_FLAGS from snake_case of TicketFlags)
        assert!(
            result.contains("TICKET_FLAGS_IS_SET(bs, bit)"),
            "IS_SET helper"
        );
        assert!(result.contains("TICKET_FLAGS_SET(bs, bit)"), "SET helper");
        assert!(
            result.contains("TICKET_FLAGS_CLEAR(bs, bit)"),
            "CLEAR helper"
        );
        // Helper macros reference the C API functions
        assert!(result.contains("synta_bitstring_is_set"), "is_set API call");
        assert!(result.contains("synta_bitstring_set"), "set API call");
        assert!(result.contains("synta_bitstring_clear"), "clear API call");
    }

    #[test]
    fn test_named_bit_string_empty_list() {
        // BIT STRING with empty NamedBitList — just a typedef, no defines
        let module = make_named_bit_module("EmptyFlags", vec![]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("typedef SyntaBitString EmptyFlags;"),
            "typedef present"
        );
        assert!(
            !result.contains("EMPTY_FLAGS_"),
            "no defines for empty list"
        );
    }

    // -----------------------------------------------------------------------
    // Named-bit BIT STRING + SIZE constraint — Task 12
    //
    // BIT STRING { bits } (SIZE N..MAX) is parsed as
    //   Intersection([NamedBitList(bits), SizeConstraint(...)]).
    // The C codegen must extract the NamedBitList and generate typedef + #defines,
    // not fall through to generate_constrained_string_c.
    // -----------------------------------------------------------------------

    fn make_named_bit_with_size_module(name: &str, bits: Vec<NamedNumber>) -> Module {
        // Produces BIT STRING { bits } (SIZE (32..MAX))
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: name.to_string(),
                ty: Type::Constrained {
                    base_type: Box::new(Type::BitString(None)),
                    constraint: Constraint {
                        spec: ConstraintSpec::Subtype(SubtypeConstraint::Intersection(vec![
                            SubtypeConstraint::NamedBitList(bits),
                            SubtypeConstraint::SizeConstraint(Box::new(
                                SubtypeConstraint::ValueRange {
                                    min: ConstraintValue::Integer(32),
                                    max: ConstraintValue::Max,
                                },
                            )),
                        ])),
                        exception: None,
                    },
                },
            }],
        }
    }

    #[test]
    fn test_named_bit_string_with_size_emits_typedef() {
        // BIT STRING { bits } (SIZE (32..MAX)) → typedef SyntaBitString, not struct
        let module = make_named_bit_with_size_module(
            "TicketFlags",
            vec![
                NamedNumber {
                    name: "forwardable".to_string(),
                    value: 1,
                },
                NamedNumber {
                    name: "proxiable".to_string(),
                    value: 3,
                },
            ],
        );
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("typedef SyntaBitString TicketFlags;"),
            "combined form must still typedef SyntaBitString; got:\n{}",
            result
        );
        assert!(
            result.contains("#define TICKET_FLAGS_FORWARDABLE_BIT"),
            "FORWARDABLE_BIT define must appear; got:\n{}",
            result
        );
        assert!(
            result.contains("#define TICKET_FLAGS_PROXIABLE_BIT"),
            "PROXIABLE_BIT define must appear; got:\n{}",
            result
        );
        // Must NOT produce a struct { SyntaByteArray value; }
        assert!(
            !result.contains("typedef struct { SyntaByteArray value; } TicketFlags;"),
            "combined form must not fall through to constrained-string struct; got:\n{}",
            result
        );
    }

    #[test]
    fn test_named_bit_string_with_size_helpers() {
        // Helpers should still be emitted for the combined form when enabled
        let module = make_named_bit_with_size_module(
            "KdcOptions",
            vec![NamedNumber {
                name: "forwardable".to_string(),
                value: 1,
            }],
        );
        let config = CCodeGenConfig {
            generate_helpers: true,
            ..Default::default()
        };
        let result = generate_c_with_config(&module, config).unwrap();
        assert!(
            result.contains("KDC_OPTIONS_IS_SET(bs, bit)"),
            "IS_SET helper must appear; got:\n{}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // DEFAULT value annotation tests
    // -----------------------------------------------------------------------

    fn make_default_module(fields: Vec<SequenceField>) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "Config".to_string(),
                ty: Type::Sequence(fields),
            }],
        }
    }

    #[test]
    fn test_sequence_default_comment_in_struct() {
        // Fields with a DEFAULT value get an inline /* DEFAULT … */ comment.
        let module = make_default_module(vec![
            SequenceField {
                name: "port".to_string(),
                ty: Type::Integer(None, vec![]),
                optional: false,
                default: Some("8080".to_string()),
            },
            SequenceField {
                name: "enabled".to_string(),
                ty: Type::Boolean,
                optional: false,
                default: Some("TRUE".to_string()),
            },
        ]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("SyntaInteger* port; /* DEFAULT 8080 */"),
            "integer default comment"
        );
        assert!(
            result.contains("bool enabled; /* DEFAULT TRUE */"),
            "boolean default comment"
        );
    }

    #[test]
    fn test_sequence_default_prototype_generated() {
        // When every field is OPTIONAL or has a DEFAULT, a _default() prototype appears.
        let module = make_default_module(vec![SequenceField {
            name: "port".to_string(),
            ty: Type::Integer(None, vec![]),
            optional: false,
            default: Some("8080".to_string()),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("Config config_default(void);"),
            "default prototype generated"
        );
    }

    #[test]
    fn test_sequence_no_default_prototype_for_required_field() {
        // A required field with no DEFAULT means no _default() prototype.
        let module = make_default_module(vec![SequenceField {
            name: "name".to_string(),
            ty: Type::Integer(None, vec![]),
            optional: false,
            default: None,
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            !result.contains("config_default(void)"),
            "no prototype for required-only sequence"
        );
    }

    // -----------------------------------------------------------------------
    // Tag annotation comment tests
    // -----------------------------------------------------------------------

    fn make_tagged_seq_module(
        field_name: &str,
        class: TagClass,
        number: u32,
        tagging: Tagging,
        inner: Type,
    ) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "Msg".to_string(),
                ty: Type::Sequence(vec![SequenceField {
                    name: field_name.to_string(),
                    ty: Type::Tagged {
                        tag: TagInfo {
                            class,
                            number,
                            tagging,
                        },
                        inner: Box::new(inner),
                    },
                    optional: false,
                    default: None,
                }]),
            }],
        }
    }

    #[test]
    fn test_explicit_tag_annotation_in_struct() {
        // [0] EXPLICIT INTEGER → comment on struct field
        let module = make_tagged_seq_module(
            "id",
            TagClass::ContextSpecific,
            0,
            Tagging::Explicit,
            Type::Integer(None, vec![]),
        );
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("SyntaInteger* id; /* [0] EXPLICIT */"),
            "explicit tag comment missing; got:\n{}",
            result
        );
    }

    #[test]
    fn test_implicit_tag_annotation_in_struct() {
        // [1] IMPLICIT OCTET STRING → comment on struct field
        let module = make_tagged_seq_module(
            "data",
            TagClass::ContextSpecific,
            1,
            Tagging::Implicit,
            Type::OctetString(None),
        );
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("SyntaOctetString* data; /* [1] IMPLICIT */"),
            "implicit tag comment missing; got:\n{}",
            result
        );
    }

    #[test]
    fn test_application_tag_annotation_in_struct() {
        // [APPLICATION 2] IMPLICIT INTEGER → comment on struct field
        let module = make_tagged_seq_module(
            "val",
            TagClass::Application,
            2,
            Tagging::Implicit,
            Type::Integer(None, vec![]),
        );
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("SyntaInteger* val; /* [APPLICATION 2] IMPLICIT */"),
            "APPLICATION tag comment missing; got:\n{}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // Value constants (OID arrays, integer/boolean/string defines)
    // -----------------------------------------------------------------------

    fn make_values_module(values: Vec<crate::ast::ValueAssignment>) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values,
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![],
        }
    }

    #[test]
    fn test_oid_value_constant_emitted() {
        // id-ori OBJECT IDENTIFIER ::= { 1 2 840 113549 1 9 16 13 }
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "id-ori".to_string(),
            ty: Type::ObjectIdentifier,
            value: Value::ObjectIdentifier(vec![
                OidComponent::Number(1),
                OidComponent::Number(2),
                OidComponent::Number(840),
                OidComponent::Number(113549),
                OidComponent::Number(1),
                OidComponent::Number(9),
                OidComponent::Number(16),
                OidComponent::Number(13),
            ]),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("static const uint32_t ID_ORI[] = {1, 2, 840, 113549, 1, 9, 16, 13};"),
            "OID array missing:\n{}",
            result
        );
        assert!(
            result.contains("#define ID_ORI_LEN 8"),
            "_LEN define missing:\n{}",
            result
        );
    }

    #[test]
    fn test_oid_named_reference_resolved() {
        // id-ori       ::= { 1 2 840 113549 1 9 16 13 }
        // id-ori-kem   ::= { id-ori 3 }
        let module = make_values_module(vec![
            crate::ast::ValueAssignment {
                name: "id-ori".to_string(),
                ty: Type::ObjectIdentifier,
                value: Value::ObjectIdentifier(vec![
                    OidComponent::Number(1),
                    OidComponent::Number(2),
                    OidComponent::Number(840),
                    OidComponent::Number(113549),
                    OidComponent::Number(1),
                    OidComponent::Number(9),
                    OidComponent::Number(16),
                    OidComponent::Number(13),
                ]),
            },
            crate::ast::ValueAssignment {
                name: "id-ori-kem".to_string(),
                ty: Type::ObjectIdentifier,
                value: Value::ObjectIdentifier(vec![
                    OidComponent::NamedRef("id-ori".to_string()),
                    OidComponent::Number(3),
                ]),
            },
        ]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains(
                "static const uint32_t ID_ORI_KEM[] = {1, 2, 840, 113549, 1, 9, 16, 13, 3};"
            ),
            "resolved child OID missing:\n{}",
            result
        );
        assert!(
            result.contains("#define ID_ORI_KEM_LEN 9"),
            "_LEN for child OID missing:\n{}",
            result
        );
    }

    #[test]
    fn test_oid_unresolvable_named_ref_emits_comment() {
        // An OID that references an undefined name should emit a comment, not a crash.
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "my-oid".to_string(),
            ty: Type::ObjectIdentifier,
            value: Value::ObjectIdentifier(vec![
                OidComponent::NamedRef("undefined-base".to_string()),
                OidComponent::Number(1),
            ]),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("could not be fully resolved"),
            "unresolvable OID should produce a comment:\n{}",
            result
        );
        // Must not crash or produce a broken array
        assert!(
            !result.contains("static const uint32_t MY_OID[] ="),
            "broken array must not be emitted:\n{}",
            result
        );
    }

    #[test]
    fn test_integer_value_constant() {
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "max-count".to_string(),
            ty: Type::Integer(None, vec![]),
            value: Value::Integer(256),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#define MAX_COUNT ((int64_t)256)"),
            "integer constant missing:\n{}",
            result
        );
    }

    #[test]
    fn test_boolean_value_constant() {
        let module = make_values_module(vec![
            crate::ast::ValueAssignment {
                name: "flag-true".to_string(),
                ty: Type::Boolean,
                value: Value::Boolean(true),
            },
            crate::ast::ValueAssignment {
                name: "flag-false".to_string(),
                ty: Type::Boolean,
                value: Value::Boolean(false),
            },
        ]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#define FLAG_TRUE (true)"),
            "true constant missing:\n{}",
            result
        );
        assert!(
            result.contains("#define FLAG_FALSE (false)"),
            "false constant missing:\n{}",
            result
        );
    }

    #[test]
    fn test_string_value_constant() {
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "default-realm".to_string(),
            ty: Type::Utf8String(None),
            value: Value::String("EXAMPLE.COM".to_string()),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#define DEFAULT_REALM \"EXAMPLE.COM\""),
            "string constant missing:\n{}",
            result
        );
    }

    #[test]
    fn test_string_escape_in_constant() {
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "path".to_string(),
            ty: Type::Utf8String(None),
            value: Value::String("C:\\foo\\bar".to_string()),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#define PATH \"C:\\\\foo\\\\bar\""),
            "backslash not escaped:\n{}",
            result
        );
    }

    #[test]
    fn test_value_constants_section_header() {
        // When there are value assignments, the "Value constants" comment must appear.
        let module = make_values_module(vec![crate::ast::ValueAssignment {
            name: "x".to_string(),
            ty: Type::Integer(None, vec![]),
            value: Value::Integer(1),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("/* Value constants */"),
            "section comment missing"
        );
    }

    #[test]
    fn test_no_value_constants_section_when_empty() {
        // When there are no value assignments, no "Value constants" comment.
        let module = make_values_module(vec![]);
        let result = generate_c(&module).unwrap();
        assert!(
            !result.contains("/* Value constants */"),
            "spurious section comment"
        );
    }

    // -----------------------------------------------------------------------
    // Import #include generation
    // -----------------------------------------------------------------------

    fn make_import_module(imports: Vec<Import>) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports,
            exports: vec![],
            definitions: vec![],
        }
    }

    #[test]
    fn test_import_generates_include() {
        // IMPORTS AlgorithmIdentifier FROM AlgorithmInformation-2009
        let module = make_import_module(vec![Import {
            symbols: vec!["AlgorithmIdentifier".to_string()],
            module_name: "AlgorithmInformation-2009".to_string(),
        }]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#include \"algorithm_information_2009.h\""),
            "import include missing:\n{}",
            result
        );
        assert!(
            result.contains("/* Imported module headers */"),
            "import section comment missing:\n{}",
            result
        );
    }

    #[test]
    fn test_multiple_imports_generate_includes() {
        let module = make_import_module(vec![
            Import {
                symbols: vec!["Name".to_string()],
                module_name: "PKIX1Explicit88".to_string(),
            },
            Import {
                symbols: vec!["AlgorithmIdentifier".to_string()],
                module_name: "AlgorithmInformation-2009".to_string(),
            },
        ]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("#include \"pkix1_explicit88.h\""),
            "first import missing:\n{}",
            result
        );
        assert!(
            result.contains("#include \"algorithm_information_2009.h\""),
            "second import missing:\n{}",
            result
        );
    }

    #[test]
    fn test_no_imports_no_import_section() {
        let module = make_import_module(vec![]);
        let result = generate_c(&module).unwrap();
        assert!(
            !result.contains("/* Imported module headers */"),
            "spurious import section:\n{}",
            result
        );
    }

    // -----------------------------------------------------------------------
    // CHOICE with inline SEQUENCE/SET union member
    // -----------------------------------------------------------------------

    #[test]
    fn test_choice_inline_sequence_generates_named_struct() {
        // A CHOICE variant with an anonymous inline SEQUENCE must be extracted
        // into a named struct `{ChoiceName}{VariantName}` and referenced by
        // value in the union — no void* placeholder.
        let module = Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: "MyChoice".to_string(),
                ty: Type::Choice(vec![
                    ChoiceVariant {
                        name: "seqVal".to_string(),
                        ty: Type::Sequence(vec![SequenceField {
                            name: "x".to_string(),
                            ty: Type::Integer(None, vec![]),
                            optional: false,
                            default: None,
                        }]),
                    },
                    ChoiceVariant {
                        name: "intVal".to_string(),
                        ty: Type::Integer(None, vec![]),
                    },
                ]),
            }],
        };
        let result = generate_c(&module).unwrap();
        // Anonymous SEQUENCE must become a named struct
        assert!(
            result.contains("struct MyChoiceSeqVal {"),
            "expected named struct MyChoiceSeqVal for inline SEQUENCE variant:\n{}",
            result
        );
        // Union member must reference the named struct by value (no void*)
        assert!(
            result.contains("MyChoiceSeqVal seq_val;"),
            "union member should be 'MyChoiceSeqVal seq_val;':\n{}",
            result
        );
        // No void* placeholder must remain
        assert!(
            !result.contains("void* seq_val"),
            "void* placeholder must not appear after expansion:\n{}",
            result
        );
        // Regular integer variant unchanged
        assert!(
            result.contains("SyntaInteger* int_val;"),
            "regular integer variant missing:\n{}",
            result
        );
        // MyChoiceSeqVal must be forward-declared before MyChoice
        let fwd_inner = result
            .find("typedef struct MyChoiceSeqVal")
            .unwrap_or(usize::MAX);
        let fwd_outer = result
            .find("typedef struct MyChoice MyChoice;")
            .unwrap_or(usize::MAX);
        assert!(
            fwd_inner < fwd_outer,
            "MyChoiceSeqVal forward decl must precede MyChoice:\n{}",
            result
        );
    }

    #[test]
    fn test_sequence_all_optional_gets_default_prototype() {
        // A sequence where all fields are OPTIONAL (even with no explicit DEFAULT)
        // also qualifies for a _default() prototype since it can be zero-initialised.
        let module = make_default_module(vec![
            SequenceField {
                name: "host".to_string(),
                ty: Type::OctetString(None),
                optional: true,
                default: None,
            },
            SequenceField {
                name: "port".to_string(),
                ty: Type::Integer(None, vec![]),
                optional: true,
                default: None,
            },
        ]);
        let result = generate_c(&module).unwrap();
        assert!(
            result.contains("Config config_default(void);"),
            "prototype for all-optional sequence"
        );
    }
}
