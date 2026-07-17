//! C implementation code generator for encoder/decoder functions

use crate::ast::*;
use crate::c_codegen::{generate_c_alphabet_expr, get_c_type};
use crate::naming::{to_pascal_case, to_snake_case};
use std::fmt::Write;

/// Controls PATTERN (regex) constraint validation in generated encode functions.
///
/// Without a regex library, PATTERN constraints are skipped and a comment is
/// emitted documenting which flag enables runtime validation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum PatternMode {
    /// Emit a skip comment; no runtime validation (default).
    #[default]
    Skip,
    /// Validate using POSIX ERE (`<regex.h>`, `regcomp`/`regexec`).
    ///
    /// Requires linking with a POSIX-compatible C library.  The generated
    /// code allocates a null-terminated copy of each string before calling
    /// `regexec`.
    Posix,
    /// Validate using PCRE2 (`<pcre2.h>`, `pcre2_compile`/`pcre2_match`).
    ///
    /// Requires linking against `libpcre2-8`.  PCRE2 supports a superset of
    /// the POSIX ERE syntax and handles the full ASN.1 PATTERN value notation.
    Pcre2,
}

/// Configuration for C implementation generation
#[derive(Debug, Clone, Default)]
pub struct CImplConfig {
    /// Header file to include
    pub header_file: String,
    /// Generate _decode_arena() variants
    pub arena_mode: bool,
    /// Controls PATTERN constraint validation (default: `PatternMode::Skip`)
    pub pattern_mode: PatternMode,
    /// Emit CONTAINING constraint validation using a scratch decoder (default: false).
    ///
    /// When true, fields constrained with `CONTAINING InnerType` emit a
    /// `synta_decoder_new` / `inner_type_decode` / `synta_decoder_free` block
    /// that verifies the bytes actually hold a valid DER-encoded `InnerType`.
    pub with_containing: bool,
}

/// Context threaded through field-encode helpers.
struct EncodeCtx<'a> {
    mode: &'a PatternMode,
    with_containing: bool,
    defs: &'a [Definition],
}

/// Generate C implementation file
pub fn generate_c_impl(
    module: &Module,
    config: CImplConfig,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut output = String::new();

    // Header comment
    writeln!(
        &mut output,
        "/* Generated implementation from ASN.1 module {} */",
        module.name
    )?;
    writeln!(&mut output, "/* DO NOT EDIT - auto-generated code */")?;
    writeln!(&mut output)?;

    // Includes
    writeln!(&mut output, "#include \"{}\"", config.header_file)?;
    writeln!(&mut output, "#include <string.h>")?;
    writeln!(&mut output, "#include <stdlib.h>")?;
    match config.pattern_mode {
        PatternMode::Posix => {
            writeln!(&mut output, "#include <regex.h>")?;
        }
        PatternMode::Pcre2 => {
            writeln!(&mut output, "#define PCRE2_CODE_UNIT_WIDTH 8")?;
            writeln!(&mut output, "#include <pcre2.h>")?;
        }
        PatternMode::Skip => {}
    }
    writeln!(&mut output)?;

    let mode = config.pattern_mode;
    let with_containing = config.with_containing;

    // Generate implementations for each type
    for def in &module.definitions {
        generate_type_impl(
            &mut output,
            def,
            &mode,
            with_containing,
            &module.definitions,
        )?;
        writeln!(&mut output)?;
    }

    // Generate arena implementations if enabled
    if config.arena_mode {
        for def in &module.definitions {
            generate_type_arena_impl(&mut output, def, &module.definitions)?;
            writeln!(&mut output)?;
        }
    }

    Ok(output)
}

/// Dispatch to the appropriate C implementation emitter for a single top-level
/// ASN.1 definition.
///
/// Handles SEQUENCE, SET, CHOICE, INTEGER with named numbers, ENUMERATED,
/// SEQUENCE OF, SET OF, constrained SEQUENCE OF / SET OF, and type aliases.
/// For SEQUENCE / SET types where every field is OPTIONAL or carries a DEFAULT,
/// also emits a `<prefix>_default` zero-constructor via
/// [`generate_sequence_default_impl`].
fn generate_type_impl(
    output: &mut String,
    def: &Definition,
    mode: &PatternMode,
    with_containing: bool,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    match &def.ty {
        Type::Sequence(fields) => {
            generate_sequence_impl(
                output,
                &def.name,
                fields,
                mode,
                with_containing,
                defs,
                false,
            )?;
            if fields.iter().all(|f| f.optional || f.default.is_some()) {
                writeln!(output)?;
                generate_sequence_default_impl(output, &def.name, fields)?;
            }
        }
        Type::Set(fields) => {
            generate_sequence_impl(output, &def.name, fields, mode, with_containing, defs, true)?;
            if fields.iter().all(|f| f.optional || f.default.is_some()) {
                writeln!(output)?;
                generate_sequence_default_impl(output, &def.name, fields)?;
            }
        }
        Type::Choice(variants) => {
            generate_choice_impl(output, &def.name, variants, defs)?;
        }
        Type::Integer(_, named_numbers) if !named_numbers.is_empty() => {
            generate_named_integer_impl(output, &def.name)?;
        }
        Type::Enumerated(_) => {
            generate_enum_impl(output, &def.name)?;
        }
        Type::SequenceOf(inner, opt_constraint) => {
            let size_c = opt_constraint.as_ref().map(legacy_size_to_bounds);
            generate_array_impl(output, &def.name, inner, true, size_c, defs)?;
        }
        Type::SetOf(inner, opt_constraint) => {
            let size_c = opt_constraint.as_ref().map(legacy_size_to_bounds);
            generate_array_impl(output, &def.name, inner, false, size_c, defs)?;
        }
        // Constrained SEQUENCE OF / SET OF: the outer constraint holds the SIZE spec.
        Type::Constrained {
            base_type,
            constraint,
        } => {
            let size_c = modern_size_to_bounds(&constraint.spec);
            match base_type.as_ref() {
                Type::SequenceOf(inner, _) => {
                    generate_array_impl(output, &def.name, inner, true, size_c, defs)?;
                }
                Type::SetOf(inner, _) => {
                    generate_array_impl(output, &def.name, inner, false, size_c, defs)?;
                }
                _ => {
                    generate_simple_impl(output, &def.name, &def.ty)?;
                }
            }
        }
        _ => {
            // Simple type alias - generate wrapper functions for the base type
            generate_simple_impl(output, &def.name, &def.ty)?;
        }
    }
    Ok(())
}

/// Convert a legacy `SizeConstraint` to `(min, max)` element-count bounds.
fn legacy_size_to_bounds(sc: &SizeConstraint) -> ArraySizeBounds {
    match sc {
        SizeConstraint::Fixed(n) => (Some(*n), Some(*n)),
        SizeConstraint::Range(min, max) => (*min, *max),
    }
}

/// Extract `(min, max)` element-count bounds from a modern `ConstraintSpec`
/// if it is a `SizeConstraint` wrapping a `ValueRange` or `SingleValue`.
/// Returns `None` for all other constraint forms.
fn modern_size_to_bounds(spec: &ConstraintSpec) -> Option<ArraySizeBounds> {
    if let ConstraintSpec::Subtype(SubtypeConstraint::SizeConstraint(inner)) = spec {
        match inner.as_ref() {
            SubtypeConstraint::ValueRange { min, max } => {
                let lo = match min {
                    ConstraintValue::Integer(n) if *n >= 0 => Some(*n as u64),
                    _ => None,
                };
                let hi = match max {
                    ConstraintValue::Integer(n) if *n >= 0 => Some(*n as u64),
                    _ => None,
                };
                Some((lo, hi))
            }
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(n)) if *n >= 0 => {
                Some((Some(*n as u64), Some(*n as u64)))
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Generate encode/decode/free C functions for a top-level SEQUENCE or SET type.
///
/// **Memory contract for the generated decoder** — if decoding fails partway
/// through, any fields that were already successfully decoded and heap-allocated
/// (e.g. `SyntaInteger*`, `SyntaOctetString*`) are **not** freed before
/// returning the error.  Callers are responsible for calling `<name>_free` on
/// the partially-filled output struct to avoid leaks.
fn generate_sequence_impl(
    output: &mut String,
    name: &str,
    fields: &[SequenceField],
    mode: &PatternMode,
    with_containing: bool,
    defs: &[Definition],
    is_set: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let container_kind = if is_set { "set" } else { "sequence" };
    let enter_fn = if is_set {
        "synta_decoder_enter_set"
    } else {
        "synta_decoder_enter_sequence"
    };
    let start_fn = if is_set {
        "synta_encoder_start_set"
    } else {
        "synta_encoder_start_sequence"
    };

    // Decode function
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    // Enter {}", container_kind.to_uppercase())?;
    writeln!(output, "    SyntaDecoder* seq_decoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = {}(decoder, &seq_decoder);",
        enter_fn
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    // Decode each field
    for field in fields {
        let field_name = to_snake_case(&field.name);

        if field.optional {
            writeln!(output, "    // Decode optional field: {}", field_name)?;
            let tag_check = get_tag_check_condition(&field.ty, defs);
            writeln!(output, "    {{")?;
            writeln!(output, "        SyntaTag tag;")?;
            writeln!(
                output,
                "        if (synta_decoder_peek_tag(seq_decoder, &tag) == SyntaErrorCode_Success &&"
            )?;
            writeln!(output, "            ({})) {{", tag_check)?;
            generate_field_decode(output, &field.ty, &format!("out->{}", field_name), 3, defs)?;
            writeln!(output, "            out->has_{} = true;", field_name)?;
            writeln!(output, "        }} else {{")?;
            writeln!(output, "            out->has_{} = false;", field_name)?;
            writeln!(output, "        }}")?;
            writeln!(output, "    }}")?;
        } else {
            writeln!(output, "    // Decode field: {}", field_name)?;
            generate_field_decode(output, &field.ty, &format!("out->{}", field_name), 1, defs)?;
        }
        writeln!(output)?;
    }

    writeln!(output, "    synta_decoder_free(seq_decoder);")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Encode function
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const {}* value) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    // Start {}", container_kind.to_uppercase())?;
    writeln!(output, "    SyntaEncoder* seq_encoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = {}(encoder, &seq_encoder);",
        start_fn
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;

    let enc_ctx = EncodeCtx {
        mode,
        with_containing,
        defs,
    };
    for field in fields {
        let field_name = to_snake_case(&field.name);

        if field.optional {
            writeln!(output, "    if (value->has_{}) {{", field_name)?;
            generate_field_encode(
                output,
                &field.ty,
                &format!("value->{}", field_name),
                "seq_encoder",
                2,
                &enc_ctx,
            )?;
            writeln!(output, "    }}")?;
        } else {
            generate_field_encode(
                output,
                &field.ty,
                &format!("value->{}", field_name),
                "seq_encoder",
                1,
                &enc_ctx,
            )?;
        }
    }

    writeln!(output)?;
    writeln!(
        output,
        "    err = synta_encoder_end_constructed(seq_encoder);"
    )?;
    writeln!(output, "    return err;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Free function
    writeln!(output, "void {}_free({}* value) {{", fn_prefix, struct_name)?;
    writeln!(output, "    if (value == NULL) return;")?;
    writeln!(output)?;

    for field in fields {
        let field_name = to_snake_case(&field.name);
        match &field.ty {
            Type::Integer(_, _) => {
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    writeln!(output, "        synta_integer_free(value->{});", field_name)?;
                    writeln!(output, "    }}")?;
                } else {
                    writeln!(output, "    synta_integer_free(value->{});", field_name)?;
                }
            }
            Type::ObjectIdentifier => {
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    writeln!(output, "        synta_oid_free(value->{});", field_name)?;
                    writeln!(output, "    }}")?;
                } else {
                    writeln!(output, "    synta_oid_free(value->{});", field_name)?;
                }
            }
            Type::RelativeOid => {
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    writeln!(output, "        synta_reloid_free(value->{});", field_name)?;
                    writeln!(output, "    }}")?;
                } else {
                    writeln!(output, "    synta_reloid_free(value->{});", field_name)?;
                }
            }
            Type::OctetString(_)
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::UtcTime
            | Type::GeneralizedTime
            | Type::Any
            | Type::AnyDefinedBy(_) => {
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    writeln!(
                        output,
                        "        synta_octet_string_free(value->{});",
                        field_name
                    )?;
                    writeln!(output, "    }}")?;
                } else {
                    writeln!(
                        output,
                        "    synta_octet_string_free(value->{});",
                        field_name
                    )?;
                }
            }
            Type::BitString(_) => {
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    writeln!(
                        output,
                        "        synta_byte_array_free(&value->{}.data);",
                        field_name
                    )?;
                    writeln!(output, "    }}")?;
                } else {
                    writeln!(
                        output,
                        "    synta_byte_array_free(&value->{}.data);",
                        field_name
                    )?;
                }
            }
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
                // Free array elements if needed
                if needs_freeing(inner, defs) {
                    writeln!(output, "    // Free array elements")?;
                    writeln!(
                        output,
                        "    for (size_t i = 0; i < value->{}_count; i++) {{",
                        field_name
                    )?;
                    generate_free_element(
                        output,
                        inner,
                        &format!("value->{}[i]", field_name),
                        defs,
                    )?;
                    writeln!(output, "    }}")?;
                }
                writeln!(output, "    // Free array")?;
                writeln!(output, "    free(value->{});", field_name)?;
            }
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                // Free nested inline SEQUENCE/SET fields
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }

                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("value->{}.{}", field_name, inner_name);

                    match &inner_field.ty {
                        Type::Integer(_, _) => {
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                writeln!(output, "        synta_integer_free({});", nested_var)?;
                                writeln!(output, "    }}")?;
                            } else {
                                writeln!(output, "    synta_integer_free({});", nested_var)?;
                            }
                        }
                        Type::ObjectIdentifier => {
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                writeln!(output, "        synta_oid_free({});", nested_var)?;
                                writeln!(output, "    }}")?;
                            } else {
                                writeln!(output, "    synta_oid_free({});", nested_var)?;
                            }
                        }
                        Type::RelativeOid => {
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                writeln!(output, "        synta_reloid_free({});", nested_var)?;
                                writeln!(output, "    }}")?;
                            } else {
                                writeln!(output, "    synta_reloid_free({});", nested_var)?;
                            }
                        }
                        Type::OctetString(_)
                        | Type::Utf8String(_)
                        | Type::PrintableString(_)
                        | Type::IA5String(_) => {
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                writeln!(
                                    output,
                                    "        synta_octet_string_free({});",
                                    nested_var
                                )?;
                                writeln!(output, "    }}")?;
                            } else {
                                writeln!(output, "    synta_octet_string_free({});", nested_var)?;
                            }
                        }
                        Type::BitString(_) => {
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                writeln!(
                                    output,
                                    "        synta_byte_array_free(&{}.data);",
                                    nested_var
                                )?;
                                writeln!(output, "    }}")?;
                            } else {
                                writeln!(
                                    output,
                                    "    synta_byte_array_free(&{}.data);",
                                    nested_var
                                )?;
                            }
                        }
                        Type::TypeRef(type_name) => {
                            let name = type_name.clone();
                            if inner_field.optional {
                                writeln!(
                                    output,
                                    "    if (value->{}.has_{}) {{",
                                    field_name, inner_name
                                )?;
                                emit_typeref_free(output, &name, &nested_var, "        ", defs)?;
                                writeln!(output, "    }}")?;
                            } else {
                                emit_typeref_free(output, &name, &nested_var, "    ", defs)?;
                            }
                        }
                        _ => {}
                    }
                }
            }
            Type::TypeRef(type_name) if needs_freeing(&field.ty, defs) => {
                let name = type_name.clone();
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    emit_typeref_free(
                        output,
                        &name,
                        &format!("value->{}", field_name),
                        "        ",
                        defs,
                    )?;
                    writeln!(output, "    }}")?;
                } else {
                    emit_typeref_free(
                        output,
                        &name,
                        &format!("value->{}", field_name),
                        "    ",
                        defs,
                    )?;
                }
            }
            Type::Tagged { inner, .. }
            | Type::Constrained {
                base_type: inner, ..
            } => {
                // Unwrap tag/constraint wrapper and free the underlying value
                let base_ty = unwrap_type(inner);
                if field.optional {
                    writeln!(output, "    if (value->has_{}) {{", field_name)?;
                    generate_free_stmt(
                        output,
                        base_ty,
                        &format!("value->{}", field_name),
                        "        ",
                    )?;
                    writeln!(output, "    }}")?;
                } else {
                    generate_free_stmt(output, base_ty, &format!("value->{}", field_name), "    ")?;
                }
            }
            _ => {}
        }
    }

    writeln!(output, "}}")?;

    Ok(())
}

/// Generate a `TypeName_default(void)` constructor for sequences where every
/// field is either OPTIONAL or carries a DEFAULT value.
///
/// The returned struct is zero-initialised (`{0}`), so optional `has_*` flags
/// are already `false` and all pointers are `NULL`.  Fields with a DEFAULT are
/// annotated:
///
/// * `BOOLEAN DEFAULT TRUE` — assigned directly (`out.field = true;`).
/// * `REAL DEFAULT <n>` — assigned directly (`out.field = <n>;`).
/// * All other types — a comment is emitted instead, because the C
///   representation is a pointer that cannot be trivially assigned a literal.
fn generate_sequence_default_impl(
    output: &mut String,
    name: &str,
    fields: &[SequenceField],
) -> Result<(), Box<dyn std::error::Error>> {
    let c_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);

    writeln!(output, "{c_name} {fn_prefix}_default(void) {{")?;
    writeln!(output, "    {c_name} out = {{0}};")?;

    for field in fields {
        let Some(ref default_val) = field.default else {
            continue;
        };
        let field_name = to_snake_case(&field.name);
        match unwrap_type(&field.ty) {
            Type::Boolean => {
                // Only emit an assignment when the default is not false (zero already gives false).
                let is_true = default_val.eq_ignore_ascii_case("true");
                if is_true {
                    writeln!(output, "    out.{field_name} = true;")?;
                }
            }
            Type::Real => {
                writeln!(output, "    out.{field_name} = {default_val};")?;
            }
            _ => {
                writeln!(
                    output,
                    "    /* out.{field_name}: DEFAULT {default_val} — set by caller or decoder */"
                )?;
            }
        }
    }

    writeln!(output, "    return out;")?;
    writeln!(output, "}}")?;
    Ok(())
}

/// Generate encode, decode, and free C functions for a top-level CHOICE type.
///
/// The decoder peeks at the next tag, walks an if-else chain to select the
/// matching variant, sets the discriminant field, and delegates to the
/// variant's type-specific decoder.  The encoder switches on the discriminant
/// and calls the matching variant encoder.  The free function switches on the
/// discriminant and frees only the active variant's heap data.
fn generate_choice_impl(
    output: &mut String,
    name: &str,
    variants: &[ChoiceVariant],
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let tag_enum_name = format!("{}Tag", struct_name);

    // Decode function
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    // Peek at the next tag to determine which variant"
    )?;
    writeln!(output, "    SyntaTag tag;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decoder_peek_tag(decoder, &tag);"
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    // Generate if-else chain to match variants by tag
    for (i, variant) in variants.iter().enumerate() {
        let variant_name = to_snake_case(&variant.name);
        let variant_pascal = to_pascal_case(&variant.name);
        let tag_check = get_tag_check_condition(&variant.ty, defs);

        let else_if = if i == 0 { "if" } else { "} else if" };

        writeln!(output, "    {} ({}) {{", else_if, tag_check)?;
        writeln!(output, "        // Decode {} variant", variant_name)?;
        writeln!(
            output,
            "        out->tag = {}_{};",
            tag_enum_name, variant_pascal
        )?;
        generate_choice_variant_decode(
            output,
            &variant.ty,
            &format!("out->value.{}", variant_name),
        )?;
        writeln!(output, "        return SyntaErrorCode_Success;")?;
    }

    writeln!(output, "    }} else {{")?;
    writeln!(
        output,
        "        /* no matching variant found for the observed tag */"
    )?;
    writeln!(output, "        return SyntaErrorCode_InvalidEncoding;")?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Encode function
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const {}* value) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    SyntaErrorCode err;")?;
    writeln!(output, "    switch (value->tag) {{")?;

    // Generate case for each variant
    for variant in variants {
        let variant_name = to_snake_case(&variant.name);
        let variant_pascal = to_pascal_case(&variant.name);

        writeln!(
            output,
            "        case {}_{}: {{",
            tag_enum_name, variant_pascal
        )?;
        generate_choice_variant_encode(
            output,
            &variant.ty,
            &format!("value->value.{}", variant_name),
        )?;
        writeln!(output, "            return SyntaErrorCode_Success;")?;
        writeln!(output, "        }}")?;
    }

    writeln!(output, "        default:")?;
    writeln!(output, "            return SyntaErrorCode_InvalidEncoding;")?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Free function
    writeln!(output, "void {}_free({}* value) {{", fn_prefix, struct_name)?;
    writeln!(output, "    if (value == NULL) return;")?;
    writeln!(output)?;
    writeln!(output, "    switch (value->tag) {{")?;

    // Generate case for each variant that needs freeing
    for variant in variants {
        let variant_name = to_snake_case(&variant.name);
        let variant_pascal = to_pascal_case(&variant.name);

        // Check if this variant needs freeing
        if needs_freeing(&variant.ty, defs) {
            writeln!(
                output,
                "        case {}_{}: {{",
                tag_enum_name, variant_pascal
            )?;
            generate_choice_variant_free(
                output,
                &variant.ty,
                &format!("value->value.{}", variant_name),
                defs,
            )?;
            writeln!(output, "            break;")?;
            writeln!(output, "        }}")?;
        }
    }

    writeln!(output, "        default:")?;
    writeln!(output, "            break;")?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// (min, max) element-count bounds for a SEQUENCE OF / SET OF SIZE constraint.
/// `None` means the bound is absent (unbounded in that direction).
type ArraySizeBounds = (Option<u64>, Option<u64>);

/// Generate encode, decode, and free C functions for a top-level SEQUENCE OF
/// or SET OF type.
///
/// The decoder uses a heap array with an initial capacity of 4 elements,
/// doubling on overflow (`realloc`).  If any element decode fails, the
/// partial array and the inner `array_decoder` are freed before returning the
/// error.  An optional SIZE constraint is checked after all elements are
/// decoded (decode path) or before encoding begins (encode path).  The free
/// function iterates over the array, frees each element that requires it,
/// then frees the array pointer itself.
fn generate_array_impl(
    output: &mut String,
    name: &str,
    inner_ty: &Type,
    is_sequence: bool,
    size_constraint: Option<ArraySizeBounds>,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let container_type = if is_sequence { "sequence" } else { "set" };
    let elem_c_type = get_c_type(inner_ty);
    let array_type = format!("{}*", elem_c_type);

    // Decode function
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, struct {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(output, "    // Enter SEQUENCE/SET")?;
    writeln!(output, "    SyntaDecoder* array_decoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decoder_enter_{}(decoder, &array_decoder);",
        container_type
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(output, "    // Allocate dynamic array for elements")?;
    writeln!(output, "    size_t capacity = 4; // Initial capacity")?;
    writeln!(output, "    size_t count = 0;")?;
    writeln!(
        output,
        "    {} array = ({})calloc(capacity, sizeof({}));",
        array_type, array_type, elem_c_type
    )?;
    writeln!(output, "    if (array == NULL) {{")?;
    writeln!(output, "        synta_decoder_free(array_decoder);")?;
    writeln!(output, "        return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(
        output,
        "    while (!synta_decoder_at_end(array_decoder)) {{"
    )?;
    writeln!(output, "        // Grow array if needed")?;
    writeln!(output, "        if (count >= capacity) {{")?;
    writeln!(output, "            capacity *= 2;")?;
    writeln!(
        output,
        "            {} new_array = ({})realloc(array, capacity * sizeof({}));",
        array_type, array_type, elem_c_type
    )?;
    writeln!(output, "            if (new_array == NULL) {{")?;
    writeln!(output, "                free(array);")?;
    writeln!(output, "                synta_decoder_free(array_decoder);")?;
    writeln!(output, "                return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "            }}")?;
    writeln!(output, "            array = new_array;")?;
    writeln!(output, "        }}")?;
    writeln!(output)?;

    // Generate decode for element
    writeln!(output, "        // Decode element")?;
    generate_decode_element_toplevel(output, inner_ty, "array_decoder", "array[count]")?;
    writeln!(output, "        count++;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    // SIZE constraint check after the decode loop
    if let Some(size_spec) = size_constraint {
        emit_array_size_check(output, size_spec, "count")?;
    }

    writeln!(output, "    out->count = count;")?;
    writeln!(output, "    out->items = array;")?;
    writeln!(output, "    synta_decoder_free(array_decoder);")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Encode function
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const struct {}* value) {{",
        fn_prefix, struct_name
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    // SIZE constraint check before encoding
    if let Some(size_spec) = size_constraint {
        emit_array_size_check_encode(output, size_spec, "value->count")?;
    }

    writeln!(output, "    // Start SEQUENCE/SET")?;
    writeln!(output, "    SyntaEncoder* array_encoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_encoder_start_{}(encoder, &array_encoder);",
        container_type
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;

    writeln!(output, "    // Encode each element")?;
    writeln!(output, "    for (size_t i = 0; i < value->count; i++) {{")?;
    generate_encode_element_toplevel(output, inner_ty, "array_encoder", "value->items[i]")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(
        output,
        "    return synta_encoder_end_constructed(array_encoder);"
    )?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Free function
    writeln!(output, "void {}_free({}* value) {{", fn_prefix, struct_name)?;
    writeln!(output, "    if (value == NULL) return;")?;
    writeln!(output)?;

    if needs_freeing(inner_ty, defs) {
        writeln!(output, "    // Free each element")?;
        writeln!(output, "    for (size_t i = 0; i < value->count; i++) {{")?;
        generate_free_element(output, inner_ty, "value->items[i]", defs)?;
        writeln!(output, "    }}")?;
        writeln!(output)?;
    }

    writeln!(output, "    // Free array")?;
    writeln!(output, "    free(value->items);")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate encode and decode C functions for an ASN.1 ENUMERATED type.
///
/// The decoder reads a DER INTEGER TLV via `synta_integer_decode`, extracts
/// the value with `synta_integer_to_i64`, and casts it to the C `enum` type.
/// The encoder wraps the value in a temporary `SyntaInteger*` and encodes it.
/// No range validation is performed; the caller is responsible for ensuring
/// only valid enumerators are stored.
fn generate_enum_impl(output: &mut String, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let fn_prefix = to_snake_case(name);

    // Decode function
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, enum {}* out) {{",
        fn_prefix,
        to_pascal_case(name)
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    SyntaInteger* int_val = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decode_integer(decoder, &int_val);"
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    int64_t val;")?;
    writeln!(output, "    err = synta_integer_to_i64(int_val, &val);")?;
    writeln!(output, "    synta_integer_free(int_val);")?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    *out = (enum {})val;", to_pascal_case(name))?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Encode function
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const enum {}* value) {{",
        fn_prefix,
        to_pascal_case(name)
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    SyntaInteger* int_val = synta_integer_new_i64((int64_t)*value);"
    )?;
    writeln!(output, "    if (int_val == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_encode_integer(encoder, int_val);"
    )?;
    writeln!(output, "    synta_integer_free(int_val);")?;
    writeln!(output, "    return err;")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate decode/encode functions for an unconstrained INTEGER with named numbers.
///
/// The C type is `typedef int64_t TypeName;` (see the "Why `int64_t`?" note in
/// `generate_defines_for_integer` in `c_codegen.rs`), so the pointer parameter
/// is `TypeName*` (i.e. `int64_t*`).  No enum cast is performed: the decode
/// path assigns `*out = val` directly and the encode path passes `*value`
/// straight to `synta_integer_new_i64`, avoiding a round-trip through an enum
/// type whose C representation size is implementation-defined.
fn generate_named_integer_impl(
    output: &mut String,
    name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let fn_prefix = to_snake_case(name);
    let c_name = to_pascal_case(name);

    // Decode function
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, {}* out) {{",
        fn_prefix, c_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    SyntaInteger* int_val = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decode_integer(decoder, &int_val);"
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    int64_t val;")?;
    writeln!(output, "    err = synta_integer_to_i64(int_val, &val);")?;
    writeln!(output, "    synta_integer_free(int_val);")?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    *out = val;")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;
    writeln!(output)?;

    // Encode function
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const {}* value) {{",
        fn_prefix, c_name
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    SyntaInteger* int_val = synta_integer_new_i64(*value);"
    )?;
    writeln!(output, "    if (int_val == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_encode_integer(encoder, int_val);"
    )?;
    writeln!(output, "    synta_integer_free(int_val);")?;
    writeln!(output, "    return err;")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Unwrap Tagged/Constrained wrappers to find the underlying base type.
fn unwrap_type(ty: &Type) -> &Type {
    match ty {
        Type::Tagged { inner, .. } => unwrap_type(inner),
        Type::Constrained { base_type, .. } => unwrap_type(base_type),
        other => other,
    }
}

/// Generate decode/encode wrapper functions for a simple type alias.
///
/// Dispatches to the correct C API based on the actual underlying type so
/// that, e.g., a `MyBool ::= BOOLEAN` alias calls `synta_decode_boolean`
/// rather than the formerly hard-coded `synta_decode_integer`.
fn generate_simple_impl(
    output: &mut String,
    name: &str,
    ty: &Type,
) -> Result<(), Box<dyn std::error::Error>> {
    let fn_prefix = to_snake_case(name);
    let type_name = to_pascal_case(name);
    let base = unwrap_type(ty);

    // ── decode ────────────────────────────────────────────────────────────
    writeln!(
        output,
        "SyntaErrorCode {}_decode(SyntaDecoder* decoder, {}* out) {{",
        fn_prefix, type_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    match base {
        Type::Boolean => {
            writeln!(output, "    return synta_decode_boolean(decoder, out);")?;
        }
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(output, "    return synta_decode_integer(decoder, out);")?;
        }
        Type::Real => {
            writeln!(output, "    return synta_decode_real(decoder, out);")?;
        }
        Type::Null => {
            writeln!(output, "    (void)out;")?;
            writeln!(output, "    return synta_decode_null(decoder);")?;
        }
        Type::ObjectIdentifier => {
            writeln!(
                output,
                "    return synta_decode_object_identifier(decoder, out);"
            )?;
        }
        Type::RelativeOid => {
            writeln!(
                output,
                "    return synta_decode_relative_oid(decoder, out);"
            )?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "    return synta_decode_bit_string(decoder, &out->data, &out->unused_bits);"
            )?;
        }
        Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_) => {
            writeln!(
                output,
                "    return synta_decode_octet_string(decoder, out);"
            )?;
        }
        Type::Utf8String(_) => {
            writeln!(
                output,
                "    return synta_decode_utf8_string_os(decoder, out);"
            )?;
        }
        Type::PrintableString(_) => {
            writeln!(
                output,
                "    return synta_decode_printable_string_os(decoder, out);"
            )?;
        }
        Type::IA5String(_) => {
            writeln!(
                output,
                "    return synta_decode_ia5_string_os(decoder, out);"
            )?;
        }
        Type::UtcTime => {
            writeln!(output, "    return synta_decode_utctime_os(decoder, out);")?;
        }
        Type::GeneralizedTime => {
            writeln!(
                output,
                "    return synta_decode_generalized_time_os(decoder, out);"
            )?;
        }
        Type::TypeRef(ref_name) => {
            let ref_fn = to_snake_case(ref_name);
            writeln!(output, "    return {}_decode(decoder, out);", ref_fn)?;
        }
        _ => {
            writeln!(output, "    /* unsupported simple type alias */")?;
            writeln!(output, "    return SyntaErrorCode_InvalidEncoding;")?;
        }
    }
    writeln!(output, "}}")?;
    writeln!(output)?;

    // ── encode ────────────────────────────────────────────────────────────
    writeln!(
        output,
        "SyntaErrorCode {}_encode(SyntaEncoder* encoder, const {}* value) {{",
        fn_prefix, type_name
    )?;
    writeln!(output, "    if (encoder == NULL || value == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    match base {
        Type::Boolean => {
            writeln!(output, "    return synta_encode_boolean(encoder, *value);")?;
        }
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(output, "    return synta_encode_integer(encoder, value);")?;
        }
        Type::Real => {
            writeln!(output, "    return synta_encode_real(encoder, *value);")?;
        }
        Type::Null => {
            writeln!(output, "    (void)value;")?;
            writeln!(output, "    return synta_encode_null(encoder);")?;
        }
        Type::ObjectIdentifier => {
            writeln!(
                output,
                "    return synta_encode_object_identifier(encoder, value);"
            )?;
        }
        Type::RelativeOid => {
            writeln!(
                output,
                "    return synta_encode_relative_oid(encoder, value);"
            )?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "    return synta_encode_bit_string(encoder, value->data.data, value->data.len, value->unused_bits);"
            )?;
        }
        // For pointer typedef aliases (e.g. `typedef SyntaOctetString* Label`),
        // `value` is `const Label*` = `SyntaOctetString* const*`.  Dereference once
        // to obtain the `SyntaOctetString*` and use the type-specific encode function
        // so the correct ASN.1 tag is written to the output.
        Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_) => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_octet_string(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::Utf8String(_) => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_utf8_string_bytes(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::PrintableString(_) => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_printable_string_bytes(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::IA5String(_) => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_ia5_string_bytes(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::UtcTime => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_utctime_bytes(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::GeneralizedTime => {
            writeln!(
                output,
                "    if (*value == NULL) return SyntaErrorCode_NullPointer;"
            )?;
            writeln!(
                output,
                "    return synta_encode_generalized_time_bytes(encoder, synta_octet_string_data(*value), synta_octet_string_len(*value));"
            )?;
        }
        Type::TypeRef(ref_name) => {
            let ref_fn = to_snake_case(ref_name);
            writeln!(output, "    return {}_encode(encoder, value);", ref_fn)?;
        }
        _ => {
            writeln!(output, "    /* unsupported simple type alias */")?;
            writeln!(output, "    return SyntaErrorCode_InvalidEncoding;")?;
        }
    }
    writeln!(output, "}}")?;

    Ok(())
}

/// Build the C API call string to decode `ty` from `decoder` into `var`.
///
/// Returns `None` for types that require structural handling (SEQUENCE, SEQUENCE OF,
/// SET, SET OF) so callers can emit that code explicitly.
/// Automatically unwraps `Tagged` and `Constrained` wrappers by recursion.
fn make_decode_call(ty: &Type, decoder: &str, var: &str) -> Option<String> {
    match ty {
        Type::Boolean => Some(format!("synta_decode_boolean({}, &{})", decoder, var)),
        Type::Integer(_, _) | Type::Enumerated(_) => {
            Some(format!("synta_decode_integer({}, &{})", decoder, var))
        }
        Type::Real => Some(format!("synta_decode_real({}, &{})", decoder, var)),
        Type::Null => Some(format!("synta_decode_null({})", decoder)),
        Type::ObjectIdentifier => Some(format!(
            "synta_decode_object_identifier({}, &{})",
            decoder, var
        )),
        Type::RelativeOid => Some(format!("synta_decode_relative_oid({}, &{})", decoder, var)),
        Type::BitString(_) => Some(format!(
            "synta_decode_bit_string({}, &{}.data, &{}.unused_bits)",
            decoder, var, var
        )),
        Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_) => {
            Some(format!("synta_decode_octet_string({}, &{})", decoder, var))
        }
        Type::Utf8String(_) => Some(format!(
            "synta_decode_utf8_string_os({}, &{})",
            decoder, var
        )),
        Type::PrintableString(_) => Some(format!(
            "synta_decode_printable_string_os({}, &{})",
            decoder, var
        )),
        Type::IA5String(_) => Some(format!("synta_decode_ia5_string_os({}, &{})", decoder, var)),
        Type::UtcTime => Some(format!("synta_decode_utctime_os({}, &{})", decoder, var)),
        Type::GeneralizedTime => Some(format!(
            "synta_decode_generalized_time_os({}, &{})",
            decoder, var
        )),
        Type::TypeRef(name) => Some(format!(
            "{}_decode({}, &{})",
            to_snake_case(name),
            decoder,
            var
        )),
        Type::Tagged { tag, inner } => match tag.tagging {
            // EXPLICIT always wraps the inner TLV in a constructed outer TLV;
            // return None so the caller falls through to structural handling in
            // generate_field_decode where the enter_constructed wrapper is emitted.
            Tagging::Explicit => None,
            // IMPLICIT: the tag is replaced but the value bytes are unchanged,
            // so make a best-effort attempt to decode the inner type directly.
            Tagging::Implicit => make_decode_call(inner, decoder, var),
        },
        Type::Constrained {
            base_type: inner, ..
        } => make_decode_call(inner, decoder, var),
        _ => None,
    }
}

/// Build the C API call string to encode `ty` from `var` into `encoder`.
///
/// Returns `None` for types that require structural handling.
/// Automatically unwraps `Tagged` and `Constrained` wrappers by recursion.
fn make_encode_call(ty: &Type, encoder: &str, var: &str) -> Option<String> {
    match ty {
        Type::Boolean => Some(format!("synta_encode_boolean({}, {})", encoder, var)),
        Type::Integer(_, _) | Type::Enumerated(_) => {
            Some(format!("synta_encode_integer({}, {})", encoder, var))
        }
        Type::Real => Some(format!("synta_encode_real({}, {})", encoder, var)),
        Type::Null => Some(format!("synta_encode_null({})", encoder)),
        Type::ObjectIdentifier => {
            Some(format!("synta_encode_object_identifier({}, {})", encoder, var))
        }
        Type::RelativeOid => {
            Some(format!("synta_encode_relative_oid({}, {})", encoder, var))
        }
        Type::BitString(_) => Some(format!(
            "synta_encode_bit_string({}, {}.data.data, {}.data.len, {}.unused_bits)",
            encoder, var, var, var
        )),
        Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_) => Some(format!(
            "synta_encode_octet_string({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::Utf8String(_) => Some(format!(
            "synta_encode_utf8_string_bytes({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::PrintableString(_) => Some(format!(
            "synta_encode_printable_string_bytes({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::IA5String(_) => Some(format!(
            "synta_encode_ia5_string_bytes({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::UtcTime => Some(format!(
            "synta_encode_utctime_bytes({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::GeneralizedTime => Some(format!(
            "synta_encode_generalized_time_bytes({}, synta_octet_string_data({}), synta_octet_string_len({}))",
            encoder, var, var
        )),
        Type::TypeRef(name) => Some(format!(
            "{}_encode({}, &{})",
            to_snake_case(name),
            encoder,
            var
        )),
        Type::Tagged { tag, inner } => match tag.tagging {
            Tagging::Explicit => None,
            Tagging::Implicit => make_encode_call(inner, encoder, var),
        },
        Type::Constrained { base_type: inner, .. } => make_encode_call(inner, encoder, var),
        _ => None,
    }
}

/// Generate C code to decode one field of a SEQUENCE/SET into `var_name`.
///
/// **Caller contract** — the generated code assumes the following variables are
/// already declared and in scope at the call site:
/// - `SyntaErrorCode err` — reused for every decode call
/// - `SyntaDecoder* seq_decoder` — the decoder for the enclosing SEQUENCE/SET;
///   freed and returned on error
///
/// On decode error, the generated code frees `seq_decoder` and returns `err`.
/// Fields that were successfully decoded before the failure are **not** freed;
/// callers that want clean-up on partial decode must call the corresponding
/// `_free` function even when this returns an error.
fn generate_field_decode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    indent: usize,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    let ind = "    ".repeat(indent);

    // For IMPLICIT-tagged fields, check whether the concrete inner type is structural
    // (SEQUENCE, SET, SEQUENCE OF, SET OF via TypeRef).  If so, generate inline
    // decode with context-specific constructed TLV entry and return early, before
    // make_decode_call gets a chance to emit a call to the TypeRef's own decoder
    // (which would use the wrong tag).  For primitive inner types, fall through to
    // the make_decode_call path below with a transparency comment.
    if let Type::Tagged {
        tag: tag_info,
        inner,
    } = ty
    {
        if matches!(tag_info.tagging, Tagging::Implicit) {
            let concrete = resolve_to_base(inner, defs);
            match concrete {
                Type::Sequence(_) | Type::Set(_) | Type::SequenceOf(_, _) | Type::SetOf(_, _) => {
                    // Delegate to the structural handler in the else-branch below.
                    // We fall through to `make_decode_call` which returns None for
                    // these structural types, so the else-branch handles them.
                    // But make_decode_call on a Tagged{Implicit, TypeRef} would
                    // return Some (the TypeRef's decode call), so we must bypass it.
                    // Recurse with the concrete type and var_name substituted so
                    // that generate_field_decode re-enters as the Tagged variant
                    // and falls into the else -> Tagging::Implicit -> structural arm.
                    //
                    // Actually: pass through the Tagged ty itself but call the new
                    // inline code path directly via the else-branch by temporarily
                    // preventing make_decode_call from short-circuiting. The cleanest
                    // approach is to inline the structural handling here.
                    let class = tag_class_c_str(&tag_info.class);
                    match concrete {
                        Type::Sequence(seq_fields) | Type::Set(seq_fields) => {
                            let is_set = matches!(concrete, Type::Set(_));
                            let ct_label = if is_set { "SET" } else { "SEQUENCE" };
                            writeln!(
                                output,
                                "{}// IMPLICIT [{}]: enter as CONSTRUCTED, decode {} fields inline",
                                ind, tag_info.number, ct_label
                            )?;
                            writeln!(output, "{}SyntaDecoder* nested_decoder = NULL;", ind)?;
                            writeln!(output, "{}{{", ind)?;
                            writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                            writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                            writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                            writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                            writeln!(
                                output,
                                "{}    err = synta_decoder_enter_constructed(seq_decoder, impl_tag, &nested_decoder);",
                                ind
                            )?;
                            writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                            writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}        return err;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            for seq_field in seq_fields {
                                if matches!(seq_field.ty, Type::Null) {
                                    continue;
                                }
                                let inner_name = to_snake_case(&seq_field.name);
                                let nested_var = format!("{}.{}", var_name, inner_name);
                                if seq_field.optional {
                                    let tag_check = get_tag_check_condition(&seq_field.ty, defs);
                                    writeln!(
                                        output,
                                        "{}// Decode optional nested field: {}",
                                        ind, seq_field.name
                                    )?;
                                    writeln!(output, "{}{{", ind)?;
                                    writeln!(output, "{}    SyntaTag tag;", ind)?;
                                    writeln!(
                                        output,
                                        "{}    if (synta_decoder_peek_tag(nested_decoder, &tag) == SyntaErrorCode_Success &&",
                                        ind
                                    )?;
                                    writeln!(output, "{}        ({})) {{", ind, tag_check)?;
                                    let deeper_ind = format!("{}        ", ind);
                                    generate_nested_inline_field_decode(
                                        output,
                                        &seq_field.ty,
                                        &nested_var,
                                        &deeper_ind,
                                    )?;
                                    writeln!(
                                        output,
                                        "{}        {}.has_{} = true;",
                                        ind, var_name, inner_name
                                    )?;
                                    writeln!(output, "{}    }} else {{", ind)?;
                                    writeln!(
                                        output,
                                        "{}        {}.has_{} = false;",
                                        ind, var_name, inner_name
                                    )?;
                                    writeln!(output, "{}    }}", ind)?;
                                    writeln!(output, "{}}}", ind)?;
                                } else {
                                    writeln!(output, "{}// Decode field: {}", ind, seq_field.name)?;
                                    generate_nested_inline_field_decode(
                                        output,
                                        &seq_field.ty,
                                        &nested_var,
                                        &ind,
                                    )?;
                                }
                                writeln!(output)?;
                            }
                            writeln!(output, "{}synta_decoder_free(nested_decoder);", ind)?;
                            return Ok(());
                        }
                        Type::SequenceOf(elem_ty, _) | Type::SetOf(elem_ty, _) => {
                            let is_seq = matches!(concrete, Type::SequenceOf(_, _));
                            let ct_label = if is_seq { "SEQUENCE OF" } else { "SET OF" };
                            writeln!(
                                output,
                                "{}// IMPLICIT [{}]: enter as CONSTRUCTED, decode {} elements inline",
                                ind, tag_info.number, ct_label
                            )?;
                            writeln!(output, "{}SyntaDecoder* array_decoder = NULL;", ind)?;
                            writeln!(output, "{}{{", ind)?;
                            writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                            writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                            writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                            writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                            writeln!(
                                output,
                                "{}    err = synta_decoder_enter_constructed(seq_decoder, impl_tag, &array_decoder);",
                                ind
                            )?;
                            writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                            writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}        return err;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            let elem_c_type = get_c_type(elem_ty);
                            let array_type = format!("{}*", elem_c_type);
                            writeln!(output, "{}size_t capacity = 4;", ind)?;
                            writeln!(output, "{}size_t count = 0;", ind)?;
                            writeln!(
                                output,
                                "{}{} array = ({})calloc(capacity, sizeof({}));",
                                ind, array_type, array_type, elem_c_type
                            )?;
                            writeln!(output, "{}if (array == NULL) {{", ind)?;
                            writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
                            writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}    return SyntaErrorCode_OutOfMemory;", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            writeln!(
                                output,
                                "{}while (!synta_decoder_at_end(array_decoder)) {{",
                                ind
                            )?;
                            writeln!(output, "{}    if (count >= capacity) {{", ind)?;
                            writeln!(output, "{}        capacity *= 2;", ind)?;
                            writeln!(
                                output,
                                "{}        {} new_array = ({})realloc(array, capacity * sizeof({}));",
                                ind, array_type, array_type, elem_c_type
                            )?;
                            writeln!(output, "{}        if (new_array == NULL) {{", ind)?;
                            writeln!(output, "{}            free(array);", ind)?;
                            writeln!(
                                output,
                                "{}            synta_decoder_free(array_decoder);",
                                ind
                            )?;
                            writeln!(
                                output,
                                "{}            synta_decoder_free(seq_decoder);",
                                ind
                            )?;
                            writeln!(
                                output,
                                "{}            return SyntaErrorCode_OutOfMemory;",
                                ind
                            )?;
                            writeln!(output, "{}        }}", ind)?;
                            writeln!(output, "{}        array = new_array;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output)?;
                            generate_decode_element(
                                output,
                                elem_ty,
                                "array_decoder",
                                "array[count]",
                                "    ",
                            )?;
                            writeln!(output, "{}    count++;", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            writeln!(output, "{}{}.items = array;", ind, var_name)?;
                            writeln!(output, "{}{}.count = count;", ind, var_name)?;
                            writeln!(output, "{}synta_decoder_free(array_decoder);", ind)?;
                            return Ok(());
                        }
                        _ => unreachable!(),
                    }
                }
                _ => {
                    // Primitive inner type: fall through to make_decode_call with a
                    // transparency comment.
                    let cls = match tag_info.class {
                        TagClass::ContextSpecific => tag_info.number.to_string(),
                        TagClass::Application => format!("APPLICATION {}", tag_info.number),
                        TagClass::Universal => format!("UNIVERSAL {}", tag_info.number),
                        TagClass::Private => format!("PRIVATE {}", tag_info.number),
                    };
                    writeln!(
                        output,
                        "{}/* IMPLICIT [{}]: primitive inner type decoded directly (tag check relaxed) */",
                        ind, cls
                    )?;
                }
            }
        }
    }

    if let Some(call) = make_decode_call(ty, "seq_decoder", var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
        writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
        writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
        writeln!(output, "{}    return err;", ind)?;
        writeln!(output, "{}}}", ind)?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(
                    output,
                    "{}// Decode nested {}",
                    ind,
                    container_type.to_uppercase()
                )?;
                writeln!(output, "{}SyntaDecoder* nested_decoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_decoder_enter_{}(seq_decoder, &nested_decoder);",
                    ind, container_type
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                // Decode each field of the nested sequence
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }

                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    if inner_field.optional {
                        writeln!(
                            output,
                            "{}// Decode optional nested field: {}",
                            ind, inner_field.name
                        )?;
                        let tag_check = get_tag_check_condition(&inner_field.ty, defs);
                        writeln!(output, "{}{{", ind)?;
                        writeln!(output, "{}    SyntaTag tag;", ind)?;
                        writeln!(
                        output,
                        "{}    if (synta_decoder_peek_tag(nested_decoder, &tag) == SyntaErrorCode_Success &&",
                        ind
                    )?;
                        writeln!(output, "{}        ({})) {{", ind, tag_check)?;
                        let deeper_ind = format!("{}        ", ind);
                        generate_nested_inline_field_decode(
                            output,
                            &inner_field.ty,
                            &nested_var,
                            &deeper_ind,
                        )?;
                        writeln!(
                            output,
                            "{}        {}.has_{} = true;",
                            ind, var_name, inner_name
                        )?;
                        writeln!(output, "{}    }} else {{", ind)?;
                        writeln!(
                            output,
                            "{}        {}.has_{} = false;",
                            ind, var_name, inner_name
                        )?;
                        writeln!(output, "{}    }}", ind)?;
                        writeln!(output, "{}}}", ind)?;
                    } else {
                        writeln!(output, "{}// Decode field: {}", ind, inner_field.name)?;
                        generate_nested_inline_field_decode(
                            output,
                            &inner_field.ty,
                            &nested_var,
                            &ind,
                        )?;
                    }
                    writeln!(output)?;
                }

                writeln!(output, "{}synta_decoder_free(nested_decoder);", ind)?;
            }
            Type::SequenceOf(inner_ty, _) | Type::SetOf(inner_ty, _) => {
                let is_sequence = matches!(ty, Type::SequenceOf(_, _));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(output, "{}// Decode SEQUENCE OF / SET OF", ind)?;
                writeln!(output, "{}SyntaDecoder* array_decoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_decoder_enter_{}(seq_decoder, &array_decoder);",
                    ind, container_type
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(output, "{}// Allocate dynamic array for elements", ind)?;
                writeln!(output, "{}size_t capacity = 4; // Initial capacity", ind)?;
                writeln!(output, "{}size_t count = 0;", ind)?;
                let elem_c_type = get_c_type(inner_ty);
                let array_type = format!("{}*", elem_c_type); // Array of element pointers
                writeln!(
                    output,
                    "{}{} array = ({})calloc(capacity, sizeof({}));",
                    ind, array_type, array_type, elem_c_type
                )?;
                writeln!(output, "{}if (array == NULL) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return SyntaErrorCode_OutOfMemory;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(
                    output,
                    "{}while (!synta_decoder_at_end(array_decoder)) {{",
                    ind
                )?;
                writeln!(output, "{}    // Grow array if needed", ind)?;
                writeln!(output, "{}    if (count >= capacity) {{", ind)?;
                writeln!(output, "{}        capacity *= 2;", ind)?;
                writeln!(
                    output,
                    "{}        {} new_array = ({})realloc(array, capacity * sizeof({}));",
                    ind, array_type, array_type, elem_c_type
                )?;
                writeln!(output, "{}        if (new_array == NULL) {{", ind)?;
                writeln!(output, "{}            free(array);", ind)?;
                writeln!(
                    output,
                    "{}            synta_decoder_free(array_decoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}            synta_decoder_free(seq_decoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}            return SyntaErrorCode_OutOfMemory;",
                    ind
                )?;
                writeln!(output, "{}        }}", ind)?;
                writeln!(output, "{}        array = new_array;", ind)?;
                writeln!(output, "{}    }}", ind)?;
                writeln!(output)?;

                // Generate decode for element
                writeln!(output, "{}    // Decode element", ind)?;
                generate_decode_element(output, inner_ty, "array_decoder", "array[count]", "    ")?;
                writeln!(output, "{}    count++;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(output, "{}{} = array;", ind, var_name)?;
                writeln!(output, "{}{}_count = count;", ind, var_name)?;
                writeln!(output, "{}synta_decoder_free(array_decoder);", ind)?;
            }
            // make_decode_call returned None for a Tagged type: must be EXPLICIT
            // (IMPLICIT would have returned Some via recursion into the inner type).
            Type::Tagged {
                tag: tag_info,
                inner,
            } => match tag_info.tagging {
                Tagging::Explicit => {
                    let class = tag_class_c_str(&tag_info.class);
                    writeln!(
                        output,
                        "{}// Enter EXPLICIT [{cls} {num}] tag wrapper",
                        ind,
                        cls = class,
                        num = tag_info.number
                    )?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    SyntaDecoder* tagged_decoder = NULL;", ind)?;
                    writeln!(output, "{}    SyntaTag explicit_tag;", ind)?;
                    writeln!(output, "{}    explicit_tag.class_ = {};", ind, class)?;
                    writeln!(output, "{}    explicit_tag.constructed = true;", ind)?;
                    writeln!(
                        output,
                        "{}    explicit_tag.number = {};",
                        ind, tag_info.number
                    )?;
                    writeln!(
                        output,
                        "{}    err = synta_decoder_enter_constructed(seq_decoder, explicit_tag, &tagged_decoder);",
                        ind
                    )?;
                    writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                    writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                    writeln!(output, "{}        return err;", ind)?;
                    writeln!(output, "{}    }}", ind)?;
                    if let Some(call) = make_decode_call(inner, "tagged_decoder", var_name) {
                        writeln!(output, "{}    err = {};", ind, call)?;
                        writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                        writeln!(output, "{}        synta_decoder_free(tagged_decoder);", ind)?;
                        writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                        writeln!(output, "{}        return err;", ind)?;
                        writeln!(output, "{}    }}", ind)?;
                    } else {
                        // Inline structural type (e.g. anonymous SEQUENCE) inside an
                        // EXPLICIT tag is not yet supported; emit an error placeholder.
                        writeln!(output, "{}    /* structural inner type inside EXPLICIT tag: not yet supported */", ind)?;
                        writeln!(output, "{}    err = SyntaErrorCode_InvalidEncoding;", ind)?;
                        writeln!(output, "{}    synta_decoder_free(tagged_decoder);", ind)?;
                        writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                        writeln!(output, "{}    return err;", ind)?;
                    }
                    writeln!(output, "{}    synta_decoder_free(tagged_decoder);", ind)?;
                    writeln!(output, "{}}}", ind)?;
                }
                Tagging::Implicit => {
                    // IMPLICIT: context-specific tag replaces the inner type's own tag.
                    // For structural inner types (SEQUENCE, SET, SEQUENCE OF, SET OF or
                    // TypeRefs that resolve to them), enter the context-specific constructed
                    // TLV and decode the contents inline.  For primitive inner types the
                    // inner-type decoder reads value bytes without rechecking the outer tag,
                    // so we can call it directly.
                    let concrete = resolve_to_base(inner, defs);
                    match concrete {
                        Type::Sequence(seq_fields) | Type::Set(seq_fields) => {
                            let class = tag_class_c_str(&tag_info.class);
                            let is_set = matches!(concrete, Type::Set(_));
                            let ct_label = if is_set { "SET" } else { "SEQUENCE" };
                            writeln!(
                                output,
                                "{}// IMPLICIT [{}]: enter as CONSTRUCTED, decode {} fields inline",
                                ind, tag_info.number, ct_label
                            )?;
                            writeln!(output, "{}SyntaDecoder* nested_decoder = NULL;", ind)?;
                            writeln!(output, "{}{{", ind)?;
                            writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                            writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                            writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                            writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                            writeln!(
                                output,
                                "{}    err = synta_decoder_enter_constructed(seq_decoder, impl_tag, &nested_decoder);",
                                ind
                            )?;
                            writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                            writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}        return err;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            for seq_field in seq_fields {
                                if matches!(seq_field.ty, Type::Null) {
                                    continue;
                                }
                                let inner_name = to_snake_case(&seq_field.name);
                                let nested_var = format!("{}.{}", var_name, inner_name);
                                if seq_field.optional {
                                    let tag_check = get_tag_check_condition(&seq_field.ty, defs);
                                    writeln!(
                                        output,
                                        "{}// Decode optional nested field: {}",
                                        ind, seq_field.name
                                    )?;
                                    writeln!(output, "{}{{", ind)?;
                                    writeln!(output, "{}    SyntaTag tag;", ind)?;
                                    writeln!(
                                        output,
                                        "{}    if (synta_decoder_peek_tag(nested_decoder, &tag) == SyntaErrorCode_Success &&",
                                        ind
                                    )?;
                                    writeln!(output, "{}        ({})) {{", ind, tag_check)?;
                                    let deeper_ind = format!("{}        ", ind);
                                    generate_nested_inline_field_decode(
                                        output,
                                        &seq_field.ty,
                                        &nested_var,
                                        &deeper_ind,
                                    )?;
                                    writeln!(
                                        output,
                                        "{}        {}.has_{} = true;",
                                        ind, var_name, inner_name
                                    )?;
                                    writeln!(output, "{}    }} else {{", ind)?;
                                    writeln!(
                                        output,
                                        "{}        {}.has_{} = false;",
                                        ind, var_name, inner_name
                                    )?;
                                    writeln!(output, "{}    }}", ind)?;
                                    writeln!(output, "{}}}", ind)?;
                                } else {
                                    writeln!(output, "{}// Decode field: {}", ind, seq_field.name)?;
                                    generate_nested_inline_field_decode(
                                        output,
                                        &seq_field.ty,
                                        &nested_var,
                                        &ind,
                                    )?;
                                }
                                writeln!(output)?;
                            }
                            writeln!(output, "{}synta_decoder_free(nested_decoder);", ind)?;
                        }
                        Type::SequenceOf(elem_ty, _) | Type::SetOf(elem_ty, _) => {
                            let class = tag_class_c_str(&tag_info.class);
                            let is_seq = matches!(concrete, Type::SequenceOf(_, _));
                            let ct_label = if is_seq { "SEQUENCE OF" } else { "SET OF" };
                            writeln!(
                                output,
                                "{}// IMPLICIT [{}]: enter as CONSTRUCTED, decode {} elements inline",
                                ind, tag_info.number, ct_label
                            )?;
                            writeln!(output, "{}SyntaDecoder* array_decoder = NULL;", ind)?;
                            writeln!(output, "{}{{", ind)?;
                            writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                            writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                            writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                            writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                            writeln!(
                                output,
                                "{}    err = synta_decoder_enter_constructed(seq_decoder, impl_tag, &array_decoder);",
                                ind
                            )?;
                            writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                            writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}        return err;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            let elem_c_type = get_c_type(elem_ty);
                            let array_type = format!("{}*", elem_c_type);
                            writeln!(output, "{}size_t capacity = 4;", ind)?;
                            writeln!(output, "{}size_t count = 0;", ind)?;
                            writeln!(
                                output,
                                "{}{} array = ({})calloc(capacity, sizeof({}));",
                                ind, array_type, array_type, elem_c_type
                            )?;
                            writeln!(output, "{}if (array == NULL) {{", ind)?;
                            writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
                            writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                            writeln!(output, "{}    return SyntaErrorCode_OutOfMemory;", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            writeln!(
                                output,
                                "{}while (!synta_decoder_at_end(array_decoder)) {{",
                                ind
                            )?;
                            writeln!(output, "{}    if (count >= capacity) {{", ind)?;
                            writeln!(output, "{}        capacity *= 2;", ind)?;
                            writeln!(
                                output,
                                "{}        {} new_array = ({})realloc(array, capacity * sizeof({}));",
                                ind, array_type, array_type, elem_c_type
                            )?;
                            writeln!(output, "{}        if (new_array == NULL) {{", ind)?;
                            writeln!(output, "{}            free(array);", ind)?;
                            writeln!(
                                output,
                                "{}            synta_decoder_free(array_decoder);",
                                ind
                            )?;
                            writeln!(
                                output,
                                "{}            synta_decoder_free(seq_decoder);",
                                ind
                            )?;
                            writeln!(
                                output,
                                "{}            return SyntaErrorCode_OutOfMemory;",
                                ind
                            )?;
                            writeln!(output, "{}        }}", ind)?;
                            writeln!(output, "{}        array = new_array;", ind)?;
                            writeln!(output, "{}    }}", ind)?;
                            writeln!(output)?;
                            generate_decode_element(
                                output,
                                elem_ty,
                                "array_decoder",
                                "array[count]",
                                "    ",
                            )?;
                            writeln!(output, "{}    count++;", ind)?;
                            writeln!(output, "{}}}", ind)?;
                            writeln!(output)?;
                            writeln!(output, "{}{}.items = array;", ind, var_name)?;
                            writeln!(output, "{}{}.count = count;", ind, var_name)?;
                            writeln!(output, "{}synta_decoder_free(array_decoder);", ind)?;
                        }
                        _ => {
                            // Primitive or scalar inner type: decode without re-entering a tag wrapper.
                            generate_field_decode(output, inner, var_name, indent, defs)?;
                        }
                    }
                }
            },
            Type::Constrained {
                base_type: inner, ..
            } => {
                generate_field_decode(output, inner, var_name, indent, defs)?;
            }
            _ => {
                writeln!(
                    output,
                    "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported field type */",
                    ind
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
            }
        }
    } // closes else

    Ok(())
}

/// Generate C code to encode one field of a SEQUENCE/SET from `var_name`.
///
/// **Caller contract** — the generated code assumes the following variables are
/// already declared and in scope at the call site:
/// - `SyntaErrorCode err` — reused for every encode call
/// - A `SyntaEncoder*` whose name is passed as `encoder_name`
///
/// On encode error, the generated code returns `err` immediately.
fn generate_field_encode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    encoder_name: &str,
    indent: usize,
    ctx: &EncodeCtx<'_>,
) -> Result<(), Box<dyn std::error::Error>> {
    let ind = "    ".repeat(indent);

    // Constrained type: emit validation before the actual encode, then encode inner.
    if let Type::Constrained {
        base_type: inner,
        constraint,
    } = ty
    {
        emit_constraint_validation(
            output,
            constraint,
            inner,
            var_name,
            &ind,
            ctx.mode,
            ctx.with_containing,
        )?;
        return generate_field_encode(output, inner, var_name, encoder_name, indent, ctx);
    }

    // For IMPLICIT-tagged structural types (SEQUENCE, SET, SEQUENCE OF, SET OF or
    // TypeRefs resolving to them), generate context-specific constructed TLV encode
    // inline instead of calling the TypeRef's encode function (which would emit the
    // wrong outer tag).
    if let Type::Tagged {
        tag: tag_info,
        inner,
    } = ty
    {
        if matches!(tag_info.tagging, Tagging::Implicit) {
            let concrete = resolve_to_base(inner, ctx.defs);
            match concrete {
                Type::Sequence(seq_fields) | Type::Set(seq_fields) => {
                    let class = tag_class_c_str(&tag_info.class);
                    let is_set = matches!(concrete, Type::Set(_));
                    let ct_label = if is_set { "SET" } else { "SEQUENCE" };
                    writeln!(
                        output,
                        "{}// IMPLICIT [{}]: start CONSTRUCTED, encode {} fields inline",
                        ind, tag_info.number, ct_label
                    )?;
                    writeln!(output, "{}SyntaEncoder* nested_encoder = NULL;", ind)?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                    writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                    writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                    writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                    writeln!(
                        output,
                        "{}    err = synta_encoder_start_constructed({}, impl_tag, &nested_encoder);",
                        ind, encoder_name
                    )?;
                    writeln!(
                        output,
                        "{}    if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    writeln!(output, "{}}}", ind)?;
                    for seq_field in seq_fields {
                        if matches!(seq_field.ty, Type::Null) {
                            continue;
                        }
                        let inner_name = to_snake_case(&seq_field.name);
                        let nested_var = format!("{}.{}", var_name, inner_name);
                        let field_ind = if seq_field.optional {
                            writeln!(output, "{}if ({}.has_{}) {{", ind, var_name, inner_name)?;
                            format!("{}    ", ind)
                        } else {
                            ind.clone()
                        };
                        generate_nested_inline_field_encode(
                            output,
                            &seq_field.ty,
                            &nested_var,
                            &field_ind,
                        )?;
                        if seq_field.optional {
                            writeln!(output, "{}}}", ind)?;
                        }
                    }
                    writeln!(output)?;
                    writeln!(
                        output,
                        "{}err = synta_encoder_end_constructed(nested_encoder);",
                        ind
                    )?;
                    writeln!(
                        output,
                        "{}if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    return Ok(());
                }
                Type::SequenceOf(elem_ty, _) | Type::SetOf(elem_ty, _) => {
                    let class = tag_class_c_str(&tag_info.class);
                    let is_seq = matches!(concrete, Type::SequenceOf(_, _));
                    let ct_label = if is_seq { "SEQUENCE OF" } else { "SET OF" };
                    writeln!(
                        output,
                        "{}// IMPLICIT [{}]: start CONSTRUCTED, encode {} elements inline",
                        ind, tag_info.number, ct_label
                    )?;
                    writeln!(output, "{}SyntaEncoder* array_encoder = NULL;", ind)?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    SyntaTag impl_tag;", ind)?;
                    writeln!(output, "{}    impl_tag.class_ = {};", ind, class)?;
                    writeln!(output, "{}    impl_tag.constructed = true;", ind)?;
                    writeln!(output, "{}    impl_tag.number = {};", ind, tag_info.number)?;
                    writeln!(
                        output,
                        "{}    err = synta_encoder_start_constructed({}, impl_tag, &array_encoder);",
                        ind, encoder_name
                    )?;
                    writeln!(
                        output,
                        "{}    if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    writeln!(output, "{}}}", ind)?;
                    writeln!(output)?;
                    writeln!(
                        output,
                        "{}for (size_t i = 0; i < {}.count; i++) {{",
                        ind, var_name
                    )?;
                    generate_encode_element_field(
                        output,
                        elem_ty,
                        "array_encoder",
                        &format!("{}.items[i]", var_name),
                        "    ",
                    )?;
                    writeln!(output, "{}}}", ind)?;
                    writeln!(output)?;
                    writeln!(
                        output,
                        "{}err = synta_encoder_end_constructed(array_encoder);",
                        ind
                    )?;
                    writeln!(
                        output,
                        "{}if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    return Ok(());
                }
                _ => {
                    // Primitive: emit comment and fall through to make_encode_call below.
                    let cls = match tag_info.class {
                        TagClass::ContextSpecific => tag_info.number.to_string(),
                        TagClass::Application => format!("APPLICATION {}", tag_info.number),
                        TagClass::Universal => format!("UNIVERSAL {}", tag_info.number),
                        TagClass::Private => format!("PRIVATE {}", tag_info.number),
                    };
                    writeln!(
                        output,
                        "{}/* IMPLICIT [{}]: primitive inner type encoded directly */",
                        ind, cls
                    )?;
                }
            }
        }
    }

    if let Some(call) = make_encode_call(ty, encoder_name, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
        writeln!(
            output,
            "{}if (err != SyntaErrorCode_Success) return err;",
            ind
        )?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(
                    output,
                    "{}// Encode nested {}",
                    ind,
                    container_type.to_uppercase()
                )?;
                writeln!(output, "{}SyntaEncoder* nested_encoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_encoder_start_{}({}, &nested_encoder);",
                    ind, container_type, encoder_name
                )?;
                writeln!(
                    output,
                    "{}if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
                writeln!(output)?;

                // Encode each field of the nested sequence
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }

                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    let field_ind = if inner_field.optional {
                        writeln!(output, "{}if ({}.has_{}) {{", ind, var_name, inner_name)?;
                        format!("{}    ", ind)
                    } else {
                        ind.clone()
                    };
                    generate_nested_inline_field_encode(
                        output,
                        &inner_field.ty,
                        &nested_var,
                        &field_ind,
                    )?;
                    if inner_field.optional {
                        writeln!(output, "{}}}", ind)?;
                    }
                }
                writeln!(output)?;

                writeln!(
                    output,
                    "{}err = synta_encoder_end_constructed(nested_encoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
            }
            Type::SequenceOf(inner_ty, _) | Type::SetOf(inner_ty, _) => {
                let is_sequence = matches!(ty, Type::SequenceOf(_, _));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(output, "{}// Encode SEQUENCE OF / SET OF", ind)?;
                writeln!(output, "{}SyntaEncoder* array_encoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_encoder_start_{}({}, &array_encoder);",
                    ind, container_type, encoder_name
                )?;
                writeln!(
                    output,
                    "{}if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
                writeln!(output)?;

                writeln!(output, "{}// Encode each element", ind)?;
                writeln!(
                    output,
                    "{}for (size_t i = 0; i < {}_count; i++) {{",
                    ind, var_name
                )?;
                generate_encode_element_field(
                    output,
                    inner_ty,
                    "array_encoder",
                    &format!("{}[i]", var_name),
                    "    ",
                )?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(
                    output,
                    "{}err = synta_encoder_end_constructed(array_encoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
            }
            // make_encode_call returned None for a Tagged type: must be EXPLICIT
            // (Constrained is handled by the early return above).
            Type::Tagged {
                tag: tag_info,
                inner,
            } => match tag_info.tagging {
                Tagging::Explicit => {
                    let class = tag_class_c_str(&tag_info.class);
                    writeln!(
                        output,
                        "{}// Wrap in EXPLICIT [{cls} {num}] tag",
                        ind,
                        cls = class,
                        num = tag_info.number
                    )?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    SyntaEncoder* tagged_encoder = NULL;", ind)?;
                    writeln!(output, "{}    SyntaTag explicit_tag;", ind)?;
                    writeln!(output, "{}    explicit_tag.class_ = {};", ind, class)?;
                    writeln!(output, "{}    explicit_tag.constructed = true;", ind)?;
                    writeln!(
                        output,
                        "{}    explicit_tag.number = {};",
                        ind, tag_info.number
                    )?;
                    writeln!(
                        output,
                        "{}    err = synta_encoder_start_constructed({}, explicit_tag, &tagged_encoder);",
                        ind, encoder_name
                    )?;
                    writeln!(
                        output,
                        "{}    if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    if let Some(call) = make_encode_call(inner, "tagged_encoder", var_name) {
                        writeln!(output, "{}    err = {};", ind, call)?;
                        writeln!(
                            output,
                            "{}    if (err != SyntaErrorCode_Success) return err;",
                            ind
                        )?;
                    } else {
                        writeln!(output, "{}    /* structural inner type inside EXPLICIT tag: not yet supported */", ind)?;
                        writeln!(output, "{}    return SyntaErrorCode_InvalidEncoding;", ind)?;
                    }
                    writeln!(
                        output,
                        "{}    err = synta_encoder_end_constructed(tagged_encoder);",
                        ind
                    )?;
                    writeln!(
                        output,
                        "{}    if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    writeln!(output, "{}}}", ind)?;
                }
                Tagging::Implicit => {
                    // Structural IMPLICIT types are handled by the early-return block above;
                    // this arm handles the primitive case (make_encode_call returned Some).
                    generate_field_encode(output, inner, var_name, encoder_name, indent, ctx)?;
                }
            },
            _ => {
                writeln!(
                    output,
                    "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported field type */",
                    ind
                )?;
                writeln!(
                    output,
                    "{}if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
            }
        }
    } // closes else

    Ok(())
}

/// Emit a decode-side SIZE constraint check for a SEQUENCE OF / SET OF count.
///
/// Generates C code that verifies `count_var` (a `size_t`) against the
/// `bounds` constraint *after* all elements have been decoded.  On failure,
/// `array` and `array_decoder` are freed and `SyntaErrorCode_InvalidEncoding`
/// is returned.
fn emit_array_size_check(
    output: &mut String,
    bounds: ArraySizeBounds,
    count_var: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let (min, max) = bounds;
    let mut conditions: Vec<String> = Vec::new();
    if let Some(n) = min {
        if n > 0 {
            conditions.push(format!("{} < (size_t){}ULL", count_var, n));
        }
        // min == 0: always satisfied for size_t
    }
    if let Some(n) = max {
        conditions.push(format!("{} > (size_t){}ULL", count_var, n));
    }
    if !conditions.is_empty() {
        writeln!(output, "    // Validate SIZE constraint on collection")?;
        writeln!(output, "    if ({}) {{", conditions.join(" || "))?;
        writeln!(output, "        free(array);")?;
        writeln!(output, "        synta_decoder_free(array_decoder);")?;
        writeln!(output, "        return SyntaErrorCode_InvalidEncoding;")?;
        writeln!(output, "    }}")?;
    }
    Ok(())
}

/// Emit an encode-side SIZE constraint check for a SEQUENCE OF / SET OF count.
///
/// Generates C code that verifies `count_var` (a `size_t` expression) against
/// the `bounds` constraint *before* encoding any elements.  On failure,
/// `SyntaErrorCode_InvalidArgument` is returned immediately.
fn emit_array_size_check_encode(
    output: &mut String,
    bounds: ArraySizeBounds,
    count_var: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let (min, max) = bounds;
    let mut conditions: Vec<String> = Vec::new();
    if let Some(n) = min {
        if n > 0 {
            conditions.push(format!("{} < (size_t){}ULL", count_var, n));
        }
    }
    if let Some(n) = max {
        conditions.push(format!("{} > (size_t){}ULL", count_var, n));
    }
    if !conditions.is_empty() {
        writeln!(output, "    // Validate SIZE constraint before encoding")?;
        writeln!(output, "    if ({}) {{", conditions.join(" || "))?;
        writeln!(output, "        return SyntaErrorCode_InvalidArgument;")?;
        writeln!(output, "    }}")?;
    }
    Ok(())
}

/// Emit a C permitted-alphabet (FROM) validation loop for a string field.
///
/// Iterates over the raw bytes of `var_name` (a `SyntaOctetString*`) and
/// returns `SyntaErrorCode_InvalidArgument` if any byte falls outside the
/// permitted character ranges.
///
/// For ASCII-range alphabets this is a simple byte comparison.  Multi-byte
/// UTF-8 code points are not supported: the generated loop compares raw
/// bytes, so callers must ensure the schema only contains ASCII ranges when
/// using this in C bindings.
fn emit_permitted_alphabet_validation(
    output: &mut String,
    ranges: &[CharRange],
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let alpha_expr = generate_c_alphabet_expr(ranges);
    writeln!(
        output,
        "{}// Validate FROM (permitted alphabet) constraint",
        ind
    )?;
    writeln!(output, "{}{{", ind)?;
    writeln!(
        output,
        "{}    size_t _alen = synta_octet_string_len({});",
        ind, var_name
    )?;
    writeln!(
        output,
        "{}    const unsigned char* _ap = (const unsigned char*)synta_octet_string_data({});",
        ind, var_name
    )?;
    writeln!(output, "{}    size_t _ai;", ind)?;
    writeln!(output, "{}    for (_ai = 0; _ai < _alen; _ai++) {{", ind)?;
    writeln!(output, "{}        unsigned char _c = _ap[_ai];", ind)?;
    writeln!(
        output,
        "{}        if (!({alpha})) return SyntaErrorCode_InvalidArgument;",
        ind,
        alpha = alpha_expr
    )?;
    writeln!(output, "{}    }}", ind)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Emit C validation code for an ASN.1 constraint before an encode call.
///
/// Only emits code for constraint types that can be statically validated:
/// - INTEGER `ValueRange` and `SingleValue` constraints
/// - `SizeConstraint` (length bounds) on OCTET STRING and string types
/// - `PermittedAlphabet` (FROM) on string types
/// - `Intersection` of the above (e.g. `SIZE (1..64) FROM ('A'..'Z')`)
///
/// Unknown or unsupported constraints are silently skipped so the generated
/// code compiles without errors even when no validation is emitted.
fn emit_constraint_validation(
    output: &mut String,
    constraint: &Constraint,
    base_type: &Type,
    var_name: &str,
    ind: &str,
    mode: &PatternMode,
    with_containing: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    if let ConstraintSpec::Subtype(ref spec) = constraint.spec {
        emit_subtype_constraint_validation(
            output,
            spec,
            base_type,
            var_name,
            ind,
            mode,
            with_containing,
        )?;
    }
    // GeneralConstraint (table constraints, user-defined): no validation generated
    Ok(())
}

/// Emit C validation for a `SubtypeConstraint` element.
fn emit_subtype_constraint_validation(
    output: &mut String,
    spec: &SubtypeConstraint,
    base_type: &Type,
    var_name: &str,
    ind: &str,
    mode: &PatternMode,
    with_containing: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let actual_base = unwrap_type(base_type);
    match spec {
        SubtypeConstraint::ValueRange { min, max } => {
            if matches!(actual_base, Type::Integer(_, _)) {
                writeln!(output, "{}// Validate INTEGER range constraint", ind)?;
                writeln!(output, "{}{{", ind)?;
                writeln!(output, "{}    int64_t _constraint_val;", ind)?;
                writeln!(
                    output,
                    "{}    err = synta_integer_to_i64({}, &_constraint_val);",
                    ind, var_name
                )?;
                writeln!(
                    output,
                    "{}    if (err != SyntaErrorCode_Success) return err;",
                    ind
                )?;
                if let ConstraintValue::Integer(n) = min {
                    writeln!(
                        output,
                        "{}    if (_constraint_val < {}LL) return SyntaErrorCode_InvalidArgument;",
                        ind, n
                    )?;
                }
                if let ConstraintValue::Integer(n) = max {
                    writeln!(
                        output,
                        "{}    if (_constraint_val > {}LL) return SyntaErrorCode_InvalidArgument;",
                        ind, n
                    )?;
                }
                writeln!(output, "{}}}", ind)?;
            }
        }
        SubtypeConstraint::SingleValue(val) => {
            if matches!(actual_base, Type::Integer(_, _)) {
                if let ConstraintValue::Integer(n) = val {
                    writeln!(output, "{}// Validate INTEGER single-value constraint", ind)?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    int64_t _constraint_val;", ind)?;
                    writeln!(
                        output,
                        "{}    err = synta_integer_to_i64({}, &_constraint_val);",
                        ind, var_name
                    )?;
                    writeln!(
                        output,
                        "{}    if (err != SyntaErrorCode_Success) return err;",
                        ind
                    )?;
                    writeln!(
                        output,
                        "{}    if (_constraint_val != {}LL) return SyntaErrorCode_InvalidArgument;",
                        ind, n
                    )?;
                    writeln!(output, "{}}}", ind)?;
                }
            }
        }
        SubtypeConstraint::SizeConstraint(inner_spec) => match actual_base {
            Type::OctetString(_)
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::Any
            | Type::AnyDefinedBy(_) => {
                emit_size_constraint_validation(output, inner_spec, var_name, ind)?;
            }
            _ => {}
        },
        SubtypeConstraint::PermittedAlphabet(ranges) => {
            if matches!(
                actual_base,
                Type::OctetString(_)
                    | Type::Utf8String(_)
                    | Type::PrintableString(_)
                    | Type::IA5String(_)
            ) {
                emit_permitted_alphabet_validation(output, ranges, var_name, ind)?;
            }
        }
        SubtypeConstraint::Intersection(parts) => {
            // Recurse over each part so combined constraints like
            // `SIZE (1..64) FROM ('A'..'Z')` each get their own check.
            for part in parts {
                emit_subtype_constraint_validation(
                    output,
                    part,
                    base_type,
                    var_name,
                    ind,
                    mode,
                    with_containing,
                )?;
            }
        }
        SubtypeConstraint::Union(_) => {
            writeln!(
                output,
                "{}/* UNION constraint: validation not generated */",
                ind
            )?;
        }
        SubtypeConstraint::ContainedSubtype(inner_ty) => {
            let is_byte_string = matches!(
                actual_base,
                Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_)
            );
            if is_byte_string {
                if with_containing {
                    emit_containing_validation(output, inner_ty, var_name, ind)?;
                } else {
                    writeln!(
                        output,
                        "{}/* CONTAINING constraint skipped; use --with-containing to enable validation */",
                        ind
                    )?;
                }
            }
        }
        SubtypeConstraint::Pattern(p) => {
            let is_string = matches!(
                unwrap_type(base_type),
                Type::OctetString(_)
                    | Type::Utf8String(_)
                    | Type::PrintableString(_)
                    | Type::IA5String(_)
            );
            if is_string {
                match mode {
                    PatternMode::Skip => {
                        writeln!(
                            output,
                            "{}/* PATTERN constraint \"{}\" skipped; compile with --with-regex for validation */",
                            ind, p
                        )?;
                    }
                    PatternMode::Posix => {
                        emit_posix_pattern_validation(output, p, var_name, ind)?;
                    }
                    PatternMode::Pcre2 => {
                        emit_pcre2_pattern_validation(output, p, var_name, ind)?;
                    }
                }
            }
        }
        // InnerType, Complement: validation not generated
        _ => {}
    }
    Ok(())
}

/// Emit a POSIX ERE validation block for a PATTERN constraint.
///
/// Uses `regcomp` / `regexec` / `regfree` from `<regex.h>`.  Because
/// `regexec` requires a null-terminated string, a temporary heap allocation
/// is made for the string value.  The regex is compiled on every call;
/// for hot paths a static + `pthread_once` optimisation can be applied
/// manually after code generation.
fn emit_posix_pattern_validation(
    output: &mut String,
    pattern: &str,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // Escape backslashes and double-quotes for embedding in a C string literal.
    let escaped = pattern.replace('\\', "\\\\").replace('"', "\\\"");
    writeln!(
        output,
        "{}// Validate PATTERN constraint \"{}\" (POSIX ERE)",
        ind, pattern
    )?;
    writeln!(output, "{}{{", ind)?;
    writeln!(
        output,
        "{}    size_t _plen = synta_octet_string_len({});",
        ind, var_name
    )?;
    writeln!(output, "{}    char* _pstr = (char*)malloc(_plen + 1);", ind)?;
    writeln!(
        output,
        "{}    if (_pstr == NULL) return SyntaErrorCode_OutOfMemory;",
        ind
    )?;
    writeln!(
        output,
        "{}    memcpy(_pstr, synta_octet_string_data({}), _plen);",
        ind, var_name
    )?;
    writeln!(output, "{}    _pstr[_plen] = '\\0';", ind)?;
    writeln!(output, "{}    regex_t _pre;", ind)?;
    writeln!(
        output,
        "{}    int _prc = regcomp(&_pre, \"{}\", REG_EXTENDED | REG_NOSUB);",
        ind, escaped
    )?;
    writeln!(output, "{}    if (_prc == 0) {{", ind)?;
    writeln!(
        output,
        "{}        _prc = regexec(&_pre, _pstr, 0, NULL, 0);",
        ind
    )?;
    writeln!(output, "{}        regfree(&_pre);", ind)?;
    writeln!(output, "{}    }}", ind)?;
    writeln!(output, "{}    free(_pstr);", ind)?;
    writeln!(
        output,
        "{}    if (_prc != 0) return SyntaErrorCode_InvalidArgument;",
        ind
    )?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Emit a PCRE2 validation block for a PATTERN constraint.
///
/// Uses `pcre2_compile` / `pcre2_match` / `pcre2_code_free` from `<pcre2.h>`
/// (8-bit code-unit width, `PCRE2_CODE_UNIT_WIDTH 8`).  Unlike the POSIX
/// path, no null-termination is required; the raw `SyntaOctetString` data
/// is passed directly with its length.
fn emit_pcre2_pattern_validation(
    output: &mut String,
    pattern: &str,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let escaped = pattern.replace('\\', "\\\\").replace('"', "\\\"");
    writeln!(
        output,
        "{}// Validate PATTERN constraint \"{}\" (PCRE2)",
        ind, pattern
    )?;
    writeln!(output, "{}{{", ind)?;
    writeln!(output, "{}    int _perr;", ind)?;
    writeln!(output, "{}    PCRE2_SIZE _perr_ofs;", ind)?;
    writeln!(
        output,
        "{}    size_t _plen = synta_octet_string_len({});",
        ind, var_name
    )?;
    writeln!(
        output,
        "{}    const PCRE2_UCHAR8* _pdata = (const PCRE2_UCHAR8*)synta_octet_string_data({});",
        ind, var_name
    )?;
    writeln!(
        output,
        "{}    pcre2_code* _pcode = pcre2_compile((PCRE2_SPTR8)\"{}\", PCRE2_ZERO_TERMINATED, 0, &_perr, &_perr_ofs, NULL);",
        ind, escaped
    )?;
    writeln!(output, "{}    if (_pcode != NULL) {{", ind)?;
    writeln!(
        output,
        "{}        pcre2_match_data* _pmatch = pcre2_match_data_create_from_pattern(_pcode, NULL);",
        ind
    )?;
    writeln!(
        output,
        "{}        int _prc = (int)pcre2_match(_pcode, _pdata, _plen, 0, 0, _pmatch, NULL);",
        ind
    )?;
    writeln!(output, "{}        pcre2_match_data_free(_pmatch);", ind)?;
    writeln!(output, "{}        pcre2_code_free(_pcode);", ind)?;
    writeln!(
        output,
        "{}        if (_prc < 0) return SyntaErrorCode_InvalidArgument;",
        ind
    )?;
    writeln!(output, "{}    }}", ind)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Emit a CONTAINING constraint validation block.
///
/// Creates a scratch `SyntaDecoder` over the field's raw bytes and calls the
/// inner type's generated `_decode()` function.  If decoding fails the
/// encode function returns `SyntaErrorCode_InvalidArgument`.
///
/// Only `TypeRef` inner types are supported; for built-in types a comment is
/// emitted instead (they lack a generated `_decode` symbol to call).
fn emit_containing_validation(
    output: &mut String,
    inner_type: &Type,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // Resolve the inner type name.  Only TypeRef is directly supported.
    let (inner_c_type, inner_fn) = match inner_type {
        Type::TypeRef(name) => (to_pascal_case(name), to_snake_case(name)),
        _ => {
            writeln!(
                output,
                "{}/* CONTAINING (built-in type): validation not generated */",
                ind
            )?;
            return Ok(());
        }
    };
    writeln!(
        output,
        "{}// Validate CONTAINING constraint ({})",
        ind, inner_c_type
    )?;
    writeln!(output, "{}{{", ind)?;
    writeln!(
        output,
        "{}    SyntaDecoder* _inner_dec = synta_decoder_new(",
        ind
    )?;
    writeln!(
        output,
        "{}        synta_octet_string_data({}),",
        ind, var_name
    )?;
    writeln!(
        output,
        "{}        (uint32_t)synta_octet_string_len({}),",
        ind, var_name
    )?;
    writeln!(output, "{}        SyntaEncoding_Der);", ind)?;
    writeln!(
        output,
        "{}    if (_inner_dec == NULL) return SyntaErrorCode_OutOfMemory;",
        ind
    )?;
    writeln!(output, "{}    {} _inner_val;", ind, inner_c_type)?;
    writeln!(
        output,
        "{}    SyntaErrorCode _inner_err = {}_decode(_inner_dec, &_inner_val);",
        ind, inner_fn
    )?;
    writeln!(output, "{}    synta_decoder_free(_inner_dec);", ind)?;
    writeln!(
        output,
        "{}    if (_inner_err != SyntaErrorCode_Success) return SyntaErrorCode_InvalidArgument;",
        ind
    )?;
    writeln!(output, "{}    {}_free(&_inner_val);", ind, inner_fn)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Emit C validation for a SIZE constraint on string / OCTET STRING fields.
///
/// The `spec` is the constraint nested inside `SubtypeConstraint::SizeConstraint`
/// and describes the allowed length range (a `ValueRange` or `SingleValue`).
fn emit_size_constraint_validation(
    output: &mut String,
    spec: &SubtypeConstraint,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    match spec {
        SubtypeConstraint::ValueRange { min, max } => {
            writeln!(output, "{}// Validate SIZE range constraint", ind)?;
            writeln!(output, "{}{{", ind)?;
            writeln!(
                output,
                "{}    size_t _len = synta_octet_string_len({});",
                ind, var_name
            )?;
            if let ConstraintValue::Integer(n) = min {
                writeln!(
                    output,
                    "{}    if (_len < (size_t){}UL) return SyntaErrorCode_InvalidArgument;",
                    ind, n
                )?;
            }
            if let ConstraintValue::Integer(n) = max {
                writeln!(
                    output,
                    "{}    if (_len > (size_t){}UL) return SyntaErrorCode_MaxLengthExceeded;",
                    ind, n
                )?;
            }
            writeln!(output, "{}}}", ind)?;
        }
        SubtypeConstraint::SingleValue(val) => {
            if let ConstraintValue::Integer(n) = val {
                writeln!(output, "{}// Validate fixed SIZE constraint", ind)?;
                writeln!(output, "{}{{", ind)?;
                writeln!(
                    output,
                    "{}    size_t _len = synta_octet_string_len({});",
                    ind, var_name
                )?;
                writeln!(
                    output,
                    "{}    if (_len != (size_t){}UL) return SyntaErrorCode_InvalidArgument;",
                    ind, n
                )?;
                writeln!(output, "{}}}", ind)?;
            }
        }
        _ => {
            writeln!(
                output,
                "{}/* complex SIZE constraint: validation not generated */",
                ind
            )?;
        }
    }
    Ok(())
}

/// Map an ASN.1 tag class to the corresponding C `SyntaTagClass_*` constant name.
fn tag_class_c_str(class: &TagClass) -> &'static str {
    match class {
        TagClass::Universal => "SyntaTagClass_Universal",
        TagClass::Application => "SyntaTagClass_Application",
        TagClass::ContextSpecific => "SyntaTagClass_ContextSpecific",
        TagClass::Private => "SyntaTagClass_Private",
    }
}

/// Resolve a `TypeRef` name to its underlying `Type` definition (one level only).
fn resolve_typeref_once<'a>(name: &str, defs: &'a [Definition]) -> Option<&'a Type> {
    defs.iter()
        .find(|d| d.name.eq_ignore_ascii_case(name))
        .map(|d| &d.ty)
}

/// Follow TypeRef aliases to find the underlying concrete type.
/// Stops when the type is not a TypeRef or when it cannot be resolved.
fn resolve_to_base<'a>(ty: &'a Type, defs: &'a [Definition]) -> &'a Type {
    match ty {
        Type::TypeRef(name) => {
            if let Some(resolved) = resolve_typeref_once(name, defs) {
                resolve_to_base(resolved, defs)
            } else {
                ty
            }
        }
        Type::Tagged { inner, .. }
        | Type::Constrained {
            base_type: inner, ..
        } => resolve_to_base(inner, defs),
        other => other,
    }
}

/// Get the tag checking condition for a given type
fn get_tag_check_condition(ty: &Type, defs: &[Definition]) -> String {
    match ty {
        Type::Boolean => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 1 && !tag.constructed"
                .to_string()
        }
        Type::Integer(_, _) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 2 && !tag.constructed"
                .to_string()
        }
        Type::BitString(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 3 && !tag.constructed"
                .to_string()
        }
        Type::OctetString(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 4 && !tag.constructed"
                .to_string()
        }
        Type::Null => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 5 && !tag.constructed"
                .to_string()
        }
        Type::ObjectIdentifier => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 6 && !tag.constructed"
                .to_string()
        }
        Type::RelativeOid => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 13 && !tag.constructed"
                .to_string()
        }
        Type::Real => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 9 && !tag.constructed"
                .to_string()
        }
        Type::Enumerated(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 10 && !tag.constructed"
                .to_string()
        }
        Type::Utf8String(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 12 && !tag.constructed"
                .to_string()
        }
        Type::PrintableString(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 19 && !tag.constructed"
                .to_string()
        }
        Type::IA5String(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 22 && !tag.constructed"
                .to_string()
        }
        Type::Sequence(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 16 && tag.constructed"
                .to_string()
        }
        Type::SequenceOf(_, _) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 16 && tag.constructed"
                .to_string()
        }
        Type::Set(_) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 17 && tag.constructed"
                .to_string()
        }
        Type::SetOf(_, _) => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 17 && tag.constructed"
                .to_string()
        }
        Type::UtcTime => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 23 && !tag.constructed"
                .to_string()
        }
        Type::GeneralizedTime => {
            "tag.class_ == SyntaTagClass_Universal && tag.number == 24 && !tag.constructed"
                .to_string()
        }
        Type::Tagged {
            tag: tag_info,
            inner,
        } => {
            let class = tag_class_c_str(&tag_info.class);
            // EXPLICIT tagging always produces a constructed outer TLV.
            // IMPLICIT tagging inherits the constructed bit of the inner type:
            //   constructed for SEQUENCE, SET, SEQUENCE OF, SET OF, CHOICE;
            //   primitive otherwise.
            let constructed = match tag_info.tagging {
                crate::ast::Tagging::Explicit => "tag.constructed",
                crate::ast::Tagging::Implicit => {
                    let concrete = resolve_to_base(inner, defs);
                    if matches!(
                        concrete,
                        Type::Sequence(_)
                            | Type::Set(_)
                            | Type::SequenceOf(_, _)
                            | Type::SetOf(_, _)
                            | Type::Choice(_)
                    ) {
                        "tag.constructed"
                    } else {
                        "!tag.constructed"
                    }
                }
            };
            format!(
                "tag.class_ == {} && tag.number == {} && {}",
                class, tag_info.number, constructed
            )
        }
        Type::TypeRef(name) => {
            // Resolve the TypeRef to its underlying type and get the tag check.
            // Walk at most two levels to handle chained aliases.
            if let Some(underlying) = resolve_typeref_once(name, defs) {
                if let Type::TypeRef(_) = underlying {
                    get_tag_check_condition(underlying, defs)
                } else {
                    get_tag_check_condition(underlying, defs)
                }
            } else {
                "true /* TypeRef - unresolved, match any tag */".to_string()
            }
        }
        Type::Any | Type::AnyDefinedBy(_) => {
            // ANY has no fixed tag — accept whatever tag is present
            "true /* ANY - match any tag */".to_string()
        }
        _ => {
            // For other types, we can't determine the tag
            "false /* Unknown type tag */".to_string()
        }
    }
}

/// Generate code to decode a choice variant
fn generate_choice_variant_decode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call(ty, "decoder", var_name) {
        writeln!(output, "        err = {};", call)?;
        writeln!(
            output,
            "        if (err != SyntaErrorCode_Success) return err;"
        )?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };
                writeln!(
                    output,
                    "        /* Decode nested {} choice variant */",
                    container_type.to_uppercase()
                )?;
                writeln!(output, "        SyntaDecoder* nested_decoder = NULL;")?;
                writeln!(
                    output,
                    "        err = synta_decoder_enter_{}(decoder, &nested_decoder);",
                    container_type
                )?;
                writeln!(
                    output,
                    "        if (err != SyntaErrorCode_Success) return err;"
                )?;
                writeln!(output)?;
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }
                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    generate_choice_seq_field_decode(
                        output,
                        &inner_field.ty,
                        &nested_var,
                        "        ",
                    )?;
                    writeln!(output)?;
                }
                writeln!(output, "        synta_decoder_free(nested_decoder);")?;
            }
            _ => {
                writeln!(output, "        return SyntaErrorCode_InvalidEncoding;")?;
            }
        }
    } // closes else
    Ok(())
}

/// Generate code to encode a choice variant
fn generate_choice_variant_encode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_encode_call(ty, "encoder", var_name) {
        writeln!(output, "            err = {};", call)?;
        writeln!(
            output,
            "            if (err != SyntaErrorCode_Success) return err;"
        )?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };
                writeln!(
                    output,
                    "            /* Encode nested {} choice variant */",
                    container_type.to_uppercase()
                )?;
                writeln!(output, "            SyntaEncoder* nested_encoder = NULL;")?;
                writeln!(
                    output,
                    "            err = synta_encoder_start_{}(encoder, &nested_encoder);",
                    container_type
                )?;
                writeln!(
                    output,
                    "            if (err != SyntaErrorCode_Success) return err;"
                )?;
                writeln!(output)?;
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }
                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    generate_nested_inline_field_encode(
                        output,
                        &inner_field.ty,
                        &nested_var,
                        "            ",
                    )?;
                }
                writeln!(output)?;
                writeln!(
                    output,
                    "            err = synta_encoder_end_constructed(nested_encoder);"
                )?;
                writeln!(
                    output,
                    "            if (err != SyntaErrorCode_Success) return err;"
                )?;
            }
            _ => {
                writeln!(output, "            return SyntaErrorCode_InvalidEncoding;")?;
            }
        }
    } // closes else
    Ok(())
}

/// Generate code to free a choice variant
fn generate_choice_variant_free(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    match ty {
        Type::Integer(_, _) => {
            writeln!(output, "            synta_integer_free({});", var_name)?;
        }
        Type::Enumerated(_) => {
            // C enum stored by value — no heap allocation, nothing to free
        }
        Type::ObjectIdentifier => {
            writeln!(output, "            synta_oid_free({});", var_name)?;
        }
        Type::RelativeOid => {
            writeln!(output, "            synta_reloid_free({});", var_name)?;
        }
        Type::OctetString(_)
        | Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::UtcTime
        | Type::GeneralizedTime
        | Type::Any
        | Type::AnyDefinedBy(_) => {
            writeln!(output, "            synta_octet_string_free({});", var_name)?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "            synta_byte_array_free(&{}.data);",
                var_name
            )?;
        }
        Type::TypeRef(type_name) => {
            let name = type_name.clone();
            emit_typeref_free(output, &name, var_name, "            ", defs)?;
        }
        Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
            for inner_field in inner_fields {
                if !needs_freeing(&inner_field.ty, defs) {
                    continue;
                }
                let inner_name = to_snake_case(&inner_field.name);
                let nested_var = format!("{}.{}", var_name, inner_name);
                if inner_field.optional {
                    writeln!(
                        output,
                        "            if ({}.has_{}) {{",
                        var_name, inner_name
                    )?;
                    generate_free_stmt(output, &inner_field.ty, &nested_var, "                ")?;
                    writeln!(output, "            }}")?;
                } else {
                    generate_free_stmt(output, &inner_field.ty, &nested_var, "            ")?;
                }
            }
        }
        _ => {
            // No freeing needed for this type
        }
    }
    Ok(())
}

/// Emit the correct free statement for a `TypeRef(type_name)` field.
///
/// Looks up `type_name` in `defs` and emits whichever primitive free call
/// (or `{type_fn}_free`) is appropriate.  For value types that need no heap
/// cleanup (ENUMERATED, named INTEGER, BOOLEAN, …) nothing is emitted.
fn emit_typeref_free(
    output: &mut String,
    type_name: &str,
    field_access: &str,
    ind: &str,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(def) = defs.iter().find(|d| d.name == type_name) {
        match &def.ty {
            // Complex types that have a generated _free function
            Type::Sequence(_)
            | Type::Set(_)
            | Type::Choice(_)
            | Type::SequenceOf(_, _)
            | Type::SetOf(_, _) => {
                let type_fn = to_snake_case(type_name);
                writeln!(output, "{}{}_free(&{});", ind, type_fn, field_access)?;
            }
            // Constrained string/bit newtypes have a generated static-inline _free
            Type::Constrained { base_type, .. }
                if matches!(
                    base_type.as_ref(),
                    Type::IA5String(_)
                        | Type::PrintableString(_)
                        | Type::Utf8String(_)
                        | Type::OctetString(_)
                        | Type::BitString(_)
                ) =>
            {
                let type_fn = to_snake_case(type_name);
                writeln!(output, "{}{}_free(&{});", ind, type_fn, field_access)?;
            }
            // Named integer (typedef int64_t) — no allocation, no free
            Type::Integer(_, named) if !named.is_empty() => {}
            // Regular integer — SyntaInteger*
            Type::Integer(_, _) => {
                writeln!(output, "{}synta_integer_free({});", ind, field_access)?;
            }
            // ENUMERATED — C enum stored by value, no allocation
            Type::Enumerated(_) => {}
            // OID alias
            Type::ObjectIdentifier => {
                writeln!(output, "{}synta_oid_free({});", ind, field_access)?;
            }
            // RELATIVE-OID alias
            Type::RelativeOid => {
                writeln!(output, "{}synta_reloid_free({});", ind, field_access)?;
            }
            // Unconstrained string / time / ANY aliases — SyntaOctetString*
            Type::OctetString(_)
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::UtcTime
            | Type::GeneralizedTime
            | Type::Any
            | Type::AnyDefinedBy(_) => {
                writeln!(output, "{}synta_octet_string_free({});", ind, field_access)?;
            }
            // BitString alias — by-value struct with embedded SyntaByteArray
            Type::BitString(_) => {
                writeln!(
                    output,
                    "{}synta_byte_array_free(&{}.data);",
                    ind, field_access
                )?;
            }
            // Chained TypeRef — recurse
            Type::TypeRef(inner_name) => {
                let inner = inner_name.clone();
                emit_typeref_free(output, &inner, field_access, ind, defs)?;
            }
            // Tagged wrapper — unwrap to find the real type
            Type::Tagged { inner, .. } => {
                let base = unwrap_type(inner);
                generate_free_stmt(output, base, field_access, ind)?;
            }
            // Boolean, Real, Null, other value types — no free needed
            _ => {}
        }
    } else {
        // Unknown definition (e.g. from another module) — assume _free exists
        let type_fn = to_snake_case(type_name);
        writeln!(output, "{}{}_free(&{});", ind, type_fn, field_access)?;
    }
    Ok(())
}

/// Check if a type needs explicit freeing
fn needs_freeing(ty: &Type, defs: &[Definition]) -> bool {
    match ty {
        // Named integer is typedef int64_t — no heap allocation
        Type::Integer(_, named) if !named.is_empty() => false,
        // Regular integer is SyntaInteger* — needs freeing
        Type::Integer(_, _)
        | Type::ObjectIdentifier
        | Type::OctetString(_)
        | Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::UtcTime
        | Type::GeneralizedTime
        | Type::Any
        | Type::AnyDefinedBy(_)
        | Type::BitString(_)
        | Type::Sequence(_)
        | Type::Set(_)
        | Type::Choice(_)
        | Type::SequenceOf(_, _)
        | Type::SetOf(_, _) => true,
        // ENUMERATED is a C enum stored by value — no heap allocation
        Type::Enumerated(_) => false,
        Type::TypeRef(name) => {
            // Resolve to underlying type and check recursively
            if let Some(def) = defs.iter().find(|d| &d.name == name) {
                needs_freeing(&def.ty, defs)
            } else {
                true // unknown type — assume it needs freeing
            }
        }
        Type::Boolean | Type::Real | Type::Null => false,
        _ => false,
    }
}

/// Generate code to decode a single element at top level (for SEQUENCE OF / SET OF types)
fn generate_decode_element_toplevel(
    output: &mut String,
    ty: &Type,
    decoder_name: &str,
    var_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call(ty, decoder_name, var_name) {
        writeln!(output, "        err = {};", call)?;
    } else {
        writeln!(output, "        err = SyntaErrorCode_InvalidEncoding;")?;
    }
    writeln!(output, "        if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "            free(array);")?;
    writeln!(output, "            synta_decoder_free(array_decoder);")?;
    writeln!(output, "            return err;")?;
    writeln!(output, "        }}")?;
    Ok(())
}

/// Generate code to encode a single element at top level
fn generate_encode_element_toplevel(
    output: &mut String,
    ty: &Type,
    encoder_name: &str,
    var_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_encode_call(ty, encoder_name, var_name) {
        writeln!(output, "        err = {};", call)?;
    } else {
        writeln!(output, "        err = SyntaErrorCode_InvalidEncoding;")?;
    }
    writeln!(
        output,
        "        if (err != SyntaErrorCode_Success) return err;"
    )?;
    Ok(())
}

/// Generate code to free a single element (for SEQUENCE OF / SET OF items).
fn generate_free_element(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    match ty {
        Type::Integer(_, _) => {
            writeln!(output, "        synta_integer_free({});", var_name)?;
        }
        Type::ObjectIdentifier => {
            writeln!(
                output,
                "        synta_object_identifier_free({});",
                var_name
            )?;
        }
        Type::RelativeOid => {
            writeln!(output, "        synta_relative_oid_free({});", var_name)?;
        }
        Type::OctetString(_) => {
            writeln!(output, "        synta_octet_string_free({});", var_name)?;
        }
        Type::BitString(_) => {
            writeln!(output, "        synta_byte_array_free(&{}.data);", var_name)?;
        }
        Type::TypeRef(type_name) => {
            let name = type_name.clone();
            emit_typeref_free(output, &name, var_name, "        ", defs)?;
        }
        _ => {}
    }
    Ok(())
}

/// Generate code to encode array element within a field
fn generate_encode_element_field(
    output: &mut String,
    ty: &Type,
    encoder_name: &str,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_encode_call(ty, encoder_name, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(output, "{}err = SyntaErrorCode_InvalidEncoding;", ind)?;
    }
    writeln!(
        output,
        "{}if (err != SyntaErrorCode_Success) return err;",
        ind
    )?;
    Ok(())
}

/// Generate code to decode a single element (for use in arrays)
fn generate_decode_element(
    output: &mut String,
    ty: &Type,
    decoder_name: &str,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call(ty, decoder_name, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(output, "{}return SyntaErrorCode_InvalidEncoding;", ind)?;
        return Ok(());
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    free(array);", ind)?;
    writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
    writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Generate decode code for one field of an inline nested SEQUENCE/SET.
/// Uses `nested_decoder`; frees both `nested_decoder` and `seq_decoder` on error.
fn generate_nested_inline_field_decode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call(ty, "nested_decoder", var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(
            output,
            "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported nested field type */",
            ind
        )?;
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    synta_decoder_free(nested_decoder);", ind)?;
    writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Generate decode code for one field inside a SEQUENCE/SET that is a choice variant.
///
/// Like `generate_nested_inline_field_decode` but only frees `nested_decoder`
/// on error — there is no outer `seq_decoder` in a choice variant context.
fn generate_choice_seq_field_decode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call(ty, "nested_decoder", var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(
            output,
            "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported nested field type */",
            ind
        )?;
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    synta_decoder_free(nested_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    Ok(())
}

/// Generate a free statement for a variable of the given type.
///
/// Does not handle optionality — the caller must emit a `has_` guard if needed.
fn generate_free_stmt(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    match ty {
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(output, "{}synta_integer_free({});", ind, var_name)?;
        }
        Type::ObjectIdentifier => {
            writeln!(output, "{}synta_oid_free({});", ind, var_name)?;
        }
        Type::RelativeOid => {
            writeln!(output, "{}synta_reloid_free({});", ind, var_name)?;
        }
        Type::OctetString(_)
        | Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::UtcTime
        | Type::GeneralizedTime
        | Type::Any
        | Type::AnyDefinedBy(_) => {
            writeln!(output, "{}synta_octet_string_free({});", ind, var_name)?;
        }
        Type::BitString(_) => {
            writeln!(output, "{}synta_byte_array_free(&{}.data);", ind, var_name)?;
        }
        Type::TypeRef(type_name) => {
            let fn_name = to_snake_case(type_name);
            writeln!(output, "{}{}_free(&{});", ind, fn_name, var_name)?;
        }
        Type::Tagged { inner, .. }
        | Type::Constrained {
            base_type: inner, ..
        } => {
            generate_free_stmt(output, inner, var_name, ind)?;
        }
        _ => {} // Boolean, Real, Null, etc. — no heap allocation to free
    }
    Ok(())
}

/// Generate encode code for one field of an inline nested SEQUENCE/SET.
/// Uses `nested_encoder`; returns on error.
fn generate_nested_inline_field_encode(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_encode_call(ty, "nested_encoder", var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(
            output,
            "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported nested field type */",
            ind
        )?;
    }
    writeln!(
        output,
        "{}if (err != SyntaErrorCode_Success) return err;",
        ind
    )?;
    Ok(())
}

// ─── Arena / bump-allocator variants ────────────────────────────────────────

/// Dispatch to the appropriate arena decode generator for a top-level definition.
fn generate_type_arena_impl(
    output: &mut String,
    def: &Definition,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    match &def.ty {
        Type::Sequence(fields) => {
            generate_sequence_arena_impl(output, &def.name, fields, defs, false)?;
        }
        Type::Set(fields) => {
            generate_sequence_arena_impl(output, &def.name, fields, defs, true)?;
        }
        Type::Choice(variants) => {
            generate_choice_arena_impl(output, &def.name, variants, defs)?;
        }
        Type::Integer(_, named_numbers) if !named_numbers.is_empty() => {
            generate_enum_arena_impl(output, &def.name)?;
        }
        Type::Enumerated(_) => {
            generate_enum_arena_impl(output, &def.name)?;
        }
        Type::SequenceOf(inner, opt_constraint) => {
            let size_c = opt_constraint.as_ref().map(legacy_size_to_bounds);
            generate_array_arena_impl(output, &def.name, inner, true, size_c)?;
        }
        Type::SetOf(inner, opt_constraint) => {
            let size_c = opt_constraint.as_ref().map(legacy_size_to_bounds);
            generate_array_arena_impl(output, &def.name, inner, false, size_c)?;
        }
        // Constrained SEQUENCE OF / SET OF: outer constraint holds the SIZE spec.
        Type::Constrained {
            base_type,
            constraint,
        } => {
            let size_c = modern_size_to_bounds(&constraint.spec);
            match base_type.as_ref() {
                Type::SequenceOf(inner, _) => {
                    generate_array_arena_impl(output, &def.name, inner, true, size_c)?;
                }
                Type::SetOf(inner, _) => {
                    generate_array_arena_impl(output, &def.name, inner, false, size_c)?;
                }
                _ => {
                    generate_simple_arena_impl(output, &def.name, &def.ty)?;
                }
            }
        }
        _ => {
            generate_simple_arena_impl(output, &def.name, &def.ty)?;
        }
    }
    Ok(())
}

/// Like `make_decode_call` but uses `{name}_decode_arena` for TypeRef fields
/// so that sub-structure tracking is delegated to the referenced type's arena
/// decoder.  All scalar API calls (integer, octet-string, …) are unchanged.
fn make_decode_call_arena(ty: &Type, decoder: &str, arena: &str, var: &str) -> Option<String> {
    match ty {
        Type::Boolean => Some(format!("synta_decode_boolean({}, &{})", decoder, var)),
        Type::Integer(_, _) | Type::Enumerated(_) => {
            Some(format!("synta_decode_integer({}, &{})", decoder, var))
        }
        Type::Real => Some(format!("synta_decode_real({}, &{})", decoder, var)),
        Type::Null => Some(format!("synta_decode_null({})", decoder)),
        Type::ObjectIdentifier => Some(format!(
            "synta_decode_object_identifier({}, &{})",
            decoder, var
        )),
        Type::RelativeOid => Some(format!("synta_decode_relative_oid({}, &{})", decoder, var)),
        Type::BitString(_) => Some(format!(
            "synta_decode_bit_string({}, &{}.data, &{}.unused_bits)",
            decoder, var, var
        )),
        Type::OctetString(_) | Type::Any | Type::AnyDefinedBy(_) => {
            Some(format!("synta_decode_octet_string({}, &{})", decoder, var))
        }
        Type::Utf8String(_) => Some(format!(
            "synta_decode_utf8_string_os({}, &{})",
            decoder, var
        )),
        Type::PrintableString(_) => Some(format!(
            "synta_decode_printable_string_os({}, &{})",
            decoder, var
        )),
        Type::IA5String(_) => Some(format!("synta_decode_ia5_string_os({}, &{})", decoder, var)),
        Type::UtcTime => Some(format!("synta_decode_utctime_os({}, &{})", decoder, var)),
        Type::GeneralizedTime => Some(format!(
            "synta_decode_generalized_time_os({}, &{})",
            decoder, var
        )),
        // TypeRef → call the arena variant so sub-field tracking is handled there.
        Type::TypeRef(name) => Some(format!(
            "{}_decode_arena({}, {}, &{})",
            to_snake_case(name),
            decoder,
            arena,
            var
        )),
        Type::Tagged { tag, inner } => match tag.tagging {
            Tagging::Explicit => None,
            Tagging::Implicit => make_decode_call_arena(inner, decoder, arena, var),
        },
        Type::Constrained {
            base_type: inner, ..
        } => make_decode_call_arena(inner, decoder, arena, var),
        _ => None,
    }
}

/// Emit an `_synta_arena_track` call for `var_name` of type `ty` into `output`.
///
/// Only emits for types that produce heap-allocated handles (Integer, OctetString,
/// OID, BitString data).  For TypeRef the tracking is done inside the called
/// `_decode_arena` function, so nothing is emitted here.
fn emit_arena_track_field(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    arena: &str,
    ind: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    match unwrap_type(ty) {
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(
                output,
                "{}_synta_arena_track({}, {}, (void(*)(void*))synta_integer_free);",
                ind, arena, var_name
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
            writeln!(
                output,
                "{}_synta_arena_track({}, {}, (void(*)(void*))synta_octet_string_free);",
                ind, arena, var_name
            )?;
        }
        Type::ObjectIdentifier => {
            writeln!(
                output,
                "{}_synta_arena_track({}, {}, (void(*)(void*))synta_oid_free);",
                ind, arena, var_name
            )?;
        }
        Type::RelativeOid => {
            writeln!(
                output,
                "{}_synta_arena_track({}, {}, (void(*)(void*))synta_reloid_free);",
                ind, arena, var_name
            )?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "{}if ({}.data.owned) _synta_arena_track({}, (void*){}.data.data, free);",
                ind, var_name, arena, var_name
            )?;
        }
        // TypeRef, Boolean, Real, Null, Sequence, SequenceOf, Choice, … — no tracking here.
        _ => {}
    }
    Ok(())
}

/// Arena-aware version of `generate_nested_inline_field_decode`.
/// Uses `nested_decoder`; frees both `nested_decoder` and `seq_decoder` on error.
fn generate_nested_inline_field_decode_arena(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
    arena: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call_arena(ty, "nested_decoder", arena, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(
            output,
            "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported nested field type */",
            ind
        )?;
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    synta_decoder_free(nested_decoder);", ind)?;
    writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    emit_arena_track_field(output, ty, var_name, arena, ind)?;
    Ok(())
}

/// Arena-aware version of `generate_choice_seq_field_decode`.
/// Uses `nested_decoder`; only frees `nested_decoder` on error (no outer seq_decoder).
fn generate_choice_seq_field_decode_arena(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    ind: &str,
    arena: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call_arena(ty, "nested_decoder", arena, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(
            output,
            "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported nested field type */",
            ind
        )?;
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    synta_decoder_free(nested_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    emit_arena_track_field(output, ty, var_name, arena, ind)?;
    Ok(())
}

/// Arena-aware element decode for use inside a SEQUENCE OF field within a SEQUENCE body.
/// Frees `array`, `array_decoder`, and `seq_decoder` on error.
fn generate_decode_element_arena(
    output: &mut String,
    ty: &Type,
    decoder_name: &str,
    var_name: &str,
    ind: &str,
    arena: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call_arena(ty, decoder_name, arena, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
    } else {
        writeln!(output, "{}return SyntaErrorCode_InvalidEncoding;", ind)?;
        return Ok(());
    }
    writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
    writeln!(output, "{}    free(array);", ind)?;
    writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
    writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
    writeln!(output, "{}    return err;", ind)?;
    writeln!(output, "{}}}", ind)?;
    emit_arena_track_field(output, ty, var_name, arena, ind)?;
    Ok(())
}

/// Arena-aware element decode for top-level SEQUENCE OF / SET OF types.
/// Frees `array` and `array_decoder` on error (no outer `seq_decoder`).
fn generate_decode_element_toplevel_arena(
    output: &mut String,
    ty: &Type,
    decoder_name: &str,
    var_name: &str,
    arena: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call_arena(ty, decoder_name, arena, var_name) {
        writeln!(output, "        err = {};", call)?;
    } else {
        writeln!(output, "        err = SyntaErrorCode_InvalidEncoding;")?;
    }
    writeln!(output, "        if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "            free(array);")?;
    writeln!(output, "            synta_decoder_free(array_decoder);")?;
    writeln!(output, "            return err;")?;
    writeln!(output, "        }}")?;
    emit_arena_track_field(output, ty, var_name, arena, "        ")?;
    Ok(())
}

/// Arena-aware field decode inside a SEQUENCE/SET body.
///
/// Mirrors `generate_field_decode` but:
/// - Uses `make_decode_call_arena` (TypeRef → `_decode_arena` variant).
/// - Emits `_synta_arena_track` calls after each successful pointer allocation.
/// - For inline SEQUENCE/SET fields, recurses with `generate_nested_inline_field_decode_arena`.
/// - For SEQUENCE OF/SET OF fields, tracks the array pointer with `free`.
fn generate_field_decode_arena(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    indent: usize,
    arena: &str,
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    let ind = "    ".repeat(indent);

    if let Some(call) = make_decode_call_arena(ty, "seq_decoder", arena, var_name) {
        writeln!(output, "{}err = {};", ind, call)?;
        writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
        writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
        writeln!(output, "{}    return err;", ind)?;
        writeln!(output, "{}}}", ind)?;
        emit_arena_track_field(output, ty, var_name, arena, &ind)?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(
                    output,
                    "{}// Decode nested {}",
                    ind,
                    container_type.to_uppercase()
                )?;
                writeln!(output, "{}SyntaDecoder* nested_decoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_decoder_enter_{}(seq_decoder, &nested_decoder);",
                    ind, container_type
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }

                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    if inner_field.optional {
                        writeln!(
                            output,
                            "{}// Decode optional nested field: {}",
                            ind, inner_field.name
                        )?;
                        let tag_check = get_tag_check_condition(&inner_field.ty, defs);
                        writeln!(output, "{}{{", ind)?;
                        writeln!(output, "{}    SyntaTag tag;", ind)?;
                        writeln!(
                            output,
                            "{}    if (synta_decoder_peek_tag(nested_decoder, &tag) == SyntaErrorCode_Success &&",
                            ind
                        )?;
                        writeln!(output, "{}        ({})) {{", ind, tag_check)?;
                        let deeper_ind = format!("{}        ", ind);
                        generate_nested_inline_field_decode_arena(
                            output,
                            &inner_field.ty,
                            &nested_var,
                            &deeper_ind,
                            arena,
                        )?;
                        writeln!(
                            output,
                            "{}        {}.has_{} = true;",
                            ind, var_name, inner_name
                        )?;
                        writeln!(output, "{}    }} else {{", ind)?;
                        writeln!(
                            output,
                            "{}        {}.has_{} = false;",
                            ind, var_name, inner_name
                        )?;
                        writeln!(output, "{}    }}", ind)?;
                        writeln!(output, "{}}}", ind)?;
                    } else {
                        writeln!(output, "{}// Decode field: {}", ind, inner_field.name)?;
                        generate_nested_inline_field_decode_arena(
                            output,
                            &inner_field.ty,
                            &nested_var,
                            &ind,
                            arena,
                        )?;
                    }
                    writeln!(output)?;
                }

                writeln!(output, "{}synta_decoder_free(nested_decoder);", ind)?;
            }
            Type::SequenceOf(inner_ty, _) | Type::SetOf(inner_ty, _) => {
                let is_sequence = matches!(ty, Type::SequenceOf(_, _));
                let container_type = if is_sequence { "sequence" } else { "set" };

                writeln!(output, "{}// Decode SEQUENCE OF / SET OF", ind)?;
                writeln!(output, "{}SyntaDecoder* array_decoder = NULL;", ind)?;
                writeln!(
                    output,
                    "{}err = synta_decoder_enter_{}(seq_decoder, &array_decoder);",
                    ind, container_type
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(output, "{}// Allocate dynamic array for elements", ind)?;
                writeln!(output, "{}size_t capacity = 4; // Initial capacity", ind)?;
                writeln!(output, "{}size_t count = 0;", ind)?;
                let elem_c_type = get_c_type(inner_ty);
                let array_type = format!("{}*", elem_c_type);
                writeln!(
                    output,
                    "{}{} array = ({})calloc(capacity, sizeof({}));",
                    ind, array_type, array_type, elem_c_type
                )?;
                writeln!(output, "{}if (array == NULL) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(array_decoder);", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return SyntaErrorCode_OutOfMemory;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(
                    output,
                    "{}while (!synta_decoder_at_end(array_decoder)) {{",
                    ind
                )?;
                writeln!(output, "{}    // Grow array if needed", ind)?;
                writeln!(output, "{}    if (count >= capacity) {{", ind)?;
                writeln!(output, "{}        capacity *= 2;", ind)?;
                writeln!(
                    output,
                    "{}        {} new_array = ({})realloc(array, capacity * sizeof({}));",
                    ind, array_type, array_type, elem_c_type
                )?;
                writeln!(output, "{}        if (new_array == NULL) {{", ind)?;
                writeln!(output, "{}            free(array);", ind)?;
                writeln!(
                    output,
                    "{}            synta_decoder_free(array_decoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}            synta_decoder_free(seq_decoder);",
                    ind
                )?;
                writeln!(
                    output,
                    "{}            return SyntaErrorCode_OutOfMemory;",
                    ind
                )?;
                writeln!(output, "{}        }}", ind)?;
                writeln!(output, "{}        array = new_array;", ind)?;
                writeln!(output, "{}    }}", ind)?;
                writeln!(output)?;

                writeln!(output, "{}    // Decode element", ind)?;
                generate_decode_element_arena(
                    output,
                    inner_ty,
                    "array_decoder",
                    "array[count]",
                    "    ",
                    arena,
                )?;
                writeln!(output, "{}    count++;", ind)?;
                writeln!(output, "{}}}", ind)?;
                writeln!(output)?;

                writeln!(output, "{}{} = array;", ind, var_name)?;
                writeln!(output, "{}{}_count = count;", ind, var_name)?;
                writeln!(output, "{}synta_decoder_free(array_decoder);", ind)?;
                // Track the array pointer with free
                writeln!(
                    output,
                    "{}_synta_arena_track({}, {}, free);",
                    ind, arena, var_name
                )?;
            }
            Type::Tagged {
                tag: tag_info,
                inner,
            } => match tag_info.tagging {
                Tagging::Explicit => {
                    let class = tag_class_c_str(&tag_info.class);
                    writeln!(
                        output,
                        "{}// Enter EXPLICIT [{cls} {num}] tag wrapper",
                        ind,
                        cls = class,
                        num = tag_info.number
                    )?;
                    writeln!(output, "{}{{", ind)?;
                    writeln!(output, "{}    SyntaDecoder* tagged_decoder = NULL;", ind)?;
                    writeln!(output, "{}    SyntaTag explicit_tag;", ind)?;
                    writeln!(output, "{}    explicit_tag.class_ = {};", ind, class)?;
                    writeln!(output, "{}    explicit_tag.constructed = true;", ind)?;
                    writeln!(
                        output,
                        "{}    explicit_tag.number = {};",
                        ind, tag_info.number
                    )?;
                    writeln!(
                        output,
                        "{}    err = synta_decoder_enter_constructed(seq_decoder, explicit_tag, &tagged_decoder);",
                        ind
                    )?;
                    writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                    writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                    writeln!(output, "{}        return err;", ind)?;
                    writeln!(output, "{}    }}", ind)?;
                    if let Some(call) =
                        make_decode_call_arena(inner, "tagged_decoder", arena, var_name)
                    {
                        writeln!(output, "{}    err = {};", ind, call)?;
                        writeln!(output, "{}    if (err != SyntaErrorCode_Success) {{", ind)?;
                        writeln!(output, "{}        synta_decoder_free(tagged_decoder);", ind)?;
                        writeln!(output, "{}        synta_decoder_free(seq_decoder);", ind)?;
                        writeln!(output, "{}        return err;", ind)?;
                        writeln!(output, "{}    }}", ind)?;
                        emit_arena_track_field(
                            output,
                            inner,
                            var_name,
                            arena,
                            &format!("{}    ", ind),
                        )?;
                    } else {
                        writeln!(output, "{}    /* structural inner type inside EXPLICIT tag: not yet supported */", ind)?;
                        writeln!(output, "{}    err = SyntaErrorCode_InvalidEncoding;", ind)?;
                        writeln!(output, "{}    synta_decoder_free(tagged_decoder);", ind)?;
                        writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                        writeln!(output, "{}    return err;", ind)?;
                    }
                    writeln!(output, "{}    synta_decoder_free(tagged_decoder);", ind)?;
                    writeln!(output, "{}}}", ind)?;
                }
                Tagging::Implicit => {
                    let class = tag_class_c_str(&tag_info.class);
                    writeln!(
                        output,
                        "{}/* IMPLICIT [{cls} {num}]: decoded transparently (tag check relaxed) */",
                        ind,
                        cls = class,
                        num = tag_info.number
                    )?;
                    generate_field_decode_arena(output, inner, var_name, indent, arena, defs)?;
                }
            },
            Type::Constrained {
                base_type: inner, ..
            } => {
                generate_field_decode_arena(output, inner, var_name, indent, arena, defs)?;
            }
            _ => {
                writeln!(
                    output,
                    "{}err = SyntaErrorCode_InvalidEncoding; /* unsupported field type */",
                    ind
                )?;
                writeln!(output, "{}if (err != SyntaErrorCode_Success) {{", ind)?;
                writeln!(output, "{}    synta_decoder_free(seq_decoder);", ind)?;
                writeln!(output, "{}    return err;", ind)?;
                writeln!(output, "{}}}", ind)?;
            }
        }
    }

    Ok(())
}

/// Generate the `_decode_arena` function for a SEQUENCE or SET type.
///
/// The generated function is identical in structure to `_decode` but passes
/// `arena` through every decode call and registers each heap-allocated handle
/// with `_synta_arena_track`.  The `_encode` and `_free` functions are NOT
/// re-generated — callers should still use the regular variants.
fn generate_sequence_arena_impl(
    output: &mut String,
    name: &str,
    fields: &[SequenceField],
    defs: &[Definition],
    is_set: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let container_kind = if is_set { "set" } else { "sequence" };
    let enter_fn = if is_set {
        "synta_decoder_enter_set"
    } else {
        "synta_decoder_enter_sequence"
    };

    writeln!(
        output,
        "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(
        output,
        "    if (decoder == NULL || arena == NULL || out == NULL) {{"
    )?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    // Enter {}", container_kind.to_uppercase())?;
    writeln!(output, "    SyntaDecoder* seq_decoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = {}(decoder, &seq_decoder);",
        enter_fn
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    for field in fields {
        let field_name = to_snake_case(&field.name);

        if field.optional {
            writeln!(output, "    // Decode optional field: {}", field_name)?;
            let tag_check = get_tag_check_condition(&field.ty, defs);
            writeln!(output, "    {{")?;
            writeln!(output, "        SyntaTag tag;")?;
            writeln!(
                output,
                "        if (synta_decoder_peek_tag(seq_decoder, &tag) == SyntaErrorCode_Success &&"
            )?;
            writeln!(output, "            ({})) {{", tag_check)?;
            generate_field_decode_arena(
                output,
                &field.ty,
                &format!("out->{}", field_name),
                3,
                "arena",
                defs,
            )?;
            writeln!(output, "            out->has_{} = true;", field_name)?;
            writeln!(output, "        }} else {{")?;
            writeln!(output, "            out->has_{} = false;", field_name)?;
            writeln!(output, "        }}")?;
            writeln!(output, "    }}")?;
        } else {
            writeln!(output, "    // Decode field: {}", field_name)?;
            generate_field_decode_arena(
                output,
                &field.ty,
                &format!("out->{}", field_name),
                1,
                "arena",
                defs,
            )?;
        }
        writeln!(output)?;
    }

    writeln!(output, "    synta_decoder_free(seq_decoder);")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate the `_decode_arena` function for a CHOICE type.
fn generate_choice_arena_impl(
    output: &mut String,
    name: &str,
    variants: &[ChoiceVariant],
    defs: &[Definition],
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let tag_enum_name = format!("{}Tag", struct_name);

    writeln!(
        output,
        "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(
        output,
        "    if (decoder == NULL || arena == NULL || out == NULL) {{"
    )?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    // Peek at the next tag to determine which variant"
    )?;
    writeln!(output, "    SyntaTag tag;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decoder_peek_tag(decoder, &tag);"
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    for (i, variant) in variants.iter().enumerate() {
        let variant_name = to_snake_case(&variant.name);
        let variant_pascal = to_pascal_case(&variant.name);
        let tag_check = get_tag_check_condition(&variant.ty, defs);

        let else_if = if i == 0 { "if" } else { "} else if" };

        writeln!(output, "    {} ({}) {{", else_if, tag_check)?;
        writeln!(output, "        // Decode {} variant", variant_name)?;
        writeln!(
            output,
            "        out->tag = {}_{};",
            tag_enum_name, variant_pascal
        )?;
        generate_choice_variant_decode_arena(
            output,
            &variant.ty,
            &format!("out->value.{}", variant_name),
            "arena",
        )?;
        writeln!(output, "        return SyntaErrorCode_Success;")?;
    }

    writeln!(output, "    }} else {{")?;
    writeln!(
        output,
        "        /* no matching variant found for the observed tag */"
    )?;
    writeln!(output, "        return SyntaErrorCode_InvalidEncoding;")?;
    writeln!(output, "    }}")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Emit arena-aware decode code for one CHOICE variant.
fn generate_choice_variant_decode_arena(
    output: &mut String,
    ty: &Type,
    var_name: &str,
    arena: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    if let Some(call) = make_decode_call_arena(ty, "decoder", arena, var_name) {
        writeln!(output, "        err = {};", call)?;
        writeln!(
            output,
            "        if (err != SyntaErrorCode_Success) return err;"
        )?;
        emit_arena_track_field(output, ty, var_name, arena, "        ")?;
    } else {
        match ty {
            Type::Sequence(inner_fields) | Type::Set(inner_fields) => {
                let is_sequence = matches!(ty, Type::Sequence(_));
                let container_type = if is_sequence { "sequence" } else { "set" };
                writeln!(
                    output,
                    "        /* Decode nested {} choice variant */",
                    container_type.to_uppercase()
                )?;
                writeln!(output, "        SyntaDecoder* nested_decoder = NULL;")?;
                writeln!(
                    output,
                    "        err = synta_decoder_enter_{}(decoder, &nested_decoder);",
                    container_type
                )?;
                writeln!(
                    output,
                    "        if (err != SyntaErrorCode_Success) return err;"
                )?;
                writeln!(output)?;
                for inner_field in inner_fields {
                    if matches!(inner_field.ty, Type::Null) {
                        continue;
                    }
                    let inner_name = to_snake_case(&inner_field.name);
                    let nested_var = format!("{}.{}", var_name, inner_name);
                    generate_choice_seq_field_decode_arena(
                        output,
                        &inner_field.ty,
                        &nested_var,
                        "        ",
                        arena,
                    )?;
                    writeln!(output)?;
                }
                writeln!(output, "        synta_decoder_free(nested_decoder);")?;
            }
            _ => {
                writeln!(output, "        return SyntaErrorCode_InvalidEncoding;")?;
            }
        }
    }
    Ok(())
}

/// Generate the `_decode_arena` function for a top-level SEQUENCE OF / SET OF type.
fn generate_array_arena_impl(
    output: &mut String,
    name: &str,
    inner_ty: &Type,
    is_sequence: bool,
    size_constraint: Option<ArraySizeBounds>,
) -> Result<(), Box<dyn std::error::Error>> {
    let struct_name = to_pascal_case(name);
    let fn_prefix = to_snake_case(name);
    let container_type = if is_sequence { "sequence" } else { "set" };
    let elem_c_type = get_c_type(inner_ty);
    let array_type = format!("{}*", elem_c_type);

    writeln!(
        output,
        "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, struct {}* out) {{",
        fn_prefix, struct_name
    )?;
    writeln!(
        output,
        "    if (decoder == NULL || arena == NULL || out == NULL) {{"
    )?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(output, "    // Enter SEQUENCE/SET")?;
    writeln!(output, "    SyntaDecoder* array_decoder = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decoder_enter_{}(decoder, &array_decoder);",
        container_type
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) {{")?;
    writeln!(output, "        return err;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(output, "    // Allocate dynamic array for elements")?;
    writeln!(output, "    size_t capacity = 4; // Initial capacity")?;
    writeln!(output, "    size_t count = 0;")?;
    writeln!(
        output,
        "    {} array = ({})calloc(capacity, sizeof({}));",
        array_type, array_type, elem_c_type
    )?;
    writeln!(output, "    if (array == NULL) {{")?;
    writeln!(output, "        synta_decoder_free(array_decoder);")?;
    writeln!(output, "        return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    writeln!(
        output,
        "    while (!synta_decoder_at_end(array_decoder)) {{"
    )?;
    writeln!(output, "        // Grow array if needed")?;
    writeln!(output, "        if (count >= capacity) {{")?;
    writeln!(output, "            capacity *= 2;")?;
    writeln!(
        output,
        "            {} new_array = ({})realloc(array, capacity * sizeof({}));",
        array_type, array_type, elem_c_type
    )?;
    writeln!(output, "            if (new_array == NULL) {{")?;
    writeln!(output, "                free(array);")?;
    writeln!(output, "                synta_decoder_free(array_decoder);")?;
    writeln!(output, "                return SyntaErrorCode_OutOfMemory;")?;
    writeln!(output, "            }}")?;
    writeln!(output, "            array = new_array;")?;
    writeln!(output, "        }}")?;
    writeln!(output)?;

    writeln!(output, "        // Decode element")?;
    generate_decode_element_toplevel_arena(
        output,
        inner_ty,
        "array_decoder",
        "array[count]",
        "arena",
    )?;
    writeln!(output, "        count++;")?;
    writeln!(output, "    }}")?;
    writeln!(output)?;

    // SIZE constraint check after the decode loop
    if let Some(size_spec) = size_constraint {
        emit_array_size_check(output, size_spec, "count")?;
    }

    writeln!(output, "    out->count = count;")?;
    writeln!(output, "    out->items = array;")?;
    writeln!(output, "    _synta_arena_track(arena, out->items, free);")?;
    writeln!(output, "    synta_decoder_free(array_decoder);")?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate the `_decode_arena` function for an enumerated or named-integer type.
///
/// Enums decode into an `int64_t` on the stack (the temporary `SyntaInteger*`
/// is freed immediately), so no arena tracking is needed.  The `arena` parameter
/// is accepted but marked unused so the caller's code compiles cleanly.
fn generate_enum_arena_impl(
    output: &mut String,
    name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let fn_prefix = to_snake_case(name);

    writeln!(
        output,
        "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, enum {}* out) {{",
        fn_prefix,
        to_pascal_case(name)
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;
    writeln!(
        output,
        "    (void)arena; /* enum decode does not leave heap allocations */"
    )?;
    writeln!(output)?;
    writeln!(output, "    SyntaInteger* int_val = NULL;")?;
    writeln!(
        output,
        "    SyntaErrorCode err = synta_decode_integer(decoder, &int_val);"
    )?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    int64_t val;")?;
    writeln!(output, "    err = synta_integer_to_i64(int_val, &val);")?;
    writeln!(output, "    synta_integer_free(int_val);")?;
    writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
    writeln!(output)?;
    writeln!(output, "    *out = (enum {})val;", to_pascal_case(name))?;
    writeln!(output, "    return SyntaErrorCode_Success;")?;
    writeln!(output, "}}")?;

    Ok(())
}

/// Generate the `_decode_arena` function for a simple type alias.
///
/// For value types (Boolean, Real, Null) no tracking is needed.
/// For pointer types (Integer, OctetString, OID) the result is registered
/// with the arena after a successful decode.
/// For type aliases (TypeRef) the call is forwarded to `{ref}_decode_arena`.
fn generate_simple_arena_impl(
    output: &mut String,
    name: &str,
    ty: &Type,
) -> Result<(), Box<dyn std::error::Error>> {
    let fn_prefix = to_snake_case(name);
    let type_name = to_pascal_case(name);
    let base = unwrap_type(ty);

    writeln!(
        output,
        "SyntaErrorCode {}_decode_arena(SyntaDecoder* decoder, SyntaArena* arena, {}* out) {{",
        fn_prefix, type_name
    )?;
    writeln!(output, "    if (decoder == NULL || out == NULL) {{")?;
    writeln!(output, "        return SyntaErrorCode_NullPointer;")?;
    writeln!(output, "    }}")?;

    match base {
        Type::Boolean => {
            writeln!(output, "    (void)arena;")?;
            writeln!(output, "    return synta_decode_boolean(decoder, out);")?;
        }
        Type::Integer(_, _) | Type::Enumerated(_) => {
            writeln!(
                output,
                "    SyntaErrorCode err = synta_decode_integer(decoder, out);"
            )?;
            writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
            writeln!(
                output,
                "    _synta_arena_track(arena, *out, (void(*)(void*))synta_integer_free);"
            )?;
            writeln!(output, "    return SyntaErrorCode_Success;")?;
        }
        Type::Real => {
            writeln!(output, "    (void)arena;")?;
            writeln!(output, "    return synta_decode_real(decoder, out);")?;
        }
        Type::Null => {
            writeln!(output, "    (void)arena; (void)out;")?;
            writeln!(output, "    return synta_decode_null(decoder);")?;
        }
        Type::ObjectIdentifier => {
            writeln!(
                output,
                "    SyntaErrorCode err = synta_decode_object_identifier(decoder, out);"
            )?;
            writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
            writeln!(
                output,
                "    _synta_arena_track(arena, *out, (void(*)(void*))synta_oid_free);"
            )?;
            writeln!(output, "    return SyntaErrorCode_Success;")?;
        }
        Type::RelativeOid => {
            writeln!(
                output,
                "    SyntaErrorCode err = synta_decode_relative_oid(decoder, out);"
            )?;
            writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
            writeln!(
                output,
                "    _synta_arena_track(arena, *out, (void(*)(void*))synta_reloid_free);"
            )?;
            writeln!(output, "    return SyntaErrorCode_Success;")?;
        }
        Type::BitString(_) => {
            writeln!(
                output,
                "    SyntaErrorCode err = synta_decode_bit_string(decoder, &out->data, &out->unused_bits);"
            )?;
            writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
            writeln!(
                output,
                "    if (out->data.owned) _synta_arena_track(arena, (void*)out->data.data, free);"
            )?;
            writeln!(output, "    return SyntaErrorCode_Success;")?;
        }
        Type::OctetString(_)
        | Type::Utf8String(_)
        | Type::PrintableString(_)
        | Type::IA5String(_)
        | Type::UtcTime
        | Type::GeneralizedTime
        | Type::Any
        | Type::AnyDefinedBy(_) => {
            writeln!(
                output,
                "    SyntaErrorCode err = synta_decode_octet_string(decoder, out);"
            )?;
            writeln!(output, "    if (err != SyntaErrorCode_Success) return err;")?;
            writeln!(
                output,
                "    _synta_arena_track(arena, *out, (void(*)(void*))synta_octet_string_free);"
            )?;
            writeln!(output, "    return SyntaErrorCode_Success;")?;
        }
        Type::TypeRef(ref_name) => {
            let ref_fn = to_snake_case(ref_name);
            writeln!(
                output,
                "    return {}_decode_arena(decoder, arena, out);",
                ref_fn
            )?;
        }
        _ => {
            writeln!(output, "    /* unsupported simple type alias */")?;
            writeln!(output, "    return SyntaErrorCode_InvalidEncoding;")?;
        }
    }
    writeln!(output, "}}")?;
    writeln!(output)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_module(name: &str, ty: Type) -> Module {
        Module {
            name: "TestModule".to_string(),
            oid: None,
            values: vec![],
            tagging_mode: None,
            imports: vec![],
            exports: vec![],
            definitions: vec![Definition {
                name: name.to_string(),
                ty,
            }],
        }
    }

    fn impl_config() -> CImplConfig {
        CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Skip,
            with_containing: false,
        }
    }

    // -----------------------------------------------------------------------
    // No SIZE constraint → no check emitted
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_no_size_constraint_no_check() {
        let module = make_module(
            "Items",
            Type::SequenceOf(Box::new(Type::Integer(None, vec![])), None),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // Basic structure present
        assert!(result.contains("items_decode"), "decode function generated");
        assert!(result.contains("items_encode"), "encode function generated");
        // No SIZE check emitted
        assert!(
            !result.contains("Validate SIZE constraint"),
            "no SIZE check without constraint"
        );
    }

    // -----------------------------------------------------------------------
    // Fixed SIZE (e.g. SIZE (3)) → exact count check on decode and encode
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_fixed_size_generates_check() {
        let module = make_module(
            "Triple",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Fixed(3)),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // Decode-side: check after loop
        assert!(
            result.contains("< (size_t)3ULL") || result.contains("> (size_t)3ULL"),
            "fixed SIZE check on decode"
        );
        // Encode-side: check before encode loop
        assert!(result.contains("value->count"), "encode-side count checked");
        // Both bounds present for exact count
        assert!(result.contains("< (size_t)3ULL"), "lower bound (count < 3)");
        assert!(result.contains("> (size_t)3ULL"), "upper bound (count > 3)");
    }

    // -----------------------------------------------------------------------
    // Range with lower bound 1 and no upper bound → only lower bound check
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_range_lower_only() {
        let module = make_module(
            "NonEmpty",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(1), None)),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // Lower bound check
        assert!(result.contains("< (size_t)1ULL"), "lower bound emitted");
        // No upper bound check
        assert!(!result.contains("> (size_t)"), "no upper bound emitted");
    }

    // -----------------------------------------------------------------------
    // Range with lower bound 0 → lower bound skipped (always satisfied)
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_range_zero_lower_bound_skipped() {
        let module = make_module(
            "Items",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(0), Some(10))),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // Upper bound check present
        assert!(result.contains("> (size_t)10ULL"), "upper bound emitted");
        // Lower bound (0) skipped — `< (size_t)0ULL` would always be false
        assert!(
            !result.contains("< (size_t)0ULL"),
            "zero lower bound is not emitted"
        );
    }

    // -----------------------------------------------------------------------
    // Range with both lower and upper bounds
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_range_both_bounds() {
        let module = make_module(
            "Items",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(2), Some(5))),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(result.contains("< (size_t)2ULL"), "lower bound emitted");
        assert!(result.contains("> (size_t)5ULL"), "upper bound emitted");
        // Both on same line (joined with ||)
        assert!(result.contains("||"), "conditions joined with ||");
    }

    // -----------------------------------------------------------------------
    // Encode-side check uses value->count, not count
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_encode_side_check_uses_value_count() {
        let module = make_module(
            "Items",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(1), Some(4))),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("value->count < (size_t)1ULL"),
            "encode-side lower bound uses value->count"
        );
        assert!(
            result.contains("value->count > (size_t)4ULL"),
            "encode-side upper bound uses value->count"
        );
    }

    // -----------------------------------------------------------------------
    // Decode-side check placed after decode loop, before out->count assignment
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_decode_check_before_assignment() {
        let module = make_module(
            "Items",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(1), None)),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // SIZE check must appear before "out->count = count;" assignment
        let check_pos = result
            .find("Validate SIZE constraint on collection")
            .expect("SIZE check present");
        let assign_pos = result
            .find("out->count = count;")
            .expect("assignment present");
        assert!(
            check_pos < assign_pos,
            "SIZE check comes before out->count assignment"
        );
    }

    // -----------------------------------------------------------------------
    // Encode-side check placed before encode loop
    // -----------------------------------------------------------------------

    #[test]
    fn sequence_of_encode_check_before_loop() {
        let module = make_module(
            "Items",
            Type::SequenceOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(1), None)),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // SIZE check must appear before "for (size_t i = 0;" loop
        let check_pos = result
            .find("Validate SIZE constraint before encoding")
            .expect("encode-side SIZE check present");
        let loop_pos = result
            .find("for (size_t i = 0;")
            .expect("encode loop present");
        assert!(
            check_pos < loop_pos,
            "encode SIZE check comes before the encode for-loop"
        );
    }

    // -----------------------------------------------------------------------
    // SET OF behaves the same as SEQUENCE OF for SIZE constraints
    // -----------------------------------------------------------------------

    #[test]
    fn set_of_size_constraint_generates_check() {
        let module = make_module(
            "Items",
            Type::SetOf(
                Box::new(Type::Integer(None, vec![])),
                Some(SizeConstraint::Range(Some(1), Some(8))),
            ),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(result.contains("< (size_t)1ULL"), "lower bound for SET OF");
        assert!(result.contains("> (size_t)8ULL"), "upper bound for SET OF");
    }

    // -----------------------------------------------------------------------
    // Type::Constrained wrapper with modern SIZE constraint
    // -----------------------------------------------------------------------

    #[test]
    fn constrained_sequence_of_modern_size() {
        let module = make_module(
            "Items",
            Type::Constrained {
                base_type: Box::new(Type::SequenceOf(
                    Box::new(Type::Integer(None, vec![])),
                    None,
                )),
                constraint: Constraint {
                    spec: ConstraintSpec::Subtype(SubtypeConstraint::SizeConstraint(Box::new(
                        SubtypeConstraint::ValueRange {
                            min: ConstraintValue::Integer(2),
                            max: ConstraintValue::Integer(6),
                        },
                    ))),
                    exception: None,
                },
            },
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("< (size_t)2ULL"),
            "modern SIZE lower bound extracted"
        );
        assert!(
            result.contains("> (size_t)6ULL"),
            "modern SIZE upper bound extracted"
        );
    }

    // -----------------------------------------------------------------------
    // legacy_size_to_bounds / modern_size_to_bounds unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn legacy_size_fixed_maps_to_equal_bounds() {
        let bounds = legacy_size_to_bounds(&SizeConstraint::Fixed(7));
        assert_eq!(bounds, (Some(7), Some(7)));
    }

    #[test]
    fn legacy_size_range_maps_correctly() {
        let bounds = legacy_size_to_bounds(&SizeConstraint::Range(Some(1), Some(10)));
        assert_eq!(bounds, (Some(1), Some(10)));
    }

    #[test]
    fn legacy_size_range_unbounded_max() {
        let bounds = legacy_size_to_bounds(&SizeConstraint::Range(Some(1), None));
        assert_eq!(bounds, (Some(1), None));
    }

    #[test]
    fn modern_size_extracts_value_range() {
        let spec = ConstraintSpec::Subtype(SubtypeConstraint::SizeConstraint(Box::new(
            SubtypeConstraint::ValueRange {
                min: ConstraintValue::Integer(3),
                max: ConstraintValue::Integer(9),
            },
        )));
        let bounds = modern_size_to_bounds(&spec);
        assert_eq!(bounds, Some((Some(3), Some(9))));
    }

    #[test]
    fn modern_size_non_size_constraint_returns_none() {
        let spec = ConstraintSpec::Subtype(SubtypeConstraint::ValueRange {
            min: ConstraintValue::Integer(0),
            max: ConstraintValue::Integer(100),
        });
        let bounds = modern_size_to_bounds(&spec);
        assert_eq!(bounds, None);
    }

    // -----------------------------------------------------------------------
    // Permitted-alphabet (FROM) constraint validation — Task 4
    // -----------------------------------------------------------------------

    fn make_constrained_sequence(field_base_ty: Type, constraint: SubtypeConstraint) -> Module {
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
                    name: "field".to_string(),
                    ty: Type::Constrained {
                        base_type: Box::new(field_base_ty),
                        constraint: Constraint {
                            spec: ConstraintSpec::Subtype(constraint),
                            exception: None,
                        },
                    },
                    optional: false,
                    default: None,
                }]),
            }],
        }
    }

    #[test]
    fn permitted_alphabet_ia5string_generates_loop() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'A', max: 'Z' }]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("for (_ai = 0; _ai < _alen; _ai++)"),
            "alphabet loop emitted"
        );
        assert!(result.contains("unsigned char _c = _ap[_ai]"), "byte fetch");
        assert!(result.contains("_c >= 'A' && _c <= 'Z'"), "range A-Z");
        assert!(
            result.contains("SyntaErrorCode_InvalidArgument"),
            "returns InvalidArgument on bad char"
        );
    }

    #[test]
    fn permitted_alphabet_single_char_uses_equality() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'x', max: 'x' }]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(result.contains("_c == 'x'"), "single char uses ==");
        assert!(!result.contains("_c >= 'x'"), "no range for single char");
    }

    #[test]
    fn permitted_alphabet_multiple_ranges_joined_with_or() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::PermittedAlphabet(vec![
                CharRange { min: 'A', max: 'Z' },
                CharRange { min: '0', max: '9' },
            ]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(result.contains("_c >= 'A' && _c <= 'Z'"), "first range");
        assert!(result.contains("_c >= '0' && _c <= '9'"), "second range");
        assert!(result.contains(" || "), "ranges joined with ||");
    }

    #[test]
    fn permitted_alphabet_not_emitted_for_integer_field() {
        // PermittedAlphabet on an INTEGER base type must be silently skipped
        let module = make_constrained_sequence(
            Type::Integer(None, vec![]),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'A', max: 'Z' }]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            !result.contains("for (_ai = 0"),
            "no alphabet loop for INTEGER"
        );
    }

    #[test]
    fn permitted_alphabet_uses_synta_octet_string_helpers() {
        let module = make_constrained_sequence(
            Type::PrintableString(None),
            SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'a', max: 'z' }]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("synta_octet_string_len("),
            "uses synta_octet_string_len"
        );
        assert!(
            result.contains("synta_octet_string_data("),
            "uses synta_octet_string_data"
        );
    }

    #[test]
    fn intersection_emits_both_size_and_alphabet_checks() {
        // SIZE (1..64) FROM ('A'..'Z'): both checks must appear in encode
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Intersection(vec![
                SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(1),
                    max: ConstraintValue::Integer(64),
                })),
                SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'A', max: 'Z' }]),
            ]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("Validate SIZE range constraint"),
            "SIZE check present"
        );
        assert!(
            result.contains("Validate FROM (permitted alphabet) constraint"),
            "alphabet check present"
        );
    }

    #[test]
    fn intersection_size_check_before_alphabet_check() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Intersection(vec![
                SubtypeConstraint::SizeConstraint(Box::new(SubtypeConstraint::ValueRange {
                    min: ConstraintValue::Integer(1),
                    max: ConstraintValue::Integer(64),
                })),
                SubtypeConstraint::PermittedAlphabet(vec![CharRange { min: 'A', max: 'Z' }]),
            ]),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        let size_pos = result
            .find("Validate SIZE range constraint")
            .expect("SIZE check present");
        let alpha_pos = result
            .find("Validate FROM (permitted alphabet) constraint")
            .expect("alphabet check present");
        assert!(size_pos < alpha_pos, "SIZE check precedes alphabet check");
    }

    // -----------------------------------------------------------------------
    // PATTERN constraint validation — Task 5
    // -----------------------------------------------------------------------

    #[test]
    fn pattern_skip_emits_comment_not_regex() {
        // Skip mode (default): emit a comment, no regex call.
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Pattern("[0-9]+".to_string()),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("PATTERN constraint \"[0-9]+\" skipped"),
            "skip comment present"
        );
        assert!(
            !result.contains("regcomp") && !result.contains("pcre2_compile"),
            "no regex call in Skip mode"
        );
    }

    #[test]
    fn pattern_posix_emits_regex_include_and_regcomp() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Pattern("[A-Z]+".to_string()),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Posix,
            with_containing: false,
        };
        let result = generate_c_impl(&module, config).unwrap();
        // Header include
        assert!(result.contains("#include <regex.h>"), "regex.h included");
        // Validation comment
        assert!(
            result.contains("Validate PATTERN constraint \"[A-Z]+\" (POSIX ERE)"),
            "posix comment present"
        );
        // POSIX API calls
        assert!(result.contains("regcomp("), "regcomp call present");
        assert!(result.contains("regexec("), "regexec call present");
        assert!(result.contains("regfree("), "regfree call present");
        // No PCRE2
        assert!(
            !result.contains("pcre2_compile"),
            "no pcre2 call in Posix mode"
        );
    }

    #[test]
    fn pattern_pcre2_emits_pcre2_include_and_compile() {
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Pattern("[0-9]{3}".to_string()),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Pcre2,
            with_containing: false,
        };
        let result = generate_c_impl(&module, config).unwrap();
        // Header includes
        assert!(
            result.contains("#define PCRE2_CODE_UNIT_WIDTH 8"),
            "PCRE2 width define present"
        );
        assert!(result.contains("#include <pcre2.h>"), "pcre2.h included");
        // Validation comment
        assert!(
            result.contains("Validate PATTERN constraint \"[0-9]{3}\" (PCRE2)"),
            "pcre2 comment present"
        );
        // PCRE2 API calls
        assert!(result.contains("pcre2_compile("), "pcre2_compile call");
        assert!(result.contains("pcre2_match("), "pcre2_match call");
        assert!(result.contains("pcre2_code_free("), "pcre2_code_free call");
        // No POSIX
        assert!(!result.contains("regcomp"), "no regcomp in Pcre2 mode");
    }

    #[test]
    fn pattern_non_string_type_no_validation() {
        // PATTERN on INTEGER is a no-op (only strings are validated)
        let module = make_constrained_sequence(
            Type::Integer(None, vec![]),
            SubtypeConstraint::Pattern("[0-9]+".to_string()),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Posix,
            with_containing: false,
        };
        let result = generate_c_impl(&module, config).unwrap();
        assert!(
            !result.contains("regcomp") && !result.contains("pcre2_compile"),
            "no regex for non-string type"
        );
    }

    #[test]
    fn pattern_posix_escapes_special_chars() {
        // Pattern with backslash: \d+ should become \\d+ in the C string literal
        let module = make_constrained_sequence(
            Type::IA5String(None),
            SubtypeConstraint::Pattern("\\d+".to_string()),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Posix,
            with_containing: false,
        };
        let result = generate_c_impl(&module, config).unwrap();
        // The C string literal should have the backslash escaped
        assert!(
            result.contains("\"\\\\d+\""),
            "backslash escaped in C string literal"
        );
    }

    // -----------------------------------------------------------------------
    // CONTAINING constraint validation — Task 6
    // -----------------------------------------------------------------------

    #[test]
    fn containing_skip_emits_comment_not_decoder() {
        // Default: skip mode — emit a comment, no scratch decoder.
        let module = make_constrained_sequence(
            Type::OctetString(None),
            SubtypeConstraint::ContainedSubtype(Box::new(Type::TypeRef("Certificate".to_string()))),
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("CONTAINING constraint skipped"),
            "skip comment present"
        );
        assert!(
            !result.contains("synta_decoder_new"),
            "no decoder call in skip mode"
        );
    }

    #[test]
    fn containing_enabled_emits_scratch_decoder_block() {
        // with_containing: true — emit full validation block.
        let module = make_constrained_sequence(
            Type::OctetString(None),
            SubtypeConstraint::ContainedSubtype(Box::new(Type::TypeRef("Certificate".to_string()))),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Skip,
            with_containing: true,
        };
        let result = generate_c_impl(&module, config).unwrap();
        // Comment
        assert!(
            result.contains("Validate CONTAINING constraint (Certificate)"),
            "containing comment present"
        );
        // Scratch decoder
        assert!(
            result.contains("synta_decoder_new("),
            "synta_decoder_new called"
        );
        assert!(
            result.contains("certificate_decode(_inner_dec, &_inner_val)"),
            "inner decode called"
        );
        assert!(
            result.contains("synta_decoder_free(_inner_dec)"),
            "decoder freed"
        );
        assert!(
            result.contains("certificate_free(&_inner_val)"),
            "inner value freed"
        );
        // Error check
        assert!(
            result.contains("SyntaErrorCode_InvalidArgument"),
            "returns InvalidArgument on decode failure"
        );
    }

    #[test]
    fn containing_builtin_inner_type_emits_comment() {
        // Built-in inner types (e.g. INTEGER) cannot be validated — emit comment.
        let module = make_constrained_sequence(
            Type::OctetString(None),
            SubtypeConstraint::ContainedSubtype(Box::new(Type::Integer(None, vec![]))),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Skip,
            with_containing: true,
        };
        let result = generate_c_impl(&module, config).unwrap();
        assert!(
            result.contains("CONTAINING (built-in type): validation not generated"),
            "built-in comment present"
        );
        assert!(
            !result.contains("synta_decoder_new"),
            "no decoder for built-in type"
        );
    }

    #[test]
    fn containing_non_byte_string_no_validation() {
        // CONTAINING on INTEGER (not an octet string) is a no-op.
        let module = make_constrained_sequence(
            Type::Integer(None, vec![]),
            SubtypeConstraint::ContainedSubtype(Box::new(Type::TypeRef("Inner".to_string()))),
        );
        let config = CImplConfig {
            header_file: "test.h".to_string(),
            arena_mode: false,
            pattern_mode: PatternMode::Skip,
            with_containing: true,
        };
        let result = generate_c_impl(&module, config).unwrap();
        assert!(
            !result.contains("synta_decoder_new"),
            "no containing check for non-byte-string base type"
        );
    }

    // -----------------------------------------------------------------------
    // _default() implementation tests
    // -----------------------------------------------------------------------

    fn make_default_seq(fields: Vec<SequenceField>) -> Module {
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

    // -----------------------------------------------------------------------
    // Explicit / Implicit tag handling tests
    // -----------------------------------------------------------------------

    fn make_tagged_seq(
        field_name: &str,
        class: TagClass,
        number: u32,
        tagging: Tagging,
        inner: Type,
        optional: bool,
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
                    optional,
                    default: None,
                }]),
            }],
        }
    }

    #[test]
    fn explicit_tag_decode_enters_constructed() {
        // [0] EXPLICIT INTEGER decode → synta_decoder_enter_constructed with tag [0] constructed
        let module = make_tagged_seq(
            "id",
            TagClass::ContextSpecific,
            0,
            Tagging::Explicit,
            Type::Integer(None, vec![]),
            false,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("synta_decoder_enter_constructed"),
            "explicit tag decode must use synta_decoder_enter_constructed; got:\n{}",
            result
        );
        assert!(
            result.contains("SyntaTagClass_ContextSpecific"),
            "explicit tag decode must set ContextSpecific class; got:\n{}",
            result
        );
        assert!(
            result.contains("explicit_tag.number = 0"),
            "explicit tag decode must set tag number 0; got:\n{}",
            result
        );
        assert!(
            result.contains("explicit_tag.constructed = true"),
            "explicit tag must be constructed; got:\n{}",
            result
        );
        assert!(
            result.contains("synta_decode_integer"),
            "inner type still decoded with synta_decode_integer; got:\n{}",
            result
        );
    }

    #[test]
    fn explicit_tag_encode_starts_constructed() {
        // [0] EXPLICIT INTEGER encode → synta_encoder_start_constructed + end_constructed
        let module = make_tagged_seq(
            "id",
            TagClass::ContextSpecific,
            0,
            Tagging::Explicit,
            Type::Integer(None, vec![]),
            false,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("synta_encoder_start_constructed"),
            "explicit tag encode must use synta_encoder_start_constructed; got:\n{}",
            result
        );
        assert!(
            result.contains("synta_encoder_end_constructed"),
            "explicit tag encode must call synta_encoder_end_constructed; got:\n{}",
            result
        );
        assert!(
            result.contains("synta_encode_integer"),
            "inner type still encoded with synta_encode_integer; got:\n{}",
            result
        );
    }

    #[test]
    fn explicit_optional_tag_peek_uses_tag_class_and_number() {
        // OPTIONAL [1] EXPLICIT BOOLEAN → peek_tag checks class and number 1
        let module = make_tagged_seq(
            "flag",
            TagClass::ContextSpecific,
            1,
            Tagging::Explicit,
            Type::Boolean,
            true,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("synta_decoder_peek_tag"),
            "optional field must peek at tag; got:\n{}",
            result
        );
        assert!(
            result.contains("SyntaTagClass_ContextSpecific"),
            "peek must check ContextSpecific class; got:\n{}",
            result
        );
        assert!(
            result.contains("tag.number == 1"),
            "peek must check tag number 1; got:\n{}",
            result
        );
    }

    #[test]
    fn implicit_tag_decode_emits_transparency_comment() {
        // [2] IMPLICIT OCTET STRING → fallback with comment (tag replacement not yet supported)
        let module = make_tagged_seq(
            "data",
            TagClass::ContextSpecific,
            2,
            Tagging::Implicit,
            Type::OctetString(None),
            false,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("IMPLICIT"),
            "implicit tag decode should emit IMPLICIT comment; got:\n{}",
            result
        );
        // Still decodes the inner type
        assert!(
            result.contains("synta_decode_octet_string"),
            "implicit tag falls back to inner type decode; got:\n{}",
            result
        );
    }

    #[test]
    fn implicit_tag_encode_emits_transparency_comment() {
        // [2] IMPLICIT OCTET STRING encode → fallback with comment
        let module = make_tagged_seq(
            "data",
            TagClass::ContextSpecific,
            2,
            Tagging::Implicit,
            Type::OctetString(None),
            false,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("IMPLICIT"),
            "implicit tag encode should emit IMPLICIT comment; got:\n{}",
            result
        );
        // Still encodes the inner type
        assert!(
            result.contains("synta_encode_octet_string"),
            "implicit tag falls back to inner type encode; got:\n{}",
            result
        );
    }

    #[test]
    fn explicit_tag_decode_frees_tagged_decoder_on_error() {
        // The generated code must call synta_decoder_free(tagged_decoder) on error
        let module = make_tagged_seq(
            "id",
            TagClass::ContextSpecific,
            0,
            Tagging::Explicit,
            Type::Integer(None, vec![]),
            false,
        );
        let result = generate_c_impl(&module, impl_config()).unwrap();
        // tagged_decoder must be freed on the error path
        assert!(
            result.contains("synta_decoder_free(tagged_decoder)"),
            "tagged_decoder must be freed; got:\n{}",
            result
        );
    }

    #[test]
    fn default_bool_true_assigns_directly() {
        // BOOLEAN DEFAULT TRUE → `out.field = true;` in the generated _default().
        let module = make_default_seq(vec![SequenceField {
            name: "enabled".to_string(),
            ty: Type::Boolean,
            optional: false,
            default: Some("TRUE".to_string()),
        }]);
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("Config config_default(void)"),
            "_default function present"
        );
        assert!(
            result.contains("out.enabled = true;"),
            "TRUE default assigned"
        );
    }

    #[test]
    fn default_bool_false_no_assignment() {
        // BOOLEAN DEFAULT FALSE → zero-init already provides false; no explicit assignment.
        let module = make_default_seq(vec![SequenceField {
            name: "disabled".to_string(),
            ty: Type::Boolean,
            optional: false,
            default: Some("FALSE".to_string()),
        }]);
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("Config config_default(void)"),
            "_default function present"
        );
        assert!(
            !result.contains("out.disabled = false;"),
            "no redundant false assignment"
        );
    }

    #[test]
    fn default_integer_emits_comment() {
        // INTEGER DEFAULT → a comment; pointer type can't be trivially initialised.
        let module = make_default_seq(vec![SequenceField {
            name: "port".to_string(),
            ty: Type::Integer(None, vec![]),
            optional: false,
            default: Some("8080".to_string()),
        }]);
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("/* out.port: DEFAULT 8080"),
            "integer default comment emitted"
        );
        assert!(
            !result.contains("out.port = 8080"),
            "no direct assignment for pointer integer"
        );
    }

    #[test]
    fn default_function_not_generated_for_required_field() {
        // A required field with no DEFAULT means no _default() implementation.
        let module = make_default_seq(vec![SequenceField {
            name: "name".to_string(),
            ty: Type::Integer(None, vec![]),
            optional: false,
            default: None,
        }]);
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            !result.contains("_default(void)"),
            "no _default for required-field sequence"
        );
    }

    #[test]
    fn default_function_for_all_optional_sequence() {
        // All-OPTIONAL sequence: _default() is generated with zero-init body.
        let module = make_default_seq(vec![
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
        let result = generate_c_impl(&module, impl_config()).unwrap();
        assert!(
            result.contains("Config config_default(void)"),
            "_default function present"
        );
        assert!(result.contains("Config out = {0};"), "zero-init present");
        assert!(result.contains("return out;"), "returns out");
    }
}
