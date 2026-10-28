//! ASN.1-to-Vest code generation.
//!
//! The frontend is a locally maintained adaptation of Synta's parser and AST.
//! The backend emits concrete
//! nominal `vest_lib::asn1` BER or DER formats, so generated parsers and
//! serializers use Vest's verified combinators directly while enclosing formats
//! depend on compact, already-proved interfaces.
//!
//! The [ASN.1 guide](https://secure-foundations.github.io/vest/guide/asn1/)
//! documents encoding-rule selection, generated APIs, supported syntax, and
//! current limitations.

mod codegen;
mod error;
mod frontend;
mod naming;

pub use codegen::{
    generate, generate_with_options, generate_with_rule_overrides, CodegenOptions, EncodingRules,
};
pub use error::{CodegenError, Error};
pub use frontend::ast::{Definition, Module, Type};
pub use frontend::{
    ast, parse as parse_synta, ParseError, SchemaModule, SchemaValue, SchemaValueAssignment,
};

/// Parse one complete ASN.1 module with the locally maintained Synta frontend.
///
/// A final `END` is required; trailing input and syntax that the frontend would
/// otherwise discard or approximate are rejected. Backend support is checked
/// separately by [`generate`].
pub fn parse(source: &str) -> Result<SchemaModule, Error> {
    Ok(parse_synta(source)?)
}

/// Parse an ASN.1 module and generate nominal Vest DER formats.
///
/// This compatibility entry point defaults to DER.
pub fn compile(source: &str) -> Result<String, Error> {
    compile_with_options(source, CodegenOptions::default())
}

/// Parse an ASN.1 module and generate nominal formats using the selected rules.
pub fn compile_with_options(source: &str, options: CodegenOptions) -> Result<String, Error> {
    let module = parse(source)?;
    Ok(generate_with_options(&module, options)?)
}

/// Parse an ASN.1 module and generate it with definition-global encoding-rule
/// overrides. An override applies to the named definition and its transitive
/// dependencies; parent definitions retain the module default. Each ASN.1
/// definition is emitted exactly once.
pub fn compile_with_rule_overrides(
    source: &str,
    options: CodegenOptions,
    definition_rules: &std::collections::BTreeMap<String, EncodingRules>,
) -> Result<String, Error> {
    let module = parse(source)?;
    Ok(generate_with_rule_overrides(
        &module,
        options,
        definition_rules,
    )?)
}
