//! ASN.1-to-Vest code generation.
//!
//! The frontend is Synta's ASN.1 parser and AST. The backend emits concrete
//! nominal `vest_lib2::asn1` BER or DER formats, so generated parsers and
//! serializers use Vest's verified combinators directly while enclosing formats
//! depend on compact, already-proved interfaces.

mod codegen;
mod error;
mod frontend;
mod naming;

pub use codegen::{
    generate, generate_with_options, generate_with_rule_overrides, CodegenOptions, EncodingRules,
};
pub use error::{CodegenError, Error};
pub use frontend::{SchemaModule, SchemaValue, SchemaValueAssignment};
pub use synta_codegen::ast;
pub use synta_codegen::{parse as parse_synta, Definition, Module, ParseError, Type};

/// Parse with the locally patched, lossless-for-supported-syntax Synta frontend.
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
