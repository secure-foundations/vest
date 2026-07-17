//! ASN.1-to-Vest code generation.
//!
//! The frontend is Synta's ASN.1 parser and AST. The backend emits concrete
//! `vest_lib2::asn1` DER formats, so the generated parsers and serializers use
//! Vest's verified combinators directly.

mod codegen;
mod error;
mod frontend;
mod naming;

pub use codegen::generate;
pub use error::{CodegenError, Error};
pub use frontend::{SchemaModule, SchemaValue, SchemaValueAssignment};
pub use synta_codegen::ast;
pub use synta_codegen::{parse as parse_synta, Definition, Module, ParseError, Type};

/// Parse with the locally patched, lossless-for-supported-syntax Synta frontend.
pub fn parse(source: &str) -> Result<SchemaModule, Error> {
    Ok(parse_synta(source)?)
}

/// Parse an ASN.1 module and generate Vest DER format declarations.
pub fn compile(source: &str) -> Result<String, Error> {
    let module = parse(source)?;
    Ok(generate(&module)?)
}
