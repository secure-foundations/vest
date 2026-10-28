//! The locally maintained Synta frontend. See the crate's `THIRD_PARTY.md`.

pub mod ast;
mod parser;

pub use parser::{parse, ParseError};

pub type SchemaModule = ast::Module;
pub type SchemaValueAssignment = ast::ValueAssignment;
pub type SchemaValue = ast::Value;
