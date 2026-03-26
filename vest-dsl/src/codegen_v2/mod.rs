//! Token-based code generator for vest-dsl.

mod combir;
mod format;
mod lower;
mod output;

use std::error::Error;

pub use combir::*;
pub use format::format_rust_code;
pub use lower::lower_definitions;
pub use output::generate_module;

use crate::vestir::Definition;
use crate::VestError;

/// Generate a complete Rust module from VestIR definitions.
pub fn generate_rust_module(
    definitions: &[Definition],
    ctx: &CodegenCtx,
) -> Result<String, Box<dyn Error>> {
    let mut ctx = ctx.clone();

    // Lower VestIR to CombIR
    let comb_defs = lower_definitions(definitions, &mut ctx);

    // Generate module code
    let code = generate_module(&comb_defs, &ctx)
        .map_err(|_e| Box::new(VestError::CodegenError) as Box<dyn Error>)?;

    Ok(code)
}
