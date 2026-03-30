//! Native Rust code generation pipeline for executable Vest output.

mod analysis;
mod emit;
mod helper_specs;
mod ir;
mod lower;
mod names;
mod rust_format;

use std::error::Error;

pub use analysis::{analyze_definitions, Analysis, AnalysisMap, ValType};
pub use emit::{
    generate_module, generate_module_tokens, generate_nominal_sections, ModuleSections,
    NominalSections,
};
pub use ir::*;
pub use lower::lower_definitions;
pub use names::{build_name_map, snake_to_upper_camel, DefinitionNames, NamesMap};

use crate::vestir::Definition;
use crate::VestError;

#[derive(Debug, Clone)]
pub struct CodegenPlan {
    pub ctx: CodegenCtx,
    pub defs: Vec<CombDef>,
    pub names: NamesMap,
    pub analysis: AnalysisMap,
}

pub fn build_plan(definitions: &[Definition], ctx: &CodegenCtx) -> CodegenPlan {
    let mut lowered_ctx = ctx.clone();
    let defs = lower_definitions(definitions, &mut lowered_ctx);
    let names = build_name_map(&defs);
    let analysis = analyze_definitions(&defs);

    CodegenPlan {
        ctx: lowered_ctx,
        defs,
        names,
        analysis,
    }
}

pub fn generate_from_plan(plan: &CodegenPlan) -> Result<String, Box<dyn Error>> {
    generate_module(plan).map_err(|_e| Box::new(VestError::CodegenError) as Box<dyn Error>)
}

pub fn generate_rust_module(
    definitions: &[Definition],
    ctx: &CodegenCtx,
) -> Result<String, Box<dyn Error>> {
    let plan = build_plan(definitions, ctx);
    generate_from_plan(&plan)
}
