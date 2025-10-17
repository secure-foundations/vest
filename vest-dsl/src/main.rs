use std::{error::Error, io::Write, path::PathBuf};

mod ast;
mod elab;
mod type_check;
mod utils;
mod vestir;

use clap::Parser;

/// Vest: A generator for formally verified parsers/serializers in Verus
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name or directory of the vest file
    vest_file: String,

    /// Name of the output verus file
    #[arg(short, long)]
    output: Option<String>,

    /// Codegen options
    /// all: Generate all the code
    /// types: Only generate the format type definitions
    /// impls: Only generate the implementation (and the data type definitions)
    /// anns: Only generate the annotations (spec data types, spec combinators, etc.)
    #[arg(short, long)]
    codegen: Option<String>,
}

fn replace_extension(filename: &str, new_ext: &str) -> String {
    let mut path = PathBuf::from(filename);
    path.set_extension(new_ext);
    path.to_string_lossy().into_owned()
}

#[derive(Debug)]
pub enum VestError {
    ParsingError,
    TypeError,
    CodegenError,
}

impl std::fmt::Display for VestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VestError::ParsingError => write!(f, "Failed to compile, parsing error."),
            VestError::TypeError => write!(f, "Failed to compile, type error."),
            VestError::CodegenError => write!(f, "Failed to compile, codegen error."),
        }
    }
}

impl std::error::Error for VestError {}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let codegen_opt = args
        .codegen
        .map(|s| match s.as_str() {
            "all" => vest_dsl::codegen::CodegenOpts::All,
            "types" => vest_dsl::codegen::CodegenOpts::Types,
            "impls" => vest_dsl::codegen::CodegenOpts::Impls,
            "anns" => vest_dsl::codegen::CodegenOpts::Anns,
            _ => panic!("Invalid codegen option"),
        })
        .unwrap_or(vest_dsl::codegen::CodegenOpts::All);
    let output_file = args
        .output
        .unwrap_or(replace_extension(args.vest_file.as_str(), "rs"));
    vest_dsl::compile_to(&args.vest_file, codegen_opt, &output_file)?;
    Ok(())
}
