use std::{error::Error, path::PathBuf};

use clap::{Parser, ValueEnum};
use vest::{codegen::CodegenOpts, compile_to, compile_to_v2};

/// Target language for code generation
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Target {
    /// Generate Verus code with specs and proofs
    Verus,
    /// Generate pure Rust code (executable only)
    Rust,
}

/// Vest: A generator for formally verified parsers/serializers in Verus
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name or directory of the vest file
    vest_file: String,

    /// Name of the output verus file
    #[arg(short, long)]
    output: Option<String>,

    /// Target language for code generation
    #[arg(short, long, value_enum, default_value_t = Target::Rust)]
    target: Target,

    /// Codegen options (only for verus target)
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

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let output_file = args
        .output
        .unwrap_or(replace_extension(args.vest_file.as_str(), "rs"));

    match args.target {
        Target::Rust => {
            // Use the new token-based code generator
            compile_to_v2(&args.vest_file, &output_file)?;
        }
        Target::Verus => {
            // Use the existing Verus code generator
            let codegen_opt = args
                .codegen
                .map(|s| match s.as_str() {
                    "all" => CodegenOpts::All,
                    "types" => CodegenOpts::Types,
                    "impls" => CodegenOpts::Impls,
                    "anns" => CodegenOpts::Anns,
                    _ => panic!("Invalid codegen option"),
                })
                .unwrap_or(CodegenOpts::All);
            compile_to(&args.vest_file, codegen_opt, &output_file)?;
        }
    }

    Ok(())
}
