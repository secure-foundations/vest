use std::{error::Error, path::PathBuf};

use clap::Parser;
use vest_dsl_vps::compile_to;

/// Vest DSL frontend targeting the VPS verified-combinator backend.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name or path of the `.vest` schema file
    schema_file: String,

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

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    let output_file = args
        .output
        .unwrap_or(replace_extension(args.schema_file.as_str(), "rs"));
    compile_to(&args.schema_file, &output_file)?;
    Ok(())
}
