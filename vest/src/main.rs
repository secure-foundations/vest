use std::{error::Error, path::PathBuf};

use clap::Parser;
use vest::compile_to;

/// Vest: A generator for formally verified parsers/serializers in Verus
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Name or directory of the vest file
    vest_file: String,

    /// Name of the output verus file
    #[arg(short, long)]
    output: Option<String>,
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
    compile_to(&args.vest_file, &output_file)?;
    Ok(())
}
