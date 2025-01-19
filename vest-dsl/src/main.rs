use std::{io::Write, path::PathBuf};

mod ast;
mod codegen;
mod elab;
mod type_check;
mod utils;
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

fn main() {
    let args = Args::parse();

    // parse the vest file
    let vest = std::fs::read_to_string(&args.vest_file).expect("cannot read the vest file");
    println!("📜 Parsing the vest file...");
    let mut ast = ast::from_str(&vest).expect("cannot parse the vest file");

    // elaborate the AST
    println!("🔨 Elaborating the AST...");
    elab::elaborate(&mut ast);

    // type check the AST
    println!("🔍 Type checking...");
    let ctx = type_check::check(&ast);

    // code gen to a file
    // if there is no output file specified, use the same name as the name of input vest file
    let mut verus = std::fs::File::create(
        args.output
            .unwrap_or(replace_extension(args.vest_file.as_str(), "rs")),
    )
    .expect("cannot create the verus file");

    println!("📝 Generating the verus file...");
    let codegen_opt = args
        .codegen
        .map(|s| match s.as_str() {
            "all" => codegen::CodegenOpts::All,
            "types" => codegen::CodegenOpts::Types,
            "impls" => codegen::CodegenOpts::Impls,
            "anns" => codegen::CodegenOpts::Anns,
            _ => panic!("Invalid codegen option"),
        })
        .unwrap_or(codegen::CodegenOpts::All);
    let code = codegen::code_gen(&ast, &ctx, codegen_opt);
    verus
        .write_all(code.as_bytes())
        .expect("cannot write to the file");
    println!("👏 Done!");
    // let tokens = zip_parse_result.tokens();
    //
    // for token in tokens {
    //     println!("{:?}", token);
    // }
}
