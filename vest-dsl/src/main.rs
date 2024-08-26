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
    let code = codegen::code_gen(&ast, &ctx);
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
