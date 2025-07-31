use std::path::PathBuf;

mod ast;
// mod codegen;
mod elab;
mod type_check;
mod utils;
mod vestir;
use ariadne::{Report, ReportKind};
use clap::Parser;
use pest::error::InputLocation;

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

fn main() -> Result<(), VestError> {
    let args = Args::parse();

    // parse the vest file
    let vest = std::fs::read_to_string(&args.vest_file).expect("cannot read the vest file");
    let source = (
        args.vest_file.as_str(),
        &ariadne::Source::from(vest.clone()),
    );
    // println!("📜 Parsing the vest file...");
    let mut ast = ast::from_str(&vest).map_err(|e| {
        let span = match e.location {
            InputLocation::Pos(pos) => pos..pos,
            InputLocation::Span(span) => span.0..span.1,
        };
        Report::build(ReportKind::Error, (source.0, span.clone()))
            // .with_message(format!("{e}"))
            .with_message(format!("{}", e.variant.message()))
            .with_label(
                ariadne::Label::new((source.0, span))
                    .with_message("here")
                    .with_color(ariadne::Color::Red),
            )
            .finish()
            .eprint(source)
            .unwrap();
        VestError::ParsingError
    })?;

    // elaborate the AST
    // println!("🔨 Elaborating the AST...");
    elab::elaborate(&mut ast);

    // type check the AST
    // println!("🔍 Type checking...");
    let ctx = type_check::check(&ast, source)?;

    // code gen to a file
    // if there is no output file specified, use the same name as the name of input vest file
    // let mut verus = std::fs::File::create(
    //     args.output
    //         .unwrap_or(replace_extension(args.vest_file.as_str(), "rs")),
    // )?;

    // println!("📝 Generating the verus file...");
    // let codegen_opt = args
    //     .codegen
    //     .map(|s| match s.as_str() {
    //         "all" => codegen::CodegenOpts::All,
    //         "types" => codegen::CodegenOpts::Types,
    //         "impls" => codegen::CodegenOpts::Impls,
    //         "anns" => codegen::CodegenOpts::Anns,
    //         _ => panic!("Invalid codegen option"),
    //     })
    //     .unwrap_or(codegen::CodegenOpts::All);
    // let code = codegen::code_gen(&ast, &ctx, codegen_opt);
    // verus.write_all(code.as_bytes())?;
    println!("👏 Done!");

    Ok(())
    // let tokens = zip_parse_result.tokens();
    //
    // for token in tokens {
    //     println!("{:?}", token);
    // }
}
