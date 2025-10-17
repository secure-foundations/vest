use std::error::Error;
use std::io::Write;

mod ast;
pub mod codegen;
mod elab;
mod type_check;
mod utils;
mod vestir;

use ariadne::{Report, ReportKind};
use pest::error::InputLocation;

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

/// Compiles the given source code and returns the resulting output.
///
/// # Example
/// ```rust
/// use std::error::Error;
/// use std::io::Write;
///
/// // build.rs
/// fn main() -> Result<(), Box<dyn Error>> {
///   println!("cargo::rerun-if-changed=src/tlv.vest");
///   let file_name = "src/tlv.vest";
///   let vest = std::fs::read_to_string(file_name)?;
///   let code = compile(file_name, vest, CodegenOpts::All)?;
///   let mut verus = std::fs::File::create("src/tlv.rs")?;
///   verus.write_all(code.as_bytes())?;
///   Ok(())
/// }
/// ```
pub fn compile(
    file_name: &str,
    input: String,
    codegen_opt: codegen::CodegenOpts,
) -> Result<String, Box<dyn Error>> {
    let source = (file_name, &ariadne::Source::from(input.clone()));

    // parse the vest file
    println!("📜 Parsing the vest file...");
    match ast::from_str(&input) {
        Ok(mut ast) => {
            // elaborate the AST
            println!("🔨 Elaborating the AST...");
            elab::elaborate(&mut ast);

            // type check the AST
            println!("🔍 Type checking...");
            match type_check::check(&ast, source) {
                Ok(ctx) => {
                    // code gen to a file
                    // if there is no output file specified, use the same name as the name of input vest file

                    println!("📝 Generating the verus file...");
                    let ir: Vec<vestir::Definition> = ast
                        .clone()
                        .into_iter()
                        .map(vestir::Definition::from)
                        .collect();
                    let code = codegen::code_gen(&ir, &(&ctx).into(), codegen_opt);
                    println!("👏 Done!");

                    Ok(code)
                }
                Err(e) => {
                    eprintln!("❌ Type checking failed.");
                    Err(Box::new(e))
                }
            }
            // let ctx = type_check::check(&ast, source)?;
        }
        Err(e) => {
            let span = match e.location {
                InputLocation::Pos(pos) => pos..pos,
                InputLocation::Span(span) => span.0..span.1,
            };
            eprintln!("❌ Failed to parse the vest file.");
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
            Err(Box::new(VestError::ParsingError))
        }
    }
}

/// Compiles the given file and returns the resulting output.
///
/// # Example
/// ```rust
/// // build.rs
/// use std::error::Error;
/// use std::io::Write;
///
/// fn main() -> Result<(), Box<dyn Error>> {
///   println!("cargo::rerun-if-changed=src/tlv.vest");
///   let file_name = "src/tlv.vest";
///   let code = compile_file(file_name, CodegenOpts::All)?;
///   let mut verus = std::fs::File::create("src/tlv.rs")?;
///   verus.write_all(code.as_bytes())?;
///   Ok(())
/// }
/// ```
pub fn compile_file(
    file_name: &str,
    codegen: codegen::CodegenOpts,
) -> Result<String, Box<dyn Error>> {
    let vest = std::fs::read_to_string(file_name)?;
    compile(file_name, vest, codegen)
}

/// Compiles the given file and saves it to `output_file`.
///
/// # Example
/// ```rust
/// // build.rs
/// use std::error::Error;
///
/// fn main() -> Result<(), Box<dyn Error>> {
///   println!("cargo::rerun-if-changed=src/tlv.vest");
///   let input_file = "src/tlv.vest";
///   let output_file = "src/tlv.rs";
///   let code = compile_to(file_name, CodegenOpts::All, output_file)?;
///   Ok(())
/// }
/// ```
pub fn compile_to(
    input_file: &str,
    codegen: codegen::CodegenOpts,
    output_file: &str,
) -> Result<(), Box<dyn Error>> {
    let vest = std::fs::read_to_string(input_file)?;
    let code = compile(input_file, vest, codegen)?;
    let mut verus = std::fs::File::create(output_file)?;
    verus.write_all(code.as_bytes())?;
    Ok(())
}
