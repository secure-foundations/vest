use std::env;
use std::error::Error;
use std::fs;
use std::path::PathBuf;

fn main() {
    if let Err(error) = run() {
        eprintln!("vestasn1: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = env::args_os().skip(1);
    let mut input = None;
    let mut output = None;

    while let Some(arg) = args.next() {
        if arg == "-h" || arg == "--help" {
            print_help();
            return Ok(());
        }
        if arg == "-o" || arg == "--output" {
            output = Some(PathBuf::from(
                args.next().ok_or("expected a path after --output")?,
            ));
            continue;
        }
        if input.replace(PathBuf::from(arg)).is_some() {
            return Err("expected exactly one ASN.1 input file".into());
        }
    }

    let input = input.ok_or("missing ASN.1 input file (try --help)")?;
    let source = fs::read_to_string(&input)?;
    let generated = vestasn1::compile(&source)?;
    if let Some(output) = output {
        fs::write(output, generated)?;
    } else {
        print!("{generated}");
    }
    Ok(())
}

fn print_help() {
    println!(
        "vestasn1 - generate verified Vest DER formats from ASN.1\n\n\
         Usage: vestasn1 [OPTIONS] <SCHEMA.asn1>\n\n\
         Options:\n  -o, --output <FILE>  Write generated Rust to FILE\n  -h, --help           Print help"
    );
}
