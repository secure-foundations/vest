use std::collections::BTreeMap;
use std::env;
use std::error::Error;
use std::fs;
use std::path::PathBuf;

fn main() {
    if let Err(error) = run() {
        eprintln!("vps-asn1: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = env::args_os().skip(1);
    let mut input = None;
    let mut output = None;
    let mut encoding_rules = vps_asn1::EncodingRules::Der;
    let mut definition_rules = BTreeMap::new();

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
        if arg == "--rules" {
            let value = args.next().ok_or("expected `der` or `ber` after --rules")?;
            encoding_rules = match value.to_str() {
                Some("der") => vps_asn1::EncodingRules::Der,
                Some("ber") => vps_asn1::EncodingRules::Ber,
                _ => return Err("--rules must be either `der` or `ber`".into()),
            };
            continue;
        }
        if arg == "--der-definition" || arg == "--ber-definition" {
            let rule = if arg == "--der-definition" {
                vps_asn1::EncodingRules::Der
            } else {
                vps_asn1::EncodingRules::Ber
            };
            let name = args
                .next()
                .ok_or("expected an ASN.1 definition name after the rule override")?
                .into_string()
                .map_err(|_| "ASN.1 definition names must be valid UTF-8")?;
            if let Some(previous) = definition_rules.insert(name.clone(), rule) {
                if previous != rule {
                    return Err(format!("definition `{name}` was assigned both DER and BER").into());
                }
            }
            continue;
        }
        if input.replace(PathBuf::from(arg)).is_some() {
            return Err("expected exactly one ASN.1 input file".into());
        }
    }

    let input = input.ok_or("missing ASN.1 input file (try --help)")?;
    let source = fs::read_to_string(&input)?;
    let options = vps_asn1::CodegenOptions { encoding_rules };
    let generated = if definition_rules.is_empty() {
        vps_asn1::compile_with_options(&source, options)?
    } else {
        vps_asn1::compile_with_rule_overrides(&source, options, &definition_rules)?
    };
    if let Some(output) = output {
        fs::write(output, generated)?;
    } else {
        print!("{generated}");
    }
    Ok(())
}

fn print_help() {
    println!(
        "vps-asn1 - generate verified VPS BER or DER formats from ASN.1\n\n\
         Usage: vps-asn1 [OPTIONS] <SCHEMA.asn1>\n\n\
         Options:\n  -o, --output <FILE>          Write generated Rust to FILE\n      --rules <der|ber>         Select the default rules (default: der)\n      --der-definition <NAME>   Force one definition and its inherited closure to DER\n      --ber-definition <NAME>   Force one definition and its inherited closure to BER\n  -h, --help                   Print help"
    );
}
