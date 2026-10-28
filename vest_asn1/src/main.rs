use clap::{Parser, ValueEnum};
use std::collections::BTreeMap;
use std::error::Error;
use std::fs;
use std::path::PathBuf;
use vest_asn1::{CodegenOptions, EncodingRules};

#[derive(Clone, Copy, ValueEnum)]
enum Rules {
    Der,
    Ber,
}

impl From<Rules> for EncodingRules {
    fn from(rules: Rules) -> Self {
        match rules {
            Rules::Der => Self::Der,
            Rules::Ber => Self::Ber,
        }
    }
}

/// Generate Vest parsers and serializers from one ASN.1 module.
#[derive(Parser)]
#[command(version)]
struct Args {
    /// ASN.1 schema to compile
    #[arg(value_name = "SCHEMA.asn1")]
    input: PathBuf,

    /// Write generated Rust to FILE instead of stdout
    #[arg(short, long, value_name = "FILE")]
    output: Option<PathBuf>,

    /// Default encoding rules
    #[arg(long, value_enum, default_value = "der")]
    rules: Rules,

    /// Use DER for NAME and its transitive dependencies (repeatable)
    #[arg(long, value_name = "NAME")]
    der_definition: Vec<String>,

    /// Use BER for NAME and its transitive dependencies (repeatable)
    #[arg(long, value_name = "NAME")]
    ber_definition: Vec<String>,
}

fn main() {
    if let Err(error) = run(Args::parse()) {
        eprintln!("vest_asn1: {error}");
        std::process::exit(1);
    }
}

fn run(args: Args) -> Result<(), Box<dyn Error>> {
    let mut definition_rules = BTreeMap::new();
    for (names, rule) in [
        (&args.der_definition, EncodingRules::Der),
        (&args.ber_definition, EncodingRules::Ber),
    ] {
        for name in names {
            if let Some(previous) = definition_rules.insert(name.clone(), rule) {
                if previous != rule {
                    return Err(format!("definition '{name}' was assigned both DER and BER").into());
                }
            }
        }
    }

    let source = fs::read_to_string(&args.input)
        .map_err(|error| format!("{}: {error}", args.input.display()))?;
    let options = CodegenOptions {
        encoding_rules: args.rules.into(),
    };
    let generated = vest_asn1::compile_with_rule_overrides(&source, options, &definition_rules)?;
    if let Some(output) = args.output {
        fs::write(&output, generated).map_err(|error| format!("{}: {error}", output.display()))?;
    } else {
        print!("{generated}");
    }
    Ok(())
}
