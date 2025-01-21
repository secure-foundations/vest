use std::fs::File;
use std::io::{BufReader, BufWriter};
use wasmbin::Module;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: {} <input> <output>", args[0]);
        std::process::exit(1);
    }

    // Parse
    let file = File::open(&args[1])?;
    let mut reader = BufReader::new(file);
    let module = Module::decode_from(reader)?;

    // Serialize
    let file = File::create(&args[2])?;
    let mut writer = BufWriter::new(file);
    module.encode_into(writer)?;

    Ok(())
}
