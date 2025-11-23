use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    // Tell Cargo to rerun this build script if src/bitcoin.vest changes
    println!("cargo:rerun-if-changed=src/bitcoin.vest");

    // Get the output directory where generated files should be placed
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR environment variable not set");
    let out_path = PathBuf::from(&out_dir).join("bitcoin.rs");

    // Run the vest executable on src/bitcoin.vest
    let status = Command::new("vest")
        .arg("src/bitcoin.vest")
        .arg("--output")
        .arg(&out_path)
        .status()
        .expect("Failed to execute vest command");

    if !status.success() {
        panic!("vest command failed with status: {}", status);
    }

    // Post-process the generated file to convert inner attributes to outer attributes
    let content = fs::read_to_string(&out_path).expect("Failed to read generated file");

    let modified_content = content
        .replace("#![allow(warnings)]", "#[allow(warnings)]")
        .replace("#![allow(unused)]", "#[allow(unused)]");

    fs::write(&out_path, modified_content).expect("Failed to write modified file");
}
