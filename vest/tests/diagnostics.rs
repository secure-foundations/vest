//! Exercise the CLI boundary: a rejected input must not crash, spin, or write
//! half a Rust module. The in-process tests can then focus on individual passes.
use std::{
    fmt::Write as _,
    fs::{self, File},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

fn fixtures(directory: &Path) -> Vec<PathBuf> {
    let mut files = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "vest"))
        .collect::<Vec<_>>();
    files.sort_unstable();
    files
}

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("vest-test-{}-{timestamp}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn check_cli(input: &Path, expected_error: Option<&str>) {
    let scratch = Scratch::new();
    let output = scratch.0.join("generated.rs");
    let log = scratch.0.join("stderr");
    let mut child = Command::new(env!("CARGO_BIN_EXE_vest"))
        .arg(input)
        .arg("-o")
        .arg(&output)
        .stdout(Stdio::null())
        .stderr(File::create(&log).unwrap())
        .spawn()
        .unwrap();
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > Duration::from_secs(5) {
            let _ = child.kill();
            let _ = child.wait();
            panic!("{}: compiler did not terminate", input.display());
        }
        thread::sleep(Duration::from_millis(5));
    };
    let log = fs::read_to_string(log).unwrap();
    match expected_error {
        Some(message) => {
            assert_eq!(status.code(), Some(1), "{}: {log}", input.display());
            assert!(log.contains(message), "{}: {log}", input.display());
            assert!(!output.exists(), "rejection wrote {}", output.display());
        }
        None => {
            assert!(status.success(), "{}: {log}", input.display());
            assert!(fs::read_to_string(output).unwrap().contains("verus! {"));
        }
    }
}

#[test]
fn bad_fixtures() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let files = fixtures(&root.join("../vest_tests/bad"));
    assert!(!files.is_empty());
    for input in files {
        check_cli(&input, Some("Error"));
    }
}

#[test]
fn semantic_boundaries() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/diagnostics");
    for (filename, message) in [
        ("macro_cycle.vest", "recursive expansion of macro"),
        ("macro_arity.vest", "expects 0 arguments, got 1"),
        ("rust_name_collision.vest", "both generate the Rust name"),
        (
            "sum_import_collision.vest",
            "would generate Rust name `Sum`",
        ),
        ("const_name_collision.vest", "duplicate format definition"),
        ("wildcard_nested_path.vest", "invalid nested field access"),
    ] {
        check_cli(&root.join(filename), Some(message));
    }
}

#[test]
fn open_enum_needs_a_spare_rust_discriminant() {
    let scratch = Scratch::new();
    let input = scratch.0.join("full_enum.vest");
    let mut source = String::from("full_enum = enum {\n");
    for value in 0..=u8::MAX {
        writeln!(source, "    V{value} = {value}u8,").unwrap();
    }
    source.push_str("    ...\n}\n");
    fs::write(&input, source).unwrap();
    check_cli(&input, Some("open enum has no spare Rust discriminant"));
}

#[test]
fn reported_inputs() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let files = fixtures(&root.join("tests/fixtures/reported"));
    assert_eq!(files.len(), 49);
    for input in files {
        let name = input.file_stem().unwrap().to_str().unwrap();
        let error = match name {
            "issue58_02" => Some("a range needs at least one bound"),
            "issue58_03" | "issue58_04" | "issue58_08" => Some("integer width exceeds"),
            "issue58_05" | "issue58_06" => Some("integer literal exceeds"),
            "issue58_07" | "issue58_13" | "issue58_14" => Some("length does not fit"),
            "issue58_09" | "issue58_10" | "issue58_11" | "issue58_12" => {
                Some("choice patterns must all be")
            }
            "issue58_26" | "issue58_28" | "issue58_29" => None,
            "issue59_01" | "issue60_16" => Some("recursive type aliases"),
            "issue60_01" => Some("duplicate enum value"),
            "issue60_02" | "issue60_03" | "issue60_04" => Some("would generate Rust name `Bits`"),
            "issue60_06" => Some("repetition child can accept empty input"),
            "issue60_05" => Some("conflicts with a variant of the field's enum type"),
            "issue60_07" => Some("would generate Rust name `R`"),
            "issue60_08" => Some("invalid constant length arithmetic"),
            "issue60_11" => Some("unsupported integer type"),
            "issue60_12" => Some("duplicate enum variant"),
            "issue60_13" => Some("conflicts with an imported constructor"),
            "issue60_14" => Some("optional child can accept empty input"),
            "issue60_17" => Some("invalid field name"),
            "issue60_18" => Some("invalid enum variant name"),
            name if name.starts_with("issue60_") => None,
            _ => Some("Error"),
        };
        check_cli(&input, error);
    }
}
