//! Checked-in real-format corpora and their codec adapters.
use std::fs;
use std::path::{Path, PathBuf};

pub mod bitcoin;
pub mod cbor;
pub mod cms;
pub mod tls;

pub fn corpora_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("corpora")
}

pub(super) fn tsv_rows(path: &Path, columns: usize) -> Vec<Vec<String>> {
    let text = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    text.lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(|line| {
            let row: Vec<String> = line.split('\t').map(str::to_owned).collect();
            assert_eq!(
                row.len(),
                columns,
                "malformed row in {}: {line}",
                path.display()
            );
            row
        })
        .collect()
}

/// Sorted depth-first traversal; callers can additionally request global order.
fn files(dir: &Path, extension: &str) -> Vec<PathBuf> {
    let mut paths: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.sort();
    let mut found = Vec::new();
    for path in paths {
        if path.is_dir() {
            found.extend(files(&path, extension));
        } else if path.extension().is_some_and(|ext| ext == extension) {
            found.push(path);
        }
    }
    found
}
