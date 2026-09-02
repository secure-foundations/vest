use std::fs;
use std::path::{Path, PathBuf};

fn markdown_files(dir: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).expect("read guide source directory") {
        let path = entry.expect("read guide entry").path();
        if path.is_dir() {
            markdown_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "md") {
            files.push(path);
        }
    }
}

fn vest_blocks(markdown: &str) -> Vec<String> {
    let mut blocks: Vec<String> = Vec::new();
    let mut current: Option<String> = None;

    for line in markdown.lines() {
        match &mut current {
            Some(code) if line.trim() == "```" => {
                blocks.push(std::mem::take(code));
                current = None;
            }
            Some(code) => {
                code.push_str(line);
                code.push('\n');
            }
            None if line.trim() == "```vest" => current = Some(String::new()),
            // `vest,ignore` is reserved for deliberately incomplete syntax fragments.
            None => {}
        }
    }

    assert!(current.is_none(), "unterminated Vest code fence");
    blocks
}

#[test]
fn every_complete_vest_snippet_compiles() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    markdown_files(&source, &mut files);
    files.sort();

    let mut checked = 0;
    for file in files {
        let markdown = fs::read_to_string(&file).expect("read guide chapter");
        for (index, snippet) in vest_blocks(&markdown).into_iter().enumerate() {
            let name = format!("{}:vest-block-{}", file.display(), index + 1);
            if let Err(error) = vest::compile(&name, snippet) {
                panic!("Vest snippet {name} did not compile: {error}");
            }
            checked += 1;
        }
    }

    assert!(checked >= 30, "expected substantial checked Vest coverage, found {checked}");
}
