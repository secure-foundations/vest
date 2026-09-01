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

fn markdown_destinations(markdown: &str) -> impl Iterator<Item = &str> {
    markdown
        .split("](")
        .skip(1)
        .filter_map(|tail| tail.split_once(')').map(|(destination, _)| destination))
        .map(|destination| destination.split_whitespace().next().unwrap_or(destination))
        .map(|destination| destination.trim_matches(['<', '>']))
}

#[test]
fn local_markdown_links_resolve() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    markdown_files(&source, &mut files);

    for file in files {
        let markdown = fs::read_to_string(&file).expect("read guide chapter");
        for destination in markdown_destinations(&markdown) {
            let path = destination.split('#').next().unwrap_or(destination);
            if path.is_empty()
                || path.starts_with("http://")
                || path.starts_with("https://")
                || path.starts_with("mailto:")
                || !path.ends_with(".md")
            {
                continue;
            }

            let resolved = file.parent().expect("chapter has a parent").join(path);
            assert!(
                resolved.is_file(),
                "{} links to missing local chapter {destination}",
                file.display()
            );
        }
    }
}
