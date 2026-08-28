use std::{
    env, fs,
    path::{Path, PathBuf},
};

fn emit(name: &str, directory: &Path, output: &mut String) {
    let mut files: Vec<PathBuf> = fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("cms"))
        .collect();
    files.sort();
    output.push_str(&format!("pub static {name}: &[(&str, &[u8])] = &[\n"));
    for path in files {
        let label = path.file_name().unwrap().to_string_lossy();
        output.push_str(&format!(
            "    ({label:?}, include_bytes!({:?})),\n",
            path.canonicalize().unwrap()
        ));
    }
    output.push_str("];\n");
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpora/cms");
    let mut output = String::new();
    emit("PKITS", &root.join("pkits"), &mut output);
    emit("DSS", &root.join("dss"), &mut output);
    emit("RFC4134", &root.join("rfc4134"), &mut output);
    fs::write(
        Path::new(&env::var_os("OUT_DIR").unwrap()).join("cms_corpora.rs"),
        output,
    )
    .unwrap();
    println!("cargo:rerun-if-changed={}", root.display());
}
