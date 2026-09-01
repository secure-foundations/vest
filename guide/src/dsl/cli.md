# Command-line interface

## Synopsis

```console
vest [OPTIONS] <VEST_FILE>
```

| Argument / option         | Meaning                                                                  |
| ------------------------- | ------------------------------------------------------------------------ |
| `<VEST_FILE>`             | the `.vest` file to compile (required)                                   |
| `-o`, `--output <OUTPUT>` | where to write the generated Rust (optional; defaults to the input path with its extension replaced, so `msg.vest` becomes `msg.rs`) |
| `-h`, `--help`            | print help                                                               |
| `-V`, `--version`         | print version                                                            |

A successful run should print the following five stages and exit zero:

```console
$ vest msg.vest -o src/msg.rs
📜 Parsing the vest file...
🔨 Elaborating the AST...
🔍 Type checking...
📝 Generating the verus file...
👏 Done!
```

## Generating from `build.rs`

For a project that keeps its `.vest` schema under version control and regenerates the Rust code on
change, we recommend a `build.rs` that calls the compiler.
Add `vest` as a build
dependency and use one of three entry points:

```rust,ignore
// build.rs
use std::error::Error;
use vest::compile_to;

fn main() -> Result<(), Box<dyn Error>> {
    println!("cargo::rerun-if-changed=src/msg.vest");
    compile_to("src/msg.vest", "src/msg.rs")?;
    Ok(())
}
```

| Function       | Signature                                                             | Use when                                                                  |
| -------------- | --------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| `compile`      | `(file_name: &str, input: String) -> Result<String, Box<dyn Error>>`  | the schema is already in memory; `file_name` is used only for diagnostics |
| `compile_file` | `(file_name: &str) -> Result<String, Box<dyn Error>>`                 | you want the generated code as a `String`                                 |
| `compile_to`   | `(input_file: &str, output_file: &str) -> Result<(), Box<dyn Error>>` | you want it written to disk                                               |

All three report diagnostics to stderr and return `Err` on failure.
