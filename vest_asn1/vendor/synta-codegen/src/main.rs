//! ASN.1 to Rust/C code generator CLI tool.
//!
//! Parses one or more ASN.1 module files and generates either Rust code
//! (using `synta` derive macros) or C code (using the `libcsynta` FFI).
//!
//! C output is controlled by the `--emit` flag: `header` (default), `impl`,
//! or `both`.  Build-system integration files (`CMakeLists.txt`,
//! `meson.build`) can be generated for multi-module C projects via
//! `--cmake` / `--meson`.

use std::env;
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use synta_codegen::{
    detect_cycles, generate_c_with_config, generate_cmake, generate_meson, generate_with_config,
    module_file_stem, topological_order, CCodeGenConfig, CImplConfig, CMakeConfig, CodeGenConfig,
    MesonConfig, PatternMode,
};
use synta_codegen::{generate_c_impl, parse};

/// Controls which C output artifacts are written when using `--output-dir`.
#[derive(Debug, Clone, Default, PartialEq)]
enum EmitMode {
    /// Write only header (`.h`) files.  This is the default.
    #[default]
    Header,
    /// Write only implementation (`.c`) files.
    Impl,
    /// Write both header (`.h`) and implementation (`.c`) files.
    Both,
}

/// Print usage information to stderr.
///
/// Called when `-h` / `--help` is passed or when the user provides no input
/// files.  All recognised flags are listed, grouped by language target, with
/// brief usage examples at the end.
fn print_usage() {
    eprintln!("Usage: synta-codegen [OPTIONS] <input.asn1> [extra.asn1 ...]");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -o, --output <file>         Write output to file (default: stdout)");
    eprintln!("  --output-dir <dir>          Write one file per module into <dir>");
    eprintln!("  --lang <language>           Target language: rust (default) or c");
    eprintln!("  --c                         Shorthand for --lang c");
    eprintln!("  --check-imports             Check for circular imports and exit (no codegen)");
    eprintln!();
    eprintln!("Rust-specific options:");
    eprintln!("  --crate-imports             Generate use statements with 'crate::' prefix");
    eprintln!("  --super-imports             Generate use statements with 'super::' prefix");
    eprintln!("  --module-prefix <prefix>    Generate use statements with custom prefix");
    eprintln!(
        "  --use-core                  Emit core::convert::TryFrom instead of std:: (no_std)"
    );
    eprintln!();
    eprintln!("C-specific options:");
    eprintln!("  --header-path <path>        Path to synta.h (default: \"synta.h\")");
    eprintln!("  --with-helpers              Generate helper functions");
    eprintln!(
        "  --arena                     Generate SyntaArena type and _decode_arena() variants"
    );
    eprintln!("  --impl <header>             Single-file: generate .c impl including <header>");
    eprintln!("  --emit <artifacts>          With --output-dir: header (default), impl, or both");
    eprintln!(
        "  --with-regex                Validate PATTERN constraints via POSIX ERE (with impl)"
    );
    eprintln!("  --with-pcre                 Validate PATTERN constraints via PCRE2 (with impl)");
    eprintln!("  --with-containing           Validate CONTAINING constraints (with impl)");
    eprintln!(
        "  --cmake                     Generate CMakeLists.txt; with --output-dir also emits C sources"
    );
    eprintln!(
        "  --meson                     Generate meson.build; with --output-dir also emits C sources"
    );
    eprintln!("  --shared                    Use SHARED library type in generated build files");
    eprintln!("  --synta-root <dir>          Embed synta root path in generated build files");
    eprintln!();
    eprintln!("General options:");
    eprintln!("  -h, --help                  Show this help message");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  synta-codegen schema.asn1");
    eprintln!("  synta-codegen schema.asn1 -o generated.rs");
    eprintln!("  synta-codegen schema.asn1 --c -o generated.h");
    eprintln!("  synta-codegen schema.asn1 --c --impl generated.h -o generated.c");
    eprintln!("  synta-codegen schema.asn1 --lang c --with-helpers -o generated.h");
    eprintln!("  synta-codegen schema.asn1 --cmake -o CMakeLists.txt");
    eprintln!("  synta-codegen schema.asn1 --meson -o meson.build");
    eprintln!("  synta-codegen schema.asn1 --crate-imports");
    eprintln!("  synta-codegen schema.asn1 --module-prefix my_lib::types");
    eprintln!("  synta-codegen a.asn1 b.asn1 --check-imports");
    eprintln!("  synta-codegen a.asn1 b.asn1 c.asn1 --c --output-dir ./generated");
    eprintln!("  synta-codegen a.asn1 b.asn1 c.asn1 --c --emit both --output-dir ./generated");
    eprintln!("  synta-codegen a.asn1 b.asn1 c.asn1 --cmake --output-dir ./generated");
    eprintln!("  synta-codegen a.asn1 b.asn1 c.asn1 --meson --output-dir ./generated");
    eprintln!("  cat schema.asn1 | synta-codegen -o generated.rs");
}

/// Parse CLI arguments, read ASN.1 schema files, and invoke the appropriate
/// code-generator backend.
///
/// Exits with code 1 on any unrecoverable error: unknown flags, missing
/// required arguments, file I/O errors, ASN.1 parse errors, or circular
/// import cycles detected among the provided modules.
fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Error: No input file specified");
        eprintln!();
        print_usage();
        std::process::exit(1);
    }

    let mut input_files: Vec<String> = Vec::new();
    let mut output_file: Option<String> = None;
    let mut output_dir: Option<String> = None;
    let mut target_lang = "rust".to_string();
    let mut module_prefix: Option<String> = None;
    let mut use_core = false;
    let mut header_path: Option<String> = None;
    let mut with_helpers = false;
    let mut with_arena = false;
    let mut impl_header: Option<String> = None;
    let mut emit_mode = EmitMode::Header;
    let mut with_regex = false;
    let mut with_pcre = false;
    let mut with_containing = false;
    let mut check_imports_only = false;
    let mut generate_cmake_file = false;
    let mut generate_meson_file = false;
    let mut cmake_synta_root: Option<String> = None;
    let mut cmake_shared = false;
    let mut i = 1;

    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_usage();
                return;
            }
            "-o" | "--output" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: -o/--output requires a filename");
                    std::process::exit(1);
                }
                output_file = Some(args[i + 1].clone());
                i += 2;
            }
            "--lang" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --lang requires a value (rust or c)");
                    std::process::exit(1);
                }
                target_lang = args[i + 1].clone();
                if target_lang != "rust" && target_lang != "c" {
                    eprintln!("Error: --lang must be 'rust' or 'c'");
                    std::process::exit(1);
                }
                i += 2;
            }
            "--c" => {
                target_lang = "c".to_string();
                i += 1;
            }
            "--check-imports" => {
                check_imports_only = true;
                i += 1;
            }
            "--output-dir" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --output-dir requires a directory path");
                    std::process::exit(1);
                }
                output_dir = Some(args[i + 1].clone());
                i += 2;
            }
            "--crate-imports" => {
                module_prefix = Some("crate".to_string());
                i += 1;
            }
            "--super-imports" => {
                module_prefix = Some("super".to_string());
                i += 1;
            }
            "--module-prefix" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --module-prefix requires a value");
                    std::process::exit(1);
                }
                module_prefix = Some(args[i + 1].clone());
                i += 2;
            }
            "--use-core" => {
                use_core = true;
                i += 1;
            }
            "--header-path" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --header-path requires a value");
                    std::process::exit(1);
                }
                header_path = Some(args[i + 1].clone());
                i += 2;
            }
            "--with-helpers" => {
                with_helpers = true;
                i += 1;
            }
            "--arena" => {
                with_arena = true;
                i += 1;
            }
            "--cmake" => {
                generate_cmake_file = true;
                target_lang = "c".to_string();
                i += 1;
            }
            "--meson" => {
                generate_meson_file = true;
                target_lang = "c".to_string();
                i += 1;
            }
            "--shared" => {
                cmake_shared = true;
                i += 1;
            }
            "--synta-root" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --synta-root requires a directory path");
                    std::process::exit(1);
                }
                cmake_synta_root = Some(args[i + 1].clone());
                i += 2;
            }
            "--impl" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --impl requires a header filename");
                    std::process::exit(1);
                }
                let header = args[i + 1].clone();
                if header.contains('"') || header.contains('\n') {
                    eprintln!("Error: --impl header filename must not contain '\"' or newline");
                    std::process::exit(1);
                }
                impl_header = Some(header);
                target_lang = "c".to_string();
                i += 2;
            }
            "--emit" => {
                if i + 1 >= args.len() {
                    eprintln!("Error: --emit requires a value (header, impl, or both)");
                    std::process::exit(1);
                }
                emit_mode = match args[i + 1].as_str() {
                    "header" => EmitMode::Header,
                    "impl" => EmitMode::Impl,
                    "both" => EmitMode::Both,
                    v => {
                        eprintln!(
                            "Error: --emit must be 'header', 'impl', or 'both' (got '{}')",
                            v
                        );
                        std::process::exit(1);
                    }
                };
                i += 2;
            }
            "--with-regex" => {
                if with_pcre {
                    eprintln!("Error: --with-regex and --with-pcre are mutually exclusive");
                    std::process::exit(1);
                }
                with_regex = true;
                i += 1;
            }
            "--with-pcre" => {
                if with_regex {
                    eprintln!("Error: --with-regex and --with-pcre are mutually exclusive");
                    std::process::exit(1);
                }
                with_pcre = true;
                i += 1;
            }
            "--with-containing" => {
                with_containing = true;
                i += 1;
            }
            arg if arg.starts_with('-') => {
                eprintln!("Error: Unknown option: {}", arg);
                eprintln!();
                print_usage();
                std::process::exit(1);
            }
            arg => {
                input_files.push(arg.to_string());
                i += 1;
            }
        }
    }

    // Validate conflicting option combinations.
    if impl_header.is_some() && output_dir.is_some() && input_files.len() > 1 {
        eprintln!("Error: --impl is not compatible with --output-dir and multiple input files.");
        eprintln!("       Use --emit both with --output-dir to generate paired .h and .c files.");
        std::process::exit(1);
    }
    if emit_mode != EmitMode::Header && output_dir.is_none() {
        eprintln!("Error: --emit impl/both requires --output-dir");
        std::process::exit(1);
    }

    // Warn about flags that are irrelevant to the active target language.
    if target_lang == "c" {
        if module_prefix.is_some() {
            eprintln!("Warning: --crate-imports/--super-imports/--module-prefix has no effect with --lang c");
        }
        if use_core {
            eprintln!("Warning: --use-core has no effect with --lang c");
        }
    }
    if target_lang == "rust" {
        if header_path.is_some() {
            eprintln!("Warning: --header-path has no effect with --lang rust");
        }
        if with_helpers {
            eprintln!("Warning: --with-helpers has no effect with --lang rust");
        }
        if with_arena {
            eprintln!("Warning: --arena has no effect with --lang rust");
        }
        if with_regex {
            eprintln!("Warning: --with-regex has no effect with --lang rust");
        }
        if with_pcre {
            eprintln!("Warning: --with-pcre has no effect with --lang rust");
        }
        if with_containing {
            eprintln!("Warning: --with-containing has no effect with --lang rust");
        }
        if cmake_shared {
            eprintln!("Warning: --shared has no effect with --lang rust");
        }
        if cmake_synta_root.is_some() {
            eprintln!("Warning: --synta-root has no effect with --lang rust");
        }
        if emit_mode != EmitMode::Header {
            eprintln!("Warning: --emit has no effect with --lang rust");
        }
    }

    // Parse all provided input files (or stdin when none given).
    let mut all_modules = Vec::new();

    if input_files.is_empty() {
        // Read from stdin
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).unwrap_or_else(|e| {
            eprintln!("Error reading from stdin: {}", e);
            std::process::exit(1);
        });
        let m = parse(&buffer).unwrap_or_else(|e| {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        });
        all_modules.push(m);
    } else {
        for file in &input_files {
            let src = fs::read_to_string(file).unwrap_or_else(|e| {
                eprintln!("Error reading file '{}': {}", file, e);
                std::process::exit(1);
            });
            let m = parse(&src).unwrap_or_else(|e| {
                eprintln!("Parse error in '{}': {}", file, e);
                std::process::exit(1);
            });
            all_modules.push(m);
        }
    }

    // Detect circular imports across all provided modules.
    // Always run when >1 module, or when explicitly requested.
    if all_modules.len() > 1 || check_imports_only {
        let cycles = detect_cycles(&all_modules);
        if !cycles.is_empty() {
            eprintln!(
                "Error: {} circular import cycle{} detected:",
                cycles.len(),
                if cycles.len() == 1 { "" } else { "s" }
            );
            for cycle in &cycles {
                eprintln!("  {}", cycle.display());
            }
            eprintln!();
            eprintln!("Fix the import cycle(s) before generating code.");
            std::process::exit(1);
        }

        if check_imports_only {
            // Show the computed topological generation order.
            let order = topological_order(&all_modules);
            eprintln!("No circular imports detected.");
            eprintln!("Generation order (dependencies first):");
            for (step, &idx) in order.iter().enumerate() {
                eprintln!("  {}. {}", step + 1, all_modules[idx].name);
            }
            return;
        }
    }

    // Determine the topological generation order once, used by both branches.
    let order: Vec<usize> = if all_modules.len() > 1 {
        topological_order(&all_modules)
    } else {
        vec![0]
    };

    // Build the pattern mode for C impl generation.
    let pattern_mode = if with_pcre {
        PatternMode::Pcre2
    } else if with_regex {
        PatternMode::Posix
    } else {
        PatternMode::Skip
    };

    // --output-dir: write one file per module (works for single or multiple modules).
    if let Some(ref dir) = output_dir {
        fs::create_dir_all(dir).unwrap_or_else(|e| {
            eprintln!("Error creating output directory '{}': {}", dir, e);
            std::process::exit(1);
        });

        // When generating a build system file alongside C sources, default to
        // Both so the build file's .c references are always satisfied.
        let effective_emit = if (generate_cmake_file || generate_meson_file) && target_lang == "c" {
            EmitMode::Both
        } else {
            emit_mode
        };

        if generate_cmake_file {
            let cmake_cfg = CMakeConfig {
                synta_root: cmake_synta_root.clone(),
                shared_library: cmake_shared,
            };
            let cmake_code = generate_cmake(&all_modules, &order, cmake_cfg).unwrap_or_else(|e| {
                eprintln!("CMake generation error: {}", e);
                std::process::exit(1);
            });
            let cmake_path = PathBuf::from(dir).join("CMakeLists.txt");
            fs::write(&cmake_path, &cmake_code).unwrap_or_else(|e| {
                eprintln!("Error writing '{}': {}", cmake_path.display(), e);
                std::process::exit(1);
            });
            eprintln!("Generated CMakeLists.txt -> {}", cmake_path.display());
            // Continue: generate C source files below.
        }

        if generate_meson_file {
            let meson_cfg = MesonConfig {
                synta_root: cmake_synta_root.clone(),
                shared_library: cmake_shared,
            };
            let meson_code = generate_meson(&all_modules, &order, meson_cfg).unwrap_or_else(|e| {
                eprintln!("Meson generation error: {}", e);
                std::process::exit(1);
            });
            let meson_path = PathBuf::from(dir).join("meson.build");
            fs::write(&meson_path, &meson_code).unwrap_or_else(|e| {
                eprintln!("Error writing '{}': {}", meson_path.display(), e);
                std::process::exit(1);
            });
            eprintln!("Generated meson.build -> {}", meson_path.display());
            // Continue: generate C source files below.
        }

        for &idx in &order {
            let module = &all_modules[idx];
            let stem = module_file_stem(&module.name);

            match target_lang.as_str() {
                "rust" => {
                    let cfg = CodeGenConfig {
                        module_path_prefix: module_prefix.clone(),
                        use_core,
                        ..Default::default()
                    };
                    let code = generate_with_config(module, cfg).unwrap_or_else(|e| {
                        eprintln!("Code generation error for {}: {}", module.name, e);
                        std::process::exit(1);
                    });
                    let out_path = PathBuf::from(dir).join(format!("{}.rs", stem));
                    fs::write(&out_path, &code).unwrap_or_else(|e| {
                        eprintln!("Error writing '{}': {}", out_path.display(), e);
                        std::process::exit(1);
                    });
                    eprintln!("Generated {} -> {}", module.name, out_path.display());
                }
                "c" => {
                    if matches!(effective_emit, EmitMode::Header | EmitMode::Both) {
                        let mut cfg = CCodeGenConfig::default();
                        if let Some(ref path) = header_path {
                            cfg.synta_header_path = Some(path.clone());
                        }
                        cfg.generate_helpers = with_helpers;
                        cfg.arena_mode = with_arena;
                        let code = generate_c_with_config(module, cfg).unwrap_or_else(|e| {
                            eprintln!("Code generation error for {}: {}", module.name, e);
                            std::process::exit(1);
                        });
                        let out_path = PathBuf::from(dir).join(format!("{}.h", stem));
                        fs::write(&out_path, &code).unwrap_or_else(|e| {
                            eprintln!("Error writing '{}': {}", out_path.display(), e);
                            std::process::exit(1);
                        });
                        eprintln!("Generated {} header -> {}", module.name, out_path.display());
                    }
                    if matches!(effective_emit, EmitMode::Impl | EmitMode::Both) {
                        let impl_cfg = CImplConfig {
                            header_file: format!("{}.h", stem),
                            arena_mode: with_arena,
                            pattern_mode: pattern_mode.clone(),
                            with_containing,
                        };
                        let code = generate_c_impl(module, impl_cfg).unwrap_or_else(|e| {
                            eprintln!("Code generation error for {}: {}", module.name, e);
                            std::process::exit(1);
                        });
                        let out_path = PathBuf::from(dir).join(format!("{}.c", stem));
                        fs::write(&out_path, &code).unwrap_or_else(|e| {
                            eprintln!("Error writing '{}': {}", out_path.display(), e);
                            std::process::exit(1);
                        });
                        eprintln!("Generated {} impl -> {}", module.name, out_path.display());
                    }
                }
                _ => unreachable!(),
            }
        }
        return;
    }

    // Single-file generation (no --output-dir): use the first (primary) module.
    // When multiple input files are provided without --output-dir, only the
    // first parsed module is used; prefer --output-dir for multi-module output.
    let module = all_modules.into_iter().next().unwrap_or_else(|| {
        eprintln!("Error: No modules parsed");
        std::process::exit(1);
    });

    // CMake generation (single module, to stdout or -o).
    if generate_cmake_file {
        let cmake_cfg = CMakeConfig {
            synta_root: cmake_synta_root,
            shared_library: cmake_shared,
        };
        let cmake_code = generate_cmake(std::slice::from_ref(&module), &[0], cmake_cfg)
            .unwrap_or_else(|e| {
                eprintln!("CMake generation error: {}", e);
                std::process::exit(1);
            });
        if let Some(file) = output_file {
            fs::write(&file, cmake_code).unwrap_or_else(|e| {
                eprintln!("Error writing to file '{}': {}", file, e);
                std::process::exit(1);
            });
            eprintln!("Generated CMakeLists.txt written to: {}", file);
        } else {
            print!("{}", cmake_code);
        }
        return;
    }

    // Meson generation (single module, to stdout or -o).
    if generate_meson_file {
        let meson_cfg = MesonConfig {
            synta_root: cmake_synta_root,
            shared_library: cmake_shared,
        };
        let meson_code = generate_meson(std::slice::from_ref(&module), &[0], meson_cfg)
            .unwrap_or_else(|e| {
                eprintln!("Meson generation error: {}", e);
                std::process::exit(1);
            });
        if let Some(file) = output_file {
            fs::write(&file, meson_code).unwrap_or_else(|e| {
                eprintln!("Error writing to file '{}': {}", file, e);
                std::process::exit(1);
            });
            eprintln!("Generated meson.build written to: {}", file);
        } else {
            print!("{}", meson_code);
        }
        return;
    }

    // Generate code based on target language.
    let code = match target_lang.as_str() {
        "rust" => {
            let config = CodeGenConfig {
                module_path_prefix: module_prefix,
                use_core,
                ..Default::default()
            };
            generate_with_config(&module, config).unwrap_or_else(|e| {
                eprintln!("Code generation error: {}", e);
                std::process::exit(1);
            })
        }
        "c" => {
            if let Some(header) = impl_header {
                // Generate implementation file (.c).
                let config = CImplConfig {
                    header_file: header,
                    arena_mode: with_arena,
                    pattern_mode,
                    with_containing,
                };
                generate_c_impl(&module, config).unwrap_or_else(|e| {
                    eprintln!("Code generation error: {}", e);
                    std::process::exit(1);
                })
            } else {
                // Generate header file (.h).
                let mut config = CCodeGenConfig::default();
                if let Some(path) = header_path {
                    config.synta_header_path = Some(path);
                }
                config.generate_helpers = with_helpers;
                config.arena_mode = with_arena;
                generate_c_with_config(&module, config).unwrap_or_else(|e| {
                    eprintln!("Code generation error: {}", e);
                    std::process::exit(1);
                })
            }
        }
        _ => unreachable!(),
    };

    // Write output.
    if let Some(file) = output_file {
        fs::write(&file, code).unwrap_or_else(|e| {
            eprintln!("Error writing to file '{}': {}", file, e);
            std::process::exit(1);
        });
        let lang_name = if target_lang == "rust" { "Rust" } else { "C" };
        eprintln!("Generated {} code written to: {}", lang_name, file);
    } else {
        print!("{}", code);
    }
}
