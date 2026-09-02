//! CMake build-system file generator for synta-generated C code.
//!
//! Produces a `CMakeLists.txt` (full or fragment) that:
//! - Defines each ASN.1 module as a CMake `STATIC`/`SHARED` library target.
//! - Expresses inter-module dependencies via `target_link_libraries`.
//! - Locates the synta library and sets the required C99 standard.

use crate::ast::Module;
use crate::naming::module_file_stem;
use crate::naming::to_pascal_case;
use std::fmt::Write;

/// Configuration for CMake file generation.
#[derive(Debug, Clone, Default)]
pub struct CMakeConfig {
    /// Path to the synta source tree (the directory that contains `include/`
    /// and `target/release/`).  When `None` the generated file uses a
    /// `SYNTA_ROOT` CMake cache variable that the user must supply on the
    /// `cmake` command line.
    pub synta_root: Option<String>,
    /// Build the generated library as `SHARED` instead of `STATIC`.
    pub shared_library: bool,
}

/// Generate a `CMakeLists.txt` for one or more ASN.1 modules.
///
/// `modules` is the full slice of parsed modules; `order` is the topological
/// generation order returned by [`crate::import_graph::topological_order`]
/// (dependencies-first).  Pass `&[0]` when there is only one module.
pub fn generate_cmake(
    modules: &[Module],
    order: &[usize],
    config: CMakeConfig,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut out = String::new();

    // ── Header ────────────────────────────────────────────────────────────────
    let module_names: Vec<&str> = order.iter().map(|&i| modules[i].name.as_str()).collect();
    let project_name = if modules.len() == 1 {
        to_pascal_case(modules[0].name.as_str())
    } else {
        // Use the last module in topological order (the primary "root" module
        // that imports all the others).
        to_pascal_case(modules[*order.last().unwrap()].name.as_str())
    };

    writeln!(
        out,
        "# Generated from ASN.1 module{} {}",
        if modules.len() == 1 { "" } else { "s" },
        module_names.join(", ")
    )?;
    writeln!(out, "# DO NOT EDIT - auto-generated code")?;
    writeln!(out)?;
    writeln!(out, "cmake_minimum_required(VERSION 3.10)")?;
    writeln!(out, "project({} C)", project_name)?;
    writeln!(out)?;
    writeln!(out, "set(CMAKE_C_STANDARD 99)")?;
    writeln!(out, "set(CMAKE_C_STANDARD_REQUIRED ON)")?;
    writeln!(out)?;
    writeln!(out, "if(MSVC)")?;
    writeln!(out, "    add_compile_options(/W4)")?;
    writeln!(out, "else()")?;
    writeln!(out, "    add_compile_options(-Wall -Wextra)")?;
    writeln!(out, "endif()")?;
    writeln!(out)?;

    // ── Synta location ────────────────────────────────────────────────────────
    writeln!(out, "# Locate the synta library.")?;
    writeln!(
        out,
        "# If the parent project already defines a Synta::Synta imported target,"
    )?;
    writeln!(out, "# this block is skipped automatically.")?;
    writeln!(out, "if(NOT TARGET Synta::Synta)")?;

    if let Some(ref root) = config.synta_root {
        writeln!(out, "    set(_synta_root \"{}\")", root)?;
    } else {
        writeln!(out, "    if(NOT DEFINED SYNTA_ROOT)")?;
        writeln!(out, "        set(SYNTA_ROOT \"\" CACHE PATH")?;
        writeln!(out, "            \"Root of the synta source tree (contains include/ and target/release/)\")")?;
        writeln!(out, "    endif()")?;
        writeln!(out, "    if(\"${{SYNTA_ROOT}}\" STREQUAL \"\")")?;
        writeln!(out, "        message(FATAL_ERROR")?;
        writeln!(
            out,
            "            \"SYNTA_ROOT is not set. Pass it on the cmake command line:\\n\""
        )?;
        writeln!(
            out,
            "            \"  cmake -DSYNTA_ROOT=/path/to/synta -S . -B build\")"
        )?;
        writeln!(out, "    endif()")?;
        writeln!(out, "    set(_synta_root \"${{SYNTA_ROOT}}\")")?;
    }

    writeln!(out, "    find_library(SYNTA_LIBRARY")?;
    writeln!(out, "        NAMES synta")?;
    writeln!(out, "        PATHS \"${{_synta_root}}/target/release\"")?;
    writeln!(out, "        NO_DEFAULT_PATH")?;
    writeln!(out, "    )")?;
    writeln!(out, "    if(NOT SYNTA_LIBRARY)")?;
    writeln!(out, "        message(FATAL_ERROR")?;
    writeln!(
        out,
        "            \"synta library not found under ${{_synta_root}}/target/release\\n\""
    )?;
    writeln!(out, "            \"Build it first: cd ${{_synta_root}} && cargo build --release --features ffi\")")?;
    writeln!(out, "    endif()")?;
    writeln!(out, "    add_library(Synta::Synta UNKNOWN IMPORTED)")?;
    writeln!(out, "    set_target_properties(Synta::Synta PROPERTIES")?;
    writeln!(out, "        IMPORTED_LOCATION \"${{SYNTA_LIBRARY}}\"")?;
    writeln!(
        out,
        "        INTERFACE_INCLUDE_DIRECTORIES \"${{_synta_root}}/include\""
    )?;
    writeln!(out, "    )")?;
    writeln!(out, "endif()")?;
    writeln!(out)?;

    // ── Platform link dependencies ─────────────────────────────────────────────
    writeln!(out, "# Platform-specific libraries required by libcsynta.")?;
    writeln!(out, "if(UNIX AND NOT APPLE)")?;
    writeln!(out, "    set(_synta_platform_libs pthread dl m)")?;
    writeln!(out, "elseif(APPLE)")?;
    writeln!(out, "    set(_synta_platform_libs pthread)")?;
    writeln!(out, "elseif(WIN32)")?;
    writeln!(out, "    set(_synta_platform_libs ws2_32 userenv bcrypt)")?;
    writeln!(out, "endif()")?;
    writeln!(out)?;

    // ── Library targets ───────────────────────────────────────────────────────
    let lib_type = if config.shared_library {
        "SHARED"
    } else {
        "STATIC"
    };

    // Build a map from module name to target name for dependency edges.
    let target_for: std::collections::HashMap<&str, String> = modules
        .iter()
        .map(|m| (m.name.as_str(), to_pascal_case(&m.name)))
        .collect();

    for &idx in order {
        let module = &modules[idx];
        let stem = module_file_stem(&module.name);
        let target = to_pascal_case(&module.name);

        writeln!(out, "# ASN.1 module: {}", module.name)?;
        writeln!(out, "add_library({} {}", target, lib_type)?;
        writeln!(out, "    {}.c", stem)?;
        writeln!(out, ")")?;
        writeln!(out, "target_include_directories({} PUBLIC", target)?;
        writeln!(out, "    $<BUILD_INTERFACE:${{CMAKE_CURRENT_LIST_DIR}}>")?;
        writeln!(out, "    $<INSTALL_INTERFACE:include>")?;
        writeln!(out, ")")?;

        // Collect inter-module deps that are in the known set.
        let module_deps: Vec<&str> = module
            .imports
            .iter()
            .filter_map(|imp| target_for.get(imp.module_name.as_str()).map(|t| t.as_str()))
            .collect();

        write!(out, "target_link_libraries({} PUBLIC", target)?;
        for dep in &module_deps {
            write!(out, "\n    {}", dep)?;
        }
        writeln!(out, "\n    Synta::Synta")?;
        writeln!(out, "    ${{_synta_platform_libs}}")?;
        writeln!(out, ")")?;
        writeln!(out)?;
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    #[test]
    fn test_single_module_cmake() {
        let m = parse("MyModule DEFINITIONS ::= BEGIN Foo ::= INTEGER END").unwrap();
        let out = generate_cmake(&[m], &[0], CMakeConfig::default()).unwrap();

        assert!(out.contains("cmake_minimum_required(VERSION 3.10)"));
        assert!(out.contains("project(MyModule C)"));
        assert!(out.contains("CMAKE_C_STANDARD 99"));
        assert!(out.contains("add_library(MyModule STATIC"));
        assert!(out.contains("my_module.c"));
        assert!(out.contains("Synta::Synta"));
        assert!(out.contains("SYNTA_ROOT"));
    }

    #[test]
    fn test_cmake_with_synta_root() {
        let m = parse("Cert DEFINITIONS ::= BEGIN END").unwrap();
        let config = CMakeConfig {
            synta_root: Some("/opt/synta".to_string()),
            shared_library: false,
        };
        let out = generate_cmake(&[m], &[0], config).unwrap();

        assert!(out.contains("set(_synta_root \"/opt/synta\")"));
        // SYNTA_ROOT cache variable block should not appear
        assert!(!out.contains("CACHE PATH"));
    }

    #[test]
    fn test_cmake_shared_library() {
        let m = parse("Foo DEFINITIONS ::= BEGIN END").unwrap();
        let config = CMakeConfig {
            shared_library: true,
            ..Default::default()
        };
        let out = generate_cmake(&[m], &[0], config).unwrap();
        assert!(out.contains("add_library(Foo SHARED"));
    }

    #[test]
    fn test_multi_module_cmake_deps() {
        let a = parse("ModA DEFINITIONS ::= BEGIN IMPORTS X FROM ModB; END").unwrap();
        let b = parse("ModB DEFINITIONS ::= BEGIN END").unwrap();
        // topological order: ModB (1) before ModA (0)
        let order = vec![1usize, 0usize];
        let out = generate_cmake(&[a, b], &order, CMakeConfig::default()).unwrap();

        // ModB target defined
        assert!(out.contains("add_library(ModB STATIC"));
        // ModA target defined
        assert!(out.contains("add_library(ModA STATIC"));
        // ModA links against ModB
        assert!(out.contains("target_link_libraries(ModA PUBLIC\n    ModB"));
    }
}
