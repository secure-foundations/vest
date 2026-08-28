//! Meson build-system file generator for synta-generated C code.
//!
//! Produces a `meson.build` file that:
//! - Defines each ASN.1 module as a Meson `library()` target.
//! - Declares a companion `*_dep` dependency object for each target.
//! - Expresses inter-module dependencies via those dependency objects.
//! - Locates the synta library and enforces the C99 standard.

use crate::ast::Module;
use crate::naming::{module_file_stem, to_pascal_case};
use std::fmt::Write;

/// Configuration for Meson file generation.
#[derive(Debug, Clone, Default)]
pub struct MesonConfig {
    /// Path to the synta source tree (the directory that contains `include/`
    /// and `target/release/`).  When `None` the generated file uses a
    /// `dependency('synta')` call (resolved by pkg-config or a wrap file).
    pub synta_root: Option<String>,
    /// Build the generated library as `'shared_library'` instead of
    /// `'library'` (which defaults to the build-system preference).
    pub shared_library: bool,
}

/// Generate a `meson.build` for one or more ASN.1 modules.
///
/// `modules` is the full slice of parsed modules; `order` is the topological
/// generation order returned by [`crate::import_graph::topological_order`]
/// (dependencies-first).  Pass `&[0]` when there is only one module.
pub fn generate_meson(
    modules: &[Module],
    order: &[usize],
    config: MesonConfig,
) -> Result<String, Box<dyn std::error::Error>> {
    let mut out = String::new();

    // ── Header ────────────────────────────────────────────────────────────────
    let module_names: Vec<&str> = order.iter().map(|&i| modules[i].name.as_str()).collect();
    // Project name: snake_case of the primary (last-in-topo) module.
    let primary_idx = *order.last().unwrap();
    let project_name = module_file_stem(&modules[primary_idx].name);

    writeln!(
        out,
        "# Generated from ASN.1 module{} {}",
        if modules.len() == 1 { "" } else { "s" },
        module_names.join(", ")
    )?;
    writeln!(out, "# DO NOT EDIT - auto-generated code")?;
    writeln!(out)?;
    writeln!(out, "project('{}', 'c',", project_name)?;
    writeln!(out, "  default_options: ['c_std=c99', 'warning_level=2'],")?;
    writeln!(out, ")")?;
    writeln!(out)?;
    writeln!(out, "cc = meson.get_compiler('c')")?;
    writeln!(out)?;

    // ── Synta dependency ──────────────────────────────────────────────────────
    writeln!(
        out,
        "# ── Synta dependency ────────────────────────────────────────────────────────"
    )?;
    if let Some(ref root) = config.synta_root {
        writeln!(out, "_synta_lib = cc.find_library('synta',")?;
        writeln!(out, "  dirs: '{}' / 'target' / 'release',", root)?;
        writeln!(out, "  required: true,")?;
        writeln!(out, ")")?;
        writeln!(out, "synta_dep = declare_dependency(")?;
        writeln!(out, "  dependencies: _synta_lib,")?;
        writeln!(
            out,
            "  include_directories: include_directories('{}' / 'include'),",
            root
        )?;
        writeln!(out, ")")?;
    } else {
        writeln!(
            out,
            "# Resolved via pkg-config, a wrap file, or a parent subproject."
        )?;
        writeln!(
            out,
            "# If synta is not installed system-wide, specify its location with:"
        )?;
        writeln!(out, "#   meson setup build -Dsynta_root=/path/to/synta")?;
        writeln!(out, "# and add the following option to your meson.options:")?;
        writeln!(out, "#   option('synta_root', type: 'string', value: '',")?;
        writeln!(out, "#     description: 'Root of the synta source tree')")?;
        writeln!(out, "synta_dep = dependency('synta')")?;
    }
    writeln!(out)?;

    // ── Library function ──────────────────────────────────────────────────────
    let lib_fn = if config.shared_library {
        "shared_library"
    } else {
        "library"
    };

    // Map module name → dep variable name (for dependency edges).
    let dep_var_for: std::collections::HashMap<&str, String> = modules
        .iter()
        .map(|m| {
            let stem = module_file_stem(&m.name);
            (m.name.as_str(), format!("{}_dep", stem))
        })
        .collect();

    // ── Library targets ───────────────────────────────────────────────────────
    for &idx in order {
        let module = &modules[idx];
        let stem = module_file_stem(&module.name);
        let pascal = to_pascal_case(&module.name);
        let lib_var = format!("{}_lib", stem);
        let dep_var = format!("{}_dep", stem);

        // Inter-module deps that are in the known set.
        let module_deps: Vec<&str> = module
            .imports
            .iter()
            .filter_map(|imp| {
                dep_var_for
                    .get(imp.module_name.as_str())
                    .map(|s| s.as_str())
            })
            .collect();

        writeln!(out, "# ASN.1 module: {}", pascal)?;
        writeln!(out, "{} = {}('{}',", lib_var, lib_fn, stem)?;
        writeln!(out, "  sources: ['{}.c'],", stem)?;
        write!(out, "  dependencies: [synta_dep")?;
        for dep in &module_deps {
            write!(out, ", {}", dep)?;
        }
        writeln!(out, "],")?;
        writeln!(out, "  install: true,")?;
        writeln!(out, ")")?;
        writeln!(out)?;
        writeln!(out, "{} = declare_dependency(", dep_var)?;
        writeln!(
            out,
            "  include_directories: include_directories('.', is_system: false),"
        )?;
        writeln!(out, "  link_with: {},", lib_var)?;
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
    fn test_single_module_meson() {
        let m = parse("MyModule DEFINITIONS ::= BEGIN Foo ::= INTEGER END").unwrap();
        let out = generate_meson(&[m], &[0], MesonConfig::default()).unwrap();

        assert!(out.contains("project('my_module', 'c'"));
        assert!(out.contains("c_std=c99"));
        assert!(out.contains("library('my_module',"));
        assert!(out.contains("sources: ['my_module.c']"));
        assert!(out.contains("synta_dep = dependency('synta')"));
        assert!(out.contains("my_module_dep = declare_dependency("));
    }

    #[test]
    fn test_meson_with_synta_root() {
        let m = parse("Cert DEFINITIONS ::= BEGIN END").unwrap();
        let config = MesonConfig {
            synta_root: Some("/opt/synta".to_string()),
            shared_library: false,
        };
        let out = generate_meson(&[m], &[0], config).unwrap();

        assert!(out.contains("cc.find_library('synta'"));
        assert!(out.contains("'/opt/synta' / 'target' / 'release'"));
        assert!(out.contains("'/opt/synta' / 'include'"));
        // pkg-config fallback should not be present
        assert!(!out.contains("dependency('synta')"));
    }

    #[test]
    fn test_meson_shared_library() {
        let m = parse("Foo DEFINITIONS ::= BEGIN END").unwrap();
        let config = MesonConfig {
            shared_library: true,
            ..Default::default()
        };
        let out = generate_meson(&[m], &[0], config).unwrap();
        assert!(out.contains("shared_library('foo',"));
    }

    #[test]
    fn test_multi_module_meson_deps() {
        let a = parse("ModA DEFINITIONS ::= BEGIN IMPORTS X FROM ModB; END").unwrap();
        let b = parse("ModB DEFINITIONS ::= BEGIN END").unwrap();
        // topological order: ModB (1) before ModA (0)
        let order = vec![1usize, 0usize];
        let out = generate_meson(&[a, b], &order, MesonConfig::default()).unwrap();

        // ModB library defined
        assert!(out.contains("library('mod_b',"));
        // ModA library defined
        assert!(out.contains("library('mod_a',"));
        // ModA depends on mod_b_dep
        assert!(out.contains("dependencies: [synta_dep, mod_b_dep]"));
    }
}
