mod common;
mod datatypes;
mod execs;
mod proofs;
mod recursive;
mod specs;
mod writer;

use crate::vestir::{self, Definition};
use common::Analysis;
use quote::quote;
use writer::render_ts;
use writer::CodeWriter;

pub fn code_gen(defs: &[vestir::Definition], ctx: &vestir::GlobalCtx) -> String {
    let analysis = Analysis::new(defs, ctx);
    let defs = non_endian_defs(defs);
    let data_types = render_fragments(&analysis, &defs, |analysis, def| {
        analysis.gen_data_fragment(def)
    });
    let specs = render_fragments(&analysis, &defs, |analysis, def| {
        analysis.gen_specs_fragment(def)
    });
    let derived_specs = render_fragments(&analysis, &defs, |analysis, def| {
        analysis.gen_derived_specs_fragment(def)
    });
    let proofs = render_fragments(&analysis, &defs, |analysis, def| {
        analysis.gen_proofs_fragment(def)
    });
    let execs = render_fragments(&analysis, &defs, |analysis, def| {
        analysis.gen_execs_fragment(def)
    });

    let mut body = CodeWriter::new();
    body.push_multiline(render_section("Data Types", &data_types));
    body.blank_line();
    body.push_multiline(render_section("Format Specifications", &specs));
    body.blank_line();
    body.push_multiline(render_nested_section(
        "Derived Parser, Serializer, Length, and Consistency Specifications",
        "derived_specs",
        "use super::*;",
        &derived_specs,
    ));
    body.blank_line();
    body.push_multiline(render_nested_section(
        "Proven Format Properties",
        "derived_proofs",
        "use super::*;\nbroadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;\n",
        &proofs,
    ));
    body.blank_line();
    // body.push_multiline(render_section("Executable Implementations", &execs));
    body.push_multiline(render_nested_section(
        "Executable Implementations",
        "exec_impls",
        "use super::*;\n",
        &execs,
    ));

    let mut out = CodeWriter::new();
    out.push_multiline(prelude());
    out.line("verus! {");
    out.push_multiline(body.finish());
    out.line("}");
    out.finish()
}

fn non_endian_defs<'a>(defs: &'a [Definition]) -> Vec<&'a Definition> {
    defs.iter()
        .filter(|def| !matches!(def, Definition::Endianess(_)))
        .collect()
}

fn render_fragments(
    analysis: &Analysis<'_>,
    defs: &[&Definition],
    gen: impl Fn(&Analysis<'_>, &Definition) -> String,
) -> String {
    defs.iter()
        .map(|def| gen(analysis, def))
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn render_section(title: &str, body: &str) -> String {
    let mut out = CodeWriter::new();
    out.push_multiline(section_header(title));
    out.push_multiline(body);
    out.finish()
}

fn render_nested_section(title: &str, module: &str, imports: &str, body: &str) -> String {
    let mut out = CodeWriter::new();
    out.push_multiline(section_header(title));
    out.block(format!("mod {module}"), |w| {
        w.push_multiline(imports.trim_end());
        w.blank_line();
        w.push_multiline(body);
    });
    out.finish()
}

fn section_header(title: &str) -> String {
    format!(
        "// ============================================================\n// {}\n// ============================================================",
        title
    )
}

impl<'a> Analysis<'a> {
    pub(crate) fn gen_data_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::StructDef {
                name, combinator, ..
            } => self.gen_struct_value_types(name, combinator, &[]),
            Definition::ChoiceDef {
                name, combinator, ..
            } => self.gen_choice_value_types(name, combinator, &[]),
            Definition::EnumDef {
                name, combinator, ..
            } => self.gen_enum_value_types(name, combinator),
            Definition::BitsDef {
                name, combinator, ..
            } => self.gen_bits_value_types(name, combinator),
            Definition::CombinatorDef {
                name, combinator, ..
            } => self.gen_combinator_value_types(name, combinator, &[]),
            Definition::ConstCombinatorDef {
                name,
                const_combinator,
            } => self.gen_const_value_aliases(name, const_combinator),
            Definition::Endianess(_) => String::new(),
            Definition::RecursiveScc(scc) => self.gen_recursive_data_fragment(scc),
        }
    }

    pub(crate) fn gen_specs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::StructDef {
                name,
                combinator,
                param_defns,
            } => self.gen_struct_specs_section(name, combinator, param_defns),
            Definition::ChoiceDef {
                name,
                combinator,
                param_defns,
            } => self.gen_choice_specs_section(name, combinator, param_defns),
            Definition::EnumDef {
                name,
                combinator,
                param_defns,
            } => {
                if self.enum_is_bit_sized(combinator) {
                    self.gen_enum_bit_helpers_section(name, combinator)
                } else {
                    self.gen_enum_specs_section(name, combinator, param_defns)
                }
            }
            Definition::BitsDef {
                name,
                combinator,
                param_defns,
            } => self.gen_bits_specs_section(name, combinator, param_defns),
            Definition::CombinatorDef {
                name,
                combinator,
                param_defns,
            } => self.gen_specs_section(name, combinator, param_defns),
            Definition::ConstCombinatorDef { name, .. } => format!(
                "// TODO(specs): emit const-format spec wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
            Definition::RecursiveScc(scc) => self.gen_recursive_specs_fragment(scc),
        }
    }

    pub(crate) fn gen_derived_specs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::StructDef {
                name, param_defns, ..
            }
            | Definition::ChoiceDef {
                name, param_defns, ..
            }
            | Definition::CombinatorDef {
                name, param_defns, ..
            }
            | Definition::BitsDef {
                name, param_defns, ..
            } => self.gen_derived_specs_section_impl(name, param_defns),
            Definition::EnumDef { combinator, .. } if self.enum_is_bit_sized(combinator) => {
                String::new()
            }
            Definition::EnumDef {
                name, param_defns, ..
            } => self.gen_derived_specs_section_impl(name, param_defns),
            Definition::ConstCombinatorDef { name, .. } => format!(
                "// TODO(derived-specs): emit const-format trait wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
            Definition::RecursiveScc(scc) => self.gen_recursive_derived_specs_fragment(scc),
        }
    }

    pub(crate) fn gen_proofs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::StructDef {
                name, param_defns, ..
            }
            | Definition::ChoiceDef {
                name, param_defns, ..
            } => self.gen_top_level_proofs_section(name, param_defns),
            Definition::EnumDef { combinator, .. } if self.enum_is_bit_sized(combinator) => {
                String::new()
            }
            Definition::EnumDef {
                name, param_defns, ..
            } => self.gen_top_level_proofs_section(name, param_defns),
            Definition::BitsDef {
                name, param_defns, ..
            } => self.gen_bits_proofs_section(name, param_defns),
            Definition::CombinatorDef {
                name,
                combinator: _,
                param_defns,
            } => self.gen_proofs_section(name, param_defns),
            Definition::ConstCombinatorDef { name, .. } => format!(
                "// TODO(proofs): emit const-format proof wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
            Definition::RecursiveScc(scc) => self.gen_recursive_proofs_fragment(scc),
        }
    }

    pub(crate) fn gen_execs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::CombinatorDef {
                name,
                combinator,
                param_defns,
            } => self.gen_combinator_execs_section(name, combinator, param_defns),
            Definition::StructDef {
                name,
                combinator,
                param_defns,
            } => self.gen_struct_execs_section(name, combinator, param_defns),
            Definition::ChoiceDef {
                name,
                combinator,
                param_defns,
            } => self.gen_choice_execs_section(name, combinator, param_defns),
            Definition::EnumDef {
                name,
                combinator,
                param_defns,
            } => {
                if self.enum_is_bit_sized(combinator) {
                    String::new()
                } else {
                    self.gen_enum_execs_section(name, combinator, param_defns)
                }
            }
            Definition::BitsDef {
                name,
                combinator,
                param_defns,
            } => self.gen_bits_execs_section(name, combinator, param_defns),
            Definition::ConstCombinatorDef { name, .. } => format!(
                "// TODO(execs): emit const-format exec wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
            Definition::RecursiveScc(scc) => self.gen_recursive_execs_fragment(scc),
        }
    }
}

pub(crate) fn prelude() -> String {
    render_ts(quote! {
        #![allow(warnings)]
        use vest_lib2::combinators::mapped::spec::*;
        use vest_lib2::combinators::*;
        use vest_lib2::combinators::recursive::*;
        use Sum::Inl as L;
        use Sum::Inr as R;
        use vest_lib2::Never;
        use vest_lib2::core::exec::input::{InputBuf, InputSlice};
        use vest_lib2::core::exec::output::OutputBuf;
        use vest_lib2::core::exec::parser::*;
        use vest_lib2::core::exec::serializer::*;
        use vest_lib2::core::exec::ParseError;
        use vest_lib2::core::exec::bytes_eq;
        use vest_lib2::core::{proof::*, spec::*};
        use vest_lib2::primitives::btcvarint::VarInt;
        use vest_lib2::primitives::leb128::ULeb128;
        use vstd::prelude::*;
    })
}
