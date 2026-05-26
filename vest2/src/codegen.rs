mod common;
mod datatypes;
mod execs;
mod proofs;
mod specs;

use crate::vestir::{self, Combinator, ConstCombinator, Definition, ParamDefn};
use common::{prelude, Analysis, CodeWriter};

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
    body.push_multiline(render_section("Executable Implementations", &execs));

    let mut out = CodeWriter::new();
    out.push_multiline(prelude());
    out.block("verus!", |w| {
        w.push_multiline(body.finish());
    });
    out.line("");
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
            Definition::Combinator {
                name,
                combinator,
                param_defns,
            } => self.gen_combinator_data_fragment(name, combinator, param_defns),
            Definition::ConstCombinator {
                name,
                const_combinator,
            } => self.gen_const_data_fragment(name, const_combinator),
            Definition::Endianess(_) => String::new(),
        }
    }

    pub(crate) fn gen_specs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::Combinator {
                name,
                combinator,
                param_defns,
            } => self.gen_specs_section(name, combinator, param_defns),
            Definition::ConstCombinator { name, .. } => format!(
                "// TODO(specs): emit const-format spec wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
        }
    }

    pub(crate) fn gen_derived_specs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::Combinator {
                name,
                combinator,
                param_defns,
            } => self.gen_derived_specs_section(name, combinator, param_defns),
            Definition::ConstCombinator { name, .. } => format!(
                "// TODO(derived-specs): emit const-format trait wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
        }
    }

    pub(crate) fn gen_proofs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::Combinator {
                name,
                combinator,
                param_defns,
            } => self.gen_proofs_section(name, combinator, param_defns),
            Definition::ConstCombinator { name, .. } => format!(
                "// TODO(proofs): emit const-format proof wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
        }
    }

    pub(crate) fn gen_execs_fragment(&self, def: &Definition) -> String {
        match def {
            Definition::Combinator {
                name, combinator, ..
            } => self.gen_execs_section(name, combinator),
            Definition::ConstCombinator { name, .. } => format!(
                "// TODO(execs): emit const-format exec wrappers for {}\n",
                self.info(name).names.exec
            ),
            Definition::Endianess(_) => String::new(),
        }
    }

    fn gen_combinator_data_fragment(
        &self,
        name: &str,
        combinator: &Combinator,
        _param_defns: &[ParamDefn],
    ) -> String {
        self.gen_value_types(name, combinator)
    }

    fn gen_const_data_fragment(&self, name: &str, const_combinator: &ConstCombinator) -> String {
        self.gen_const_value_aliases(name, const_combinator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vestir::{
        self, CombinatorInner, CombinatorInvocation, ConstraintIntCombinator, Definition,
        GlobalCtx, IntCombinator, LengthExpr, StructCombinator, StructField,
    };
    use std::collections::HashMap;

    fn combinator(inner: CombinatorInner) -> Combinator {
        Combinator {
            inner,
            and_then: None,
        }
    }

    fn ctx_for(defs: &[Definition]) -> GlobalCtx {
        let mut combinators = std::collections::HashSet::new();
        let const_combinators = std::collections::HashSet::new();
        let mut enums = HashMap::new();
        for def in defs {
            match def {
                Definition::Combinator {
                    name,
                    param_defns,
                    combinator,
                } => {
                    combinators.insert(vestir::CombinatorSig {
                        name: name.clone(),
                        param_defns: param_defns.clone(),
                        resolved_combinator: combinator.inner.clone(),
                    });
                    if let CombinatorInner::Enum(enum_comb) = &combinator.inner {
                        enums.insert(name.clone(), enum_comb.clone());
                    }
                }
                Definition::ConstCombinator { .. } | Definition::Endianess(_) => {}
            }
        }
        GlobalCtx {
            combinators,
            const_combinators,
            enums,
            static_sizes: HashMap::new(),
        }
    }

    #[test]
    fn names_are_camel_cased() {
        let names = common::format_names("payload_with_header");
        assert_eq!(names.exec, "PayloadWithHeader");
        assert_eq!(names.spec, "PayloadWithHeaderSpec");
        assert_eq!(names.inner, "PayloadWithHeaderInner");
        assert_eq!(names.fmt, "PayloadWithHeaderFmt");
        assert_eq!(names.fmt_fn, "payload_with_header_fmt");
    }

    #[test]
    fn bytes_need_lifetime() {
        let defs = vec![Definition::Combinator {
            name: "msg".to_string(),
            param_defns: vec![],
            combinator: combinator(CombinatorInner::Bytes(vestir::BytesCombinator {
                len: LengthExpr::Const(4),
            })),
        }];
        let ctx = ctx_for(&defs);
        let analysis = Analysis::new(&defs, &ctx);
        assert!(analysis.info("msg").needs_lifetime);
    }

    #[test]
    fn aliases_propagate_lifetime() {
        let defs = vec![
            Definition::Combinator {
                name: "bytes4".to_string(),
                param_defns: vec![],
                combinator: combinator(CombinatorInner::Bytes(vestir::BytesCombinator {
                    len: LengthExpr::Const(4),
                })),
            },
            Definition::Combinator {
                name: "wrapper".to_string(),
                param_defns: vec![],
                combinator: combinator(CombinatorInner::Invocation(CombinatorInvocation {
                    func: "bytes4".to_string(),
                    args: vec![],
                })),
            },
        ];
        let ctx = ctx_for(&defs);
        let analysis = Analysis::new(&defs, &ctx);
        assert!(analysis.info("wrapper").needs_lifetime);
    }

    #[test]
    fn codegen_emits_structs_and_wrappers() {
        let defs = vec![Definition::Combinator {
            name: "header".to_string(),
            param_defns: vec![],
            combinator: combinator(CombinatorInner::Struct(StructCombinator(vec![
                StructField::Dependent {
                    label: "len".to_string(),
                    combinator: combinator(CombinatorInner::ConstraintInt(
                        ConstraintIntCombinator {
                            combinator: IntCombinator::Unsigned(16),
                            constraint: None,
                        },
                    )),
                },
                StructField::Ordinary {
                    label: "flags".to_string(),
                    combinator: combinator(CombinatorInner::ConstraintInt(
                        ConstraintIntCombinator {
                            combinator: IntCombinator::Unsigned(8),
                            constraint: None,
                        },
                    )),
                },
            ]))),
        }];
        let ctx = ctx_for(&defs);
        let code = code_gen(&defs, &ctx);
        assert!(code.contains("pub struct Header"));
        assert!(code.contains("pub struct HeaderSpec"));
        assert!(code.contains("pub struct HeaderFmt"));
        assert!(code.contains("header_fmt"));
    }

    #[test]
    fn codegen_emits_proof_impls_for_non_tail_formats() {
        let defs = vec![Definition::Combinator {
            name: "msg".to_string(),
            param_defns: vec![],
            combinator: combinator(CombinatorInner::Bytes(vestir::BytesCombinator {
                len: LengthExpr::Const(4),
            })),
        }];
        let ctx = ctx_for(&defs);
        let code = code_gen(&defs, &ctx);
        assert!(
            code.contains("impl  SafeParser for MsgFmt")
                || code.contains("impl SafeParser for MsgFmt")
        );
        assert!(
            code.contains("impl  NonTailFmt for MsgFmt")
                || code.contains("impl NonTailFmt for MsgFmt")
        );
        assert!(
            code.contains("impl  NonMalleable for MsgFmt")
                || code.contains("impl NonMalleable for MsgFmt")
        );
    }

    #[test]
    fn codegen_skips_tail_only_proof_traits_for_tail_formats() {
        let defs = vec![Definition::Combinator {
            name: "rest".to_string(),
            param_defns: vec![],
            combinator: combinator(CombinatorInner::Tail(vestir::TailCombinator)),
        }];
        let ctx = ctx_for(&defs);
        let code = code_gen(&defs, &ctx);
        assert!(
            code.contains("impl  SafeParser for RestFmt")
                || code.contains("impl SafeParser for RestFmt")
        );
        assert!(
            code.contains("impl  SoundParser for RestFmt")
                || code.contains("impl SoundParser for RestFmt")
        );
        assert!(!code.contains("impl NonTailFmt for RestFmt"));
        assert!(!code.contains("impl EquivSerializersGeneral for RestFmt"));
        assert!(
            code.contains("impl  NonMalleable for RestFmt")
                || code.contains("impl NonMalleable for RestFmt")
        );
    }
}
