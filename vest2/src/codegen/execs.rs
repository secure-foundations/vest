use super::common::{
    bits_tuple_pattern_tokens, int_literal, is_combinator_in_scc, syn_usize, Analysis, Op, TypeMode,
};
use super::writer::{render_ts, CodeWriter};
use crate::vestir::{
    self, BitsCombinator, ChoiceCombinator, ChoicePattern, Combinator, ConstArray, ConstCombinator,
    EnumCombinator, Param, ParamDefn, SccMember, StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

const SPINOFF_PROVER_THRESHOLD: usize = 16;

// ============================================================
// Shared scaffolding — emit the three impl blocks
// ============================================================

impl<'a> Analysis<'a> {
    fn gen_parser_serializer_prepare(
        &self,
        name: &str,
        param_defns: &[ParamDefn],
        emit_parser: impl Fn(&mut CodeWriter),
        emit_serializer: impl Fn(&mut CodeWriter),
        emit_prepare: impl Fn(&mut CodeWriter),
        use_spinoff_prover: bool,
        is_struct_parser: bool,
    ) -> String {
        let info = self.info(name);
        let exec_ty = self.render_nominal_type(name, TypeMode::Exec);
        let param_lt = self.wrapper_generics(param_defns);
        let fmt_has_lt = param_lt.to_string().contains("'i");
        let fmt_ident_str = if fmt_has_lt {
            format!("{}<'i>", info.names.fmt)
        } else {
            info.names.fmt.clone()
        };
        let reveal_fmt = &info.names.fmt;
        let exec_ty_str = render_ts(exec_ty);

        let mut out = CodeWriter::new();

        // --- Parser impl ---
        {
            out.block(format!("impl<'i> Parser<&'i [u8]> for {}", fmt_ident_str), |w| {
                w.line(format!("type PT = {};", exec_ty_str));
                w.blank_line();
                if use_spinoff_prover {
                    w.line("#[verifier::spinoff_prover]");
                }
                w.block("fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT>", |w| {
                    if is_struct_parser {
                        w.line("broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;");
                        w.line("broadcast use vest_lib2::core::spec::SoundParser::lemma_parse_sound_value;");
                        w.blank_line();
                    }
                    w.reveal_stmt(&format!("<{} as SpecParser>::spec_parse", reveal_fmt));
                    w.line("let _ = ibuf.len();");
                    w.line("let rest = *ibuf;");
                    w.blank_line();
                    self.emit_param_invariant_opening(w, param_defns);
                    emit_parser(w);
                });
            });
            out.blank_line();
        }

        // --- Serializer impl ---
        {
            out.block(
                format!("impl<'i> Serializer<{}> for {}", exec_ty_str, fmt_ident_str),
                |w| {
                    if use_spinoff_prover {
                        w.line("#[verifier::spinoff_prover]");
                    }
                    w.block(
                        format!(
                            "fn serialize(&self, v: &{}, obuf: &mut Vec<u8>)",
                            exec_ty_str
                        ),
                        |w| {
                            w.reveal_stmt(&format!(
                                "<{} as SpecSerializer>::spec_serialize",
                                reveal_fmt
                            ));
                            self.emit_param_invariant_opening(w, param_defns);
                            w.line("let ghost old_obuf = obuf@;");
                            w.blank_line();
                            emit_serializer(w);
                            w.blank_line();
                            w.line(
                                "assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));",
                            );
                        },
                    );
                },
            );
            out.blank_line();
        }

        // --- Prepare impl ---
        {
            out.block(
                format!("impl<'i> Prepare<{}> for {}", exec_ty_str, fmt_ident_str),
                |w| {
                    if use_spinoff_prover {
                        w.line("#[verifier::spinoff_prover]");
                    }
                    w.block(
                        format!(
                            "fn prepare(&self, v: &{}) -> Result<usize, PreSerializeError>",
                            exec_ty_str
                        ),
                        |w| {
                            w.reveal_stmt(&format!("<{} as SpecByteLen>::byte_len", reveal_fmt));
                            self.emit_param_invariant_opening(w, param_defns);
                            emit_prepare(w);
                        },
                    );
                },
            );
            out.blank_line();
        }

        out.finish()
    }

    fn emit_param_invariant_opening(&self, w: &mut CodeWriter, param_defns: &[ParamDefn]) {
        if param_defns.is_empty() {
            return;
        }
        w.block("proof", |w| {
            w.line("use_type_invariant(self);");
        });
        w.blank_line();
    }

    fn resolve_dep(&self, name: &str, param_defns: &[ParamDefn]) -> TokenStream {
        let base = name.split('.').next().unwrap();
        let is_param = param_defns.iter().any(|p| match p {
            ParamDefn::Dependent { name: p_name, .. } => p_name == base,
        });
        let path = name.replace('.', ".");
        if is_param {
            let ts: TokenStream = format!("self.{}", path).parse().unwrap();
            ts
        } else {
            let ts: TokenStream = path.parse().unwrap();
            ts
        }
    }
}

impl<'a> Analysis<'a> {
    pub(crate) fn gen_combinator_execs_section(
        &self,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_combinator_body_impl(w, combinator, param_defns, Op::Parse, None);
            },
            |w| {
                self.emit_combinator_body_impl(w, combinator, param_defns, Op::Serialize, None);
            },
            |w| {
                self.emit_combinator_body_impl(w, combinator, param_defns, Op::Prepare, None);
            },
            false,
            false,
        )
    }

    pub(crate) fn gen_struct_execs_section(
        &self,
        name: &str,
        combinator: &StructCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let use_spinoff = combinator.0.len() > SPINOFF_PROVER_THRESHOLD;
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_struct_body_impl(w, name, combinator, param_defns, Op::Parse, None);
            },
            |w| {
                self.emit_struct_body_impl(w, name, combinator, param_defns, Op::Serialize, None);
            },
            |w| {
                self.emit_struct_body_impl(w, name, combinator, param_defns, Op::Prepare, None);
            },
            use_spinoff,
            true,
        )
    }

    pub(crate) fn gen_choice_execs_section(
        &self,
        name: &str,
        combinator: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let use_spinoff = combinator.choices.len() > SPINOFF_PROVER_THRESHOLD;
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_choice_body_impl(w, name, combinator, param_defns, Op::Parse, None);
            },
            |w| {
                self.emit_choice_body_impl(w, name, combinator, param_defns, Op::Serialize, None);
            },
            |w| {
                self.emit_choice_body_impl(w, name, combinator, param_defns, Op::Prepare, None);
            },
            use_spinoff,
            false,
        )
    }

    pub(crate) fn gen_enum_execs_section(
        &self,
        name: &str,
        combinator: &EnumCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_enum_parser_body(w, name, combinator);
            },
            |w| {
                self.emit_enum_serializer_body(w, name, combinator);
            },
            |w| {
                self.emit_enum_prepare_body(w, name, combinator);
            },
            false,
            false,
        )
    }

    pub(crate) fn gen_bits_execs_section(
        &self,
        name: &str,
        combinator: &BitsCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let use_spinoff = combinator.0.len() > SPINOFF_PROVER_THRESHOLD;
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_bits_parser_body(w, name, combinator);
            },
            |w| {
                self.emit_bits_serializer_body(w, name, combinator);
            },
            |w| {
                self.emit_bits_prepare_body(w, name, combinator);
            },
            use_spinoff,
            false,
        )
    }
}

// ============================================================
// Struct parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_bits_parser_body(&self, w: &mut CodeWriter, name: &str, bits: &BitsCombinator) {
        let layout = self.bits_layout(bits);
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let repr_fmt = self.render_int_combinator_expr(&layout.repr_int);
        let repr_fmt_str = render_ts(repr_fmt);
        let unpack_ident = format_ident!("unpack_{}", name);
        let unpack_str = unpack_ident.to_string();

        let label_idents = layout.field_idents();
        let tuple_pat = render_ts(bits_tuple_pattern_tokens(&label_idents));

        w.call_chain_stmt(
            Some("(n, raw)"),
            &repr_fmt_str,
            "parse",
            &["ibuf"],
            Some("?;"),
        );
        w.line(format!("let {} = {}(raw);", tuple_pat, unpack_str));

        for (idx, (field, layout_field)) in bits.0.iter().zip(&layout.fields).enumerate() {
            let ident = &label_idents[idx];
            let pred = self.bits_field_refinement_pred(field, layout_field, quote! { #ident });
            if let Some(pred) = pred {
                w.if_block(format!("!({})", render_ts(pred)), |w| {
                    w.line("return Err(ParseError::predicate_failed());");
                });
            }
        }

        let ctor_fields = self.bits_ctor_fields(&layout);
        let fields_rendered = ctor_fields
            .iter()
            .map(|(ident, expr)| format!("{}: {}", ident, render_ts(expr.clone())))
            .collect::<Vec<_>>();
        w.record_constructor_stmt("final_v", &exec_ident.to_string(), &fields_rendered);
        w.line("assert(self.spec_parse(ibuf@) == Some((n as int, final_v.deep_view())));");
        w.line("Ok((n, final_v))");
    }

    fn emit_bits_serializer_body(&self, w: &mut CodeWriter, name: &str, bits: &BitsCombinator) {
        let layout = self.bits_layout(bits);
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let field_idents = layout.field_idents();
        w.push_multiline(render_ts(quote! {
            let #exec_ident { #(#field_idents),* } = *v;
        }));

        let pack_ident = format_ident!("pack_{}", name);
        let pack_args = self
            .bits_raw_field_exprs(&layout)
            .iter()
            .map(|expr| render_ts(expr.clone()))
            .collect::<Vec<_>>();
        w.line(format!(
            "let packed = {}({});",
            pack_ident,
            pack_args.join(", ")
        ));
        let repr_fmt = self.render_int_combinator_expr(&layout.repr_int);
        let repr_fmt_str = render_ts(repr_fmt);
        w.call_chain_stmt(
            None,
            &repr_fmt_str,
            "serialize",
            &["&packed", "obuf"],
            Some(";"),
        );
    }

    fn emit_bits_prepare_body(&self, w: &mut CodeWriter, name: &str, bits: &BitsCombinator) {
        let layout = self.bits_layout(bits);
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let field_idents = layout.field_idents();
        w.push_multiline(render_ts(quote! {
            let #exec_ident { #(#field_idents),* } = *v;
        }));

        let raw_exprs = self.bits_raw_field_exprs(&layout);

        let bounds_ident = format_ident!("{}_bounds", name);
        w.if_block(
            format!(
                "!({})",
                render_ts(quote! { #bounds_ident(#(#raw_exprs),*) })
            ),
            |w| {
                w.line(
                    "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed));",
                );
            },
        );

        for (idx, (_, layout_field)) in bits.0.iter().zip(&layout.fields).enumerate() {
            let field_ident = &field_idents[idx];

            let consistency = self.bits_open_enum_wf_pred(layout_field, quote! { #field_ident });
            if let Some(pred) = consistency {
                w.if_block(format!("!({})", render_ts(pred)), |w| {
                    w.line(
                        "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed));",
                    );
                });
            }
        }

        for (idx, (field, layout_field)) in bits.0.iter().zip(&layout.fields).enumerate() {
            let raw_expr = raw_exprs[idx].clone();
            let refinement = self.bits_field_refinement_pred(field, layout_field, raw_expr);

            if let Some(pred) = refinement {
                w.if_block(format!("!({})", render_ts(pred)), |w| {
                    w.line(
                        "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed));",
                    );
                });
            }
        }

        let pack_ident = format_ident!("pack_{}", name);
        w.line(format!(
            "let packed = {}({});",
            pack_ident,
            raw_exprs
                .iter()
                .map(|ts| render_ts(ts.clone()))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        let repr_fmt = self.render_int_combinator_expr(&layout.repr_int);
        let repr_fmt_str = render_ts(repr_fmt);
        w.line(format!("{}.prepare(&packed)", repr_fmt_str));
    }

    pub(crate) fn emit_struct_body_impl(
        &self,
        w: &mut CodeWriter,
        name: &str,
        s: &StructCombinator,
        param_defns: &[ParamDefn],
        op: Op,
        rec: Option<(
            &SccMember,
            &super::recursive::RecCtx<'_>,
            super::recursive::RecExecParamAccess,
        )>,
    ) {
        match op {
            Op::Parse => {
                let mut sizes = Vec::new();
                let mut seen_recursive = false;
                for (idx, field) in s.0.iter().enumerate() {
                    let n_var = format!("n{}", idx + 1);
                    match field {
                        StructField::Const { label, combinator } => {
                            let fmt_expr = self.render_exec_const_expr(
                                combinator,
                                param_defns,
                                CodegenMode::Parse,
                            );
                            let fmt_str = render_ts(quote! { #fmt_expr });
                            w.call_chain_stmt(
                                Some(&format!("({}, {})", n_var, label)),
                                &fmt_str,
                                "parse",
                                &["&rest"],
                                Some("?;"),
                            );
                        }
                        StructField::Dependent { label, combinator }
                        | StructField::Ordinary { label, combinator } => {
                            let n_ident = format_ident!("{}", n_var);
                            let label_ident = format_ident!("{}", label);
                            let (parse_expr, recursive) = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_parse_expr(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { &rest },
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr_named(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Parse,
                                );
                                (quote! { (#fmt_expr).parse(&rest) }, false)
                            };
                            if recursive && !seen_recursive {
                                w.if_block("gas == 0", |w| {
                                    w.line("return Err(ParseError::recursion_limit_exceeded());");
                                });
                                seen_recursive = true;
                            }
                            w.push_multiline(render_ts(quote! {
                                let (#n_ident, #label_ident) = #parse_expr?;
                            }));
                            if let Some(pred) =
                                self.gen_constraint_pred(combinator, quote! { #label_ident })
                            {
                                w.if_block(format!("!({})", render_ts(pred)), |w| {
                                    w.line("return Err(ParseError::predicate_failed());");
                                });
                            }
                            if rec.is_none() && idx == s.0.len() - 1 {
                                if matches!(
                                    self.ctx.resolve_alias(combinator),
                                    Combinator::Option(_) | Combinator::Vec(_)
                                ) {
                                    w.call_chain_stmt(
                                        Some("_"),
                                        "Eof",
                                        "parse",
                                        &["&rest"],
                                        Some("?;"),
                                    );
                                }
                            }
                        }
                    }
                    w.line(format!("let rest = rest.skip({});", n_var));
                    sizes.push(n_var);
                }

                let total_n_expr = if sizes.is_empty() {
                    "0usize".to_string()
                } else {
                    sizes.join(" + ")
                };
                let exec_ident = format_ident!("{}", self.info(name).names.exec);
                w.line(format!("let total_n = {};", total_n_expr));
                let struct_field_names = struct_field_name_strings(&s.0);
                if let Some((_, ctx, _)) = rec {
                    let ctor_fields: Vec<String> =
                        s.0.iter()
                            .filter_map(|f| match f {
                                StructField::Const { .. } => None,
                                StructField::Dependent { label, combinator }
                                | StructField::Ordinary { label, combinator } => {
                                    let expr = if is_combinator_in_scc(combinator, ctx.members) {
                                        format!("{}: Box::new({})", label, label)
                                    } else {
                                        format!("{}: {}", label, label)
                                    };
                                    Some(expr)
                                }
                            })
                            .collect();
                    w.record_constructor_stmt("final_v", &exec_ident.to_string(), &ctor_fields);
                    w.line("assert(parse_spec == Some((total_n as int, final_v.deep_view())));");
                } else {
                    w.record_constructor_stmt(
                        "final_v",
                        &exec_ident.to_string(),
                        &struct_field_names,
                    );
                    w.line("assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));");
                }
                w.line("Ok((total_n, final_v))");
            }
            Op::Serialize => {
                let exec_ident = format_ident!("{}", self.info(name).names.exec);
                let struct_field_names = struct_field_name_strings(&s.0);
                w.record_destructure_stmt(&exec_ident.to_string(), &struct_field_names, "v");

                for field in &s.0 {
                    match field {
                        StructField::Const { label, combinator } => {
                            let fmt_expr = self.render_exec_const_expr(
                                combinator,
                                param_defns,
                                CodegenMode::Serialize,
                            );
                            let fmt_str = render_ts(quote! { #fmt_expr });
                            w.call_chain_stmt(
                                None,
                                &fmt_str,
                                "serialize",
                                &[label, "obuf"].as_slice(),
                                Some(";"),
                            );
                        }
                        StructField::Dependent { label, combinator }
                        | StructField::Ordinary { label, combinator } => {
                            let label_ident = format_ident!("{}", label);
                            if let Some((member, ctx, access)) = rec {
                                let ser = self.render_recursive_child_serialize_stmt(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { #label_ident },
                                    None,
                                );
                                w.line(render_ts(quote! { #ser; }));
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                let fmt_str = render_ts(quote! { #fmt_expr });
                                w.call_chain_stmt(
                                    None,
                                    &fmt_str,
                                    "serialize",
                                    &[label, "obuf"].as_slice(),
                                    Some(";"),
                                );
                            }
                        }
                    }
                }
            }
            Op::Prepare => {
                let exec_ident = format_ident!("{}", self.info(name).names.exec);
                let struct_field_names = struct_field_name_strings(&s.0);
                w.record_destructure_stmt(&exec_ident.to_string(), &struct_field_names, "v");

                let mut lens = Vec::new();
                let mut seen_recursive = false;
                for (idx, field) in s.0.iter().enumerate() {
                    let l_var = format!("l{}", idx + 1);
                    let l_ident = format_ident!("{}", l_var);
                    match field {
                        StructField::Const { label, combinator } => {
                            let label_ident = format_ident!("{}", label);
                            let fmt_expr = self.render_exec_const_expr(
                                combinator,
                                param_defns,
                                CodegenMode::Serialize,
                            );
                            w.push_multiline(render_ts(quote! {
                                let #l_ident = (#fmt_expr).prepare(#label_ident)?;
                            }));
                        }
                        StructField::Dependent { label, combinator }
                        | StructField::Ordinary { label, combinator } => {
                            let label_ident = format_ident!("{}", label);
                            let (prep_expr, recursive) = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_prepare_expr(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { #label_ident },
                                    None,
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr_named(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                (
                                    self.render_prepare_value(
                                        quote! { #label_ident },
                                        fmt_expr,
                                        combinator,
                                    ),
                                    false,
                                )
                            };
                            if recursive && !seen_recursive {
                                w.if_block("gas == 0", |w| {
                                    w.line(
                                        "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded));",
                                    );
                                });
                                seen_recursive = true;
                            }
                            w.push_multiline(render_ts(quote! {
                                let #l_ident = #prep_expr?;
                            }));
                        }
                    }
                    lens.push(l_var);
                }
                let total_len_var = if rec.is_some() { "total" } else { "total_len" };
                self.emit_checked_add_return(w, total_len_var, &lens);
            }
        }
    }
}

// ============================================================
// Choice parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn emit_choice_body_impl(
        &self,
        w: &mut CodeWriter,
        name: &str,
        c: &ChoiceCombinator,
        param_defns: &[ParamDefn],
        op: Op,
        rec: Option<(
            &SccMember,
            &super::recursive::RecCtx<'_>,
            super::recursive::RecExecParamAccess,
        )>,
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let variant_names = self.choice_variant_names(c);
        let variants: Vec<_> = c
            .choices
            .iter()
            .zip(variant_names.iter())
            .map(|((pat, combinator), name)| (pat, combinator, format_ident!("{}", name)))
            .collect();

        if let Some(dep) = &c.depend_id {
            let dep_expr = if let Some((_member, _, access)) = rec {
                self.render_recursive_runtime_dep_expr(dep, param_defns, access, None, op)
            } else {
                self.resolve_dep(dep, param_defns)
            };

            let scrutinee = match op {
                Op::Parse => render_ts(quote! { #dep_expr }),
                _ => format!("({}, v)", render_ts(dep_expr)),
            };

            match op {
                Op::Parse => {
                    w.match_block_stmt(Some("(n, v)"), &scrutinee, |w| {
                        for (pat, combinator, variant_ident) in &variants {
                            let (pat_ts, _is_enum) = if let Some((member, _, _)) = rec {
                                (
                                    self.render_recursive_choice_parse_pat(pat, dep, member),
                                    false,
                                )
                            } else {
                                match pat {
                                    ChoicePattern::Enum(pat_str) => {
                                        let pat_ident = format_ident!("{}", pat_str);
                                        let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                                        let ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                                        (quote! { #ty::#pat_ident }, true)
                                    }
                                    ChoicePattern::Int(elem) => {
                                        (self.render_constraint_elem_pat(elem), false)
                                    }
                                    ChoicePattern::Array(arr) => {
                                        let pat_expr =
                                            self.render_const_array_expr(arr, TypeMode::Exec);
                                        (quote! { x if x.deep_eq(&#pat_expr) }, false)
                                    }
                                    ChoicePattern::Wildcard => (quote! { _ }, false),
                                }
                            };

                            let (parse_expr, recursive) = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_parse_expr(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { ibuf },
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr_named(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Parse,
                                );
                                (quote! { (#fmt_expr).parse(&rest) }, false)
                            };

                            let check = if let Some(pred) =
                                self.gen_constraint_pred(combinator, quote! { v })
                            {
                                quote! {
                                    if !(#pred) {
                                        return Err(ParseError::predicate_failed());
                                    }
                                }
                            } else {
                                quote! {}
                            };

                            if let Some((_, ctx, _)) = rec {
                                let inner_ident = format_ident!("inner");
                                let parse_stmt = self.render_recursive_parse_binding(
                                    parse_expr,
                                    recursive,
                                    &inner_ident,
                                );
                                let ctor = self.render_recursive_choice_ctor(
                                    combinator,
                                    ctx,
                                    &exec_ident,
                                    variant_ident,
                                    quote! { inner },
                                );
                                w.push_multiline(render_ts(quote! {
                                    #pat_ts => {
                                        #parse_stmt
                                        (n, #ctor)
                                    },
                                }));
                            } else {
                                w.push_multiline(render_ts(quote! {
                                    #pat_ts => {
                                        let (n, v) = #parse_expr?;
                                        #check
                                        (n, #exec_ident::#variant_ident(v))
                                    },
                                }));
                            }
                        }
                    });
                }
                Op::Serialize => {
                    w.match_block_stmt(None, &scrutinee, |w| {
                        for (pat, combinator, variant_ident) in &variants {
                            let pat_ts = if let Some((member, _, _)) = rec {
                                self.render_recursive_choice_pair_pat(
                                    pat, dep, member, &exec_ident, variant_ident,
                                )
                            } else {
                                match pat {
                                    ChoicePattern::Enum(pat_str) => {
                                        let pat_ident = format_ident!("{}", pat_str);
                                        let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                                        let ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                                        quote! { (#ty::#pat_ident, #exec_ident::#variant_ident(v)) }
                                    }
                                    ChoicePattern::Int(elem) => match elem {
                                        vestir::ConstraintElem::Single(v) => {
                                            let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                            quote! { (#lit, #exec_ident::#variant_ident(v)) }
                                        }
                                        _ => {
                                            let cond = self.render_constraint_elem_pred(elem, quote! { x });
                                            quote! { (x, #exec_ident::#variant_ident(v)) if #cond }
                                        }
                                    },
                                    ChoicePattern::Array(arr) => {
                                        let pat_expr = self.render_const_array_expr(arr, TypeMode::Exec);
                                        quote! { (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) }
                                    }
                                    ChoicePattern::Wildcard => {
                                        quote! { (_, #exec_ident::#variant_ident(v)) }
                                    }
                                }
                            };

                            let ser = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_serialize_stmt(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { v },
                                    Some("v"),
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                quote! { (#fmt_expr).serialize(v, obuf) }
                            };

                            w.push_multiline(render_ts(quote! {
                                #pat_ts => { #ser; },
                            }));
                        }
                        w.line("_ => {},");
                    });
                }
                Op::Prepare => {
                    if rec.is_none() {
                        let array_branches: Vec<&(ChoicePattern, Combinator)> = c
                            .choices
                            .iter()
                            .filter(|(pat, _)| {
                                matches!(pat, ChoicePattern::Array(_))
                                    || matches!(pat, ChoicePattern::Wildcard)
                            })
                            .collect();
                        if !array_branches.is_empty() {
                            let arrays: Vec<(Option<ConstArray>, Combinator)> = array_branches
                                .iter()
                                .map(|(pat, c)| match pat {
                                    ChoicePattern::Array(arr) => (Some(arr.clone()), c.clone()),
                                    ChoicePattern::Wildcard => (None, c.clone()),
                                    _ => unreachable!(),
                                })
                                .collect();
                            self.emit_array_choice_prepare_disjointness_proof(w, &arrays);
                        }
                    }

                    w.match_block_stmt(None, &scrutinee, |w| {
                        for (pat, combinator, variant_ident) in &variants {
                            let pat_ts = if let Some((member, _, _)) = rec {
                                self.render_recursive_choice_pair_pat(
                                    pat, dep, member, &exec_ident, variant_ident,
                                )
                            } else {
                                match pat {
                                    ChoicePattern::Enum(pat_str) => {
                                        let pat_ident = format_ident!("{}", pat_str);
                                        let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                                        let ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                                        quote! { (#ty::#pat_ident, #exec_ident::#variant_ident(v)) }
                                    }
                                    ChoicePattern::Int(elem) => match elem {
                                        vestir::ConstraintElem::Single(v) => {
                                            let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                            quote! { (#lit, #exec_ident::#variant_ident(v)) }
                                        }
                                        _ => {
                                            let cond = self.render_constraint_elem_pred(elem, quote! { x });
                                            quote! { (x, #exec_ident::#variant_ident(v)) if #cond }
                                        }
                                    },
                                    ChoicePattern::Array(arr) => {
                                        let pat_expr = self.render_const_array_expr(arr, TypeMode::Exec);
                                        quote! { (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) }
                                    }
                                    ChoicePattern::Wildcard => {
                                        quote! { (_, #exec_ident::#variant_ident(v)) }
                                    }
                                }
                            };

                            let (prep_expr, recursive) = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_prepare_expr(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { v },
                                    Some("v"),
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr_named(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                (self.render_prepare_value(quote! { v }, fmt_expr, combinator), false)
                            };

                            if let Some((_, _, _)) = rec {
                                let prep = self.render_recursive_prepare_result(prep_expr, recursive);
                                w.push_multiline(render_ts(quote! {
                                    #pat_ts => #prep,
                                }));
                            } else {
                                if matches!(pat, ChoicePattern::Wildcard) {
                                    let covered_enum_pats: Vec<&str> = c
                                        .choices
                                        .iter()
                                        .filter_map(|(pat, _)| match pat {
                                            ChoicePattern::Enum(name) if name != "_" => Some(name.as_str()),
                                            _ => None,
                                        })
                                        .collect();
                                    let known_int_conds: Vec<TokenStream> = c
                                        .choices
                                        .iter()
                                        .filter_map(|(pat, _)| match pat {
                                            ChoicePattern::Int(elem) => {
                                                Some(self.render_constraint_elem_pred(elem, quote! { x }))
                                            }
                                            _ => None,
                                        })
                                        .collect();
                                    let known_array_pats: Vec<&ConstArray> = c
                                        .choices
                                        .iter()
                                        .filter_map(|(pat, _)| match pat {
                                            ChoicePattern::Array(arr) => Some(arr),
                                            _ => None,
                                        })
                                        .collect();
                                    let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                                    let enum_comb = self
                                        .resolve_dep_enum_info(dep, param_defns)
                                        .map(|(_, comb)| comb);
                                    let is_enum = c
                                        .choices
                                        .iter()
                                        .any(|(pat, _)| matches!(pat, ChoicePattern::Enum(_)));

                                    if is_enum {
                                        if let (Some(ref ty), Some(ec)) = (&enum_ty, enum_comb) {
                                            let variants = match ec {
                                                EnumCombinator::Exhaustive { enums, .. }
                                                | EnumCombinator::NonExhaustive { enums, .. } => enums,
                                            };
                                            for variant in variants {
                                                if covered_enum_pats.iter().any(|p| *p == variant.name.as_str()) {
                                                    continue;
                                                }
                                                let known_ident = format_ident!("{}", variant.name);
                                                w.push_multiline(render_ts(quote! {
                                                    (#ty::#known_ident, #exec_ident::#variant_ident(v)) => #prep_expr,
                                                }));
                                            }
                                            if let EnumCombinator::NonExhaustive { enums, inferred } = ec {
                                                let disjuncts: Vec<TokenStream> = enums
                                                    .iter()
                                                    .map(|variant| {
                                                        let lit = int_literal(variant.value, inferred);
                                                        quote! { x != #lit }
                                                    })
                                                    .collect();
                                                let guard = if disjuncts.is_empty() {
                                                    quote! { true }
                                                } else {
                                                    let mut it = disjuncts.into_iter();
                                                    let first = it.next().unwrap();
                                                    it.fold(first, |acc, item| quote! { #acc && #item })
                                                };
                                                w.push_multiline(render_ts(quote! {
                                                    (#ty::Unknown(x), #exec_ident::#variant_ident(v)) if #guard => #prep_expr,
                                                }));
                                            }
                                        } else {
                                            w.push_multiline(render_ts(quote! {
                                                (_, #exec_ident::#variant_ident(v)) => #prep_expr,
                                            }));
                                        }
                                    } else if !known_array_pats.is_empty() {
                                        let guard = known_array_pats
                                            .iter()
                                            .map(|p| {
                                                let pat_expr = self.render_const_array_expr(p, TypeMode::Exec);
                                                quote! { !x.deep_eq(&#pat_expr) }
                                            })
                                            .reduce(|acc, cond| quote! { #acc && #cond })
                                            .unwrap();
                                        w.push_multiline(render_ts(quote! {
                                            (x, #exec_ident::#variant_ident(v)) if #guard => #prep_expr,
                                        }));
                                    } else if !known_int_conds.is_empty() {
                                        let guard = known_int_conds
                                            .iter()
                                            .cloned()
                                            .map(|cond| quote! { !(#cond) })
                                            .reduce(|acc, cond| quote! { #acc && #cond })
                                            .unwrap();
                                        w.push_multiline(render_ts(quote! {
                                            (x, #exec_ident::#variant_ident(v)) if #guard => #prep_expr,
                                        }));
                                    } else {
                                        w.push_multiline(render_ts(quote! {
                                            (_, #exec_ident::#variant_ident(v)) => #prep_expr,
                                        }));
                                    }
                                } else {
                                    w.push_multiline(render_ts(quote! {
                                        #pat_ts => #prep_expr,
                                    }));
                                }
                            }
                        }
                        w.line(
                            " _ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),",
                        );
                    });
                }
            }
        } else {
            // Non-dependent choice
            match op {
                Op::Parse => {
                    let mut chain = quote! { Err(ParseError::invalid_choice()) };
                    for (combinator, variant_name) in self
                        .choice_combinators_and_names(c, &variant_names)
                        .into_iter()
                        .rev()
                    {
                        let variant_ident = format_ident!("{}", variant_name);
                        let (parse_expr, recursive) = if let Some((member, ctx, access)) = rec {
                            self.render_recursive_child_parse_expr(
                                combinator,
                                member,
                                ctx,
                                access,
                                quote! { ibuf },
                            )
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr_named(
                                combinator,
                                param_defns,
                                CodegenMode::Parse,
                            );
                            (quote! { (#fmt_expr).parse(&rest) }, false)
                        };

                        if let Some((_, ctx, _)) = rec {
                            let ctor = self.render_recursive_choice_ctor(
                                combinator,
                                ctx,
                                &exec_ident,
                                &variant_ident,
                                quote! { va },
                            );
                            chain = if recursive {
                                quote! {
                                    if gas == 0 {
                                        Err(ParseError::recursion_limit_exceeded())
                                    } else {
                                        match #parse_expr {
                                            Ok((n, va)) => Ok((n, #ctor)),
                                            _ => #chain,
                                        }
                                    }
                                }
                            } else {
                                quote! {
                                    match #parse_expr {
                                        Ok((n, va)) => Ok((n, #ctor)),
                                        _ => #chain,
                                    }
                                }
                            };
                        } else {
                            if let Some(pred) = self.gen_constraint_pred(combinator, quote! { va })
                            {
                                chain = quote! {
                                    match #parse_expr {
                                        Ok((n, va)) if #pred => {
                                            Ok((n, #exec_ident::#variant_ident(va)))
                                        },
                                        _ => #chain,
                                    }
                                };
                            } else {
                                chain = quote! {
                                    match #parse_expr {
                                        Ok((n, va)) => {
                                            Ok((n, #exec_ident::#variant_ident(va)))
                                        },
                                        _ => #chain,
                                    }
                                };
                            }
                        }
                    }

                    w.line(render_ts(quote! {
                        let (n, v) = #chain?;
                    }));
                    if rec.is_some() {
                        w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
                    } else {
                        w.line(
                            "assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));",
                        );
                    }
                    w.line("Ok((n, v))");
                }
                Op::Serialize => {
                    w.match_block_stmt(None, "v", |w| {
                        for (_, combinator, variant_ident) in &variants {
                            let ser = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_serialize_stmt(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { v },
                                    Some("v"),
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                quote! { (#fmt_expr).serialize(v, obuf) }
                            };
                            w.push_multiline(render_ts(quote! {
                                #exec_ident::#variant_ident(v) => { #ser; },
                            }));
                        }
                    });
                }
                Op::Prepare => {
                    w.match_block_stmt(None, "v", |w| {
                        for (_, combinator, variant_ident) in &variants {
                            let (prep_expr, recursive) = if let Some((member, ctx, access)) = rec {
                                self.render_recursive_child_prepare_expr(
                                    combinator,
                                    member,
                                    ctx,
                                    access,
                                    quote! { v },
                                    Some("v"),
                                )
                            } else {
                                let fmt_expr = self.render_exec_combinator_expr_named(
                                    combinator,
                                    param_defns,
                                    CodegenMode::Serialize,
                                );
                                (
                                    self.render_prepare_value(quote! { v }, fmt_expr, combinator),
                                    false,
                                )
                            };

                            if let Some((_, _, _)) = rec {
                                let prep =
                                    self.render_recursive_prepare_result(prep_expr, recursive);
                                w.push_multiline(render_ts(quote! {
                                    #exec_ident::#variant_ident(v) => #prep,
                                }));
                            } else {
                                w.push_multiline(render_ts(quote! {
                                    #exec_ident::#variant_ident(v) => #prep_expr,
                                }));
                            }
                        }
                    });
                }
            }
            return;
        }

        if let Op::Parse = op {
            if rec.is_some() {
                w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
            } else {
                w.line("assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));");
            }
            w.line("Ok((n, v))");
        }
    }

    fn emit_array_choice_prepare_disjointness_proof(
        &self,
        w: &mut CodeWriter,
        branches: &[(Option<ConstArray>, Combinator)],
    ) {
        let explicit_arrays: Vec<(usize, &ConstArray)> = branches
            .iter()
            .enumerate()
            .filter_map(|(idx, (pat, _))| pat.as_ref().map(|p| (idx, p)))
            .collect();

        if explicit_arrays.len() < 2 {
            return;
        }

        w.block("proof", |w| {
            for (idx, pat) in &explicit_arrays {
                let arr_ident = format!("arr{}", idx);
                let arr_ts: TokenStream = arr_ident.parse().unwrap();
                let arr_expr = self.render_const_array_expr(pat, TypeMode::Spec);
                w.push_multiline(render_ts(quote! {
                    let ghost #arr_ts = #arr_expr.deep_view();
                }));
            }

            for i in 0..explicit_arrays.len() {
                for j in (i + 1)..explicit_arrays.len() {
                    let (lhs_idx, lhs_pat) = explicit_arrays[i];
                    let (rhs_idx, rhs_pat) = explicit_arrays[j];
                    let lhs_ident = format!("arr{}", lhs_idx);
                    let rhs_ident = format!("arr{}", rhs_idx);
                    let lhs_ts: TokenStream = lhs_ident.parse().unwrap();
                    let rhs_ts: TokenStream = rhs_ident.parse().unwrap();
                    let index = self
                        .const_array_disjointness_index(lhs_pat, rhs_pat)
                        .expect(
                            "dependent array choice branches must be pairwise disjoint and length-compatible in Prepare codegen",
                        );
                    let idx_lit = syn_usize(index);
                    w.push_multiline(render_ts(quote! {
                        assert(#lhs_ts != #rhs_ts) by {
                            assert(#lhs_ts[#idx_lit] != #rhs_ts[#idx_lit]);
                        };
                    }));
                }
            }
        });
        w.blank_line();
    }

    fn choice_combinators_and_names<'b>(
        &self,
        comb: &'b ChoiceCombinator,
        variant_names: &'b [String],
    ) -> Vec<(&'b Combinator, &'b String)> {
        comb.choices
            .iter()
            .map(|(_, c)| c)
            .zip(variant_names.iter())
            .collect()
    }
}

// ============================================================
// Enum parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_enum_parser_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = enum_parts(comb);
        let prim_expr = self.render_int_combinator_expr(inferred);

        w.call_chain_stmt(
            Some("(n, v)"),
            &render_ts(prim_expr),
            "parse",
            &["&rest"],
            Some("?;"),
        );

        let known_arms: Vec<TokenStream> = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                let ident = format_ident!("{}", variant.name);
                quote! { #value => #exec_ident::#ident, }
            })
            .collect();

        let default_arm = if exhaustive {
            quote! { _ => return Err(ParseError::invalid_tag()), }
        } else {
            quote! { x => #exec_ident::Unknown(x), }
        };

        w.match_block_stmt(Some("enum_val"), "v", |w| {
            for arm in known_arms {
                w.line(render_ts(arm));
            }
            w.line(render_ts(default_arm));
        });

        w.line(render_ts(quote! {
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        }));
        w.line("Ok((n, enum_val))");
    }

    fn emit_enum_serializer_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = enum_parts(comb);
        let prim_expr = self.render_int_combinator_expr(inferred);

        let known_arms: Vec<TokenStream> = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                let ident = format_ident!("{}", variant.name);
                quote! { #exec_ident::#ident => #value, }
            })
            .collect();

        let default_arm = if exhaustive {
            quote! {}
        } else {
            quote! { #exec_ident::Unknown(x) => x, }
        };

        w.match_block_stmt(Some("tag"), "*v", |w| {
            for arm in known_arms {
                w.line(render_ts(arm));
            }
            if !exhaustive {
                w.line(render_ts(default_arm));
            }
        });

        w.call_chain_stmt(
            None,
            &render_ts(prim_expr),
            "serialize",
            &["&tag", "obuf"],
            Some(";"),
        );
    }

    fn emit_enum_prepare_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = enum_parts(comb);
        let prim_expr = self.render_int_combinator_expr(inferred);

        let known_arms: Vec<TokenStream> = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                let ident = format_ident!("{}", variant.name);
                quote! { #exec_ident::#ident => #value, }
            })
            .collect();

        let default_arm = if exhaustive {
            quote! { _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)), }
        } else {
            let disjuncts: Vec<TokenStream> = variants
                .iter()
                .map(|variant| {
                    let lit = int_literal(variant.value, inferred);
                    quote! { x != #lit }
                })
                .collect();
            let guard = if disjuncts.is_empty() {
                quote! { true }
            } else {
                let mut it = disjuncts.into_iter();
                let first = it.next().unwrap();
                it.fold(first, |acc, item| quote! { #acc && #item })
            };
            quote! {
                #exec_ident::Unknown(x) if #guard => x,
                _ => return Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),
            }
        };

        w.match_block_stmt(Some("tag"), "*v", |w| {
            for arm in known_arms {
                w.line(render_ts(arm));
            }
            w.line(render_ts(default_arm));
        });

        w.call_chain_stmt(None, &render_ts(prim_expr), "prepare", &["&tag"], None);
    }
}

// ============================================================
// CombinatorDef parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn emit_combinator_body_impl(
        &self,
        w: &mut CodeWriter,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        op: Op,
        rec: Option<(
            &SccMember,
            &super::recursive::RecCtx<'_>,
            super::recursive::RecExecParamAccess,
        )>,
    ) {
        if let Some((member, ctx, access)) = rec {
            if let Combinator::Invocation(inv) = combinator {
                if ctx.is_in_scc(&inv.func) {
                    match op {
                        Op::Parse => {
                            w.if_block("gas == 0", |w| {
                                w.line("return Err(ParseError::recursion_limit_exceeded());");
                            });
                            let call = self.render_recursive_method_call(
                                inv,
                                member,
                                access,
                                Op::Parse,
                                quote! { ibuf },
                                None,
                            );
                            w.push_multiline(render_ts(quote! {
                                let (n, v) = #call?;
                            }));
                            w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
                            w.line("Ok((n, v))");
                        }
                        Op::Serialize => {
                            let call = self.render_recursive_method_call(
                                inv,
                                member,
                                access,
                                Op::Serialize,
                                quote! { v },
                                Some("v"),
                            );
                            w.line(render_ts(quote! { #call; }));
                        }
                        Op::Prepare => {
                            w.if_block("gas == 0", |w| {
                                w.line(
                                    "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded));",
                                );
                            });
                            let call = self.render_recursive_method_call(
                                inv,
                                member,
                                access,
                                Op::Prepare,
                                quote! { v },
                                Some("v"),
                            );
                            w.line(render_ts(call));
                        }
                    }
                    return;
                }
            }
        }

        match op {
            Op::Parse => {
                let fmt_expr = if rec.is_some() {
                    self.render_exec_combinator_expr(combinator, param_defns, CodegenMode::Parse)
                } else {
                    self.render_exec_combinator_expr_named(
                        combinator,
                        param_defns,
                        CodegenMode::Parse,
                    )
                };

                w.call_chain_stmt(
                    Some("(n, v)"),
                    &render_ts(quote! { #fmt_expr }),
                    "parse",
                    &["ibuf"],
                    Some("?;"),
                );
                if let Some(pred) = self.gen_constraint_pred(combinator, quote! { v }) {
                    w.if_block(format!("!({})", render_ts(pred)), |w| {
                        w.line("return Err(ParseError::predicate_failed());");
                    });
                }
                if rec.is_none() {
                    if matches!(
                        self.ctx.resolve_alias(combinator),
                        Combinator::Option(_) | Combinator::Vec(_)
                    ) {
                        w.line(
                            "broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;",
                        );
                        w.line("let rest = ibuf.skip(n);");
                        w.call_chain_stmt(Some("_"), "Eof", "parse", &["&rest"], Some("?;"));
                    }
                }
                if rec.is_some() {
                    w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
                } else {
                    w.line("assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));");
                }
                w.line("Ok((n, v))");
            }
            Op::Serialize => {
                if rec.is_none() {
                    if let Some(invocation) = self.direct_alias(combinator) {
                        let target_args = self.render_exec_invocation_expr(
                            invocation,
                            param_defns,
                            CodegenMode::Serialize,
                        );
                        w.call_chain_stmt(
                            None,
                            &render_ts(quote! { #target_args }),
                            "serialize",
                            &["v", "obuf"],
                            Some(";"),
                        );
                        return;
                    }
                }
                let fmt_expr = self.render_exec_combinator_expr(
                    combinator,
                    param_defns,
                    CodegenMode::Serialize,
                );
                w.call_chain_stmt(
                    None,
                    &render_ts(quote! { #fmt_expr }),
                    "serialize",
                    &["v", "obuf"],
                    Some(";"),
                );
            }
            Op::Prepare => {
                if rec.is_none() {
                    if let Some(invocation) = self.direct_alias(combinator) {
                        let target_args = self.render_named_exec_invocation_expr(
                            invocation,
                            param_defns,
                            CodegenMode::Serialize,
                        );
                        w.call_chain_stmt(
                            None,
                            &render_ts(quote! { #target_args }),
                            "prepare",
                            &["v"],
                            None,
                        );
                        return;
                    }
                }
                let fmt_expr = if rec.is_some() {
                    self.render_exec_combinator_expr(
                        combinator,
                        param_defns,
                        CodegenMode::Serialize,
                    )
                } else {
                    self.render_exec_combinator_expr_named(
                        combinator,
                        param_defns,
                        CodegenMode::Serialize,
                    )
                };
                let prep = self.render_prepare_value(quote! { v }, fmt_expr, combinator);
                w.line(render_ts(prep));
            }
        }
    }
}

// ============================================================
// Format expression builders (exec mode)
// ============================================================

/// Whether we are generating code for the parsing or serializing direction.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CodegenMode {
    Parse,
    Serialize,
}

impl<'a> Analysis<'a> {
    /// Build the exec-mode combinator expression for a `Combinator`.
    pub(crate) fn render_exec_combinator_expr(
        &self,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        self.render_exec_combinator_expr_impl(combinator, param_defns, mode, false)
    }

    pub(crate) fn render_exec_combinator_expr_named(
        &self,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        self.render_exec_combinator_expr_impl(combinator, param_defns, mode, true)
    }

    fn render_exec_combinator_expr_impl(
        &self,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
        named_invocations: bool,
    ) -> TokenStream {
        match combinator {
            Combinator::AndThen(lhs, rhs) => {
                return self.render_exec_and_then_expr_impl(
                    lhs,
                    rhs,
                    param_defns,
                    mode,
                    named_invocations,
                );
            }
            Combinator::Invocation(invocation) => {
                return if named_invocations {
                    self.render_named_exec_invocation_expr(invocation, param_defns, mode)
                } else {
                    self.render_exec_invocation_expr(invocation, param_defns, mode)
                };
            }
            _ => {}
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(c) => self.render_int_combinator_expr(&c.combinator),
            Combinator::ConstraintEnum(c) => {
                if named_invocations {
                    self.render_named_exec_invocation_expr(&c.combinator, param_defns, mode)
                } else {
                    self.render_exec_invocation_expr(&c.combinator, param_defns, mode)
                }
            }
            Combinator::Wrap(wrap) => {
                let mut body_expr = self.render_exec_combinator_expr_impl(
                    &wrap.combinator,
                    param_defns,
                    mode,
                    false,
                );
                for const_comb in wrap.post.iter() {
                    let (c_fmt, c_val) = self.render_exec_tag_expr(const_comb, param_defns, mode);
                    body_expr = quote! { SuffixTagged(#body_expr, #c_fmt, #c_val) };
                }
                for const_comb in wrap.prior.iter().rev() {
                    let (c_fmt, c_val) = self.render_exec_tag_expr(const_comb, param_defns, mode);
                    body_expr = quote! { PrefixTagged(#c_fmt, #c_val, #body_expr) };
                }
                body_expr
            }
            Combinator::Vec(vestir::VecCombinator::Vec(inner)) => {
                let inner_expr =
                    self.render_exec_combinator_expr_impl(inner, param_defns, mode, false);
                quote! { Star(#inner_expr) }
            }
            Combinator::Array(vestir::ArrayCombinator {
                combinator: inner,
                len,
            }) => {
                let inner_expr =
                    self.render_exec_combinator_expr_impl(inner, param_defns, mode, false);
                match self.eval_const_length_expr(len) {
                    Some(n) => {
                        let n_tok = syn_usize(n);
                        quote! { Array::<#n_tok, _>(#inner_expr) }
                    }
                    None => {
                        let len_expr = self.render_length_expr_with(
                            len,
                            &|name| self.resolve_dep(name, param_defns),
                            None,
                        );
                        quote! { RepeatN(#len_expr, #inner_expr) }
                    }
                }
            }
            Combinator::Bytes(bytes) => match self.eval_const_length_expr(&bytes.len) {
                Some(n) => {
                    let n_tok = syn_usize(n);
                    quote! { Fixed::<#n_tok> }
                }
                None => {
                    let len_expr = self.render_length_expr_with(
                        &bytes.len,
                        &|name| self.resolve_dep(name, param_defns),
                        None,
                    );
                    quote! { Varied(#len_expr) }
                }
            },
            Combinator::Tail(_) => quote! { Tail },
            Combinator::Option(vestir::OptionCombinator(inner)) => {
                let inner_expr =
                    self.render_exec_combinator_expr_impl(inner, param_defns, mode, false);
                quote! { Opt(#inner_expr) }
            }
            Combinator::Invocation(_) | Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn render_exec_and_then_expr_impl(
        &self,
        lhs: &Combinator,
        rhs: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
        named_invocations: bool,
    ) -> TokenStream {
        match self.ctx.resolve_alias(lhs) {
            Combinator::Bytes(bytes) => {
                let len_expr = self.render_length_expr_with(
                    &bytes.len,
                    &|name| self.resolve_dep(name, param_defns),
                    None,
                );
                let inner_expr = self.render_exec_combinator_expr_impl(
                    rhs,
                    param_defns,
                    mode,
                    named_invocations,
                );
                quote! { ExactLen(#len_expr, #inner_expr) }
            }
            _ => {
                let lhs_expr = self.render_exec_combinator_expr_impl(
                    lhs,
                    param_defns,
                    mode,
                    named_invocations,
                );
                let rhs_expr = self.render_exec_combinator_expr_impl(
                    rhs,
                    param_defns,
                    mode,
                    named_invocations,
                );
                quote! { AndThen(#lhs_expr, #rhs_expr) }
            }
        }
    }

    fn render_exec_invocation_expr(
        &self,
        invocation: &vestir::CombinatorInvocation,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        let info = self.info(&invocation.func);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let inv_param_defns = self.param_defns_for(&invocation.func);

        if invocation.args.is_empty() {
            return quote! { #fmt_ident };
        }

        // Build the struct literal
        let field_inits: Vec<TokenStream> = inv_param_defns
            .iter()
            .zip(invocation.args.iter())
            .map(|(param, arg)| match (param, arg) {
                (ParamDefn::Dependent { name, .. }, Param::Dependent(arg_name)) => {
                    let field_ident = format_ident!("{}", name);
                    let arg_tokens = self.resolve_dep(arg_name, param_defns);
                    let final_tokens = match mode {
                        CodegenMode::Parse => arg_tokens,
                        CodegenMode::Serialize => {
                            let is_param = param_defns.iter().any(|p| match p {
                                ParamDefn::Dependent { name: p_name, .. } => p_name == arg_name,
                            });
                            if is_param {
                                arg_tokens
                            } else {
                                quote! { *#arg_tokens }
                            }
                        }
                    };
                    quote! { #field_ident: #final_tokens }
                }
            })
            .collect();
        quote! { #fmt_ident { #(#field_inits),* } }
    }

    fn render_named_exec_invocation_expr(
        &self,
        invocation: &vestir::CombinatorInvocation,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        let name = invocation.func.as_str();
        let fmt_expr = self.render_exec_invocation_expr(invocation, param_defns, mode);
        quote! { Named(#name, #fmt_expr) }
    }

    /// Build the exec format expression for a ConstCombinator.
    fn render_exec_tag_expr(
        &self,
        combinator: &ConstCombinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> (TokenStream, TokenStream) {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(bytes) => {
                let n = syn_usize(bytes.len);
                let values = self.render_const_array_expr(&bytes.values, TypeMode::Exec);
                (quote! { Fixed::<#n> }, values)
            }
            ConstCombinator::ConstInt(int_comb) => {
                let prim = self.render_int_combinator_expr(&int_comb.combinator);
                let value = int_literal(int_comb.value, &int_comb.combinator);
                (prim, value)
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner =
                    self.render_exec_invocation_expr(&enum_comb.combinator, param_defns, mode);
                let enum_ty = self.render_nominal_type(&enum_comb.combinator.func, TypeMode::Exec);
                let variant = format_ident!("{}", enum_comb.variant);
                (quote! { ConstEnum(#inner) }, quote! { #enum_ty::#variant })
            }
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let info = self.info(name);
                let fmt_ident = format_ident!("{}", info.names.fmt);
                (quote! { #fmt_ident.0 }, quote! { #fmt_ident.1 })
            }
        }
    }

    pub(crate) fn render_exec_const_expr(
        &self,
        combinator: &ConstCombinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(bytes) => {
                let n = syn_usize(bytes.len);
                let values = self.render_const_array_expr(&bytes.values, TypeMode::Exec);
                quote! { Const(Fixed::<#n>, #values) }
            }
            ConstCombinator::ConstInt(int_comb) => {
                let prim = self.render_int_combinator_expr(&int_comb.combinator);
                let value = int_literal(int_comb.value, &int_comb.combinator);
                quote! { Const(#prim, #value) }
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner =
                    self.render_exec_invocation_expr(&enum_comb.combinator, param_defns, mode);
                let enum_ty = self.render_nominal_type(&enum_comb.combinator.func, TypeMode::Exec);
                let variant = format_ident!("{}", enum_comb.variant);
                quote! { Const(#inner, #enum_ty::#variant) }
            }
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let info = self.info(name);
                let fmt_ident = format_ident!("{}", info.names.fmt);
                quote! { #fmt_ident }
            }
        }
    }

    fn render_prepare_pred_value(
        &self,
        value_expr: TokenStream,
        combinator: &Combinator,
    ) -> TokenStream {
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) | Combinator::ConstraintEnum(_) => {
                quote! { *#value_expr }
            }
            _ => value_expr,
        }
    }

    pub(crate) fn render_prepare_value(
        &self,
        value_expr: TokenStream,
        fmt_expr: TokenStream,
        combinator: &Combinator,
    ) -> TokenStream {
        let pred_value = self.render_prepare_pred_value(value_expr.clone(), combinator);
        if let Some(pred) = self.gen_constraint_pred(combinator, pred_value) {
            quote! {{
                if !(#pred) {
                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (#fmt_expr).prepare(#value_expr)
                }
            }}
        } else {
            quote! { (#fmt_expr).prepare(#value_expr) }
        }
    }

    pub(crate) fn emit_checked_add_return(
        &self,
        w: &mut CodeWriter,
        total_name: &str,
        terms: &[String],
    ) {
        if terms.is_empty() {
            w.line("Ok(0usize)");
            return;
        }

        let mut acc: TokenStream = terms[0].parse().unwrap();
        for term in &terms[1..] {
            let next: TokenStream = term.parse().unwrap();
            acc = quote! { #acc.checked_add(#next).ok_or(PreSerializeError::length_too_large())? };
        }
        w.line(format!("let {} = {};", total_name, render_ts(acc)));
        w.line(format!("Ok({})", total_name));
    }

    /// Try to resolve the enum type of a dependent field `dep` in the struct or params context.
    pub(crate) fn resolve_dep_enum_type(
        &self,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Option<TokenStream> {
        self.resolve_dep_enum_info(dep, param_defns)
            .map(|(name, _)| self.render_nominal_type(name, TypeMode::Exec))
    }

    fn resolve_dep_enum_info(
        &self,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Option<(&'a str, &'a EnumCombinator)> {
        let resolved = self.resolve_dep_combinator_path(dep, param_defns)?;
        let enum_name = match resolved {
            Combinator::Invocation(inv) => inv.func,
            _ => return None,
        };

        self.defs.iter().find_map(|def| match def {
            vestir::Definition::EnumDef {
                name, combinator, ..
            } if *name == enum_name => Some((name.as_str(), combinator)),
            _ => None,
        })
    }

    fn const_array_bytes(&self, arr: &ConstArray) -> Option<Vec<u8>> {
        match arr {
            ConstArray::Char(bytes) => Some(bytes.clone()),
            ConstArray::Int(values) => Some(
                values
                    .iter()
                    .map(|value| {
                        u8::try_from(*value).expect("integer array pattern out of u8 range")
                    })
                    .collect(),
            ),
            ConstArray::Repeat(value, len) => {
                let byte = u8::try_from(*value).expect("repeat array pattern out of u8 range");
                Some(vec![byte; *len])
            }
        }
    }

    fn const_array_disjointness_index(&self, lhs: &ConstArray, rhs: &ConstArray) -> Option<usize> {
        let lhs_vals = self.const_array_bytes(lhs)?;
        let rhs_vals = self.const_array_bytes(rhs)?;
        assert_eq!(
            lhs_vals.len(),
            rhs_vals.len(),
            "type_check should guarantee equal-length array patterns for dependent array choices",
        );
        for (idx, (lhs_b, rhs_b)) in lhs_vals.iter().zip(rhs_vals.iter()).enumerate() {
            if lhs_b != rhs_b {
                return Some(idx);
            }
        }
        None
    }

    pub(crate) fn gen_constraint_pred(
        &self,
        combinator: &Combinator,
        val_tokens: TokenStream,
    ) -> Option<TokenStream> {
        let resolved = self.ctx.resolve_alias(combinator);
        match resolved {
            Combinator::ConstraintInt(c) => c.constraint.as_ref().map(|constraint| {
                self.render_int_constraint(constraint, &c.combinator, val_tokens)
            }),
            Combinator::ConstraintEnum(c) => {
                let value_ty = self.render_nominal_type(&c.combinator.func, TypeMode::Exec);
                Some(self.render_enum_constraint(&c.constraint, &value_ty, val_tokens))
            }
            _ => None,
        }
    }
}

fn struct_field_name_strings(fields: &[StructField]) -> Vec<String> {
    fields
        .iter()
        .map(|f| {
            let label = match f {
                StructField::Const { label, .. }
                | StructField::Dependent { label, .. }
                | StructField::Ordinary { label, .. } => label,
            };
            label.to_string()
        })
        .collect()
}

fn enum_parts(
    comb: &EnumCombinator,
) -> (&[crate::vestir::Enum], bool, &crate::vestir::IntCombinator) {
    match comb {
        EnumCombinator::Exhaustive { enums, inferred } => (enums.as_slice(), true, inferred),
        EnumCombinator::NonExhaustive { enums, inferred } => (enums.as_slice(), false, inferred),
    }
}
