use super::common::{int_literal, render_ts, syn_usize, Analysis, CodeWriter, TypeMode};
use crate::vestir::{
    self, ChoiceCombinator, Choices, Combinator, ConstArray, ConstCombinator, EnumCombinator,
    Param, ParamDefn, StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};

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
        let exec_ty = self.nominal_type(name, TypeMode::Exec);
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

    fn choice_branch_count(&self, choices: &Choices) -> usize {
        match choices {
            Choices::Ints(branches) => branches.len(),
            Choices::Enums(branches) => branches.len(),
            Choices::Arrays(branches) => branches.len(),
        }
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
                self.emit_combinator_parser_body(w, combinator, param_defns);
            },
            |w| {
                self.emit_combinator_serializer_body(w, combinator, param_defns);
            },
            |w| {
                self.emit_combinator_prepare_body(w, combinator, param_defns);
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
                self.emit_struct_parser_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_struct_serializer_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_struct_prepare_body(w, name, combinator, param_defns);
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
        let use_spinoff = self.choice_branch_count(&combinator.choices) > SPINOFF_PROVER_THRESHOLD;
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_choice_parser_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_choice_serializer_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_choice_prepare_body(w, name, combinator, param_defns);
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
}

// ============================================================
// Struct parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_struct_parser_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &StructCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let fields = &comb.0;
        let mut n_vars: Vec<String> = Vec::new();

        for (i, field) in fields.iter().enumerate() {
            let n_var = format!("n{}", i + 1);
            match field {
                StructField::Const { label, combinator } => {
                    let fmt_expr =
                        self.exec_const_fmt_expr(combinator, param_defns, CodegenMode::Parse);
                    let fmt_str = render_ts(quote! { #fmt_expr });
                    w.call_chain_stmt(
                        Some(&format!("({}, {})", n_var, label)),
                        &fmt_str,
                        "parse",
                        &["&rest"],
                        Some("?;"),
                    );
                    w.line(format!("let rest = rest.skip({});", n_var));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let fmt_expr =
                        self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Parse);
                    let fmt_str = render_ts(quote! { #fmt_expr });
                    w.call_chain_stmt(
                        Some(&format!("({}, {})", n_var, label)),
                        &fmt_str,
                        "parse",
                        &["&rest"],
                        Some("?;"),
                    );
                    let label_ident = format_ident!("{}", label);
                    if let Some(pred) =
                        self.gen_constraint_pred(combinator, quote! { #label_ident })
                    {
                        w.if_block(format!("!({})", render_ts(pred)), |w| {
                            w.line("return Err(ParseError::predicate_failed());");
                        });
                    }
                    w.line(format!("let rest = rest.skip({});", n_var));
                    if i == fields.len() - 1 {
                        if matches!(
                            self.ctx.resolve_alias(combinator),
                            Combinator::Option(_) | Combinator::Vec(_)
                        ) {
                            w.call_chain_stmt(Some("_"), "Eof", "parse", &["&rest"], Some("?;"));
                        }
                    }
                }
            }
            n_vars.push(n_var);
        }

        // total_n
        let total_n_expr = if n_vars.is_empty() {
            "0usize".to_string()
        } else {
            n_vars.join(" + ")
        };
        w.line(format!("let total_n = {};", total_n_expr));

        let struct_field_names = struct_field_name_strings(fields);
        w.record_constructor_stmt("final_v", &exec_ident.to_string(), &struct_field_names);
        w.line("assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));");
        w.line("Ok((total_n, final_v))");
    }

    fn emit_struct_serializer_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &StructCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let fields = &comb.0;

        // Destructure the value
        let struct_field_names = struct_field_name_strings(fields);
        w.record_destructure_stmt(&exec_ident.to_string(), &struct_field_names, "v");

        for field in fields {
            match field {
                StructField::Const { label, combinator } => {
                    let fmt_expr =
                        self.exec_const_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
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
                    let fmt_expr = self.exec_combinator_fmt_expr(
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

    fn emit_struct_prepare_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &StructCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let fields = &comb.0;

        // Destructure the value
        let struct_field_names = struct_field_name_strings(fields);
        w.record_destructure_stmt(&exec_ident.to_string(), &struct_field_names, "v");

        let mut l_vars: Vec<String> = Vec::new();
        for (i, field) in fields.iter().enumerate() {
            let l_var = format!("l{}", i + 1);
            let l_var_tok: TokenStream = l_var.parse().unwrap();
            match field {
                StructField::Const { label, combinator } => {
                    let label_ident: TokenStream = format_ident!("{}", label).into_token_stream();
                    let fmt_expr =
                        self.exec_const_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                    let prep = quote! { (#fmt_expr).prepare(#label_ident) };
                    w.push_multiline(render_ts(quote! { let #l_var_tok = #prep?; }));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident: TokenStream = format_ident!("{}", label).into_token_stream();
                    let fmt_expr = self.exec_combinator_fmt_expr(
                        combinator,
                        param_defns,
                        CodegenMode::Serialize,
                    );
                    let prep = self.exec_prepare_value(label_ident, fmt_expr, combinator);
                    w.push_multiline(render_ts(quote! { let #l_var_tok = #prep?; }));
                }
            }
            l_vars.push(l_var);
        }

        self.emit_checked_add_return(w, "total_len", &l_vars);
    }
}

// ============================================================
// Choice parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_choice_parser_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let variant_names = self.choice_variant_names(comb);

        if let Some(dep) = &comb.depend_id {
            // Dependent choice: match on the selector field
            let match_arms: Vec<TokenStream> =
                self.choice_parser_arms(comb, &variant_names, &exec_ident, dep, param_defns);
            w.match_block_stmt(Some("(n, v)"), &format!("self.{}", dep), |w| {
                for arm in match_arms {
                    w.push_multiline(render_ts(arm));
                }
            });
        } else {
            // Non-dependent choice: delegate to the spec fmt combinator
            let branches: TokenStream =
                self.choice_parse_arms_nondep(comb, &variant_names, &exec_ident, param_defns);
            w.call_chain_stmt(
                Some("(n, v)"),
                &render_ts(branches),
                "",
                &[] as &[&str],
                Some("?;"),
            );
        }
        w.line("assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));");
        w.line("Ok((n, v))");
    }

    fn choice_parser_arms(
        &self,
        comb: &ChoiceCombinator,
        variant_names: &[String],
        exec_ident: &proc_macro2::Ident,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Vec<TokenStream> {
        match &comb.choices {
            Choices::Enums(branches) => {
                // Find the enum type from the dep field
                let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                branches
                    .iter()
                    .zip(variant_names.iter())
                    .map(|((pat, combinator), variant_name)| {
                        let variant_ident = format_ident!("{}", variant_name);
                        let fmt_expr = self.exec_combinator_fmt_expr(
                            combinator,
                            param_defns,
                            CodegenMode::Parse,
                        );
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
                        if pat == "_" {
                            quote! {
                                _ => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        } else {
                            let pat_ident = format_ident!("{}", pat);
                            let enum_ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                            quote! {
                                #enum_ty::#pat_ident => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        }
                    })
                    .collect()
            }
            Choices::Ints(branches) => branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr =
                        self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Parse);
                    let check =
                        if let Some(pred) = self.gen_constraint_pred(combinator, quote! { v }) {
                            quote! {
                                if !(#pred) {
                                    return Err(ParseError::predicate_failed());
                                }
                            }
                        } else {
                            quote! {}
                        };
                    match pat {
                        None => {
                            quote! {
                                _ => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        }
                        Some(elem) => {
                            let pat_ts = self.int_constraint_elem_exec_pat(elem);
                            quote! {
                                #pat_ts => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        }
                    }
                })
                .collect(),
            Choices::Arrays(branches) => branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr =
                        self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Parse);
                    let check =
                        if let Some(pred) = self.gen_constraint_pred(combinator, quote! { v }) {
                            quote! {
                                if !(#pred) {
                                    return Err(ParseError::predicate_failed());
                                }
                            }
                        } else {
                            quote! {}
                        };
                    match pat {
                        ConstArray::Wildcard => {
                            quote! {
                                _ => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        }
                        _ => {
                            let pat_expr = self.render_const_array_expr(pat, TypeMode::Exec);
                            quote! {
                                x if x.deep_eq(&#pat_expr) => {
                                    let (n, v) = (#fmt_expr).parse(&rest)?;
                                    #check
                                    (n, #exec_ident::#variant_ident(v))
                                },
                            }
                        }
                    }
                })
                .collect(),
        }
    }

    fn choice_parse_arms_nondep(
        &self,
        comb: &ChoiceCombinator,
        variant_names: &[String],
        exec_ident: &proc_macro2::Ident,
        param_defns: &[ParamDefn],
    ) -> TokenStream {
        // For non-dependent choices we try each branch in order
        let mut chain = quote! { Err(ParseError::invalid_tag()) };
        for (combinator, variant_name) in self
            .choice_combinators_and_names(comb, variant_names)
            .into_iter()
            .rev()
        {
            let variant_ident = format_ident!("{}", variant_name);
            let fmt_expr =
                self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Parse);
            if let Some(pred) = self.gen_constraint_pred(combinator, quote! { va }) {
                chain = quote! {
                    match (#fmt_expr).parse(&rest) {
                        Ok((n, va)) if #pred => {
                            Ok((n, #exec_ident::#variant_ident(va)))
                        },
                        _ => #chain,
                    }
                };
            } else {
                chain = quote! {
                    match (#fmt_expr).parse(&rest) {
                        Ok((n, va)) => {
                            Ok((n, #exec_ident::#variant_ident(va)))
                        },
                        _ => #chain,
                    }
                };
            }
        }
        chain
    }

    fn emit_choice_serializer_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let variant_names = self.choice_variant_names(comb);

        if let Some(dep) = &comb.depend_id {
            let dep_expr = self.resolve_dep(dep, param_defns);
            let arms = self.choice_serializer_arms_dep(
                comb,
                &variant_names,
                &exec_ident,
                dep,
                param_defns,
            );
            w.match_block_stmt(None, &format!("({}, v)", render_ts(dep_expr)), |w| {
                for arm in arms {
                    w.push_multiline(render_ts(arm));
                }
                w.line("_ => {},");
            });
            return;
        }

        let arms: Vec<TokenStream> = self
            .choice_combinators_and_names(comb, &variant_names)
            .into_iter()
            .map(|(combinator, variant_name)| {
                let variant_ident = format_ident!("{}", variant_name);
                let fmt_expr =
                    self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                let ser = self.exec_serialize_value(quote! { v }, fmt_expr);
                quote! {
                    #exec_ident::#variant_ident(v) => { #ser }
                }
            })
            .collect();

        w.match_block_stmt(None, "v", |w| {
            for arm in arms {
                w.push_multiline(render_ts(arm));
            }
        });
    }

    fn choice_serializer_arms_dep(
        &self,
        comb: &ChoiceCombinator,
        variant_names: &[String],
        exec_ident: &proc_macro2::Ident,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Vec<TokenStream> {
        match &comb.choices {
            Choices::Enums(branches) => {
                let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                branches
                    .iter()
                    .zip(variant_names.iter())
                    .map(|((pat, combinator), variant_name)| {
                        let variant_ident = format_ident!("{}", variant_name);
                        let fmt_expr =
                            self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                        let ser = self.exec_serialize_value(quote! { v }, fmt_expr);
                        if pat == "_" {
                            quote! {
                                (_, #exec_ident::#variant_ident(v)) => { #ser }
                            }
                        } else {
                            let pat_ident = format_ident!("{}", pat);
                            let enum_ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                            quote! {
                                (#enum_ty::#pat_ident, #exec_ident::#variant_ident(v)) => { #ser }
                            }
                        }
                    })
                    .collect()
            }
            Choices::Ints(branches) => branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                    let ser = self.exec_serialize_value(quote! { v }, fmt_expr);
                    match pat {
                        None => {
                            quote! {
                                (_, #exec_ident::#variant_ident(v)) => { #ser }
                            }
                        }
                        Some(elem) => match elem {
                            vestir::ConstraintElem::Single(v) => {
                                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                quote! {
                                    (#lit, #exec_ident::#variant_ident(v)) => { #ser }
                                }
                            }
                            vestir::ConstraintElem::Range {
                                start: Some(start),
                                end: Some(end),
                            } => {
                                let s = proc_macro2::Literal::i128_unsuffixed(*start);
                                let e = proc_macro2::Literal::i128_unsuffixed(*end);
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if x >= #s && x <= #e => { #ser }
                                }
                            }
                            _ => {
                                let cond = self.render_constraint_elem_exec(elem, quote! { x });
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if #cond => { #ser }
                                }
                            }
                        },
                    }
                })
                .collect(),
            Choices::Arrays(branches) => branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                    let ser = self.exec_serialize_value(quote! { v }, fmt_expr);
                    match pat {
                        ConstArray::Wildcard => {
                            quote! {
                                (_, #exec_ident::#variant_ident(v)) => { #ser }
                            }
                        }
                        _ => {
                            let pat_expr = self.render_const_array_expr(pat, TypeMode::Exec);
                            quote! {
                                (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) => { #ser }
                            }
                        }
                    }
                })
                .collect(),
        }
    }

    fn emit_choice_prepare_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        comb: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let variant_names = self.choice_variant_names(comb);

        if let Some(dep) = &comb.depend_id {
            if let Choices::Arrays(branches) = &comb.choices {
                self.emit_array_choice_prepare_disjointness_proof(w, branches);
            }
            let dep_expr = self.resolve_dep(dep, param_defns);
            let arms =
                self.choice_prepare_arms_dep(comb, &variant_names, &exec_ident, dep, param_defns);
            w.match_block_stmt(None, &format!("({}, v)", render_ts(dep_expr)), |w| {
                for arm in arms {
                    w.push_multiline(render_ts(arm));
                }
                w.line(
                    " _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),",
                );
            });
            return;
        }

        let arms: Vec<TokenStream> = self
            .choice_combinators_and_names(comb, &variant_names)
            .into_iter()
            .map(|(combinator, variant_name)| {
                let variant_ident = format_ident!("{}", variant_name);
                let fmt_expr =
                    self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
                let prep = self.exec_prepare_value(quote! { v }, fmt_expr, combinator);
                quote! {
                    #exec_ident::#variant_ident(v) => #prep,
                }
            })
            .collect();

        w.match_block_stmt(None, "v", |w| {
            for arm in arms {
                w.push_multiline(render_ts(arm));
            }
        });
    }

    fn choice_prepare_arms_dep(
        &self,
        comb: &ChoiceCombinator,
        variant_names: &[String],
        exec_ident: &proc_macro2::Ident,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Vec<TokenStream> {
        match &comb.choices {
            Choices::Enums(branches) => {
                let enum_ty = self.resolve_dep_enum_type(dep, param_defns);
                let enum_comb = self.resolve_dep_enum_combinator(dep, param_defns);
                let covered_pats: Vec<&str> = branches
                    .iter()
                    .filter_map(|(pat, _)| if pat == "_" { None } else { Some(pat.as_str()) })
                    .collect();
                branches
                    .iter()
                    .zip(variant_names.iter())
                    .flat_map(|((pat, combinator), variant_name)| {
                        let variant_ident = format_ident!("{}", variant_name);
                        let fmt_expr = self.exec_combinator_fmt_expr(
                            combinator,
                            param_defns,
                            CodegenMode::Serialize,
                        );
                        let prep = self.exec_prepare_value(quote! { v }, fmt_expr, combinator);

                        if pat == "_" {
                            let mut arms = Vec::new();
                            if let (Some(enum_ty), Some(enum_comb)) = (enum_ty.clone(), enum_comb) {
                                let variants = match enum_comb {
                                    EnumCombinator::Exhaustive { enums, .. }
                                    | EnumCombinator::NonExhaustive { enums, .. } => enums,
                                };
                                for variant in variants {
                                    if covered_pats.iter().any(|pat| *pat == variant.name.as_str()) {
                                        continue;
                                    }
                                    let known_ident = format_ident!("{}", variant.name);
                                    arms.push(quote! {
                                        (#enum_ty::#known_ident, #exec_ident::#variant_ident(v)) => #prep,
                                    });
                                }
                                if let EnumCombinator::NonExhaustive { enums, inferred } = enum_comb {
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
                                    arms.push(quote! {
                                        (#enum_ty::Unknown(x), #exec_ident::#variant_ident(v)) if #guard => #prep,
                                    });
                                }
                            } else {
                                arms.push(quote! {
                                    (_, #exec_ident::#variant_ident(v)) => #prep,
                                });
                            }
                            arms
                        } else {
                            let pat_ident = format_ident!("{}", pat);
                            let enum_ty = enum_ty.clone().unwrap_or_else(|| quote! { _ });
                            vec![quote! {
                                (#enum_ty::#pat_ident, #exec_ident::#variant_ident(v)) => #prep,
                            }]
                        }
                    })
                    .collect()
            }
            Choices::Ints(branches) => {
                let known_conds: Vec<TokenStream> = branches
                    .iter()
                    .filter_map(|(pat, _)| pat.as_ref())
                    .map(|elem| self.render_constraint_elem_exec(elem, quote! { x }))
                    .collect();
                branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr = self.exec_combinator_fmt_expr(
                        combinator,
                        param_defns,
                        CodegenMode::Serialize,
                    );
                    let prep = self.exec_prepare_value(quote! { v }, fmt_expr, combinator);
                    match pat {
                        None => {
                            if known_conds.is_empty() {
                                quote! {
                                    (_, #exec_ident::#variant_ident(v)) => #prep,
                                }
                            } else {
                                let guard = known_conds
                                    .iter()
                                    .cloned()
                                    .map(|cond| quote! { !(#cond) })
                                    .reduce(|acc, cond| quote! { #acc && #cond })
                                    .unwrap();
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if #guard => #prep,
                                }
                            }
                        }
                        Some(elem) => match elem {
                            vestir::ConstraintElem::Single(v) => {
                                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                quote! {
                                    (#lit, #exec_ident::#variant_ident(v)) => #prep,
                                }
                            }
                            vestir::ConstraintElem::Range {
                                start: Some(start),
                                end: Some(end),
                            } => {
                                let s = proc_macro2::Literal::i128_unsuffixed(*start);
                                let e = proc_macro2::Literal::i128_unsuffixed(*end);
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if x >= #s && x <= #e => #prep,
                                }
                            }
                            _ => {
                                let cond = self.render_constraint_elem_exec(elem, quote! { x });
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if #cond => #prep,
                                }
                            }
                        },
                    }
                })
                .collect()
            }
            Choices::Arrays(branches) => {
                let known_pats: Vec<&ConstArray> = branches
                    .iter()
                    .filter_map(|(pat, _)| match pat {
                        ConstArray::Wildcard => None,
                        _ => Some(pat),
                    })
                    .collect();
                branches
                .iter()
                .zip(variant_names.iter())
                .map(|((pat, combinator), variant_name)| {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr = self.exec_combinator_fmt_expr(
                        combinator,
                        param_defns,
                        CodegenMode::Serialize,
                    );
                    let prep = self.exec_prepare_value(quote! { v }, fmt_expr, combinator);
                    match pat {
                        ConstArray::Wildcard => {
                            if known_pats.is_empty() {
                                quote! {
                                    (_, #exec_ident::#variant_ident(v)) => #prep,
                                }
                            } else {
                                let guard = known_pats
                                    .iter()
                                    .map(|pat| {
                                        let pat_expr =
                                            self.render_const_array_expr(pat, TypeMode::Exec);
                                        quote! { !x.deep_eq(&#pat_expr) }
                                    })
                                    .reduce(|acc, cond| quote! { #acc && #cond })
                                    .unwrap();
                                quote! {
                                    (x, #exec_ident::#variant_ident(v)) if #guard => #prep,
                                }
                            }
                        }
                        _ => {
                            let pat_expr = self.render_const_array_expr(pat, TypeMode::Exec);
                            quote! {
                                (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) => #prep,
                            }
                        }
                    }
                })
                .collect()
            }
        }
    }

    fn emit_array_choice_prepare_disjointness_proof(
        &self,
        w: &mut CodeWriter,
        branches: &[(ConstArray, Combinator)],
    ) {
        let explicit_arrays: Vec<(usize, &ConstArray)> = branches
            .iter()
            .enumerate()
            .filter_map(|(idx, (pat, _))| match pat {
                ConstArray::Wildcard => None,
                _ => Some((idx, pat)),
            })
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
}

// ============================================================
// Enum parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_enum_parser_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = enum_parts(comb);
        let prim_expr = self.int_combinator_expr(inferred);

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
        let prim_expr = self.int_combinator_expr(inferred);

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
        let prim_expr = self.int_combinator_expr(inferred);

        let known_arms: Vec<TokenStream> = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                let ident = format_ident!("{}", variant.name);
                quote! { #exec_ident::#ident => #value, }
            })
            .collect();

        let default_arm = if exhaustive {
            quote! { _ => return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)), }
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
                _ => return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
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
    fn emit_combinator_parser_body(
        &self,
        w: &mut CodeWriter,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Parse);

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
        if matches!(
            self.ctx.resolve_alias(combinator),
            Combinator::Option(_) | Combinator::Vec(_)
        ) {
            w.line("let rest = ibuf.skip(n);");
            w.call_chain_stmt(Some("_"), "Eof", "parse", &["&rest"], Some("?;"));
        }
        w.line("assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));");
        w.line("Ok((n, v))");
    }

    fn emit_combinator_serializer_body(
        &self,
        w: &mut CodeWriter,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        if let Some(invocation) = self.direct_alias(combinator) {
            let target_args =
                self.exec_invocation_fmt_expr(invocation, param_defns, CodegenMode::Serialize);
            w.call_chain_stmt(
                None,
                &render_ts(quote! { #target_args }),
                "serialize",
                &["v", "obuf"],
                Some(";"),
            );
            return;
        }
        let fmt_expr =
            self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
        w.call_chain_stmt(
            None,
            &render_ts(quote! { #fmt_expr }),
            "serialize",
            &["v", "obuf"],
            Some(";"),
        );
    }

    fn emit_combinator_prepare_body(
        &self,
        w: &mut CodeWriter,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        if let Some(invocation) = self.direct_alias(combinator) {
            let target_args =
                self.exec_invocation_fmt_expr(invocation, param_defns, CodegenMode::Serialize);
            w.call_chain_stmt(
                None,
                &render_ts(quote! { #target_args }),
                "prepare",
                &["v"],
                None,
            );
            return;
        }
        let fmt_expr =
            self.exec_combinator_fmt_expr(combinator, param_defns, CodegenMode::Serialize);
        let prep = self.exec_prepare_value(quote! { v }, fmt_expr, combinator);
        w.line(render_ts(prep));
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
    fn choice_combinators_and_names<'b>(
        &self,
        comb: &'b ChoiceCombinator,
        variant_names: &'b [String],
    ) -> Vec<(&'b Combinator, &'b String)> {
        match &comb.choices {
            Choices::Enums(b) => b.iter().map(|(_, c)| c).zip(variant_names.iter()).collect(),
            Choices::Ints(b) => b.iter().map(|(_, c)| c).zip(variant_names.iter()).collect(),
            Choices::Arrays(b) => b.iter().map(|(_, c)| c).zip(variant_names.iter()).collect(),
        }
    }

    /// Build the exec-mode combinator expression for a `Combinator`.
    pub(crate) fn exec_combinator_fmt_expr(
        &self,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        match combinator {
            Combinator::AndThen(lhs, rhs) => {
                return self.exec_and_then_fmt_expr(lhs, rhs, param_defns, mode);
            }
            Combinator::Invocation(invocation) => {
                return self.exec_invocation_fmt_expr(invocation, param_defns, mode);
            }
            _ => {}
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(c) => self.int_combinator_expr(&c.combinator),
            Combinator::ConstraintEnum(c) => {
                self.exec_invocation_fmt_expr(&c.combinator, param_defns, mode)
            }
            Combinator::Wrap(wrap) => {
                let mut body_expr =
                    self.exec_combinator_fmt_expr(&wrap.combinator, param_defns, mode);
                for const_comb in wrap.post.iter() {
                    let (c_fmt, c_val) = self.exec_tag_expr(const_comb, param_defns, mode);
                    body_expr = quote! { SuffixTagged(#body_expr, #c_fmt, #c_val) };
                }
                for const_comb in wrap.prior.iter().rev() {
                    let (c_fmt, c_val) = self.exec_tag_expr(const_comb, param_defns, mode);
                    body_expr = quote! { PrefixTagged(#c_fmt, #c_val, #body_expr) };
                }
                body_expr
            }
            Combinator::Vec(vestir::VecCombinator::Vec(inner)) => {
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, mode);
                quote! { Star(#inner_expr) }
            }
            Combinator::Array(vestir::ArrayCombinator {
                combinator: inner,
                len,
            }) => {
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, mode);
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
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, mode);
                quote! { Opt(#inner_expr) }
            }
            Combinator::Invocation(_) | Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn exec_and_then_fmt_expr(
        &self,
        lhs: &Combinator,
        rhs: &Combinator,
        param_defns: &[ParamDefn],
        mode: CodegenMode,
    ) -> TokenStream {
        match self.ctx.resolve_alias(lhs) {
            Combinator::Bytes(bytes) => {
                let len_expr = self.render_length_expr_with(
                    &bytes.len,
                    &|name| self.resolve_dep(name, param_defns),
                    None,
                );
                let inner_expr = self.exec_combinator_fmt_expr(rhs, param_defns, mode);
                quote! { ExactLen(#len_expr, #inner_expr) }
            }
            _ => {
                let lhs_expr = self.exec_combinator_fmt_expr(lhs, param_defns, mode);
                let rhs_expr = self.exec_combinator_fmt_expr(rhs, param_defns, mode);
                quote! { AndThen(#lhs_expr, #rhs_expr) }
            }
        }
    }

    fn exec_invocation_fmt_expr(
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

    /// Build the exec format expression for a ConstCombinator.
    fn exec_tag_expr(
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
                let prim = self.int_combinator_expr(&int_comb.combinator);
                let value = int_literal(int_comb.value, &int_comb.combinator);
                (prim, value)
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner = self.exec_invocation_fmt_expr(&enum_comb.combinator, param_defns, mode);
                let enum_ty = self.nominal_type(&enum_comb.combinator.func, TypeMode::Exec);
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

    fn exec_const_fmt_expr(
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
                let prim = self.int_combinator_expr(&int_comb.combinator);
                let value = int_literal(int_comb.value, &int_comb.combinator);
                quote! { Const(#prim, #value) }
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner = self.exec_invocation_fmt_expr(&enum_comb.combinator, param_defns, mode);
                let enum_ty = self.nominal_type(&enum_comb.combinator.func, TypeMode::Exec);
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

    fn int_constraint_elem_exec_pat(&self, elem: &vestir::ConstraintElem) -> TokenStream {
        match elem {
            vestir::ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #lit }
            }
            vestir::ConstraintElem::Range {
                start: Some(start),
                end: Some(end),
            } => {
                let s = proc_macro2::Literal::i128_unsuffixed(*start);
                let e = proc_macro2::Literal::i128_unsuffixed(*end);
                quote! { #s ..= #e }
            }
            _ => {
                // complex range — use a guard
                let cond = self.render_constraint_elem_exec(elem, quote! { x });
                quote! { x if #cond }
            }
        }
    }

    fn render_constraint_elem_exec(
        &self,
        elem: &vestir::ConstraintElem,
        value: TokenStream,
    ) -> TokenStream {
        match elem {
            vestir::ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #value == #lit }
            }
            vestir::ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    fn render_int_constraint_exec(
        &self,
        constraint: &vestir::IntConstraint,
        int_ty: &vestir::IntCombinator,
        value: TokenStream,
    ) -> TokenStream {
        match constraint {
            vestir::IntConstraint::Single(elem) => {
                self.render_int_constraint_elem_exec(elem, int_ty, value)
            }
            vestir::IntConstraint::Set(elems) => {
                let parts: Vec<_> = elems
                    .iter()
                    .map(|elem| self.render_int_constraint_elem_exec(elem, int_ty, value.clone()))
                    .collect();
                quote! { #(#parts)||* }
            }
            vestir::IntConstraint::Neg(inner) => {
                let inner = self.render_int_constraint_exec(inner, int_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn render_int_constraint_elem_exec(
        &self,
        elem: &vestir::ConstraintElem,
        int_ty: &vestir::IntCombinator,
        value: TokenStream,
    ) -> TokenStream {
        match elem {
            vestir::ConstraintElem::Single(v) => {
                let lit = int_literal(*v, int_ty);
                quote! { #value == #lit }
            }
            vestir::ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    fn render_enum_constraint_exec(
        &self,
        constraint: &vestir::EnumConstraint,
        enum_ty: &TokenStream,
        value: TokenStream,
    ) -> TokenStream {
        match constraint {
            vestir::EnumConstraint::Single(name) => {
                let variant = format_ident!("{}", name);
                quote! { #value == #enum_ty::#variant }
            }
            vestir::EnumConstraint::Set(names) => {
                let parts: Vec<_> = names
                    .iter()
                    .map(|name| {
                        let variant = format_ident!("{}", name);
                        quote! { #value == #enum_ty::#variant }
                    })
                    .collect();
                quote! { #(#parts)||* }
            }
            vestir::EnumConstraint::Neg(inner) => {
                let inner = self.render_enum_constraint_exec(inner, enum_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn exec_serialize_value(&self, value_expr: TokenStream, fmt_expr: TokenStream) -> TokenStream {
        quote! { (#fmt_expr).serialize(#value_expr, obuf); }
    }

    fn prepare_pred_value(&self, value_expr: TokenStream, combinator: &Combinator) -> TokenStream {
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) | Combinator::ConstraintEnum(_) => {
                quote! { *#value_expr }
            }
            _ => value_expr,
        }
    }

    fn exec_prepare_value(
        &self,
        value_expr: TokenStream,
        fmt_expr: TokenStream,
        combinator: &Combinator,
    ) -> TokenStream {
        let pred_value = self.prepare_pred_value(value_expr.clone(), combinator);
        if let Some(pred) = self.gen_constraint_pred(combinator, pred_value) {
            quote! {{
                if !(#pred) {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed))
                } else {
                    (#fmt_expr).prepare(#value_expr)
                }
            }}
        } else {
            quote! { (#fmt_expr).prepare(#value_expr) }
        }
    }

    fn emit_checked_add_return(&self, w: &mut CodeWriter, total_name: &str, terms: &[String]) {
        if terms.is_empty() {
            w.line("Ok(0usize)");
            return;
        }

        let mut acc: TokenStream = terms[0].parse().unwrap();
        for term in &terms[1..] {
            let next: TokenStream = term.parse().unwrap();
            acc = quote! { #acc.checked_add(#next).ok_or(PreSerializeError::LengthTooLarge)? };
        }
        w.line(format!("let {} = {};", total_name, render_ts(acc)));
        w.line(format!("Ok({})", total_name));
    }

    /// Try to resolve the enum type of a dependent field `dep` in the struct or params context.
    fn resolve_dep_enum_type(&self, dep: &str, param_defns: &[ParamDefn]) -> Option<TokenStream> {
        self.resolve_dep_enum_info(dep, param_defns)
            .map(|(name, _)| self.nominal_type(name, TypeMode::Exec))
    }

    fn resolve_dep_enum_combinator(
        &self,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Option<&'a EnumCombinator> {
        self.resolve_dep_enum_info(dep, param_defns)
            .map(|(_, comb)| comb)
    }

    fn resolve_dep_enum_info(
        &self,
        dep: &str,
        param_defns: &[ParamDefn],
    ) -> Option<(&'a str, &'a EnumCombinator)> {
        let base = dep.split('.').last().unwrap_or(dep);
        let mut enum_name: Option<&str> = None;
        // Search in all struct defs for a Dependent field with this name
        for def in self.defs {
            if let vestir::Definition::StructDef { combinator, .. } = def {
                for field in &combinator.0 {
                    if let StructField::Dependent { label, combinator } = field {
                        if label == base {
                            if let Combinator::Invocation(inv) = combinator {
                                enum_name = Some(inv.func.as_str());
                                break;
                            }
                        }
                    }
                }
            }
            if enum_name.is_some() {
                break;
            }
        }
        // Also search in param_defns
        if enum_name.is_none() {
            for p in param_defns {
                match p {
                    ParamDefn::Dependent { name, combinator } => {
                        if name == base {
                            if let Combinator::Invocation(inv) = combinator {
                                enum_name = Some(inv.func.as_str());
                                break;
                            }
                        }
                    }
                }
            }
        }
        let enum_name = enum_name?;
        for def in self.defs {
            if let vestir::Definition::EnumDef {
                name, combinator, ..
            } = def
            {
                if name == enum_name {
                    return Some((name.as_str(), combinator));
                }
            }
        }
        None
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
            ConstArray::Wildcard => None,
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

    fn gen_constraint_pred(
        &self,
        combinator: &Combinator,
        val_tokens: TokenStream,
    ) -> Option<TokenStream> {
        let resolved = self.ctx.resolve_alias(combinator);
        match resolved {
            Combinator::ConstraintInt(c) => c.constraint.as_ref().map(|constraint| {
                self.render_int_constraint_exec(constraint, &c.combinator, val_tokens)
            }),
            Combinator::ConstraintEnum(c) => {
                let value_ty = self.nominal_type(&c.combinator.func, TypeMode::Exec);
                Some(self.render_enum_constraint_exec(&c.constraint, &value_ty, val_tokens))
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
