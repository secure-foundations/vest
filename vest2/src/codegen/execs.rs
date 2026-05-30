use super::common::{int_literal, render_ts, syn_usize, Analysis, CodeWriter, TypeMode};
use crate::vestir::{
    self, ChoiceCombinator, Choices, Combinator, ConstArray, ConstCombinator,
    ConstraintEnumCombinator, ConstraintIntCombinator, EnumCombinator, LengthExpr, Param,
    ParamDefn, StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

// ============================================================
// Public entry points — one per definition kind
// ============================================================

impl<'a> Analysis<'a> {
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

    /// Top-level dispatcher. Called once per non-endian definition.
    pub(crate) fn gen_execs_section(
        &self,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_parser_serializer_prepare(
            name,
            param_defns,
            |w| {
                self.emit_combinator_parser_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_combinator_serializer_body(w, name, combinator, param_defns);
            },
            |w| {
                self.emit_combinator_prepare_body(w, name, combinator, param_defns);
            },
        )
    }

    pub(crate) fn gen_struct_execs_section(
        &self,
        name: &str,
        combinator: &StructCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
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
        )
    }

    pub(crate) fn gen_choice_execs_section(
        &self,
        name: &str,
        combinator: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
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
        )
    }
}

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
    ) -> String {
        let info = self.info(name);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let exec_ty = self.nominal_type(name, TypeMode::Exec);
        let spec_ty = self.nominal_type(name, TypeMode::Spec);
        let param_lt = self.wrapper_generics(param_defns);
        let needs_lt = info.needs_lifetime || param_lt.to_string().contains("'i");
        let fmt_has_lt = param_lt.to_string().contains("'i");

        // Determine lifetimes for the impl blocks
        let (parser_lt, parser_self_lt, pt_lt) = if needs_lt {
            (quote! { 'i }, quote! { <'i> }, quote! { <'i> })
        } else {
            (quote! {}, quote! {}, quote! {})
        };

        // Collect fmt struct self fields for param instantiation
        let self_fields: Vec<TokenStream> = param_defns
            .iter()
            .map(|p| match p {
                ParamDefn::Dependent { name, .. } => {
                    let ident = format_ident!("{}", name);
                    quote! { self.#ident }
                }
            })
            .collect();

        let _ = self_fields; // used inside closures below

        let mut out = CodeWriter::new();

        // --- Parser impl ---
        {
            let impl_header = if fmt_has_lt {
                render_ts(quote! {
                    impl<'i> Parser<&'i [u8]> for #fmt_ident <'i>
                })
            } else {
                render_ts(quote! {
                    impl<'i> Parser<&'i [u8]> for #fmt_ident
                })
            };
            out.push_multiline(format!("{} {{", impl_header.trim_end_matches('{')));
            out.indented(|w| {
                let pt = quote! { #exec_ty };
                w.line(render_ts(quote! { type PT = #pt; }));
                w.blank_line();
                w.block(
                    "fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT>",
                    |w| {
                        w.line(
                            "broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;",
                        );
                        w.blank_line();
                        let reveal_line = render_ts(quote! {
                            reveal(<#fmt_ident as SpecParser>::spec_parse);
                        });
                        w.line(reveal_line);
                        w.line("let _ = ibuf.len();");
                        w.line("let rest = *ibuf;");
                        w.blank_line();
                        emit_parser(w);
                    },
                );
            });
            out.line("}");
            out.blank_line();
        }

        // // --- Serializer impl ---
        // {
        //     let sv_ref = if needs_lt {
        //         quote! { &'i #exec_ty }
        //     } else {
        //         quote! { &#exec_ty }
        //     };
        //     let impl_header = if fmt_has_lt {
        //         render_ts(quote! {
        //             impl<'i> Serializer<#sv_ref> for #fmt_ident <'i>
        //         })
        //     } else {
        //         render_ts(quote! {
        //             impl Serializer<&#exec_ty> for #fmt_ident
        //         })
        //     };
        //     out.push_multiline(format!("{} {{", impl_header.trim_end_matches('{')));
        //     out.indented(|w| {
        //         w.block(
        //             if needs_lt {
        //                 "fn ex_serialize(&self, v: &'i Self::PT, obuf: &mut Vec<u8>)".to_string()
        //             } else {
        //                 "fn ex_serialize(&self, v: &Self::PT, obuf: &mut Vec<u8>)".to_string()
        //             },
        //             |w| {
        //                 let reveal_ser = render_ts(quote! {
        //                     reveal(<#fmt_ident as SpecSerializer>::spec_serialize);
        //                 });
        //                 w.line(reveal_ser);
        //                 w.line("let ghost old_obuf = obuf@;");
        //                 w.blank_line();
        //                 emit_serializer(w);
        //                 w.blank_line();
        //                 let assert_line = render_ts(quote! {
        //                     assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
        //                 });
        //                 w.line(assert_line);
        //             },
        //         );
        //     });
        //     out.line("}");
        //     out.blank_line();
        // }

        // // --- Prepare impl ---
        // {
        //     let prep_t = if needs_lt {
        //         quote! { &'i #exec_ty }
        //     } else {
        //         quote! { &#exec_ty }
        //     };
        //     let impl_header = if fmt_has_lt {
        //         render_ts(quote! {
        //             impl<'i> Prepare<#prep_t> for #fmt_ident <'i>
        //         })
        //     } else {
        //         render_ts(quote! {
        //             impl Prepare<&#exec_ty> for #fmt_ident
        //         })
        //     };
        //     out.push_multiline(format!("{} {{", impl_header.trim_end_matches('{')));
        //     out.indented(|w| {
        //         let fn_sig = if needs_lt {
        //             "fn prepare(&self, v: &'i Self::PT) -> Result<usize, PreSerializeError>"
        //                 .to_string()
        //         } else {
        //             "fn prepare(&self, v: &Self::PT) -> Result<usize, PreSerializeError>"
        //                 .to_string()
        //         };
        //         w.block(fn_sig, |w| {
        //             let reveal_cons = render_ts(quote! {
        //                 reveal(<#fmt_ident as Consistency>::consistent);
        //             });
        //             let reveal_len = render_ts(quote! {
        //                 reveal(<#fmt_ident as SpecByteLen>::byte_len);
        //             });
        //             w.line(reveal_cons);
        //             w.line(reveal_len);
        //             w.blank_line();
        //             emit_prepare(w);
        //         });
        //     });
        //     out.line("}");
        // }

        let _ = spec_ty;
        let _ = pt_lt;
        let _ = parser_lt;
        out.finish()
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
            let n_var_tok: TokenStream = n_var.parse().unwrap();
            match field {
                StructField::Const { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_const_fmt_expr(combinator, param_defns, false);
                    w.line(render_ts(quote! {
                        let (#n_var_tok, #label_ident) = (#fmt_expr).parse(&rest)?;
                    }));
                    w.line(format!("let rest = rest.skip({});", n_var));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
                    w.line(render_ts(quote! {
                        let (#n_var_tok, #label_ident) = (#fmt_expr).parse(&rest)?;
                    }));
                    if let Some(pred) =
                        self.gen_constraint_pred(combinator, quote! { #label_ident })
                    {
                        w.line(render_ts(quote! {
                            if !(#pred) {
                                return Err(ParseError::predicate_failed());
                            }
                        }));
                    }
                    w.line(format!("let rest = rest.skip({});", n_var));
                    if i == fields.len() - 1 {
                        if matches!(
                            self.ctx.resolve_alias(combinator),
                            Combinator::Option(_) | Combinator::Vec(_)
                        ) {
                            w.line(render_ts(quote! {
                                let _ = (Eof).parse(&rest)?;
                            }));
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

        // Collect all field names for struct init
        let struct_field_toks: Vec<TokenStream> = fields
            .iter()
            .map(|f| {
                let label = match f {
                    StructField::Const { label, .. }
                    | StructField::Dependent { label, .. }
                    | StructField::Ordinary { label, .. } => label,
                };
                let ident = format_ident!("{}", label);
                quote! { #ident }
            })
            .collect();

        w.line(render_ts(quote! {
            let final_v = #exec_ident { #(#struct_field_toks),* };
        }));
        w.line(render_ts(quote! {
            assert(self.spec_parse(ibuf@) == Some((total_n as int, final_v.deep_view())));
        }));
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
        let field_pats: Vec<TokenStream> = fields
            .iter()
            .map(|f| {
                let label = match f {
                    StructField::Const { label, .. }
                    | StructField::Dependent { label, .. }
                    | StructField::Ordinary { label, .. } => label,
                };
                let ident = format_ident!("{}", label);
                quote! { #ident }
            })
            .collect();
        w.line(render_ts(quote! {
            let #exec_ident { #(#field_pats),* } = v;
        }));

        for field in fields {
            match field {
                StructField::Const { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_const_fmt_expr(combinator, param_defns, true);
                    // For const fields, serialize the stored value
                    w.line(render_ts(quote! {
                        (#fmt_expr).ex_serialize(*#label_ident, obuf);
                    }));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, true);
                    let ser_line = self.exec_serialize_field(label_ident, fmt_expr, combinator);
                    w.line(render_ts(ser_line));
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
        let field_pats: Vec<TokenStream> = fields
            .iter()
            .map(|f| {
                let label = match f {
                    StructField::Const { label, .. }
                    | StructField::Dependent { label, .. }
                    | StructField::Ordinary { label, .. } => label,
                };
                let ident = format_ident!("{}", label);
                quote! { #ident }
            })
            .collect();
        w.line(render_ts(quote! {
            let #exec_ident { #(#field_pats),* } = v;
        }));

        let mut l_vars: Vec<String> = Vec::new();
        for (i, field) in fields.iter().enumerate() {
            let l_var = format!("l{}", i + 1);
            let l_var_tok: TokenStream = l_var.parse().unwrap();
            match field {
                StructField::Const { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_const_fmt_expr(combinator, param_defns, true);
                    w.line(render_ts(quote! {
                        let #l_var_tok = (#fmt_expr).prepare(*#label_ident)?;
                    }));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, true);
                    let prep = self.exec_prepare_field(label_ident, fmt_expr, combinator);
                    w.line(render_ts(quote! { let #l_var_tok = #prep?; }));
                }
            }
            l_vars.push(l_var);
        }

        // Sum up lengths with overflow checks
        if l_vars.is_empty() {
            w.line("Ok(0usize)");
        } else {
            let mut acc: TokenStream = l_vars[0].parse().unwrap();
            for l_var in &l_vars[1..] {
                let l: TokenStream = l_var.parse().unwrap();
                acc = quote! { #acc.checked_add(#l).ok_or(PreSerializeError::LengthTooLarge)? };
            }
            w.line(render_ts(quote! { Ok(#acc) }));
        }
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
            let dep_tok = format_ident!("{}", dep);

            let match_arms: Vec<TokenStream> =
                self.choice_parser_arms(comb, &variant_names, &exec_ident, dep, param_defns);
            w.line(render_ts(quote! {
                let (n, v) = match self.#dep_tok {
                    #(#match_arms)*
                };
            }));
            w.line(render_ts(quote! {
                assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            }));
            w.line("Ok((n, v))");
        } else {
            // Non-dependent choice: delegate to the spec fmt combinator
            let branches: TokenStream =
                self.choice_parse_arms_nondep(comb, &variant_names, &exec_ident, param_defns);
            w.line(render_ts(quote! {
                let (n, v) = #branches?;
            }));
            w.line(render_ts(quote! {
                assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
            }));
            w.line("Ok((n, v))");
        }
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
                let enum_ty = self.resolve_dep_enum_type(dep, comb, param_defns);
                branches
                    .iter()
                    .zip(variant_names.iter())
                    .map(|((pat, combinator), variant_name)| {
                        let variant_ident = format_ident!("{}", variant_name);
                        let fmt_expr =
                            self.exec_combinator_fmt_expr(combinator, param_defns, false);
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
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
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
                        None => quote! {
                            _ => {
                                let (n, v) = (#fmt_expr).parse(&rest)?;
                                #check
                                (n, #exec_ident::#variant_ident(v))
                            },
                        },
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
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
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
                        ConstArray::Wildcard => quote! {
                            _ => {
                                let (n, v) = (#fmt_expr).parse(&rest)?;
                                #check
                                (n, #exec_ident::#variant_ident(v))
                            },
                        },
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
        match &comb.choices {
            Choices::Enums(_) | Choices::Ints(_) | Choices::Arrays(_) => {
                let branches_iter: Vec<(&Combinator, &String)> = match &comb.choices {
                    Choices::Enums(b) => b
                        .iter()
                        .map(|(_, c)| c)
                        .zip(variant_names.iter())
                        .map(|(c, vn)| (c, vn))
                        .collect(),
                    Choices::Ints(b) => b
                        .iter()
                        .map(|(_, c)| c)
                        .zip(variant_names.iter())
                        .map(|(c, vn)| (c, vn))
                        .collect(),
                    Choices::Arrays(b) => b
                        .iter()
                        .map(|(_, c)| c)
                        .zip(variant_names.iter())
                        .map(|(c, vn)| (c, vn))
                        .collect(),
                };
                let mut chain = quote! { Err(ParseError::invalid_tag()) };
                for (combinator, variant_name) in branches_iter.into_iter().rev() {
                    let variant_ident = format_ident!("{}", variant_name);
                    let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
                    if let Some(pred) = self.gen_constraint_pred(combinator, quote! { va }) {
                        chain = quote! {
                            match (#fmt_expr).parse(&rest) {
                                Ok((n, va)) if #pred => Ok((n, #exec_ident::#variant_ident(va))),
                                _ => #chain,
                            }
                        };
                    } else {
                        chain = quote! {
                            match (#fmt_expr).parse(&rest) {
                                Ok((n, va)) => Ok((n, #exec_ident::#variant_ident(va))),
                                _ => #chain,
                            }
                        };
                    }
                }
                chain
            }
        }
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

        let branches: Vec<(&Combinator, &String)> = match &comb.choices {
            Choices::Enums(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
            Choices::Ints(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
            Choices::Arrays(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
        };

        let arms: Vec<TokenStream> = branches
            .iter()
            .map(|(combinator, variant_name)| {
                let variant_ident = format_ident!("{}", variant_name);
                let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
                let ser = self.exec_serialize_field(format_ident!("v"), fmt_expr, combinator);
                quote! {
                    #exec_ident::#variant_ident(v) => { #ser },
                }
            })
            .collect();

        w.line(render_ts(quote! {
            match v {
                #(#arms)*
            }
        }));
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

        let branches: Vec<(&Combinator, &String)> = match &comb.choices {
            Choices::Enums(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
            Choices::Ints(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
            Choices::Arrays(b) => b
                .iter()
                .map(|(_, c)| c)
                .zip(variant_names.iter())
                .map(|(c, vn)| (c, vn))
                .collect(),
        };

        let arms: Vec<TokenStream> = branches
            .iter()
            .map(|(combinator, variant_name)| {
                let variant_ident = format_ident!("{}", variant_name);
                let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
                let prep = self.exec_prepare_field(format_ident!("v"), fmt_expr, combinator);
                quote! {
                    #exec_ident::#variant_ident(v) => #prep,
                }
            })
            .collect();

        w.line(render_ts(quote! {
            match v {
                #(#arms)*
            }
        }));
    }
}

// ============================================================
// Enum parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_enum_parser_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = match comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums.as_slice(), true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => {
                (enums.as_slice(), false, inferred)
            }
        };
        let prim_expr = self.int_combinator_expr(inferred);

        w.line(render_ts(quote! {
            let (n, v) = #prim_expr.parse(&rest)?;
        }));

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

        w.line(render_ts(quote! {
            let enum_val = match v {
                #(#known_arms)*
                #default_arm
            };
        }));
        w.line(render_ts(quote! {
            assert(self.spec_parse(ibuf@) == Some((n as int, enum_val.deep_view())));
        }));
        w.line("Ok((n, enum_val))");
    }

    fn emit_enum_serializer_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = match comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums.as_slice(), true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => {
                (enums.as_slice(), false, inferred)
            }
        };
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

        w.line(render_ts(quote! {
            let tag = match *v {
                #(#known_arms)*
                #default_arm
            };
        }));
        w.line(render_ts(quote! {
            #prim_expr.ex_serialize(tag, obuf);
        }));
    }

    fn emit_enum_prepare_body(&self, w: &mut CodeWriter, name: &str, comb: &EnumCombinator) {
        let exec_ident = format_ident!("{}", self.info(name).names.exec);
        let (variants, exhaustive, inferred) = match comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums.as_slice(), true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => {
                (enums.as_slice(), false, inferred)
            }
        };
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

        w.line(render_ts(quote! {
            let tag = match *v {
                #(#known_arms)*
                #default_arm
            };
        }));
        w.line(render_ts(quote! {
            #prim_expr.prepare(tag)
        }));
    }
}

// ============================================================
// CombinatorDef parser / serializer / prepare
// ============================================================

impl<'a> Analysis<'a> {
    fn emit_combinator_parser_body(
        &self,
        w: &mut CodeWriter,
        _name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);

        w.line(render_ts(quote! {
            let (n, v) = (#fmt_expr).parse(ibuf)?;
        }));
        if let Some(pred) = self.gen_constraint_pred(combinator, quote! { v }) {
            w.line(render_ts(quote! {
                if !(#pred) {
                    return Err(ParseError::predicate_failed());
                }
            }));
        }
        if matches!(
            self.ctx.resolve_alias(combinator),
            Combinator::Option(_) | Combinator::Vec(_)
        ) {
            w.line(render_ts(quote! {
                let rest = ibuf.skip(n);
                let _ = (Eof).parse(&rest)?;
            }));
        }
        w.line(render_ts(quote! {
            assert(self.spec_parse(ibuf@) == Some((n as int, v.deep_view())));
        }));
        w.line("Ok((n, v))");
    }

    fn emit_combinator_serializer_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        if let Some(invocation) = self.direct_alias(combinator) {
            let target_args = self.exec_invocation_fmt_expr(invocation, param_defns, false);
            w.line(render_ts(quote! {
                (#target_args).ex_serialize(v, obuf);
            }));
            return;
        }
        let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
        let _ = name;
        w.line(render_ts(quote! {
            (#fmt_expr).ex_serialize(v, obuf);
        }));
    }

    fn emit_combinator_prepare_body(
        &self,
        w: &mut CodeWriter,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) {
        if let Some(invocation) = self.direct_alias(combinator) {
            let target_args = self.exec_invocation_fmt_expr(invocation, param_defns, false);
            w.line(render_ts(quote! {
                (#target_args).prepare(v)
            }));
            return;
        }
        let fmt_expr = self.exec_combinator_fmt_expr(combinator, param_defns, false);
        let _ = name;
        w.line(render_ts(quote! {
            (#fmt_expr).prepare(v)
        }));
    }
}

// ============================================================
// Format expression builders (exec mode)
// ============================================================

impl<'a> Analysis<'a> {
    /// Build the exec-mode combinator expression for a `Combinator`.
    pub(crate) fn exec_combinator_fmt_expr(
        &self,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
        is_ref: bool,
    ) -> TokenStream {
        match combinator {
            Combinator::AndThen(lhs, rhs) => {
                return self.exec_and_then_fmt_expr(lhs, rhs, param_defns, is_ref);
            }
            Combinator::Invocation(invocation) => {
                return self.exec_invocation_fmt_expr(invocation, param_defns, is_ref);
            }
            _ => {}
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(c) => self.exec_constraint_int_fmt(c, param_defns, is_ref),
            Combinator::ConstraintEnum(c) => self.exec_constraint_enum_fmt(c, param_defns, is_ref),
            Combinator::Wrap(wrap) => {
                let mut body_expr =
                    self.exec_combinator_fmt_expr(&wrap.combinator, param_defns, is_ref);
                for const_comb in wrap.post.iter() {
                    let (c_fmt, c_val) = self.exec_tag_expr(const_comb, param_defns, is_ref);
                    body_expr = quote! { SuffixTagged(#body_expr, #c_fmt, #c_val) };
                }
                for const_comb in wrap.prior.iter().rev() {
                    let (c_fmt, c_val) = self.exec_tag_expr(const_comb, param_defns, is_ref);
                    body_expr = quote! { PrefixTagged(#c_fmt, #c_val, #body_expr) };
                }
                body_expr
            }
            Combinator::Vec(vestir::VecCombinator::Vec(inner)) => {
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, is_ref);
                quote! { Star(#inner_expr) }
            }
            Combinator::Array(vestir::ArrayCombinator {
                combinator: inner,
                len,
            }) => {
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, is_ref);
                match self.eval_const_length_expr(len) {
                    Some(n) => {
                        let n_tok = syn_usize(n);
                        quote! { Array::<#n_tok, _>(#inner_expr) }
                    }
                    None => {
                        let len_expr = self.exec_length_expr(len, param_defns, is_ref);
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
                    let len_expr = self.exec_length_expr(&bytes.len, param_defns, is_ref);
                    quote! { Varied(#len_expr) }
                }
            },
            Combinator::Tail(_) => quote! { Tail },
            Combinator::Option(vestir::OptionCombinator(inner)) => {
                let inner_expr = self.exec_combinator_fmt_expr(inner, param_defns, is_ref);
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
        is_ref: bool,
    ) -> TokenStream {
        match self.ctx.resolve_alias(lhs) {
            Combinator::Bytes(bytes) => {
                let len_expr = self.exec_length_expr(&bytes.len, param_defns, is_ref);
                let inner_expr = self.exec_combinator_fmt_expr(rhs, param_defns, is_ref);
                quote! { ExactLen(#len_expr, #inner_expr) }
            }
            _ => {
                let lhs_expr = self.exec_combinator_fmt_expr(lhs, param_defns, is_ref);
                let rhs_expr = self.exec_combinator_fmt_expr(rhs, param_defns, is_ref);
                quote! { AndThen(#lhs_expr, #rhs_expr) }
            }
        }
    }

    fn exec_invocation_fmt_expr(
        &self,
        invocation: &vestir::CombinatorInvocation,
        param_defns: &[ParamDefn],
        is_ref: bool,
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
                    let final_tokens = if is_ref {
                        let is_param = param_defns.iter().any(|p| match p {
                            ParamDefn::Dependent { name: p_name, .. } => p_name == arg_name,
                        });
                        if is_param {
                            arg_tokens
                        } else {
                            quote! { *#arg_tokens }
                        }
                    } else {
                        arg_tokens
                    };
                    quote! { #field_ident: #final_tokens }
                }
            })
            .collect();
        quote! { #fmt_ident { #(#field_inits),* } }
    }

    fn exec_constraint_int_fmt(
        &self,
        c: &ConstraintIntCombinator,
        _param_defns: &[ParamDefn],
        _is_ref: bool,
    ) -> TokenStream {
        self.int_combinator_expr(&c.combinator)
    }

    fn exec_constraint_enum_fmt(
        &self,
        c: &ConstraintEnumCombinator,
        param_defns: &[ParamDefn],
        is_ref: bool,
    ) -> TokenStream {
        self.exec_invocation_fmt_expr(&c.combinator, param_defns, is_ref)
    }

    fn exec_length_expr(
        &self,
        len: &LengthExpr,
        param_defns: &[ParamDefn],
        is_ref: bool,
    ) -> TokenStream {
        match len {
            LengthExpr::Const(n) => {
                let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                quote! { #lit as usize }
            }
            LengthExpr::Dependent(name) => {
                let path = self.resolve_dep(name, param_defns);
                let base = name.split('.').next().unwrap();
                let is_param = param_defns.iter().any(|p| match p {
                    ParamDefn::Dependent { name: p_name, .. } => p_name == base,
                });
                if is_ref && !is_param {
                    quote! { (*#path as usize) }
                } else {
                    quote! { (#path as usize) }
                }
            }
            LengthExpr::SizeOf(name) => {
                if let Some(n) = self.ctx.static_sizes.get(name) {
                    let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                    quote! { #lit as usize }
                } else {
                    let fmt_spec_ident = format_ident!("{}Spec", self.info(name).names.fmt);
                    quote! { (<#fmt_spec_ident as StaticByteLen>::static_byte_len() as usize) }
                }
            }
            LengthExpr::BinOp { op, left, right } => {
                let left = self.exec_length_expr(left, param_defns, is_ref);
                let right = self.exec_length_expr(right, param_defns, is_ref);
                match op {
                    vestir::ArithOp::Add => quote! { ((#left + #right) as usize) },
                    vestir::ArithOp::Sub => quote! { ((#left - #right) as usize) },
                    vestir::ArithOp::Mul => quote! { ((#left * #right) as usize) },
                    vestir::ArithOp::Div => quote! { ((#left / #right) as usize) },
                }
            }
        }
    }

    /// Build the exec format expression for a ConstCombinator.
    fn exec_tag_expr(
        &self,
        combinator: &ConstCombinator,
        param_defns: &[ParamDefn],
        is_ref: bool,
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
                let inner =
                    self.exec_invocation_fmt_expr(&enum_comb.combinator, param_defns, is_ref);
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
        is_ref: bool,
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
                let inner =
                    self.exec_invocation_fmt_expr(&enum_comb.combinator, param_defns, is_ref);
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

    /// Wrapper: serialize a single value field.
    fn exec_serialize_field(
        &self,
        label_ident: proc_macro2::Ident,
        fmt_expr: TokenStream,
        combinator: &Combinator,
    ) -> TokenStream {
        let resolved = self.ctx.resolve_alias(combinator);
        if matches!(resolved, Combinator::ConstraintInt(_)) {
            quote! { (#fmt_expr).ex_serialize(*#label_ident, obuf); }
        } else {
            quote! { (#fmt_expr).ex_serialize(#label_ident, obuf); }
        }
    }

    /// Wrapper: prepare a single value field.
    fn exec_prepare_field(
        &self,
        label_ident: proc_macro2::Ident,
        fmt_expr: TokenStream,
        combinator: &Combinator,
    ) -> TokenStream {
        let resolved = self.ctx.resolve_alias(combinator);
        if matches!(resolved, Combinator::ConstraintInt(_)) {
            quote! { (#fmt_expr).prepare(*#label_ident) }
        } else {
            quote! { (#fmt_expr).prepare(#label_ident) }
        }
    }

    /// Try to resolve the enum type of a dependent field `dep` in the struct or params context.
    fn resolve_dep_enum_type(
        &self,
        dep: &str,
        _choice_comb: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) -> Option<TokenStream> {
        let base = dep.split('.').last().unwrap_or(dep);
        // Search in all struct defs for a Dependent field with this name
        for def in self.defs {
            if let vestir::Definition::StructDef { combinator, .. } = def {
                for field in &combinator.0 {
                    if let StructField::Dependent { label, combinator } = field {
                        if label == base {
                            if let Combinator::Invocation(inv) = combinator {
                                return Some(self.nominal_type(&inv.func, TypeMode::Exec));
                            }
                        }
                    }
                }
            }
        }
        // Also search in param_defns
        for p in param_defns {
            match p {
                ParamDefn::Dependent { name, combinator } => {
                    if name == base {
                        if let Combinator::Invocation(inv) = combinator {
                            return Some(self.nominal_type(&inv.func, TypeMode::Exec));
                        }
                    }
                }
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
