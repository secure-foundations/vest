use super::common::{int_literal, syn_usize, Analysis, TypeMode};
use crate::vestir::{
    self, ChoiceCombinator, Choices, Combinator, CombinatorInner, ConstArray, ConstCombinator,
    ConstraintElem, ConstraintEnumCombinator, ConstraintIntCombinator, EnumCombinator,
    IntCombinator, LengthExpr, Param, ParamDefn, StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

struct RenderedSpec {
    ty: TokenStream,
    expr: TokenStream,
    value_ty: TokenStream,
    has_value: bool,
}

impl<'a> Analysis<'a> {
    pub(crate) fn gen_specs_section(
        &self,
        name: &str,
        _combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let mut out = String::new();
        out.push_str(&self.gen_wrapper_type(name, param_defns));
        out.push('\n');
        out.push_str(&self.gen_format_spec_alias_and_ctor(name, _combinator, param_defns));
        out
    }

    pub(crate) fn gen_derived_specs_section(
        &self,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let info = self.info(name);
        let fmt_fn_ident = format_ident!("{}", info.names.fmt_fn);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let top_value_ty = self.render_value_type(combinator, TypeMode::Spec, true);
        let wrapper_generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);

        self.gen_derived_spec_impls(
            &fmt_ident,
            &fmt_fn_ident,
            &wrapper_generics,
            &wrapper_call_args,
            &top_value_ty,
        )
    }

    fn gen_format_spec_alias_and_ctor(
        &self,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let info = self.info(name);
        let fmt_spec_ident = format_ident!("{}Spec", info.names.fmt);
        let fmt_fn_ident = format_ident!("{}", info.names.fmt_fn);
        let raw = self.render_top_level_spec(name, combinator);
        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let named_ty = quote! { Named<#raw_ty> };
        let named_expr = quote! { Named(#name, #raw_expr) };
        let spec_params = self.spec_param_list(param_defns);
        let ctor_doc = format!("specification constructor for `{}`.", name);

        quote! {
            pub type #fmt_spec_ident = #named_ty;

            #[doc = #ctor_doc]
            pub open spec fn #fmt_fn_ident(#(#spec_params),*) -> #fmt_spec_ident {
                #named_expr
            }
        }
        .to_string()
    }

    fn gen_derived_spec_impls(
        &self,
        fmt_ident: &proc_macro2::Ident,
        fmt_fn_ident: &proc_macro2::Ident,
        wrapper_generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
        top_value_ty: &TokenStream,
    ) -> String {
        quote! {
            impl #wrapper_generics SpecParser for #fmt_ident #wrapper_generics {
                type PVal = #top_value_ty;

                #[verifier::opaque]
                open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                    #fmt_fn_ident(#(#wrapper_call_args),*).spec_parse(ibuf)
                }
            }

            impl #wrapper_generics Consistency for #fmt_ident #wrapper_generics {
                type Val = #top_value_ty;

                #[verifier::opaque]
                open spec fn consistent(&self, v: Self::Val) -> bool {
                    #fmt_fn_ident(#(#wrapper_call_args),*).consistent(v)
                }
            }

            impl #wrapper_generics SpecSerializerDps for #fmt_ident #wrapper_generics {
                type SValue = #top_value_ty;

                #[verifier::opaque]
                open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                    #fmt_fn_ident(#(#wrapper_call_args),*).spec_serialize_dps(v, obuf)
                }
            }

            impl #wrapper_generics SpecSerializer for #fmt_ident #wrapper_generics {
                type SVal = #top_value_ty;

                #[verifier::opaque]
                open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
                    #fmt_fn_ident(#(#wrapper_call_args),*).spec_serialize(v)
                }
            }

            impl #wrapper_generics SpecByteLen for #fmt_ident #wrapper_generics {
                type T = #top_value_ty;

                #[verifier::opaque]
                open spec fn byte_len(&self, v: Self::T) -> nat {
                    #fmt_fn_ident(#(#wrapper_call_args),*).byte_len(v)
                }
            }
        }
        .to_string()
    }

    fn render_top_level_spec(&self, name: &str, combinator: &Combinator) -> RenderedSpec {
        match self.ctx.resolve(combinator) {
            CombinatorInner::Struct(struct_comb) => self.render_struct_top_level(name, struct_comb),
            CombinatorInner::Choice(choice_comb) => self.render_choice_top_level(name, choice_comb),
            CombinatorInner::Enum(enum_comb) => self.render_enum_top_level(name, enum_comb),
            _ => self.render_spec_combinator(combinator),
        }
    }

    fn render_spec_combinator(&self, combinator: &Combinator) -> RenderedSpec {
        if let Some(and_then) = &combinator.and_then {
            return match self.ctx.resolve_alias(&combinator.inner) {
                CombinatorInner::Bytes(bytes) => {
                    let len_expr = self.render_length_expr_usize(&bytes.len);
                    let inner = self.render_spec_combinator(and_then);
                    let inner_ty = &inner.ty;
                    let inner_expr = &inner.expr;
                    let ty = quote! { ExactLen<#inner_ty, usize> };
                    let expr = quote! { ExactLen(#len_expr, #inner_expr) };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: inner.value_ty,
                        has_value: inner.has_value,
                    }
                }
                _ => {
                    let lhs = self.render_spec_combinator(&Combinator {
                        inner: combinator.inner.clone(),
                        and_then: None,
                    });
                    let rhs = self.render_spec_combinator(and_then);
                    let lhs_ty = &lhs.ty;
                    let lhs_expr = &lhs.expr;
                    let rhs_ty = &rhs.ty;
                    let rhs_expr = &rhs.expr;
                    let ty = quote! { AndThen<#lhs_ty, #rhs_ty> };
                    let expr = quote! { AndThen(#lhs_expr, #rhs_expr) };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: rhs.value_ty,
                        has_value: rhs.has_value,
                    }
                }
            };
        }

        if let CombinatorInner::Invocation(invocation) = &combinator.inner {
            let info = self.info(&invocation.func);
            let fmt_ident = format_ident!("{}", info.names.fmt);
            let ty_ident = format_ident!("{}Spec", info.names.fmt);
            let needs_lifetime = self
                .param_defns_for(&invocation.func)
                .iter()
                .any(|p| self.param_needs_lifetime(p));
            return RenderedSpec {
                ty: if needs_lifetime {
                    quote! { #ty_ident }
                } else {
                    quote! { #fmt_ident }
                },
                expr: if needs_lifetime {
                    let fn_ident = format_ident!("{}", info.names.fmt_fn);
                    let args = invocation
                        .args
                        .iter()
                        .map(|arg| match arg {
                            Param::Dependent(name) => path_tokens(name),
                        })
                        .collect::<Vec<_>>();
                    quote! { #fn_ident(#(#args),*) }
                } else if invocation.args.is_empty() {
                    quote! { #fmt_ident }
                } else {
                    let fields = self.param_defns_for(&invocation.func);
                    let field_inits =
                        fields
                            .iter()
                            .zip(invocation.args.iter())
                            .map(|(param, arg)| match (param, arg) {
                                (ParamDefn::Dependent { name, .. }, Param::Dependent(arg_name)) => {
                                    let field_ident = format_ident!("{}", name);
                                    if arg_name == name {
                                        quote! { #field_ident }
                                    } else {
                                        let arg = path_tokens(arg_name);
                                        quote! { #field_ident: #arg }
                                    }
                                }
                            });
                    quote! { #fmt_ident { #(#field_inits),* } }
                },
                value_ty: self.render_value_type(combinator, TypeMode::Spec, true),
                has_value: true,
            };
        }

        match self.ctx.resolve_alias(&combinator.inner) {
            CombinatorInner::ConstraintInt(c) => self.render_constraint_int(c),
            CombinatorInner::ConstraintEnum(c) => self.render_constraint_enum(c),
            CombinatorInner::Struct(struct_comb) => self.render_struct_raw(struct_comb),
            CombinatorInner::Wrap(wrap) => self.render_wrap(wrap),
            CombinatorInner::Enum(enum_comb) => self.render_enum_top_level(
                &self.definition_name_for_inner(&combinator.inner),
                enum_comb,
            ),
            CombinatorInner::Choice(choice_comb) => self.render_choice_top_level(
                &self.definition_name_for_inner(&combinator.inner),
                choice_comb,
            ),
            CombinatorInner::Vec(vec_comb) => self.render_vec(vec_comb),
            CombinatorInner::Array(array_comb) => self.render_array(array_comb),
            CombinatorInner::Bytes(bytes) => self.render_bytes(bytes),
            CombinatorInner::Tail(_) => RenderedSpec {
                ty: quote! { Tail },
                expr: quote! { Tail },
                value_ty: quote! { Seq<u8> },
                has_value: true,
            },
            CombinatorInner::Option(opt) => self.render_option(opt),
            CombinatorInner::Invocation(_) => unreachable!(),
        }
    }

    fn render_constraint_int(&self, c: &ConstraintIntCombinator) -> RenderedSpec {
        let prim_ty = self.int_combinator_ty(&c.combinator);
        let prim_expr = self.int_combinator_expr(&c.combinator);
        let value_ty = self.int_type(&c.combinator, TypeMode::Spec);
        match &c.constraint {
            None => RenderedSpec {
                ty: prim_ty,
                expr: prim_expr,
                value_ty,
                has_value: true,
            },
            Some(constraint) => {
                let pred = self.render_int_constraint(constraint, &c.combinator, quote! { x });
                let ty = quote! { Refined<#prim_ty, PredFnSpec<#value_ty>> };
                let expr = quote! { Refined(#prim_expr, |x: #value_ty| #pred) };
                RenderedSpec {
                    ty,
                    expr,
                    value_ty,
                    has_value: true,
                }
            }
        }
    }

    fn render_constraint_enum(&self, c: &ConstraintEnumCombinator) -> RenderedSpec {
        let inner = self.render_spec_combinator(&Combinator {
            inner: CombinatorInner::Invocation(c.combinator.clone()),
            and_then: None,
        });
        let value_ty = inner.value_ty.clone();
        let pred = self.render_enum_constraint(&c.constraint, &value_ty, quote! { x });
        let inner_ty = &inner.ty;
        let inner_expr = &inner.expr;
        let ty = quote! { Refined<#inner_ty, PredFnSpec<#value_ty>> };
        let expr = quote! { Refined(#inner_expr, |x: #value_ty| #pred) };
        RenderedSpec {
            ty,
            expr,
            value_ty,
            has_value: true,
        }
    }

    fn render_bytes(&self, bytes: &vestir::BytesCombinator) -> RenderedSpec {
        let value_ty = quote! { Seq<u8> };
        match self.eval_const_length_expr(&bytes.len) {
            Some(n) => {
                let n = syn_usize(n);
                RenderedSpec {
                    ty: quote! { Fixed<#n> },
                    expr: quote! { Fixed::<#n> },
                    value_ty,
                    has_value: true,
                }
            }
            None => {
                let len = self.render_length_expr_usize(&bytes.len);
                RenderedSpec {
                    ty: quote! { Varied<usize> },
                    expr: quote! { Varied(#len) },
                    value_ty,
                    has_value: true,
                }
            }
        }
    }

    fn render_vec(&self, vec_comb: &vestir::VecCombinator) -> RenderedSpec {
        match vec_comb {
            vestir::VecCombinator::Vec(inner) => {
                let inner_fmt = self.render_spec_combinator(inner);
                let inner_ty = &inner_fmt.ty;
                let inner_expr = &inner_fmt.expr;
                let inner_value_ty = &inner_fmt.value_ty;
                let value_ty = quote! { Seq<#inner_value_ty> };
                RenderedSpec {
                    ty: quote! { RepeatTillEnd<#inner_ty> },
                    expr: quote! { RepeatTillEnd(#inner_expr) },
                    value_ty,
                    has_value: true,
                }
            }
        }
    }

    fn render_array(&self, array_comb: &vestir::ArrayCombinator) -> RenderedSpec {
        let inner_fmt = self.render_spec_combinator(&array_comb.combinator);
        let inner_ty = &inner_fmt.ty;
        let inner_expr = &inner_fmt.expr;
        let inner_value_ty = &inner_fmt.value_ty;
        let value_ty = quote! { Seq<#inner_value_ty> };
        match self.eval_const_length_expr(&array_comb.len) {
            Some(n) => {
                let n = syn_usize(n);
                RenderedSpec {
                    ty: quote! { Array<#n, #inner_ty> },
                    expr: quote! { Array::<#n, _>(#inner_expr) },
                    value_ty,
                    has_value: true,
                }
            }
            None => {
                let len = self.render_length_expr_usize(&array_comb.len);
                RenderedSpec {
                    ty: quote! { RepeatN<#inner_ty, usize> },
                    expr: quote! { RepeatN(#len, #inner_expr) },
                    value_ty,
                    has_value: true,
                }
            }
        }
    }

    fn render_option(&self, opt: &vestir::OptionCombinator) -> RenderedSpec {
        let inner = self.render_spec_combinator(&opt.0);
        let inner_ty = &inner.ty;
        let inner_expr = &inner.expr;
        let inner_value_ty = &inner.value_ty;
        let value_ty = quote! { Option<#inner_value_ty> };
        RenderedSpec {
            ty: quote! { Opt<#inner_ty> },
            expr: quote! { Opt(#inner_expr) },
            value_ty,
            has_value: true,
        }
    }

    fn render_wrap(&self, wrap: &vestir::WrapCombinator) -> RenderedSpec {
        let mut body = self.render_spec_combinator(&wrap.combinator);
        for const_comb in wrap.post.iter() {
            let c = self.render_const_spec(const_comb);
            let body_ty = &body.ty;
            let body_expr = &body.expr;
            let c_ty = &c.ty;
            let c_expr = &c.expr;
            let c_value_ty = &c.value_ty;
            let c_value_expr = &c.value_expr;
            if body.has_value {
                let ty = quote! { Terminated<#body_ty, #c_ty, ()> };
                let expr =
                    quote! { Terminated { a: #body_expr, b: #c_expr, b_val: #c_value_expr } };
                body = RenderedSpec {
                    ty,
                    expr,
                    value_ty: body.value_ty,
                    has_value: true,
                };
            } else {
                let ty = quote! { Terminated<#body_ty, #c_ty, #c_value_ty> };
                let expr =
                    quote! { Terminated { a: #body_expr, b: #c_expr, b_val: #c_value_expr } };
                body = RenderedSpec {
                    ty,
                    expr,
                    value_ty: body.value_ty,
                    has_value: false,
                };
            }
        }
        for const_comb in wrap.prior.iter().rev() {
            let c = self.render_const_spec(const_comb);
            let body_ty = &body.ty;
            let body_expr = &body.expr;
            let c_ty = &c.ty;
            let c_expr = &c.expr;
            let c_value_ty = &c.value_ty;
            let c_value_expr = &c.value_expr;
            let ty = quote! { Preceded<#c_ty, #c_value_ty, #body_ty> };
            let expr = quote! { Preceded { a: #c_expr, b: #body_expr, a_val: #c_value_expr } };
            body = RenderedSpec {
                ty,
                expr,
                value_ty: body.value_ty,
                has_value: body.has_value,
            };
        }
        body
    }

    fn render_struct_raw(&self, struct_comb: &StructCombinator) -> RenderedSpec {
        self.render_struct_fields(&struct_comb.0)
    }

    fn render_struct_fields(&self, fields: &[StructField]) -> RenderedSpec {
        if fields.is_empty() {
            return RenderedSpec {
                ty: quote! { Empty },
                expr: quote! { Empty },
                value_ty: quote! { () },
                has_value: false,
            };
        }
        let first = &fields[0];
        let rest = self.render_struct_fields(&fields[1..]);
        match first {
            StructField::Const { combinator, .. } => {
                let c = self.render_const_spec(combinator);
                let c_ty = &c.ty;
                let c_expr = &c.expr;
                let c_value_ty = &c.value_ty;
                let c_value_expr = &c.value_expr;
                let rest_ty = &rest.ty;
                let rest_expr = &rest.expr;
                let ty = quote! { Preceded<#c_ty, #c_value_ty, #rest_ty> };
                let expr = quote! { Preceded { a: #c_expr, b: #rest_expr, a_val: #c_value_expr } };
                RenderedSpec {
                    ty,
                    expr,
                    value_ty: rest.value_ty,
                    has_value: rest.has_value,
                }
            }
            StructField::Ordinary { combinator, .. } => {
                let cur = self.render_spec_combinator(combinator);
                let cur_ty = &cur.ty;
                let cur_expr = &cur.expr;
                let cur_value_ty = &cur.value_ty;
                let rest_ty = &rest.ty;
                let rest_expr = &rest.expr;
                let rest_value_ty = &rest.value_ty;
                if rest.has_value {
                    let ty = quote! { Pair<#cur_ty, #rest_ty> };
                    let expr = quote! { Pair(#cur_expr, #rest_expr) };
                    let value_ty = quote! { (#cur_value_ty, #rest_value_ty) };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty,
                        has_value: true,
                    }
                } else if is_empty_ty(&rest.ty) {
                    RenderedSpec {
                        ty: cur.ty,
                        expr: cur.expr,
                        value_ty: cur.value_ty,
                        has_value: true,
                    }
                } else {
                    let ty = quote! { Terminated<#cur_ty, #rest_ty, #rest_value_ty> };
                    let expr = quote! { Terminated { a: #cur_expr, b: #rest_expr, b_val: () } };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: cur.value_ty,
                        has_value: true,
                    }
                }
            }
            StructField::Dependent { label, combinator } => {
                let cur = self.render_spec_combinator(combinator);
                let label_ident = format_ident!("{}", label);
                let cur_ty = &cur.ty;
                let cur_expr = &cur.expr;
                let cur_value_ty = &cur.value_ty;
                let rest_ty = &rest.ty;
                let rest_expr = &rest.expr;
                let rest_value_ty = &rest.value_ty;
                if rest.has_value {
                    let ty = quote! { Bind<#cur_ty, spec_fn(#cur_value_ty) -> #rest_ty> };
                    let expr = quote! { Bind(#cur_expr, |#label_ident: #cur_value_ty| #rest_expr) };
                    let value_ty = quote! { (#cur_value_ty, #rest_value_ty) };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty,
                        has_value: true,
                    }
                } else if is_empty_ty(&rest.ty) {
                    RenderedSpec {
                        ty: cur.ty,
                        expr: cur.expr,
                        value_ty: cur.value_ty,
                        has_value: true,
                    }
                } else {
                    let ty = quote! { Terminated<#cur_ty, #rest_ty, #rest_value_ty> };
                    let expr = quote! { Terminated { a: #cur_expr, b: #rest_expr, b_val: () } };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: cur.value_ty,
                        has_value: true,
                    }
                }
            }
        }
    }

    fn render_struct_top_level(&self, name: &str, struct_comb: &StructCombinator) -> RenderedSpec {
        let info = self.info(name);
        let raw = self.render_struct_raw(struct_comb);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let labels = struct_comb
            .0
            .iter()
            .filter_map(|field| match field {
                StructField::Const { .. } => None,
                StructField::Dependent { label, .. } | StructField::Ordinary { label, .. } => {
                    Some(label.clone())
                }
            })
            .collect::<Vec<_>>();
        let tuple_pat = nested_tuple_pattern(&labels);
        let struct_fields_expr = struct_init_fields_expr(&labels);
        let reverse_tuple_expr = nested_tuple_value_expr(&labels);
        let label_idents = labels
            .iter()
            .map(|label| format_ident!("{}", label))
            .collect::<Vec<_>>();
        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let ty = quote! { Mapped<#raw_ty, FnSpecMapper<#inner_ident, #spec_ident>> };
        let expr = quote! {
            Mapped {
                inner: #raw_expr,
                mapper: (
                    |parsed: #inner_ident| -> #spec_ident {
                        let #tuple_pat = parsed;
                        #spec_ident { #struct_fields_expr }
                    },
                    |value: #spec_ident| -> #inner_ident {
                        let #spec_ident { #(#label_idents),* } = value;
                        #reverse_tuple_expr
                    }
                )
            }
        };
        RenderedSpec {
            ty,
            expr,
            value_ty: quote! { #spec_ident },
            has_value: true,
        }
    }

    fn render_choice_top_level(&self, name: &str, choice_comb: &ChoiceCombinator) -> RenderedSpec {
        let info = self.info(name);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let raw = self.render_choice_raw(choice_comb, Some(name));
        let variant_names = self.choice_variant_names(choice_comb);
        let forward_arms = variant_names.iter().enumerate().map(|(idx, variant)| {
            let pat = sum_pattern(idx, variant_names.len(), quote! { v });
            let ident = format_ident!("{}", variant);
            quote! { #pat => #spec_ident::#ident(v), }
        });
        let reverse_arms = variant_names.iter().enumerate().map(|(idx, variant)| {
            let expr = sum_injection(idx, variant_names.len(), quote! { v });
            let ident = format_ident!("{}", variant);
            quote! { #spec_ident::#ident(v) => #expr, }
        });
        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let ty = quote! { Mapped<#raw_ty, FnSpecMapper<#inner_ident, #spec_ident>> };
        let expr = quote! {
            Mapped {
                inner: #raw_expr,
                mapper: (
                    |parsed: #inner_ident| -> #spec_ident {
                        match parsed {
                            #(#forward_arms)*
                        }
                    },
                    |value: #spec_ident| -> #inner_ident {
                        match value {
                            #(#reverse_arms)*
                        }
                    }
                )
            }
        };
        RenderedSpec {
            ty,
            expr,
            value_ty: quote! { #spec_ident },
            has_value: true,
        }
    }

    fn render_choice_raw(
        &self,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
    ) -> RenderedSpec {
        let branches = match &choice_comb.choices {
            Choices::Enums(branches) => branches
                .iter()
                .enumerate()
                .map(|(idx, (pat, combinator))| {
                    let fmt = self.render_spec_combinator(combinator);
                    let fmt_ty = &fmt.ty;
                    let fmt_expr = &fmt.expr;
                    let expr = if let Some(dep) = &choice_comb.depend_id {
                        let dep = path_tokens(dep);
                        if pat == "_" {
                            let enum_ty = owner_name
                                .map(|name| {
                                    self.render_enum_pattern_type(pat, choice_comb, Some(name))
                                })
                                .unwrap_or_else(|| {
                                    self.render_enum_pattern_type(pat, choice_comb, owner_name)
                                });
                            let negated = branches
                                .iter()
                                .take(idx)
                                .filter(|(prior_pat, _)| prior_pat.as_str() != "_")
                                .map(|(prior_pat, _)| {
                                    let prior_variant = format_ident!("{}", prior_pat);
                                    quote! { #dep != #enum_ty::#prior_variant }
                                })
                                .collect::<Vec<_>>();
                            if negated.is_empty() {
                                quote! { Cond(true, #fmt_expr) }
                            } else {
                                quote! { Cond(#(#negated)&&*, #fmt_expr) }
                            }
                        } else {
                            let enum_ty =
                                self.render_enum_pattern_type(pat, choice_comb, owner_name);
                            let variant = format_ident!("{}", pat);
                            quote! { Cond(#dep == #enum_ty::#variant, #fmt_expr) }
                        }
                    } else {
                        fmt.expr.clone()
                    };
                    let ty = if choice_comb.depend_id.is_some() {
                        quote! { Cond<#fmt_ty> }
                    } else {
                        fmt.ty.clone()
                    };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: fmt.value_ty,
                        has_value: true,
                    }
                })
                .collect::<Vec<_>>(),
            Choices::Ints(branches) => branches
                .iter()
                .enumerate()
                .map(|(idx, (pat, combinator))| {
                    let fmt = self.render_spec_combinator(combinator);
                    let fmt_ty = &fmt.ty;
                    let fmt_expr = &fmt.expr;
                    let expr = if let Some(dep) = &choice_comb.depend_id {
                        let dep = path_tokens(dep);
                        let cond = pat.as_ref().map_or_else(
                            || {
                                let negated = branches
                                    .iter()
                                    .take(idx)
                                    .filter_map(|(prior_pat, _)| {
                                        prior_pat.as_ref().map(|elem| {
                                            let pred = self
                                                .render_constraint_elem_pred(elem, quote! { #dep });
                                            quote! { !(#pred) }
                                        })
                                    })
                                    .collect::<Vec<_>>();
                                if negated.is_empty() {
                                    quote! { true }
                                } else {
                                    quote! { #(#negated)&&* }
                                }
                            },
                            |elem| self.render_constraint_elem_pred(elem, quote! { #dep }),
                        );
                        quote! { Cond(#cond, #fmt_expr) }
                    } else {
                        fmt.expr.clone()
                    };
                    let ty = if choice_comb.depend_id.is_some() {
                        quote! { Cond<#fmt_ty> }
                    } else {
                        fmt.ty.clone()
                    };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: fmt.value_ty,
                        has_value: true,
                    }
                })
                .collect::<Vec<_>>(),
            Choices::Arrays(branches) => branches
                .iter()
                .enumerate()
                .map(|(idx, (pat, combinator))| {
                    let fmt = self.render_spec_combinator(combinator);
                    let fmt_ty = &fmt.ty;
                    let fmt_expr = &fmt.expr;
                    let expr = if let Some(dep) = &choice_comb.depend_id {
                        let dep = path_tokens(dep);
                        let cond = match pat {
                            ConstArray::Wildcard => {
                                let negated = branches
                                    .iter()
                                    .take(idx)
                                    .filter_map(|(prior_pat, _)| match prior_pat {
                                        ConstArray::Wildcard => None,
                                        _ => {
                                            let pat_expr = self.render_const_array_expr(prior_pat);
                                            Some(quote! { #dep != #pat_expr })
                                        }
                                    })
                                    .collect::<Vec<_>>();
                                if negated.is_empty() {
                                    quote! { true }
                                } else {
                                    quote! { #(#negated)&&* }
                                }
                            }
                            _ => {
                                let pat_expr = self.render_const_array_expr(pat);
                                quote! { #dep == #pat_expr }
                            }
                        };
                        quote! { Cond(#cond, #fmt_expr) }
                    } else {
                        fmt.expr.clone()
                    };
                    let ty = if choice_comb.depend_id.is_some() {
                        quote! { Cond<#fmt_ty> }
                    } else {
                        fmt.ty.clone()
                    };
                    RenderedSpec {
                        ty,
                        expr,
                        value_ty: fmt.value_ty,
                        has_value: true,
                    }
                })
                .collect::<Vec<_>>(),
        };
        fold_choice(branches)
    }

    fn render_enum_top_level(&self, name: &str, enum_comb: &EnumCombinator) -> RenderedSpec {
        let info = self.info(name);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let (variants, exhaustive, inferred) = match enum_comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums.as_slice(), true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => {
                (enums.as_slice(), false, inferred)
            }
        };
        let prim_ty = self.int_combinator_ty(inferred);
        let prim_expr = self.int_combinator_expr(inferred);
        let int_spec_ty = self.int_spec_type(inferred);
        let mut branches = Vec::new();
        for variant in variants {
            let value_expr = int_literal(variant.value, inferred);
            let branch_ty = quote! { Const<#prim_ty, #int_spec_ty> };
            let branch_expr = quote! { Const(#prim_expr, #value_expr) };
            branches.push(RenderedSpec {
                ty: branch_ty,
                expr: branch_expr,
                value_ty: int_spec_ty.clone(),
                has_value: true,
            });
        }
        if !exhaustive {
            let pred = variants.iter().fold(quote! { true }, |acc, variant| {
                let value = int_literal(variant.value, inferred);
                quote! { #acc && x != #value }
            });
            let branch_ty = quote! { Refined<#prim_ty, PredFnSpec<#int_spec_ty>> };
            let branch_expr = quote! { Refined(#prim_expr, |x: #int_spec_ty| #pred) };
            branches.push(RenderedSpec {
                ty: branch_ty,
                expr: branch_expr,
                value_ty: int_spec_ty.clone(),
                has_value: true,
            });
        }
        let raw = fold_choice(branches);
        let forward_arms = variants.iter().enumerate().map(|(idx, variant)| {
            let pat = sum_pattern(
                idx,
                variants.len() + if exhaustive { 0 } else { 1 },
                quote! { _ },
            );
            let ident = format_ident!("{}", variant.name);
            quote! { #pat => #spec_ident::#ident, }
        });
        let unknown_forward = if exhaustive {
            quote! {}
        } else {
            let pat = sum_pattern(variants.len(), variants.len() + 1, quote! { v });
            quote! { #pat => #spec_ident::Unknown(v), }
        };
        let reverse_arms = variants.iter().enumerate().map(|(idx, variant)| {
            let value = int_literal(variant.value, inferred);
            let expr = sum_injection(
                idx,
                variants.len() + if exhaustive { 0 } else { 1 },
                quote! { #value },
            );
            let ident = format_ident!("{}", variant.name);
            quote! { #spec_ident::#ident => #expr, }
        });
        let unknown_reverse = if exhaustive {
            quote! {}
        } else {
            let expr = sum_injection(variants.len(), variants.len() + 1, quote! { v });
            quote! { #spec_ident::Unknown(v) => #expr, }
        };
        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let ty = quote! { Mapped<#raw_ty, FnSpecMapper<#inner_ident, #spec_ident>> };
        let expr = quote! {
            Mapped {
                inner: #raw_expr,
                mapper: (
                    |parsed: #inner_ident| -> #spec_ident {
                        match parsed {
                            #(#forward_arms)*
                            #unknown_forward
                        }
                    },
                    |value: #spec_ident| -> #inner_ident {
                        match value {
                            #(#reverse_arms)*
                            #unknown_reverse
                        }
                    }
                )
            }
        };
        RenderedSpec {
            ty,
            expr,
            value_ty: quote! { #spec_ident },
            has_value: true,
        }
    }

    fn render_const_spec(&self, combinator: &ConstCombinator) -> ConstRendered {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(bytes) => {
                let n = syn_usize(bytes.len);
                let values = self.render_const_array_expr(&bytes.values);
                ConstRendered {
                    ty: quote! { Const<Fixed<#n>, Seq<u8>> },
                    expr: quote! { Const(Fixed::<#n>, #values) },
                    value_ty: quote! { Seq<u8> },
                    value_expr: values,
                }
            }
            ConstCombinator::ConstInt(int_comb) => {
                let prim_ty = self.int_combinator_ty(&int_comb.combinator);
                let prim_expr = self.int_combinator_expr(&int_comb.combinator);
                let value_ty = self.int_type(&int_comb.combinator, TypeMode::Spec);
                let value_expr = int_literal(int_comb.value, &int_comb.combinator);
                ConstRendered {
                    ty: quote! { Const<#prim_ty, #value_ty> },
                    expr: quote! { Const(#prim_expr, #value_expr) },
                    value_ty,
                    value_expr,
                }
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner = self.render_spec_combinator(&Combinator {
                    inner: CombinatorInner::Invocation(enum_comb.combinator.clone()),
                    and_then: None,
                });
                let enum_ty = self.render_value_type(
                    &Combinator {
                        inner: CombinatorInner::Invocation(enum_comb.combinator.clone()),
                        and_then: None,
                    },
                    TypeMode::Spec,
                    true,
                );
                let inner_ty = &inner.ty;
                let inner_expr = &inner.expr;
                let variant_ident = format_ident!("{}", enum_comb.variant);
                let value_expr = quote! { #enum_ty::#variant_ident };
                ConstRendered {
                    ty: quote! { Const<#inner_ty, #enum_ty> },
                    expr: quote! { Const(#inner_expr, #value_expr) },
                    value_ty: enum_ty,
                    value_expr,
                }
            }
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let info = self.info(name);
                let ty_ident = format_ident!("{}Spec", info.names.fmt);
                let fn_ident = format_ident!("{}", info.names.fmt_fn);
                let value_ty = self.nominal_type(name, TypeMode::Spec);
                let value_expr = quote! { arbitrary() };
                ConstRendered {
                    ty: quote! { #ty_ident },
                    expr: quote! { #fn_ident() },
                    value_ty,
                    value_expr,
                }
            }
        }
    }

    fn render_length_expr_usize(&self, len: &LengthExpr) -> TokenStream {
        match len {
            LengthExpr::Const(n) => syn_usize(*n),
            LengthExpr::Dependent(name) => {
                let path = path_tokens(name);
                quote! { (#path as usize) }
            }
            LengthExpr::SizeOf(name) => {
                if let Some(n) = self.ctx.static_sizes.get(name) {
                    syn_usize(*n)
                } else {
                    let fmt_ident = format_ident!("{}Spec", self.info(name).names.fmt);
                    quote! { (<#fmt_ident as StaticByteLen>::static_byte_len() as usize) }
                }
            }
            LengthExpr::BinOp { op, left, right } => {
                let left = self.render_length_expr_usize(left);
                let right = self.render_length_expr_usize(right);
                match op {
                    vestir::ArithOp::Add => quote! { (#left + #right) },
                    vestir::ArithOp::Sub => quote! { (#left - #right) },
                    vestir::ArithOp::Mul => quote! { (#left * #right) },
                    vestir::ArithOp::Div => quote! { (#left / #right) },
                }
            }
        }
    }

    fn render_const_array_expr(&self, array: &ConstArray) -> TokenStream {
        match array {
            ConstArray::Char(bytes) => {
                let elems = bytes.iter().map(|b| proc_macro2::Literal::u8_suffixed(*b));
                quote! { seq![#(#elems),*] }
            }
            ConstArray::Int(values) => {
                let elems = values
                    .iter()
                    .map(|v| proc_macro2::Literal::i128_unsuffixed(*v))
                    .collect::<Vec<_>>();
                quote! { seq![#(#elems),*] }
            }
            ConstArray::Repeat(value, len) => {
                let value = proc_macro2::Literal::i128_unsuffixed(*value);
                let len = syn_usize(*len);
                quote! { Seq::new(#len as nat, |_: int| #value) }
            }
            ConstArray::Wildcard => quote! { arbitrary() },
        }
    }

    fn render_int_constraint(
        &self,
        constraint: &vestir::IntConstraint,
        int_ty: &IntCombinator,
        value: TokenStream,
    ) -> TokenStream {
        match constraint {
            vestir::IntConstraint::Single(elem) => {
                self.render_constraint_elem_with_ty(elem, int_ty, value)
            }
            vestir::IntConstraint::Set(elems) => {
                let parts = elems
                    .iter()
                    .map(|elem| self.render_constraint_elem_with_ty(elem, int_ty, value.clone()))
                    .collect::<Vec<_>>();
                quote! { #(#parts)||* }
            }
            vestir::IntConstraint::Neg(inner) => {
                let inner = self.render_int_constraint(inner, int_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn render_constraint_elem_with_ty(
        &self,
        elem: &ConstraintElem,
        int_ty: &IntCombinator,
        value: TokenStream,
    ) -> TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = int_literal(*v, int_ty);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
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

    fn render_constraint_elem_pred(
        &self,
        elem: &ConstraintElem,
        value: TokenStream,
    ) -> TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
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

    fn render_enum_constraint(
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
                let parts = names.iter().map(|name| {
                    let variant = format_ident!("{}", name);
                    quote! { #value == #enum_ty::#variant }
                });
                quote! { #(#parts)||* }
            }
            vestir::EnumConstraint::Neg(inner) => {
                let inner = self.render_enum_constraint(inner, enum_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn int_combinator_ty(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt<true> },
            IntCombinator::ULEB128 => quote! { ULeb128<true, 10> },
            other => panic!(
                "unsupported integer combinator in spec emitter: {:?}",
                other
            ),
        }
    }

    fn int_combinator_expr(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt::<true> },
            IntCombinator::ULEB128 => quote! { ULeb128::<true, 10> },
            other => panic!(
                "unsupported integer combinator in spec emitter: {:?}",
                other
            ),
        }
    }

    fn render_enum_pattern_type(
        &self,
        variant_name: &str,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
    ) -> TokenStream {
        let dep = choice_comb
            .depend_id
            .as_ref()
            .expect("enum choice should be dependent");
        let dep_base = dep.split('.').next().unwrap();
        if let Some(owner_name) = owner_name {
            if let Some(ty) =
                self.param_defns_for(owner_name)
                    .iter()
                    .find_map(|param| match param {
                        ParamDefn::Dependent { name, combinator } if name == dep_base => {
                            if let CombinatorInner::Invocation(inv) = combinator {
                                Some(self.nominal_type(&inv.func, TypeMode::Spec))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
            {
                return ty;
            }
        }
        let def = self
            .defs
            .iter()
            .find_map(|def| match def {
                vestir::Definition::Combinator { combinator, .. } => match self
                    .ctx
                    .resolve(combinator)
                {
                    CombinatorInner::Struct(struct_comb) => {
                        struct_comb.0.iter().find_map(|field| match field {
                            StructField::Dependent { label, combinator } if label == dep_base => {
                                if let CombinatorInner::Invocation(inv) = &combinator.inner {
                                    Some(self.nominal_type(&inv.func, TypeMode::Spec))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        })
                    }
                    _ => None,
                },
                _ => None,
            })
            .unwrap_or_else(|| {
                let name = variant_name;
                panic!("could not resolve enum pattern type for `{name}`")
            });
        def
    }
}

struct ConstRendered {
    ty: TokenStream,
    expr: TokenStream,
    value_ty: TokenStream,
    value_expr: TokenStream,
}

fn fold_choice(mut branches: Vec<RenderedSpec>) -> RenderedSpec {
    assert!(!branches.is_empty(), "choice must have at least one branch");
    if branches.len() == 1 {
        return branches.remove(0);
    }
    let first = branches.remove(0);
    let rest = fold_choice(branches);
    let first_ty = &first.ty;
    let first_expr = &first.expr;
    let first_value_ty = &first.value_ty;
    let rest_ty = &rest.ty;
    let rest_expr = &rest.expr;
    let rest_value_ty = &rest.value_ty;
    RenderedSpec {
        ty: quote! { Choice<#first_ty, #rest_ty> },
        expr: quote! { Choice(#first_expr, #rest_expr) },
        value_ty: quote! { Sum<#first_value_ty, #rest_value_ty> },
        has_value: true,
    }
}

fn nested_tuple_pattern(labels: &[String]) -> TokenStream {
    let idents = labels
        .iter()
        .map(|label| format_ident!("{}", label))
        .collect::<Vec<_>>();
    nested_tuple_pattern_idents(&idents)
}

fn nested_tuple_pattern_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        [first, rest @ ..] => {
            let rest = nested_tuple_pattern_idents(rest);
            quote! { (#first, #rest) }
        }
    }
}

fn struct_init_fields_expr(labels: &[String]) -> TokenStream {
    let idents = labels
        .iter()
        .map(|label| format_ident!("{}", label))
        .collect::<Vec<_>>();
    let fields = idents
        .iter()
        .map(|ident| quote! { #ident: #ident })
        .collect::<Vec<_>>();
    quote! { #(#fields),* }
}

fn nested_tuple_value_expr(labels: &[String]) -> TokenStream {
    let idents = labels
        .iter()
        .map(|label| format_ident!("{}", label))
        .collect::<Vec<_>>();
    nested_tuple_value_expr_idents(&idents)
}

fn nested_tuple_value_expr_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        [first, rest @ ..] => {
            let rest = nested_tuple_value_expr_idents(rest);
            quote! { (#first, #rest) }
        }
    }
}

fn sum_pattern(idx: usize, total: usize, leaf_pat: TokenStream) -> TokenStream {
    if total == 1 {
        return leaf_pat;
    }
    if idx == 0 {
        quote! { Sum::Inl(#leaf_pat) }
    } else {
        let rest = sum_pattern(idx - 1, total - 1, leaf_pat);
        quote! { Sum::Inr(#rest) }
    }
}

fn sum_injection(idx: usize, total: usize, leaf_expr: TokenStream) -> TokenStream {
    if total == 1 {
        return leaf_expr;
    }
    if idx == 0 {
        quote! { Sum::Inl(#leaf_expr) }
    } else {
        let rest = sum_injection(idx - 1, total - 1, leaf_expr);
        quote! { Sum::Inr(#rest) }
    }
}

fn is_empty_ty(ty: &TokenStream) -> bool {
    ty.to_string() == "Empty"
}

fn path_tokens(path: &str) -> TokenStream {
    path.parse()
        .unwrap_or_else(|_| panic!("invalid generated path `{path}`"))
}
