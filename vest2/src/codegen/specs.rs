use super::common::{int_literal, syn_usize, Analysis, FormatNames, TypeMode};
use super::writer::{render_ts, CodeWriter};
use crate::vestir::{
    self, ChoiceCombinator, ChoicePattern, Combinator, ConstCombinator, ConstraintElem,
    ConstraintEnumCombinator, ConstraintIntCombinator, EnumCombinator, Param, ParamDefn,
    StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

#[derive(Clone)]
struct RenderedSpec {
    ty: TokenStream,
    expr: TokenStream,
    value_ty: TokenStream,
    has_value: bool,
}

impl RenderedSpec {
    fn new(ty: TokenStream, expr: TokenStream, value_ty: TokenStream, has_value: bool) -> Self {
        Self {
            ty,
            expr,
            value_ty,
            has_value,
        }
    }
}

impl<'a> Analysis<'a> {
    fn gen_wrapped_specs_section(
        &self,
        name: &str,
        param_defns: &[ParamDefn],
        render_body: impl FnOnce() -> String,
    ) -> String {
        let mut out = String::new();
        out.push_str(&self.gen_wrapper_type(name, param_defns));
        out.push_str("\n\n");
        out.push_str(&render_body());
        out
    }

    pub(crate) fn gen_struct_specs_section(
        &self,
        name: &str,
        combinator: &StructCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_wrapped_specs_section(name, param_defns, || {
            self.gen_struct_format_spec_alias_and_ctor(name, combinator, param_defns)
        })
    }

    pub(crate) fn gen_choice_specs_section(
        &self,
        name: &str,
        combinator: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_wrapped_specs_section(name, param_defns, || {
            self.gen_choice_format_spec_alias_and_ctor(name, combinator, param_defns)
        })
    }

    pub(crate) fn gen_enum_specs_section(
        &self,
        name: &str,
        combinator: &EnumCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_wrapped_specs_section(name, param_defns, || {
            self.gen_enum_format_spec_alias_and_ctor(name, combinator, param_defns)
        })
    }

    pub(crate) fn gen_specs_section(
        &self,
        name: &str,
        combinator: &Combinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_wrapped_specs_section(name, param_defns, || {
            self.gen_format_spec_alias_and_ctor(name, combinator, param_defns)
        })
    }

    pub(crate) fn gen_derived_specs_section_impl(
        &self,
        name: &str,
        param_defns: &[ParamDefn],
    ) -> String {
        let info = self.info(name);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let inner_ident = info.names.spec_ctor_ident();
        let top_value_ty = self.nominal_type(name, TypeMode::Spec);
        let wrapper_generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);

        self.gen_derived_spec_impls(
            &fmt_ident,
            &inner_ident,
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
        self.gen_named_top_level_spec_alias_and_ctor(
            name,
            self.render_spec_combinator(combinator),
            param_defns,
        )
    }

    fn gen_struct_format_spec_alias_and_ctor(
        &self,
        name: &str,
        combinator: &StructCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_named_top_level_spec_alias_and_ctor(
            name,
            self.render_struct_top_level(name, combinator),
            param_defns,
        )
    }

    fn gen_choice_format_spec_alias_and_ctor(
        &self,
        name: &str,
        combinator: &ChoiceCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_named_top_level_spec_alias_and_ctor(
            name,
            self.render_choice_top_level(name, combinator),
            param_defns,
        )
    }

    fn gen_enum_format_spec_alias_and_ctor(
        &self,
        name: &str,
        combinator: &EnumCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_named_top_level_spec_alias_and_ctor(
            name,
            self.render_enum_top_level(name, combinator),
            param_defns,
        )
    }

    fn gen_named_top_level_spec_alias_and_ctor(
        &self,
        name: &str,
        raw: RenderedSpec,
        param_defns: &[ParamDefn],
    ) -> String {
        let info = self.info(name);
        let fmt_spec_ident = format_ident!("{}Spec", info.names.fmt);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let inner_ident = info.names.spec_ctor_ident();
        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let named_ty = quote! { Named<#raw_ty> };
        let named_expr = quote! { Named(#name, #raw_expr) };
        let spec_params = self.spec_param_list(param_defns);
        let ctor_doc = format!("specification constructor for `{}`.", name);
        let wrapper_generics = self.wrapper_generics(param_defns);

        let mut out = CodeWriter::new();
        out.push_multiline(render_ts(quote! { pub type #fmt_spec_ident = #named_ty; }));
        out.blank_line();
        out.push_multiline(render_ts(quote! {
            impl #wrapper_generics #fmt_ident #wrapper_generics {
                #[doc = #ctor_doc]
                pub open spec fn #inner_ident(#(#spec_params),*) -> #fmt_spec_ident {
                    #named_expr
                }
            }
        }));
        out.finish()
    }

    fn gen_derived_spec_impls(
        &self,
        fmt_ident: &proc_macro2::Ident,
        inner_ident: &proc_macro2::Ident,
        wrapper_generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
        top_value_ty: &TokenStream,
    ) -> String {
        let opaque = if wrapper_generics.is_empty() {
            quote! { #[verifier::opaque] }
        } else {
            quote! {}
        };

        render_ts(quote! {
            impl #wrapper_generics SpecParser for #fmt_ident #wrapper_generics {
                type PVal = #top_value_ty;

                #opaque
                open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).spec_parse(ibuf)
                }
            }

            impl #wrapper_generics Consistency for #fmt_ident #wrapper_generics {
                type Val = #top_value_ty;

                open spec fn consistent(&self, v: Self::Val) -> bool {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).consistent(v)
                }
            }

            impl #wrapper_generics SpecSerializerDps for #fmt_ident #wrapper_generics {
                type SValue = #top_value_ty;

                #opaque
                open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).spec_serialize_dps(v, obuf)
                }
            }

            impl #wrapper_generics SpecSerializer for #fmt_ident #wrapper_generics {
                type SVal = #top_value_ty;

                #opaque
                open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).spec_serialize(v)
                }
            }

            impl #wrapper_generics SpecByteLen for #fmt_ident #wrapper_generics {
                type T = #top_value_ty;

                #opaque
                open spec fn byte_len(&self, v: Self::T) -> nat {
                    #fmt_ident::#inner_ident(#(#wrapper_call_args),*).byte_len(v)
                }
            }
        })
    }

    fn render_sequence_with_rest(
        &self,
        current: RenderedSpec,
        rest: &RenderedSpec,
    ) -> RenderedSpec {
        let cur_ty = &current.ty;
        let cur_expr = &current.expr;
        let cur_value_ty = &current.value_ty;
        let rest_ty = &rest.ty;
        let rest_expr = &rest.expr;
        let rest_value_ty = &rest.value_ty;

        if rest.has_value {
            RenderedSpec::new(
                quote! { Pair<#cur_ty, #rest_ty> },
                quote! { Pair(#cur_expr, #rest_expr) },
                quote! { (#cur_value_ty, #rest_value_ty) },
                true,
            )
        } else if is_empty_ty(&rest.ty) {
            current
        } else {
            RenderedSpec::new(
                quote! { Terminated<#cur_ty, #rest_ty, #rest_value_ty> },
                quote! { Terminated { a: #cur_expr, b: #rest_expr, b_val: () } },
                current.value_ty,
                true,
            )
        }
    }

    fn render_invocation_spec(&self, invocation: &vestir::CombinatorInvocation) -> RenderedSpec {
        let info = self.info(&invocation.func);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let fmt_ident_inner = format_ident!("{}Spec", info.names.fmt);
        let ctor_inner_ident = info.names.spec_ctor_ident();
        let ctor_ident = info.names.wrapper_ctor_ident();
        let args = invocation
            .args
            .iter()
            .map(|arg| match arg {
                Param::Dependent(name) => path_tokens(name),
            })
            .collect::<Vec<_>>();
        // see if all params are "self view"
        let can_use_wrapper_fmt = self
            .param_defns_for(&invocation.func)
            .iter()
            .all(|p| match p {
                ParamDefn::Dependent { combinator, .. } => self.combinator_is_selfview(combinator),
            });
        let expr = if args.is_empty() {
            quote! { #fmt_ident }
        } else if can_use_wrapper_fmt {
            quote! { #fmt_ident::#ctor_ident(#(#args),*) }
        } else {
            quote! { #fmt_ident::#ctor_inner_ident(#(#args),*) }
        };

        RenderedSpec::new(
            if args.is_empty() || can_use_wrapper_fmt {
                quote! { #fmt_ident }
            } else {
                quote! { #fmt_ident_inner }
            },
            expr,
            self.render_value_type(&Combinator::Invocation(invocation.clone()), TypeMode::Spec),
            true,
        )
    }

    fn render_and_then_spec(&self, lhs: &Combinator, rhs: &Combinator) -> RenderedSpec {
        match self.ctx.resolve_alias(lhs) {
            Combinator::Bytes(bytes) => {
                let len_ty = self.int_type(&bytes.len.ty);
                let len_expr = self.render_length_expr_with(
                    &bytes.len,
                    &|name| path_tokens(name),
                    Some(&len_ty),
                );
                let inner = self.render_spec_combinator(rhs);
                let inner_ty = &inner.ty;
                let inner_expr = &inner.expr;
                RenderedSpec::new(
                    quote! { ExactLen<#inner_ty, #len_ty> },
                    quote! { ExactLen(#len_expr, #inner_expr) },
                    inner.value_ty,
                    inner.has_value,
                )
            }
            _ => {
                let lhs = self.render_spec_combinator(lhs);
                let rhs = self.render_spec_combinator(rhs);
                let lhs_ty = &lhs.ty;
                let lhs_expr = &lhs.expr;
                let rhs_ty = &rhs.ty;
                let rhs_expr = &rhs.expr;
                RenderedSpec::new(
                    quote! { AndThen<#lhs_ty, #rhs_ty> },
                    quote! { AndThen(#lhs_expr, #rhs_expr) },
                    rhs.value_ty,
                    rhs.has_value,
                )
            }
        }
    }

    fn render_spec_combinator(&self, combinator: &Combinator) -> RenderedSpec {
        match combinator {
            Combinator::AndThen(lhs, rhs) => return self.render_and_then_spec(lhs, rhs),
            Combinator::Invocation(invocation) => return self.render_invocation_spec(invocation),
            _ => {}
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(c) => self.render_constraint_int(c),
            Combinator::ConstraintEnum(c) => self.render_constraint_enum(c),
            Combinator::Wrap(wrap) => self.render_wrap(wrap),
            Combinator::Vec(vec_comb) => self.render_vec(vec_comb),
            Combinator::Array(array_comb) => self.render_array(array_comb),
            Combinator::Bytes(bytes) => self.render_bytes(bytes),
            Combinator::Tail(_) => RenderedSpec {
                ty: quote! { Tail },
                expr: quote! { Tail },
                value_ty: quote! { Seq<u8> },
                has_value: true,
            },
            Combinator::Option(opt) => self.render_option(opt),
            Combinator::Invocation(_) | Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn render_constraint_int(&self, c: &ConstraintIntCombinator) -> RenderedSpec {
        let prim_ty = self.int_combinator_ty(&c.combinator);
        let prim_expr = self.int_combinator_expr(&c.combinator);
        let value_ty = self.int_type(&c.combinator);
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
        let inner = self.render_spec_combinator(&Combinator::Invocation(c.combinator.clone()));
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
                RenderedSpec::new(quote! { Fixed<#n> }, quote! { Fixed::<#n> }, value_ty, true)
            }
            None => {
                let len_ty = self.int_type(&bytes.len.ty);
                let len = self.render_length_expr_with(
                    &bytes.len,
                    &|name| path_tokens(name),
                    Some(&len_ty),
                );
                RenderedSpec::new(
                    quote! { Varied<#len_ty> },
                    quote! { Varied(#len) },
                    value_ty,
                    true,
                )
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
                RenderedSpec::new(
                    quote! { RepeatTillEnd<#inner_ty> },
                    quote! { RepeatTillEnd(#inner_expr) },
                    value_ty,
                    true,
                )
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
                RenderedSpec::new(
                    quote! { Array<#n, #inner_ty> },
                    quote! { Array::<#n, _>(#inner_expr) },
                    value_ty,
                    true,
                )
            }
            None => {
                let len_ty = self.int_type(&array_comb.len.ty);
                let len = self.render_length_expr_with(
                    &array_comb.len,
                    &|name| path_tokens(name),
                    Some(&len_ty),
                );
                RenderedSpec::new(
                    quote! { RepeatN<#inner_ty, #len_ty> },
                    quote! { RepeatN(#len, #inner_expr) },
                    value_ty,
                    true,
                )
            }
        }
    }

    fn render_option(&self, opt: &vestir::OptionCombinator) -> RenderedSpec {
        let inner = self.render_spec_combinator(&opt.0);
        let inner_ty = &inner.ty;
        let inner_expr = &inner.expr;
        let inner_value_ty = &inner.value_ty;
        let value_ty = quote! { Option<#inner_value_ty> };
        RenderedSpec::new(
            quote! { OptionalEnd<#inner_ty> },
            quote! { OptionalEnd(#inner_expr) },
            value_ty,
            true,
        )
    }

    fn render_wrap(&self, wrap: &vestir::WrapCombinator) -> RenderedSpec {
        let mut body = self.render_spec_combinator(&wrap.combinator);
        for const_comb in wrap.post.iter() {
            let c = self.render_tag_spec(const_comb);
            let body_ty = &body.ty;
            let body_expr = &body.expr;
            let c_ty = &c.ty;
            let c_expr = &c.expr;
            let c_value_expr = &c.value_expr;
            let ty = quote! { SuffixTagged<#body_ty, #c_ty> };
            let expr = quote! { SuffixTagged(#body_expr, #c_expr, #c_value_expr) };
            body = RenderedSpec::new(ty, expr, body.value_ty, body.has_value);
        }
        for const_comb in wrap.prior.iter().rev() {
            let c = self.render_tag_spec(const_comb);
            let body_ty = &body.ty;
            let body_expr = &body.expr;
            let c_ty = &c.ty;
            let c_expr = &c.expr;
            let c_value_expr = &c.value_expr;
            let ty = quote! { PrefixTagged<#c_ty, #body_ty> };
            let expr = quote! { PrefixTagged(#c_expr, #c_value_expr, #body_expr) };
            body = RenderedSpec::new(ty, expr, body.value_ty, body.has_value);
        }
        body
    }

    fn render_struct_fields(&self, fields: &[StructField]) -> RenderedSpec {
        if fields.is_empty() {
            return RenderedSpec::new(quote! { Empty }, quote! { Empty }, quote! { () }, false);
        }
        let first = &fields[0];
        let rest = self.render_struct_fields(&fields[1..]);
        match first {
            StructField::Const { combinator, .. } => {
                let c = self.render_const_spec(combinator);
                self.render_sequence_with_rest(
                    RenderedSpec::new(c.ty, c.expr, c.value_ty, true),
                    &rest,
                )
            }
            StructField::Ordinary { combinator, .. } => {
                if let Some(rendered) = self.render_optional_or_repeat_with_rest(combinator, &rest)
                {
                    return rendered;
                }
                self.render_sequence_with_rest(self.render_spec_combinator(combinator), &rest)
            }
            StructField::Dependent { label, combinator } => {
                if let Some(rendered) = self.render_optional_or_repeat_with_rest(combinator, &rest)
                {
                    return rendered;
                }
                let cur = self.render_spec_combinator(combinator);
                let label_ident = format_ident!("{}", label);
                let cur_ty = &cur.ty;
                let cur_expr = &cur.expr;
                let cur_value_ty = &cur.value_ty;
                let rest_ty = &rest.ty;
                let rest_expr = &rest.expr;
                let rest_value_ty = &rest.value_ty;
                if rest.has_value {
                    RenderedSpec::new(
                        quote! { Bind<#cur_ty, spec_fn(#cur_value_ty) -> #rest_ty> },
                        quote! { Bind(#cur_expr, |#label_ident: #cur_value_ty| #rest_expr) },
                        quote! { (#cur_value_ty, #rest_value_ty) },
                        true,
                    )
                } else if is_empty_ty(&rest.ty) {
                    cur
                } else {
                    RenderedSpec::new(
                        quote! { Terminated<#cur_ty, #rest_ty, #rest_value_ty> },
                        quote! { Terminated { a: #cur_expr, b: #rest_expr, b_val: () } },
                        cur.value_ty,
                        true,
                    )
                }
            }
        }
    }

    fn render_optional_or_repeat_with_rest(
        &self,
        combinator: &Combinator,
        rest: &RenderedSpec,
    ) -> Option<RenderedSpec> {
        if matches!(combinator, Combinator::AndThen(_, _)) {
            return None;
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::Option(opt) => {
                let inner = self.render_spec_combinator(&opt.0);
                let inner_ty = &inner.ty;
                let inner_expr = &inner.expr;
                let inner_value_ty = &inner.value_ty;
                let value_ty = quote! { Option<#inner_value_ty> };
                if is_empty_ty(&rest.ty) {
                    Some(RenderedSpec {
                        ty: quote! { OptionalEnd<#inner_ty> },
                        expr: quote! { OptionalEnd(#inner_expr) },
                        value_ty,
                        has_value: true,
                    })
                } else {
                    let rest_ty = &rest.ty;
                    let rest_expr = &rest.expr;
                    let rest_value_ty = &rest.value_ty;
                    let pair_ty = quote! { (#value_ty, #rest_value_ty) };
                    Some(RenderedSpec {
                        ty: quote! { Optional<#inner_ty, #rest_ty> },
                        expr: quote! { Optional(#inner_expr, #rest_expr) },
                        value_ty: pair_ty,
                        has_value: true,
                    })
                }
            }
            Combinator::Vec(vec_comb) => match vec_comb {
                vestir::VecCombinator::Vec(inner_comb) => {
                    let inner = self.render_spec_combinator(inner_comb);
                    let inner_ty = &inner.ty;
                    let inner_expr = &inner.expr;
                    let inner_value_ty = &inner.value_ty;
                    let value_ty = quote! { Seq<#inner_value_ty> };
                    if is_empty_ty(&rest.ty) {
                        Some(RenderedSpec {
                            ty: quote! { RepeatTillEnd<#inner_ty> },
                            expr: quote! { RepeatTillEnd(#inner_expr) },
                            value_ty,
                            has_value: true,
                        })
                    } else {
                        let rest_ty = &rest.ty;
                        let rest_expr = &rest.expr;
                        let rest_value_ty = &rest.value_ty;
                        let pair_ty = quote! { (#value_ty, #rest_value_ty) };
                        Some(RenderedSpec {
                            ty: quote! { Repeat<#inner_ty, #rest_ty> },
                            expr: quote! { Repeat(#inner_expr, #rest_expr) },
                            value_ty: pair_ty,
                            has_value: true,
                        })
                    }
                }
            },
            _ => None,
        }
    }

    fn render_tag_spec(&self, combinator: &ConstCombinator) -> ConstRendered {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(bytes) => {
                let n = syn_usize(bytes.len);
                let values = self.render_const_array_expr(&bytes.values, TypeMode::Spec);
                ConstRendered {
                    ty: quote! { Fixed<#n> },
                    expr: quote! { Fixed::<#n> },
                    value_ty: quote! { Seq<u8> },
                    value_expr: values,
                }
            }
            ConstCombinator::ConstInt(int_comb) => {
                let prim_ty = self.int_combinator_ty(&int_comb.combinator);
                let prim_expr = self.int_combinator_expr(&int_comb.combinator);
                let value_ty = self.int_type(&int_comb.combinator);
                let value_expr = int_literal(int_comb.value, &int_comb.combinator);
                ConstRendered {
                    ty: prim_ty,
                    expr: prim_expr,
                    value_ty,
                    value_expr,
                }
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner = self
                    .render_spec_combinator(&Combinator::Invocation(enum_comb.combinator.clone()));
                let enum_ty = self.render_value_type(
                    &Combinator::Invocation(enum_comb.combinator.clone()),
                    TypeMode::Spec,
                );
                let inner_ty = inner.ty;
                let inner_expr = inner.expr;
                let variant_ident = format_ident!("{}", enum_comb.variant);
                let value_expr = quote! { #enum_ty::#variant_ident };
                ConstRendered {
                    ty: inner_ty,
                    expr: inner_expr,
                    value_ty: enum_ty,
                    value_expr,
                }
            }
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let info = self.info(name);
                let fmt_ident = format_ident!("{}", info.names.fmt);
                let ty_ident = format_ident!("{}Spec", info.names.fmt);
                let inner_ident = info.names.spec_ctor_ident();
                let value_ty = self.nominal_type(name, TypeMode::Spec);
                let value_expr = quote! { arbitrary() };
                ConstRendered {
                    ty: quote! { #ty_ident },
                    expr: quote! { #fmt_ident::#inner_ident() },
                    value_ty,
                    value_expr,
                }
            }
        }
    }

    fn render_struct_top_level(&self, name: &str, struct_comb: &StructCombinator) -> RenderedSpec {
        let info = self.info(name);
        let raw = self.render_struct_fields(&struct_comb.0);

        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let labels = struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { label, .. }
                | StructField::Dependent { label, .. }
                | StructField::Ordinary { label, .. } => label.clone(),
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
        if choice_comb.depend_id.is_some() {
            return self.render_dependent_choice_raw(choice_comb, owner_name);
        }

        self.render_choice_raw_via_choice(choice_comb, owner_name)
    }

    fn negated_prior_conditions(
        &self,
        choice_comb: &ChoiceCombinator,
        idx: usize,
        dep: &TokenStream,
        owner_name: Option<&str>,
    ) -> Vec<TokenStream> {
        choice_comb
            .choices
            .iter()
            .take(idx)
            .filter_map(|(prior_pat, _)| match prior_pat {
                ChoicePattern::Enum(name) => {
                    let enum_ty = owner_name
                        .map(|n| self.render_enum_pattern_type(name, choice_comb, Some(n)))
                        .unwrap_or_else(|| {
                            self.render_enum_pattern_type(name, choice_comb, owner_name)
                        });
                    let variant = format_ident!("{}", name);
                    Some(quote! { #dep != #enum_ty::#variant })
                }
                ChoicePattern::Int(elem) => {
                    let pred = self.render_constraint_elem_pred(elem, quote! { #dep });
                    Some(quote! { !(#pred) })
                }
                ChoicePattern::Array(arr) => {
                    let pat_expr = self.render_const_array_expr(arr, TypeMode::Spec);
                    Some(quote! { #dep != #pat_expr })
                }
                ChoicePattern::Wildcard => None,
            })
            .collect()
    }

    fn render_choice_raw_via_choice(
        &self,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
    ) -> RenderedSpec {
        let branches = choice_comb
            .choices
            .iter()
            .enumerate()
            .map(|(idx, (pat, combinator))| {
                let fmt = self.render_spec_combinator(combinator);
                let fmt_ty = &fmt.ty;
                let fmt_expr = &fmt.expr;
                let expr = if let Some(dep) = &choice_comb.depend_id {
                    let dep = path_tokens(dep);
                    let cond = match pat {
                        ChoicePattern::Enum(pat_str) => {
                            let enum_ty =
                                self.render_enum_pattern_type(pat_str, choice_comb, owner_name);
                            let variant = format_ident!("{}", pat_str);
                            quote! { #dep == #enum_ty::#variant }
                        }
                        ChoicePattern::Int(elem) => {
                            self.render_constraint_elem_pred(elem, quote! { #dep })
                        }
                        ChoicePattern::Array(arr) => {
                            let pat_expr = self.render_const_array_expr(arr, TypeMode::Spec);
                            quote! { #dep == #pat_expr }
                        }
                        ChoicePattern::Wildcard => {
                            let negated =
                                self.negated_prior_conditions(choice_comb, idx, &dep, owner_name);
                            if negated.is_empty() {
                                quote! { true }
                            } else {
                                quote! { #(#negated)&&* }
                            }
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
            .collect::<Vec<_>>();
        fold_choice(branches)
    }

    fn render_dependent_choice_raw(
        &self,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
    ) -> RenderedSpec {
        let (branch_specs, match_arms): (Vec<_>, Vec<_>) = choice_comb
            .choices
            .iter()
            .enumerate()
            .map(|(idx, (pat, combinator))| {
                let fmt = self.render_spec_combinator(combinator);
                let inj = sum_injection(idx, choice_comb.choices.len(), fmt.expr.clone());
                let arm = match pat {
                    ChoicePattern::Enum(pat_str) => {
                        let enum_ty = owner_name.and_then(|name| {
                            choice_comb.choices.iter().find_map(|(pat, _)| match pat {
                                ChoicePattern::Enum(pat_str) => Some(
                                    self.render_enum_pattern_type(pat_str, choice_comb, Some(name)),
                                ),
                                _ => None,
                            })
                        });
                        let variant = format_ident!("{}", pat_str);
                        let ty = enum_ty.clone().unwrap_or_else(|| {
                            self.render_enum_pattern_type(pat_str, choice_comb, owner_name)
                        });
                        quote! { #ty::#variant => #inj, }
                    }
                    ChoicePattern::Int(elem) => self.render_int_choice_match_arm(elem, inj),
                    ChoicePattern::Array(arr) => {
                        let pat_expr = self.render_const_array_expr(arr, TypeMode::Spec);
                        quote! { x if x == #pat_expr.deep_view() => #inj, }
                    }
                    ChoicePattern::Wildcard => {
                        quote! { _ => #inj, }
                    }
                };
                (fmt, arm)
            })
            .unzip();

        let branch_tys = branch_specs
            .iter()
            .map(|fmt| fmt.ty.clone())
            .collect::<Vec<_>>();
        let branch_value_tys = branch_specs
            .iter()
            .map(|fmt| fmt.value_ty.clone())
            .collect::<Vec<_>>();
        let ty = self.choice_sum_type(&branch_tys);
        let value_ty = self.choice_sum_type(&branch_value_tys);
        let dep = path_tokens(
            choice_comb
                .depend_id
                .as_ref()
                .expect("dependent choose should have a selector"),
        );

        let expr = quote! {
            match #dep {
                #(#match_arms)*
            }
        };

        RenderedSpec::new(ty, expr, value_ty, true)
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
        let int_spec_ty = self.int_type(inferred);
        let eq_terms = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                quote! { x == #value }
            })
            .collect::<Vec<_>>();
        let allowed_pred = fold_bool_or(eq_terms);
        let disallowed_terms = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                quote! { x != #value }
            })
            .collect::<Vec<_>>();
        let disallowed_pred = fold_bool_and(disallowed_terms);

        let raw = if exhaustive {
            RenderedSpec::new(
                quote! { Refined<#prim_ty, PredFnSpec<#int_spec_ty>> },
                quote! { Refined(#prim_expr, |x: #int_spec_ty| #allowed_pred) },
                int_spec_ty.clone(),
                true,
            )
        } else {
            RenderedSpec::new(
                quote! { Choice<Refined<#prim_ty, PredFnSpec<#int_spec_ty>>, Refined<#prim_ty, PredFnSpec<#int_spec_ty>>> },
                quote! {
                    Choice(
                        Refined(#prim_expr, |x: #int_spec_ty| #allowed_pred),
                        Refined(#prim_expr, |x: #int_spec_ty| #disallowed_pred)
                    )
                },
                quote! { #inner_ident },
                true,
            )
        };

        let exhaustive_forward_arms = variants.iter().map(|variant| {
            let value = int_literal(variant.value, inferred);
            let ident = format_ident!("{}", variant.name);
            quote! { #value => #spec_ident::#ident, }
        });
        let exhaustive_reverse_arms = variants.iter().map(|variant| {
            let value = int_literal(variant.value, inferred);
            let ident = format_ident!("{}", variant.name);
            if exhaustive {
                quote! { #spec_ident::#ident => #value, }
            } else {
                quote! { #spec_ident::#ident => L(#value), }
            }
        });

        let forward_expr = if exhaustive {
            quote! {
                match parsed {
                    #(#exhaustive_forward_arms)*
                    _ => arbitrary(),
                }
            }
        } else {
            quote! {
                match parsed {
                    L(x) => match x {
                        #(#exhaustive_forward_arms)*
                        _ => arbitrary(),
                    },
                    R(x) => #spec_ident::Unknown(x),
                }
            }
        };
        let reverse_expr = if exhaustive {
            quote! {
                match value {
                    #(#exhaustive_reverse_arms)*
                }
            }
        } else {
            quote! {
                match value {
                    #(#exhaustive_reverse_arms)*
                    #spec_ident::Unknown(x) => R(x),
                }
            }
        };

        let raw_ty = &raw.ty;
        let raw_expr = &raw.expr;
        let ty = quote! { Mapped<#raw_ty, FnSpecMapper<#inner_ident, #spec_ident>> };
        let expr = quote! {
            Mapped {
                inner: #raw_expr,
                mapper: (
                    |parsed: #inner_ident| -> #spec_ident {
                        #forward_expr
                    },
                    |value: #spec_ident| -> #inner_ident {
                        #reverse_expr
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
                let values = self.render_const_array_expr(&bytes.values, TypeMode::Spec);
                ConstRendered {
                    ty: quote! { Const<Fixed<#n>, [u8; #n]> },
                    expr: quote! { Const(Fixed::<#n>, #values) },
                    value_ty: quote! { Seq<u8> },
                    value_expr: values,
                }
            }
            ConstCombinator::ConstInt(int_comb) => {
                let prim_ty = self.int_combinator_ty(&int_comb.combinator);
                let prim_expr = self.int_combinator_expr(&int_comb.combinator);
                let value_ty = self.int_type(&int_comb.combinator);
                let value_expr = int_literal(int_comb.value, &int_comb.combinator);
                ConstRendered {
                    ty: quote! { Const<#prim_ty, #value_ty> },
                    expr: quote! { Const(#prim_expr, #value_expr) },
                    value_ty,
                    value_expr,
                }
            }
            ConstCombinator::ConstEnum(enum_comb) => {
                let inner = self
                    .render_spec_combinator(&Combinator::Invocation(enum_comb.combinator.clone()));
                let enum_ty = self.render_value_type(
                    &Combinator::Invocation(enum_comb.combinator.clone()),
                    TypeMode::Spec,
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
                let fmt_ident = format_ident!("{}", info.names.fmt);
                let inner_ident = info.names.spec_ctor_ident();
                let value_ty = self.nominal_type(name, TypeMode::Spec);
                let value_expr = quote! { arbitrary() };
                ConstRendered {
                    ty: quote! { #ty_ident },
                    expr: quote! { #fmt_ident::#inner_ident() },
                    value_ty,
                    value_expr,
                }
            }
        }
    }

    fn render_int_choice_match_arm(
        &self,
        elem: &ConstraintElem,
        branch_expr: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        let pat = self.render_constraint_elem_pat(elem);
        quote! { #pat => #branch_expr, }
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
                            if let Combinator::Invocation(inv) = combinator {
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
                vestir::Definition::StructDef { combinator, .. } => {
                    combinator.0.iter().find_map(|field| match field {
                        StructField::Dependent { label, combinator } if label == dep_base => {
                            if let Combinator::Invocation(inv) = combinator {
                                Some(self.nominal_type(&inv.func, TypeMode::Spec))
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                }
                _ => None,
            })
            .unwrap_or_else(|| {
                let name = variant_name;
                panic!("could not resolve enum pattern type for `{name}`")
            });
        def
    }

    fn spec_param_list(&self, param_defns: &[ParamDefn]) -> Vec<TokenStream> {
        param_defns
            .iter()
            .map(|param| match param {
                ParamDefn::Dependent { name, combinator } => {
                    let ident = format_ident!("{}", name);
                    let ty = self.render_value_type(combinator, TypeMode::Spec);
                    quote! { #ident: #ty }
                }
            })
            .collect()
    }

    fn gen_wrapper_type(&self, name: &str, param_defns: &[ParamDefn]) -> String {
        let info = self.info(name);
        let fmt_ident = format_ident!("{}", info.names.fmt);
        let doc = format!("named format combinator for `{}`.", name);
        let lifetime = if param_defns
            .iter()
            .any(|param| self.param_needs_lifetime(param))
        {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let fields = param_defns
            .iter()
            .map(|param| match param {
                ParamDefn::Dependent { name, combinator } => {
                    let field_ident = FormatNames::wrapper_field_ident(name);
                    let ty = self.render_value_type(combinator, TypeMode::Exec);
                    quote! { #field_ident: #ty }
                }
            })
            .collect::<Vec<_>>();
        let accessors = param_defns
            .iter()
            .map(|param| match param {
                ParamDefn::Dependent { name, combinator } => {
                    let field_ident = FormatNames::wrapper_field_ident(name);
                    let accessor_ident = FormatNames::wrapper_accessor_ident(name);
                    let spec_ty = self.render_value_type(combinator, TypeMode::Spec);
                    quote! {
                        pub closed spec fn #accessor_ident(&self) -> #spec_ty {
                            self.#field_ident.deep_view()
                        }
                    }
                }
            })
            .collect::<Vec<_>>();
        let invariant_terms = param_defns
            .iter()
            .filter_map(|param| match param {
                ParamDefn::Dependent { name, combinator } => {
                    let field_ident = FormatNames::wrapper_field_ident(name);
                    match self.ctx.resolve_alias(combinator) {
                        Combinator::ConstraintInt(c) => c.constraint.as_ref().map(|constraint| {
                            self.render_int_constraint(
                                constraint,
                                &c.combinator,
                                quote! { self.#field_ident },
                            )
                        }),
                        Combinator::ConstraintEnum(c) => Some(self.render_enum_constraint(
                            &c.constraint,
                            &self.nominal_type(&c.combinator.func, TypeMode::Spec),
                            quote! { self.#field_ident },
                        )),
                        Combinator::Invocation(invocation) => {
                            let rendered = self.render_invocation_spec(&invocation);
                            let expr = rendered.expr;
                            Some(quote! { #expr.consistent(self.#field_ident.deep_view()) })
                        }
                        _ => None,
                    }
                }
            })
            .collect::<Vec<_>>();
        if fields.is_empty() {
            render_ts(quote! {
                #[doc = #doc]
                #[derive(Clone, Copy)]
                pub struct #fmt_ident;
            })
        } else {
            let invariant = if invariant_terms.is_empty() {
                quote! { true }
            } else {
                quote! { #(#invariant_terms)&&* }
            };
            let ctor_ident = info.names.wrapper_ctor_ident();
            let ctor_params = param_defns
                .iter()
                .map(|param| match param {
                    ParamDefn::Dependent { name, combinator } => {
                        let ident = format_ident!("{}", name);
                        let ty = self.render_value_type(combinator, TypeMode::Exec);
                        quote! { #ident: #ty }
                    }
                })
                .collect::<Vec<_>>();
            let ctor_inits = param_defns
                .iter()
                .map(|param| match param {
                    ParamDefn::Dependent { name, .. } => {
                        let ident = format_ident!("{}", name);
                        quote! { #ident }
                    }
                })
                .collect::<Vec<_>>();
            let ctor = quote! {
                    pub closed spec fn #ctor_ident(#(#ctor_params),*) -> Self {
                        #fmt_ident { #(#ctor_inits),* }
                    }

            };
            render_ts(quote! {
                #[doc = #doc]
                #[derive(Clone, Copy)]
                pub struct #fmt_ident #lifetime {
                    #(#fields,)*
                }

                impl #lifetime #fmt_ident #lifetime {
                    #[verifier::type_invariant]
                    spec fn wf(&self) -> bool {
                        #invariant
                    }

                    #(#accessors)*
                    #ctor
                }
            })
        }
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

fn fold_bool_or(mut terms: Vec<TokenStream>) -> TokenStream {
    let first = terms
        .drain(..1)
        .next()
        .expect("boolean disjunction requires at least one term");
    terms
        .into_iter()
        .fold(first, |acc, term| quote! { #acc || #term })
}

fn fold_bool_and(mut terms: Vec<TokenStream>) -> TokenStream {
    let first = terms
        .drain(..1)
        .next()
        .expect("boolean conjunction requires at least one term");
    terms
        .into_iter()
        .fold(first, |acc, term| quote! { #acc && #term })
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
        .map(|ident| quote! { #ident })
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
        quote! { L(#leaf_pat) }
    } else {
        let rest = sum_pattern(idx - 1, total - 1, leaf_pat);
        quote! { R(#rest) }
    }
}

fn sum_injection(idx: usize, total: usize, leaf_expr: TokenStream) -> TokenStream {
    if total == 1 {
        return leaf_expr;
    }
    if idx == 0 {
        quote! { L(#leaf_expr) }
    } else {
        let rest = sum_injection(idx - 1, total - 1, leaf_expr);
        quote! { R(#rest) }
    }
}

fn is_empty_ty(ty: &TokenStream) -> bool {
    ty.to_string() == "Empty"
}

fn path_tokens(path: &str) -> TokenStream {
    path.parse()
        .unwrap_or_else(|_| panic!("invalid generated path `{path}`"))
}
