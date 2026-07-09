use super::common::{
    bits_tuple_expr_from_idents, bits_tuple_expr_tokens, bits_tuple_pattern_tokens,
    bits_tuple_type_tokens, int_literal, nested_tuple_pattern_idents,
    nested_tuple_value_expr_idents, sum_pattern, syn_usize, tuple_index_expr, Analysis,
    FormatNames, TypeMode,
};
use super::writer::{render_ts, CodeWriter};
use crate::vestir::{
    self, BitsCombinator, ChoiceCombinator, ChoicePattern, Combinator, ConstCombinator,
    ConstraintElem, EnumCombinator, Param, ParamDefn, StructCombinator, StructField,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

#[derive(Clone)]
pub(crate) struct RenderedSpec {
    pub(crate) ty: TokenStream,
    pub(crate) expr: TokenStream,
    pub(crate) value_ty: TokenStream,
    pub(crate) has_value: bool,
}

struct RenderedBitsField {
    label_ident: proc_macro2::Ident,
    carrier_ty: TokenStream,
    logical_width: u8,
    carrier_width: u8,
    mask: u64,
    shift: usize,
    mask_ident: proc_macro2::Ident,
    shift_ident: proc_macro2::Ident,
    max_ident: proc_macro2::Ident,
    max_ty: TokenStream,
}

impl RenderedSpec {
    pub(crate) fn new(
        ty: TokenStream,
        expr: TokenStream,
        value_ty: TokenStream,
        has_value: bool,
    ) -> Self {
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

    pub(crate) fn gen_bits_specs_section(
        &self,
        name: &str,
        combinator: &BitsCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        self.gen_wrapped_specs_section(name, param_defns, || {
            self.gen_bits_format_spec_alias_and_ctor(name, combinator, param_defns)
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

    pub(crate) fn gen_enum_bit_helpers_section(
        &self,
        name: &str,
        combinator: &EnumCombinator,
    ) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let inferred = match combinator {
            EnumCombinator::Exhaustive { inferred, .. }
            | EnumCombinator::NonExhaustive { inferred, .. } => inferred,
        };
        let repr_ty = self.render_int_type(inferred);
        let from_bits_ident = format_ident!("{}_from_bits", name);
        let to_bits_ident = format_ident!("{}_to_bits", name);
        let wf_ident = format_ident!("{}_wf", name);

        let variants = match combinator {
            EnumCombinator::Exhaustive { enums, .. }
            | EnumCombinator::NonExhaustive { enums, .. } => enums.as_slice(),
        };
        let variant_idents = variants
            .iter()
            .map(|variant| format_ident!("{}", variant.name))
            .collect::<Vec<_>>();
        let variant_values = variants
            .iter()
            .map(|variant| int_literal(variant.value, inferred))
            .collect::<Vec<_>>();
        let variant_value_exprs = variant_values
            .iter()
            .map(|value| quote! { (#value as #repr_ty) })
            .collect::<Vec<_>>();

        let from_bits_arms = variant_idents
            .iter()
            .zip(variant_values.iter())
            .map(|(ident, value)| quote! { #value => #exec_ident::#ident, })
            .collect::<Vec<_>>();
        let to_bits_arms = variant_idents
            .iter()
            .zip(variant_value_exprs.iter())
            .map(|(ident, value)| quote! { #exec_ident::#ident => #value, })
            .collect::<Vec<_>>();

        match combinator {
            EnumCombinator::Exhaustive { .. } => {
                let fallback_ident = variant_idents
                    .last()
                    .expect("bit-sized enum must have at least one variant");
                render_ts(quote! {
                    #[verifier::allow_in_spec]
                    pub fn #from_bits_ident(bits: #repr_ty) -> #exec_ident
                        returns
                            match bits {
                                #(#variant_values => #exec_ident::#variant_idents,)*
                                _ => #exec_ident::#fallback_ident,
                            },
                    {
                        match bits {
                            #(#from_bits_arms)*
                            _ => #exec_ident::#fallback_ident,
                        }
                    }

                    #[verifier::allow_in_spec]
                    pub fn #to_bits_ident(kind: #exec_ident) -> #repr_ty
                        returns
                            match kind {
                                #(#exec_ident::#variant_idents => #variant_value_exprs,)*
                            },
                    {
                        match kind {
                            #(#to_bits_arms)*
                        }
                    }
                })
            }
            EnumCombinator::NonExhaustive { .. } => {
                let wf_terms = variant_values
                    .iter()
                    .map(|value| quote! { x != #value })
                    .collect::<Vec<_>>();
                let wf_body = if wf_terms.is_empty() {
                    quote! { true }
                } else {
                    quote! { #(#wf_terms)&&* }
                };
                render_ts(quote! {
                    #[verifier::allow_in_spec]
                    pub fn #wf_ident(kind: #exec_ident) -> bool
                        returns
                            match kind {
                                #(#exec_ident::#variant_idents => true,)*
                                #exec_ident::Unknown(x) => #wf_body,
                            },
                    {
                        match kind {
                            #(#exec_ident::#variant_idents => true,)*
                            #exec_ident::Unknown(x) => #wf_body,
                        }
                    }

                    #[verifier::allow_in_spec]
                    pub fn #from_bits_ident(bits: #repr_ty) -> #exec_ident
                        returns
                            match bits {
                                #(#variant_values => #exec_ident::#variant_idents,)*
                                _ => #exec_ident::Unknown(bits),
                            },
                    {
                        match bits {
                            #(#from_bits_arms)*
                            _ => #exec_ident::Unknown(bits),
                        }
                    }

                    #[verifier::allow_in_spec]
                    pub fn #to_bits_ident(kind: #exec_ident) -> #repr_ty
                        returns
                            match kind {
                                #(#exec_ident::#variant_idents => #variant_value_exprs,)*
                                #exec_ident::Unknown(x) => x,
                            },
                    {
                        match kind {
                            #(#to_bits_arms)*
                            #exec_ident::Unknown(x) => x,
                        }
                    }
                })
            }
        }
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
        let top_value_ty = self.render_nominal_type(name, TypeMode::Spec);
        let wrapper_generics = self.wrapper_generics(param_defns);
        let wrapper_call_args = self.wrapper_spec_call_args(param_defns);

        self.gen_derived_spec_impls(
            &fmt_ident,
            &wrapper_generics,
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

    fn gen_bits_format_spec_alias_and_ctor(
        &self,
        name: &str,
        combinator: &BitsCombinator,
        param_defns: &[ParamDefn],
    ) -> String {
        let mut out = CodeWriter::new();
        out.push_multiline(self.gen_bits_helpers(name, combinator));
        out.blank_line();
        out.push_multiline(self.gen_named_top_level_spec_alias_and_ctor(
            name,
            self.render_bits_top_level(name, combinator),
            param_defns,
        ));
        out.finish()
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

    pub(crate) fn gen_derived_spec_impls(
        &self,
        fmt_ident: &proc_macro2::Ident,
        impl_generics: &TokenStream,
        type_generics: &TokenStream,
        wrapper_call_args: &[TokenStream],
        top_value_ty: &TokenStream,
    ) -> String {
        let opaque = if impl_generics.is_empty() {
            quote! { #[verifier::opaque] }
        } else {
            quote! {}
        };

        render_ts(quote! {
            impl #impl_generics SpecParser for #fmt_ident #type_generics {
                type PVal = #top_value_ty;

                #opaque
                open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                    Self::spec_inner(#(#wrapper_call_args),*).spec_parse(ibuf)
                }
            }

            impl #impl_generics Consistency for #fmt_ident #type_generics {
                type Val = #top_value_ty;

                open spec fn consistent(&self, v: Self::Val) -> bool {
                    Self::spec_inner(#(#wrapper_call_args),*).consistent(v)
                }
            }

            impl #impl_generics SpecSerializerDps for #fmt_ident #type_generics {
                type SValue = #top_value_ty;

                #opaque
                open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                    Self::spec_inner(#(#wrapper_call_args),*).spec_serialize_dps(v, obuf)
                }
            }

            impl #impl_generics SpecSerializer for #fmt_ident #type_generics {
                type SVal = #top_value_ty;

                #opaque
                open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
                    Self::spec_inner(#(#wrapper_call_args),*).spec_serialize(v)
                }
            }

            impl #impl_generics SpecByteLen for #fmt_ident #type_generics {
                type T = #top_value_ty;

                #opaque
                open spec fn byte_len(&self, v: Self::T) -> nat {
                    Self::spec_inner(#(#wrapper_call_args),*).byte_len(v)
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
                let len_ty = self.render_int_type(&bytes.len.ty);
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

    pub(crate) fn render_spec_combinator(&self, combinator: &Combinator) -> RenderedSpec {
        match combinator {
            Combinator::AndThen(lhs, rhs) => return self.render_and_then_spec(lhs, rhs),
            Combinator::Invocation(invocation) => return self.render_invocation_spec(invocation),
            _ => {}
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(c) => {
                let prim_ty = self.render_int_combinator_ty(&c.combinator);
                let prim_expr = self.render_int_combinator_expr(&c.combinator);
                let value_ty = self.render_int_type(&c.combinator);
                let (ty, expr) = match &c.constraint {
                    None => (prim_ty, prim_expr),
                    Some(constraint) => {
                        let pred =
                            self.render_int_constraint(constraint, &c.combinator, quote! { x });
                        let ty = quote! { Refined<#prim_ty, PredFnSpec<#value_ty>> };
                        let expr = quote! { Refined(#prim_expr, |x: #value_ty| #pred) };
                        (ty, expr)
                    }
                };
                RenderedSpec::new(ty, expr, value_ty, true)
            }
            Combinator::ConstraintEnum(c) => {
                let inner =
                    self.render_spec_combinator(&Combinator::Invocation(c.combinator.clone()));
                let value_ty = inner.value_ty.clone();
                let pred = self.render_enum_constraint(&c.constraint, &value_ty, quote! { x });
                let inner_ty = &inner.ty;
                let inner_expr = &inner.expr;
                let ty = quote! { Refined<#inner_ty, PredFnSpec<#value_ty>> };
                let expr = quote! { Refined(#inner_expr, |x: #value_ty| #pred) };
                RenderedSpec::new(ty, expr, value_ty, true)
            }
            Combinator::Wrap(wrap) => {
                let mut body = self.render_spec_combinator(&wrap.combinator);
                for const_comb in wrap.post.iter() {
                    let c = self.render_tag_spec(const_comb);
                    let body_ty = &body.ty;
                    let body_expr = &body.expr;
                    let c_ty = &c.ty;
                    let c_expr = &c.expr;
                    let c_value_expr = &c.value_expr;
                    let c_value_ty = &c.value_ty;
                    let ty = quote! { SuffixTagged<#body_ty, #c_ty, #c_value_ty> };
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
                    let c_value_ty = &c.value_ty;
                    let ty = quote! { PrefixTagged<#c_ty, #c_value_ty, #body_ty> };
                    let expr = quote! { PrefixTagged(#c_expr, #c_value_expr, #body_expr) };
                    body = RenderedSpec::new(ty, expr, body.value_ty, body.has_value);
                }
                body
            }
            Combinator::Vec(vec_comb) => match vec_comb {
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
            },
            Combinator::Array(array_comb) => {
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
                        let len_ty = self.render_int_type(&array_comb.len.ty);
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
            Combinator::Bytes(bytes) => {
                let value_ty = quote! { Seq<u8> };
                match self.eval_const_length_expr(&bytes.len) {
                    Some(n) => {
                        let n = syn_usize(n);
                        RenderedSpec::new(
                            quote! { Fixed<#n> },
                            quote! { Fixed::<#n> },
                            value_ty,
                            true,
                        )
                    }
                    None => {
                        let len_ty = self.render_int_type(&bytes.len.ty);
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
            Combinator::Tail(_) => {
                RenderedSpec::new(quote! { Tail }, quote! { Tail }, quote! { Seq<u8> }, true)
            }
            Combinator::Empty => {
                RenderedSpec::new(quote! { Empty }, quote! { Empty }, quote! { () }, true)
            }
            Combinator::Void(s) => {
                RenderedSpec::new(quote! { Void }, quote! { Void(#s) }, quote! { Never }, true)
            }
            Combinator::Option(opt) => {
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
            Combinator::Invocation(_) | Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn render_struct_fields(&self, fields: &[StructField]) -> RenderedSpec {
        self.render_struct_fields_with(fields, &|combinator| {
            self.render_spec_combinator(combinator)
        })
    }

    pub(crate) fn render_struct_fields_with(
        &self,
        fields: &[StructField],
        render_comb: &dyn Fn(&Combinator) -> RenderedSpec,
    ) -> RenderedSpec {
        if fields.is_empty() {
            return RenderedSpec::new(quote! { Empty }, quote! { Empty }, quote! { () }, false);
        }
        let first = &fields[0];
        let rest = self.render_struct_fields_with(&fields[1..], render_comb);
        match first {
            StructField::Const { combinator, .. } => {
                let c = self.render_const_spec(combinator);
                self.render_sequence_with_rest(
                    RenderedSpec::new(c.ty, c.expr, c.value_ty, true),
                    &rest,
                )
            }
            StructField::Ordinary { combinator, .. } => {
                if let Some(rendered) =
                    self.render_optional_or_repeat_with_rest_with(combinator, &rest, render_comb)
                {
                    return rendered;
                }
                self.render_sequence_with_rest(render_comb(combinator), &rest)
            }
            StructField::Dependent { label, combinator } => {
                if let Some(rendered) =
                    self.render_optional_or_repeat_with_rest_with(combinator, &rest, render_comb)
                {
                    return rendered;
                }
                let cur = render_comb(combinator);
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

    fn render_optional_or_repeat_with_rest_with(
        &self,
        combinator: &Combinator,
        rest: &RenderedSpec,
        render_comb: &dyn Fn(&Combinator) -> RenderedSpec,
    ) -> Option<RenderedSpec> {
        if matches!(combinator, Combinator::AndThen(_, _)) {
            return None;
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::Option(opt) => {
                let inner = render_comb(&opt.0);
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
                    let inner = render_comb(inner_comb);
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

    pub(crate) fn render_choice_branches_with(
        &self,
        choices: &[(ChoicePattern, Combinator)],
        render_comb: &dyn Fn(&Combinator) -> RenderedSpec,
    ) -> RenderedSpec {
        let branches = choices
            .iter()
            .map(|(_, combinator)| render_comb(combinator))
            .collect::<Vec<_>>();
        fold_choice(branches)
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
                let prim_ty = self.render_int_combinator_ty(&int_comb.combinator);
                let prim_expr = self.render_int_combinator_expr(&int_comb.combinator);
                let value_ty = self.render_int_type(&int_comb.combinator);
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
                let value_ty = self.render_nominal_type(name, TypeMode::Spec);
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
        let struct_fields_expr = struct_init_fields_expr(&labels);
        let label_idents = labels
            .iter()
            .map(|label| format_ident!("{}", label))
            .collect::<Vec<_>>();
        let tuple_pat = nested_tuple_pattern_idents(&label_idents);
        let reverse_tuple_expr = nested_tuple_value_expr_idents(&label_idents);
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

    fn gen_bits_helpers(&self, name: &str, bits_comb: &BitsCombinator) -> String {
        let layout = self.bits_layout(bits_comb);
        let repr_int = layout.repr_int;
        let repr_ty = self.render_int_type(&repr_int);
        let format_upper = shouty_snake_case(name);

        let mut fields_info = Vec::new();
        for field in &layout.fields {
            let label = field.label.clone();
            let label_ident = format_ident!("{}", label);
            let field_upper = shouty_snake_case(&label);
            let carrier_ty = self.render_int_type(&field.carrier_ty);
            let logical_width = field.logical_width;
            let carrier_width = field.carrier_ty.carrier_width();
            let mask = field.mask;
            let shift = field.shift as usize;

            let mask_ident = format_ident!("{}_{}_MASK", format_upper, field_upper);
            let shift_ident = format_ident!("{}_{}_SHIFT", format_upper, field_upper);
            let max_ident = format_ident!("{}_{}_MAX", format_upper, field_upper);

            let max_ty = if logical_width == 8
                || logical_width == 16
                || logical_width == 32
                || logical_width == 64
            {
                let next_width = match logical_width {
                    8 => 16,
                    16 => 32,
                    32 => 64,
                    _ => 64,
                };
                let next_int_ty = vestir::IntCombinator::Unsigned(next_width);
                self.render_int_type(&next_int_ty)
            } else {
                carrier_ty.clone()
            };

            fields_info.push(RenderedBitsField {
                label_ident,
                carrier_ty,
                logical_width,
                carrier_width,
                mask,
                shift,
                mask_ident,
                shift_ident,
                max_ident,
                max_ty,
            });
        }

        let consts_block = self.gen_bits_constants(&repr_int, &repr_ty, &fields_info);
        let unpack_fn = self.gen_bits_unpack(name, &repr_ty, &fields_info);
        let pack_fn = self.gen_bits_pack(name, &repr_int, &repr_ty, &fields_info);
        let bounds_fn = self.gen_bits_bounds(name, &fields_info);
        let lemmas = self.gen_bits_bv_lemmas(name, &repr_ty, &fields_info);

        render_ts(quote! {
            #consts_block
            #unpack_fn
            #pack_fn
            #bounds_fn
            #lemmas
        })
    }

    fn gen_bits_constants(
        &self,
        repr_int: &vestir::IntCombinator,
        repr_ty: &TokenStream,
        fields: &[RenderedBitsField],
    ) -> TokenStream {
        let consts = fields.iter().map(|f| {
            let mask_ident = &f.mask_ident;
            let shift_ident = &f.shift_ident;
            let shift_lit = syn_usize(f.shift);
            let mask_lit = bit_mask_literal(f.mask, repr_int);
            if f.logical_width < f.carrier_width {
                let max_ident = &f.max_ident;
                let carrier_ty = &f.max_ty;
                let max_val = 1u64 << f.logical_width;
                let max_int_ty = vestir::IntCombinator::Unsigned(f.carrier_width);
                let max_lit = bit_mask_literal(max_val, &max_int_ty);
                quote! {
                    pub const #mask_ident: #repr_ty = #mask_lit;
                    pub const #shift_ident: #repr_ty = #shift_lit;
                    pub const #max_ident: #carrier_ty = #max_lit;
                }
            } else {
                quote! {
                    pub const #mask_ident: #repr_ty = #mask_lit;
                    pub const #shift_ident: #repr_ty = #shift_lit;
                }
            }
        });
        quote! {
            #(#consts)*
        }
    }

    fn gen_bits_unpack(
        &self,
        name: &str,
        repr_ty: &TokenStream,
        fields: &[RenderedBitsField],
    ) -> TokenStream {
        let unpack_ident = format_ident!("unpack_{}", name);
        let tys = fields
            .iter()
            .map(|f| f.carrier_ty.clone())
            .collect::<Vec<_>>();
        let tuple_ty = bits_tuple_type_tokens(&tys);
        let unpack_elems = fields
            .iter()
            .map(|f| {
                let mask_ident = &f.mask_ident;
                let shift_ident = &f.shift_ident;
                let field_ty = &f.carrier_ty;
                if f.shift == 0 {
                    quote! { ((raw & #mask_ident) as #field_ty) }
                } else {
                    quote! { (((raw >> #shift_ident) & #mask_ident) as #field_ty) }
                }
            })
            .collect::<Vec<_>>();
        let unpack_tuple = bits_tuple_expr_tokens(&unpack_elems);
        quote! {
            #[verifier::allow_in_spec]
            pub fn #unpack_ident(raw: #repr_ty) -> #tuple_ty
                returns
                    #unpack_tuple,
            {
                #unpack_tuple
            }
        }
    }

    fn gen_bits_pack(
        &self,
        name: &str,
        repr_int: &vestir::IntCombinator,
        repr_ty: &TokenStream,
        fields: &[RenderedBitsField],
    ) -> TokenStream {
        let pack_ident = format_ident!("pack_{}", name);
        let pack_params = fields
            .iter()
            .map(|f| {
                let ident = &f.label_ident;
                let field_ty = &f.carrier_ty;
                quote! { #ident: #field_ty }
            })
            .collect::<Vec<_>>();
        let pack_terms = fields
            .iter()
            .map(|f| {
                let ident = &f.label_ident;
                let mask_ident = &f.mask_ident;
                let shift_ident = &f.shift_ident;
                if f.shift == 0 {
                    quote! { (((#ident as #repr_ty) & #mask_ident)) }
                } else {
                    quote! { (((#ident as #repr_ty) & #mask_ident) << #shift_ident) }
                }
            })
            .collect::<Vec<_>>();
        let pack_expr = pack_terms
            .into_iter()
            .reduce(|acc, term| quote! { #acc | #term })
            .unwrap_or_else(|| {
                let zero_lit = bit_mask_literal(0, repr_int);
                quote! { #zero_lit }
            });
        quote! {
            #[verifier::allow_in_spec]
            pub fn #pack_ident(#(#pack_params),*) -> #repr_ty
                returns
                    #pack_expr,
            {
                #pack_expr
            }
        }
    }

    fn gen_bits_bounds(&self, name: &str, fields: &[RenderedBitsField]) -> TokenStream {
        let bounds_ident = format_ident!("{}_bounds", name);
        let pack_params = fields
            .iter()
            .map(|f| {
                let ident = &f.label_ident;
                let field_ty = &f.carrier_ty;
                quote! { #ident: #field_ty }
            })
            .collect::<Vec<_>>();
        let bounds_terms = fields
            .iter()
            .filter(|f| f.logical_width < f.carrier_width)
            .map(|f| {
                let ident = &f.label_ident;
                let max_ident = &f.max_ident;
                quote! { (#ident < #max_ident) }
            })
            .collect::<Vec<_>>();
        let bounds_expr = if bounds_terms.is_empty() {
            quote! { true }
        } else {
            quote! { #(#bounds_terms)&&* }
        };
        quote! {
            #[verifier::allow_in_spec]
            pub fn #bounds_ident(#(#pack_params),*) -> bool
                returns
                    #bounds_expr,
            {
                #bounds_expr
            }
        }
    }

    fn gen_bits_bv_lemmas(
        &self,
        name: &str,
        repr_ty: &TokenStream,
        fields: &[RenderedBitsField],
    ) -> TokenStream {
        let unpack_ident = format_ident!("unpack_{}", name);
        let pack_ident = format_ident!("pack_{}", name);
        let bounds_ident = format_ident!("{}_bounds", name);
        let unpack_proof_ident = format_ident!("lemma_{}_unpack_pack", name);
        let pack_proof_ident = format_ident!("lemma_{}_pack_unpack", name);
        let wf_proof_ident = format_ident!("lemma_{}_mapper_wf_in_out", name);

        let label_idents = fields.iter().map(|f| &f.label_ident).collect::<Vec<_>>();
        let pack_params = fields
            .iter()
            .map(|f| {
                let ident = &f.label_ident;
                let field_ty = &f.carrier_ty;
                quote! { #ident: #field_ty }
            })
            .collect::<Vec<_>>();

        let unpack_components = (0..fields.len())
            .map(|idx| {
                let tuple = quote! { #unpack_ident(raw) };
                tuple_index_expr(tuple, idx)
            })
            .collect::<Vec<_>>();
        let unpack_i_components = (0..fields.len())
            .map(|idx| {
                let tuple = quote! { #unpack_ident(i) };
                tuple_index_expr(tuple, idx)
            })
            .collect::<Vec<_>>();
        let pack_unpack_ensures = label_idents
            .iter()
            .enumerate()
            .map(|(idx, ident)| {
                let unpacked_idx = tuple_index_expr(
                    quote! { #unpack_ident(#pack_ident(#(#label_idents),*)) },
                    idx,
                );
                quote! { #unpacked_idx == #ident }
            })
            .collect::<Vec<_>>();

        quote! {
            pub broadcast proof fn #unpack_proof_ident(raw: #repr_ty)
                by (bit_vector)
                ensures
                    #[trigger] #pack_ident(#(#unpack_components),*) == raw,
            {
            }

            pub broadcast proof fn #pack_proof_ident(#(#pack_params),*)
                by (bit_vector)
                requires
                    #[trigger] #bounds_ident(#(#label_idents),*),
                ensures
                    #(#pack_unpack_ensures,)*
            {
            }

            pub broadcast proof fn #wf_proof_ident(i: #repr_ty)
                by (bit_vector)
                ensures
                    #[trigger] #bounds_ident(#(#unpack_i_components),*),
            {
            }
        }
    }

    fn render_bits_top_level(&self, name: &str, bits_comb: &BitsCombinator) -> RenderedSpec {
        let info = self.info(name);
        let spec_ident = format_ident!("{}", info.names.spec);
        let layout = self.bits_layout(bits_comb);
        let repr_int = &layout.repr_int;
        let repr_fmt_ty = self.render_int_combinator_ty(repr_int);
        let repr_fmt_expr = self.render_int_combinator_expr(repr_int);
        let repr_value_ty = self.render_int_type(repr_int);

        let tys = layout
            .fields
            .iter()
            .map(|f| self.render_int_type(&f.carrier_ty))
            .collect::<Vec<_>>();
        let tuple_ty = bits_tuple_type_tokens(&tys);

        let unpack_ident = format_ident!("unpack_{}", name);
        let pack_ident = format_ident!("pack_{}", name);
        let bounds_ident = format_ident!("{}_bounds", name);

        let label_idents = layout.field_idents();
        let tuple_pat = bits_tuple_pattern_tokens(&label_idents);
        let tuple_expr = bits_tuple_expr_from_idents(&label_idents);

        let ctor_fields = self
            .bits_ctor_fields(&layout)
            .iter()
            .map(|(field_ident, expr)| quote! { #field_ident: #expr })
            .collect::<Vec<_>>();

        let dtor_lets = layout
            .fields
            .iter()
            .filter_map(|field| {
                let field_ident = format_ident!("{}", field.label);
                if field.is_enum {
                    let raw_expr = self.bits_raw_field_expr(field, quote! { #field_ident });
                    Some(quote! { let #field_ident = #raw_expr; })
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        let bounds_args = self.bits_raw_field_exprs(&layout);

        let refinement_terms = bits_comb
            .0
            .iter()
            .zip(&layout.fields)
            .filter_map(|(field, field_layout)| {
                let ident = format_ident!("{}", field_layout.label);
                self.bits_field_refinement_pred(field, field_layout, quote! { #ident })
            })
            .collect::<Vec<_>>();
        let refinement_expr = if refinement_terms.is_empty() {
            quote! { true }
        } else {
            fold_bool_and(refinement_terms)
        };

        let consistency_terms = layout
            .fields
            .iter()
            .filter_map(|field_layout| {
                let field_ident = format_ident!("{}", field_layout.label);
                self.bits_open_enum_wf_pred(field_layout, quote! { #field_ident })
            })
            .collect::<Vec<_>>();

        let consistency_body = {
            let mut terms = consistency_terms.clone();
            terms.push(quote! { #bounds_ident(#(#bounds_args),*) });
            fold_bool_and(terms)
        };

        let ty = quote! { Bits<#repr_fmt_ty, #tuple_ty, #spec_ident> };
        let expr = quote! {
            Bits {
                repr: #repr_fmt_expr,
                unpack: |packed: #repr_value_ty| #unpack_ident(packed),
                pack: |unpacked: #tuple_ty| {
                    let #tuple_pat = unpacked;
                    #pack_ident(#(#label_idents),*)
                },
                refinement: |unpacked: #tuple_ty| {
                    let #tuple_pat = unpacked;
                    #refinement_expr
                },
                ctor: |unpacked: #tuple_ty| {
                    let #tuple_pat = unpacked;
                    #spec_ident { #(#ctor_fields),* }
                },
                dtor: |value: #spec_ident| {
                    let #spec_ident { #(#label_idents),* } = value;
                    #(#dtor_lets)*
                    #tuple_expr
                },
                consistent: |value: #spec_ident| {
                    let #spec_ident { #(#label_idents),* } = value;
                    #consistency_body
                },
            }
        };
        RenderedSpec::new(ty, expr, quote! { #spec_ident }, true)
    }

    fn render_choice_top_level(&self, name: &str, choice_comb: &ChoiceCombinator) -> RenderedSpec {
        let info = self.info(name);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        // let raw = self.render_choice_raw(choice_comb, Some(name));
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

    pub(crate) fn render_dependent_choice_with(
        &self,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
        dep_expr: TokenStream,
        render_comb: &dyn Fn(&Combinator) -> RenderedSpec,
    ) -> RenderedSpec {
        let (branch_specs, match_arms): (Vec<_>, Vec<_>) = choice_comb
            .choices
            .iter()
            .enumerate()
            .map(|(idx, (pat, combinator))| {
                let fmt = render_comb(combinator);
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
        let ty = self.render_choice_sum_type(&branch_tys);
        let value_ty = self.render_choice_sum_type(&branch_value_tys);

        let expr = quote! {
            match #dep_expr {
                #(#match_arms)*
            }
        };

        RenderedSpec::new(ty, expr, value_ty, true)
    }

    fn render_dependent_choice_raw(
        &self,
        choice_comb: &ChoiceCombinator,
        owner_name: Option<&str>,
    ) -> RenderedSpec {
        let dep_id = choice_comb
            .depend_id
            .as_ref()
            .expect("dependent choose should have a selector");
        let dep_expr = path_tokens(dep_id);
        self.render_dependent_choice_with(choice_comb, owner_name, dep_expr, &|combinator| {
            self.render_spec_combinator(combinator)
        })
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
        let prim_ty = self.render_int_combinator_ty(inferred);
        let prim_expr = self.render_int_combinator_expr(inferred);
        let int_spec_ty = self.render_int_type(inferred);
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
                let prim_ty = self.render_int_combinator_ty(&int_comb.combinator);
                let prim_expr = self.render_int_combinator_expr(&int_comb.combinator);
                let value_ty = self.render_int_type(&int_comb.combinator);
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
                let value_ty = self.render_nominal_type(name, TypeMode::Spec);
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
        let param_defns = owner_name
            .map(|name| self.param_defns_for(name))
            .unwrap_or(&[]);
        let resolved = self
            .resolve_dep_combinator_path(dep, param_defns)
            .unwrap_or_else(|| panic!("could not resolve enum pattern type for `{variant_name}`"));
        match resolved {
            Combinator::Invocation(inv) => self.render_nominal_type(&inv.func, TypeMode::Spec),
            _ => panic!("enum pattern `{variant_name}` does not resolve to an enum invocation"),
        }
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
                            &self.render_nominal_type(&c.combinator.func, TypeMode::Spec),
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
        .fold(first, |acc, term| quote! { (#acc) || (#term) })
}

fn fold_bool_and(mut terms: Vec<TokenStream>) -> TokenStream {
    let first = terms
        .drain(..1)
        .next()
        .expect("boolean conjunction requires at least one term");
    terms
        .into_iter()
        .fold(first, |acc, term| quote! { (#acc) && (#term) })
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

fn shouty_snake_case(s: &str) -> String {
    let mut shouty = String::new();
    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            shouty.push(c.to_ascii_uppercase());
        } else {
            shouty.push('_');
        }
    }
    shouty
}

fn bit_mask_literal(mask: u64, int_ty: &vestir::IntCombinator) -> TokenStream {
    let width = match int_ty {
        vestir::IntCombinator::Signed(bits) | vestir::IntCombinator::Unsigned(bits) => match bits {
            1..=8 => 8,
            9..=16 => 16,
            17..=32 => 32,
            33..=64 => 64,
            _ => 64,
        },
        _ => 64,
    };
    let binary_str = match width {
        8 => format!("0b{:08b}", mask),
        16 => format!("0b{:016b}", mask),
        32 => format!("0b{:032b}", mask),
        64 => format!("0b{:064b}", mask),
        _ => format!("0b{:b}", mask),
    };
    let suffix = format!("u{width}");
    let lit_str = format!("{binary_str}{suffix}");
    lit_str.parse().unwrap()
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
