use super::common::{
    int_literal, render_ts, type_needs_exec_lifetime, Analysis, CodeWriter, TypeMode,
};
use crate::vestir::{
    ChoiceCombinator, Combinator, ConstCombinator, EnumCombinator, StructCombinator, StructField,
};
use quote::{format_ident, quote};

impl<'a> Analysis<'a> {
    fn type_doc(name: &str) -> String {
        format!("data type for `{}`.", name)
    }

    fn emit_exec_spec_aliases(
        &self,
        exec_ident: &proc_macro2::Ident,
        spec_ident: &proc_macro2::Ident,
        exec_ty: proc_macro2::TokenStream,
        spec_ty: proc_macro2::TokenStream,
        needs_lifetime: bool,
        doc: &str,
    ) -> String {
        let exec_alias = if needs_lifetime {
            quote! { pub type #exec_ident <'i> = #exec_ty; }
        } else {
            quote! { pub type #exec_ident = #exec_ty; }
        };
        let mut out = CodeWriter::new();
        out.push_multiline(render_ts(quote! { #[doc = #doc] }));
        out.push_multiline(render_ts(exec_alias));
        out.push_multiline(render_ts(quote! { pub type #spec_ident = #spec_ty; }));
        out.finish()
    }

    pub(crate) fn gen_combinator_value_types(&self, name: &str, combinator: &Combinator) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let doc = Self::type_doc(name);
        if let Some(invocation) = self.direct_alias(combinator) {
            let exec_ty = self.invocation_value_type(invocation, TypeMode::Exec);
            let spec_ty = self.invocation_value_type(invocation, TypeMode::Spec);
            return self.emit_exec_spec_aliases(
                &exec_ident,
                &spec_ident,
                exec_ty,
                spec_ty,
                info.needs_lifetime,
                &doc,
            );
        }
        let exec_ty = self.render_value_type(combinator, TypeMode::Exec, true);
        let spec_ty = self.render_value_type(combinator, TypeMode::Spec, true);
        self.emit_exec_spec_aliases(
            &exec_ident,
            &spec_ident,
            exec_ty,
            spec_ty,
            info.needs_lifetime,
            &doc,
        )
    }

    pub(crate) fn gen_struct_value_types(
        &self,
        name: &str,
        struct_comb: &StructCombinator,
    ) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let doc = Self::type_doc(name);
        let exec_fields = self.struct_value_fields(struct_comb, TypeMode::Exec);
        let spec_fields = self.struct_value_fields(struct_comb, TypeMode::Spec);
        let inner_ty = self.render_struct_inner_type(struct_comb, TypeMode::Spec);
        let exec_lifetime = if info.needs_lifetime {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let exec_struct = quote! {
            #[derive(Debug, PartialEq, Eq)]
            pub struct #exec_ident #exec_lifetime {
                #(#exec_fields,)*
            }
        };
        let spec_struct = quote! {
            #[verifier::ext_equal]
            pub struct #spec_ident {
                #(#spec_fields,)*
            }
        };
        let deep_view_fields = self.struct_deep_view_fields(struct_comb);
        render_ts(quote! {
            #[doc = #doc]
            #exec_struct
            #spec_struct
            pub type #inner_ident = #inner_ty;
            impl #exec_lifetime DeepView for #exec_ident #exec_lifetime {
                type V = #spec_ident;
                open spec fn deep_view(&self) -> Self::V {
                    #spec_ident { #(#deep_view_fields,)* }
                }
            }
        })
    }

    pub(crate) fn gen_choice_value_types(
        &self,
        name: &str,
        choice_comb: &ChoiceCombinator,
    ) -> String {
        let names = &self.info(name).names;
        let exec_ident = format_ident!("{}", names.exec);
        let spec_ident = format_ident!("{}", names.spec);
        let inner_ident = format_ident!("{}", names.inner);
        let variant_names = self.choice_variant_names(choice_comb);
        let branch_exec_types = self.choice_branch_types(choice_comb, TypeMode::Exec);
        let branch_spec_types = self.choice_branch_types(choice_comb, TypeMode::Spec);
        let inner_ty = self.choice_sum_type(&branch_spec_types);
        let exec_lifetime = if branch_exec_types.iter().any(type_needs_exec_lifetime) {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let exec_generics = exec_lifetime.clone();
        let exec_variants = variant_names
            .iter()
            .zip(branch_exec_types.iter())
            .map(|(name, ty)| {
                let ident = format_ident!("{}", name);
                quote! { #ident(#ty) }
            });
        let spec_variants = variant_names
            .iter()
            .zip(branch_spec_types.iter())
            .map(|(name, ty)| {
                let ident = format_ident!("{}", name);
                quote! { #ident(#ty) }
            });
        let deep_view_arms = variant_names.iter().map(|name| {
            let ident = format_ident!("{}", name);
            quote! { #exec_ident::#ident(v) => #spec_ident::#ident(v.deep_view()), }
        });
        let doc = format!("data type for `{}`.", names.dsl);
        render_ts(quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq)]
            pub enum #exec_ident #exec_lifetime {
                #(#exec_variants,)*
            }
            #[verifier::ext_equal]
            pub enum #spec_ident {
                #(#spec_variants,)*
            }
            pub type #inner_ident = #inner_ty;
            impl #exec_generics DeepView for #exec_ident #exec_generics {
                type V = #spec_ident;
                open spec fn deep_view(&self) -> Self::V {
                    match self {
                        #(#deep_view_arms)*
                    }
                }
            }
        })
    }

    pub(crate) fn gen_enum_value_types(&self, name: &str, enum_comb: &EnumCombinator) -> String {
        let names = &self.info(name).names;
        let exec_ident = format_ident!("{}", names.exec);
        let spec_ident = format_ident!("{}", names.spec);
        let inner_ident = format_ident!("{}", names.inner);
        let (variants, exhaustive, inferred) = match enum_comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums, true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => (enums, false, inferred),
        };
        let repr_ty = self.int_exec_type(inferred);
        let int_spec_ty = self.int_spec_type(inferred);
        let inner_ty = if exhaustive {
            int_spec_ty.clone()
        } else {
            quote! { Sum<#int_spec_ty, #int_spec_ty> }
        };
        let exec_variants = variants.iter().map(|variant| {
            let ident = format_ident!("{}", variant.name);
            let value = int_literal(variant.value, inferred);
            quote! { #ident = #value }
        });
        let extra_exec = if exhaustive {
            quote! {}
        } else {
            quote! { Unknown(#repr_ty), }
        };
        let deep_view_match = if exhaustive {
            variants
                .iter()
                .map(|variant| {
                    let ident = format_ident!("{}", variant.name);
                    quote! { #exec_ident::#ident => #spec_ident::#ident, }
                })
                .collect::<Vec<_>>()
        } else {
            let mut arms = variants
                .iter()
                .map(|variant| {
                    let ident = format_ident!("{}", variant.name);
                    quote! { #exec_ident::#ident => #spec_ident::#ident, }
                })
                .collect::<Vec<_>>();
            arms.push(quote! { #exec_ident::Unknown(v) => #spec_ident::Unknown(v), });
            arms
        };
        let doc = format!("data type for `{}`.", names.dsl);
        render_ts(quote! {
            #[doc = #doc]
            #[repr(#repr_ty)]
            #[derive(Debug, PartialEq, Eq, Clone, Copy, Structural)]
            pub enum #exec_ident {
                #(#exec_variants,)*
                #extra_exec
            }
            pub type #spec_ident = #exec_ident;
            pub type #inner_ident = #inner_ty;
            impl DeepView for #exec_ident {
                type V = #spec_ident;
                open spec fn deep_view(&self) -> Self::V {
                    match *self {
                        #(#deep_view_match)*
                    }
                }
            }
        })
    }

    pub(crate) fn gen_const_value_aliases(
        &self,
        name: &str,
        const_combinator: &ConstCombinator,
    ) -> String {
        let info = self.info(name);
        let ty = self.render_const_value_type(const_combinator, TypeMode::Exec);
        let spec_ty = self.render_const_value_type(const_combinator, TypeMode::Spec);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let doc = Self::type_doc(name);
        self.emit_exec_spec_aliases(
            &exec_ident,
            &spec_ident,
            ty,
            spec_ty,
            info.needs_lifetime,
            &doc,
        )
    }

    fn struct_value_fields(
        &self,
        struct_comb: &StructCombinator,
        mode: TypeMode,
    ) -> Vec<proc_macro2::TokenStream> {
        struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { label, combinator } => {
                    let ident = format_ident!("{}", label);
                    let ty = self.render_const_value_type(combinator, mode);
                    quote! { pub #ident: #ty }
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let ident = format_ident!("{}", label);
                    let ty = self.render_value_type(combinator, mode, true);
                    quote! { pub #ident: #ty }
                }
            })
            .collect()
    }

    fn struct_deep_view_fields(
        &self,
        struct_comb: &StructCombinator,
    ) -> Vec<proc_macro2::TokenStream> {
        struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { label, .. }
                | StructField::Dependent { label, .. }
                | StructField::Ordinary { label, .. } => {
                    let ident = format_ident!("{}", label);
                    quote! { #ident: self.#ident.deep_view() }
                }
            })
            .collect()
    }
}
