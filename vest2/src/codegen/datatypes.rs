use super::common::{int_literal, type_needs_exec_lifetime, Analysis, TypeMode};
use super::writer::{render_ts, CodeWriter};
use crate::codegen::common::{syn_usize, tuple_chain};
use crate::vestir::{
    BitsCombinator, ChoiceCombinator, Combinator, ConstCombinator, EnumCombinator,
    StructCombinator, StructField,
};
use proc_macro2::TokenStream;
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

    pub(crate) fn gen_combinator_value_types(
        &self,
        name: &str,
        combinator: &Combinator,
        scc_members: &[String],
    ) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let doc = Self::type_doc(name);
        if let Some(invocation) = self.direct_alias(combinator) {
            let exec_ty =
                self.render_nominal_type_scc(&invocation.func, TypeMode::Exec, scc_members);
            let spec_ty =
                self.render_nominal_type_scc(&invocation.func, TypeMode::Spec, scc_members);
            return self.emit_exec_spec_aliases(
                &exec_ident,
                &spec_ident,
                exec_ty,
                spec_ty,
                info.needs_lifetime,
                &doc,
            );
        }
        let exec_ty = self.render_value_type_scc(combinator, TypeMode::Exec, scc_members);
        let spec_ty = self.render_value_type_scc(combinator, TypeMode::Spec, scc_members);
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
        scc_members: &[String],
    ) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let doc = Self::type_doc(name);

        let exec_fields: Vec<_> = struct_comb
            .0
            .iter()
            .filter_map(|field| match field {
                StructField::Const { label, combinator } => {
                    if scc_members.is_empty() {
                        let id = format_ident!("{}", label);
                        let ty = self.render_const_value_type(combinator, TypeMode::Exec);
                        Some(quote! { pub #id: #ty })
                    } else {
                        None
                    }
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Exec, scc_members);
                    Some(quote! { pub #id: #ty })
                }
            })
            .collect();

        let spec_fields: Vec<_> = struct_comb
            .0
            .iter()
            .filter_map(|field| match field {
                StructField::Const { label, combinator } => {
                    if scc_members.is_empty() {
                        let id = format_ident!("{}", label);
                        let ty = self.render_const_value_type(combinator, TypeMode::Spec);
                        Some(quote! { pub #id: #ty })
                    } else {
                        None
                    }
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Spec, scc_members);
                    Some(quote! { pub #id: #ty })
                }
            })
            .collect();

        let mut retained = Vec::new();
        for field in &struct_comb.0 {
            match field {
                StructField::Const { combinator, .. } => {
                    retained.push(self.render_const_value_type(combinator, TypeMode::Spec));
                }
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    retained.push(self.render_value_type_scc(
                        combinator,
                        TypeMode::Spec,
                        scc_members,
                    ));
                }
            }
        }
        let inner_ty = tuple_chain(&retained);

        let exec_lifetime = if info.needs_lifetime {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let derives = if !scc_members.is_empty() {
            quote! { #[derive(Debug, PartialEq, Eq)] }
        } else if self.is_copyable(name) {
            quote! { #[derive(Debug, PartialEq, Eq, Clone, Copy)] }
        } else {
            quote! { #[derive(Debug, PartialEq, Eq, Clone)] }
        };
        let self_view = scc_members.is_empty() && self.is_selfview(name);
        let spec_derive = if self_view {
            quote! { #[verifier::ext_equal] }
        } else {
            quote! {}
        };
        let exec_struct = quote! {
            #derives
            #spec_derive
            pub struct #exec_ident #exec_lifetime {
                #(#exec_fields,)*
            }
        };
        let spec_struct = if self_view {
            quote! {
                pub type #spec_ident = #exec_ident;
            }
        } else {
            quote! {
                #[verifier::ext_equal]
                pub struct #spec_ident {
                    #(#spec_fields,)*
                }
            }
        };

        let self_or_x = if !scc_members.is_empty() {
            quote! { x }
        } else {
            quote! { self }
        };
        let deep_view_fields: Vec<_> = struct_comb
            .0
            .iter()
            .filter_map(|field| match field {
                StructField::Const { label, .. } => {
                    if scc_members.is_empty() {
                        let id = format_ident!("{}", label);
                        Some(quote! { #id: #self_or_x.#id.deep_view() })
                    } else {
                        None
                    }
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let expr = if !scc_members.is_empty()
                        && super::common::is_combinator_in_scc(combinator, scc_members)
                    {
                        let vfn = format_ident!(
                            "{}_view",
                            super::common::get_invocation_name(combinator)
                        );
                        quote! { Box::new(#vfn(&*#self_or_x.#id)) }
                    } else {
                        quote! { #self_or_x.#id.deep_view() }
                    };
                    Some(quote! { #id: #expr })
                }
            })
            .collect();

        let deep_view_impl = if self_view {
            quote! {
                impl #exec_lifetime DeepView for #exec_ident #exec_lifetime {
                    type V = Self;
                    open spec fn deep_view(&self) -> Self::V {
                        *self
                    }
                }
            }
        } else if !scc_members.is_empty() {
            let view_fn = format_ident!("{}_view", info.names.dsl);
            quote! {
                pub open spec fn #view_fn(x: &#exec_ident) -> #spec_ident decreases *x, {
                    #spec_ident { #(#deep_view_fields,)* }
                }
                impl<'i> DeepView for #exec_ident<'i> {
                    type V = #spec_ident;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        } else {
            quote! {
                impl #exec_lifetime DeepView for #exec_ident #exec_lifetime {
                    type V = #spec_ident;
                    open spec fn deep_view(&self) -> Self::V {
                        #spec_ident { #(#deep_view_fields,)* }
                    }
                }
            }
        };

        render_ts(quote! {
            #[doc = #doc]
            #exec_struct
            #spec_struct
            pub type #inner_ident = #inner_ty;
            #deep_view_impl
        })
    }

    pub(crate) fn gen_bits_value_types(&self, name: &str, bits_comb: &BitsCombinator) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let doc = Self::type_doc(name);
        let layout = self.bits_layout(bits_comb);
        let exec_fields: Vec<_> = layout
            .fields
            .iter()
            .map(|field| {
                let ident = format_ident!("{}", field.label);
                let ty = if field.is_enum {
                    self.render_nominal_type(field.enum_name.as_ref().unwrap(), TypeMode::Exec)
                } else {
                    self.render_int_type(&field.carrier_ty)
                };
                quote! { pub #ident: #ty }
            })
            .collect();
        let inner_ty = self.render_int_type(&layout.repr_int);
        let derives = quote! { #[derive(Debug, PartialEq, Eq, Clone, Copy)] };
        let spec_derive = quote! { #[verifier::ext_equal] };
        let exec_struct = quote! {
            #derives
            #spec_derive
            pub struct #exec_ident {
                #(#exec_fields,)*
            }
        };
        let spec_type = quote! { pub type #spec_ident = #exec_ident; };
        let deep_view_impl = quote! {
            impl DeepView for #exec_ident {
                type V = Self;
                open spec fn deep_view(&self) -> Self::V {
                    *self
                }
            }
        };
        render_ts(quote! {
            #[doc = #doc]
            #exec_struct
            #spec_type
            pub type #inner_ident = #inner_ty;
            #deep_view_impl
        })
    }

    pub(crate) fn gen_choice_value_types(
        &self,
        name: &str,
        choice_comb: &ChoiceCombinator,
        scc_members: &[String],
    ) -> String {
        let names = &self.info(name).names;
        let exec_ident = format_ident!("{}", names.exec);
        let spec_ident = format_ident!("{}", names.spec);
        let inner_ident = format_ident!("{}", names.inner);
        let variant_names = self.choice_variant_names(choice_comb);
        let branch_exec_types: Vec<_> = choice_comb
            .choices
            .iter()
            .map(|(_, comb)| self.render_value_type_scc(comb, TypeMode::Exec, scc_members))
            .collect();
        let branch_spec_types: Vec<_> = choice_comb
            .choices
            .iter()
            .map(|(_, comb)| self.render_value_type_scc(comb, TypeMode::Spec, scc_members))
            .collect();
        let inner_ty = self.render_choice_sum_type(&branch_spec_types);
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
        let doc = format!("data type for `{}`.", names.dsl);
        let derives = if !scc_members.is_empty() {
            quote! { #[derive(Debug, PartialEq, Eq)] }
        } else if self.is_copyable(name) {
            quote! { #[derive(Debug, PartialEq, Eq, Clone, Copy)] }
        } else {
            quote! { #[derive(Debug, PartialEq, Eq, Clone)] }
        };
        let self_view = scc_members.is_empty() && self.is_selfview(name);
        let spec_derive = if self_view {
            quote! { #[verifier::ext_equal] }
        } else {
            quote! {}
        };
        let exec_enum = quote! {
            #derives
            #spec_derive
            pub enum #exec_ident #exec_lifetime {
                #(#exec_variants,)*
            }
        };
        let spec_enum = if self_view {
            quote! {
                pub type #spec_ident = #exec_ident;
            }
        } else {
            quote! {
                #[verifier::ext_equal]
                pub enum #spec_ident {
                    #(#spec_variants,)*
                }
            }
        };

        let deep_view_arms =
            variant_names
                .iter()
                .zip(&choice_comb.choices)
                .map(|(vn, (_, comb))| {
                    let ident = format_ident!("{}", vn);
                    let expr = if !scc_members.is_empty()
                        && super::common::is_combinator_in_scc(comb, scc_members)
                    {
                        let vfn =
                            format_ident!("{}_view", super::common::get_invocation_name(comb));
                        quote! { Box::new(#vfn(&**v)) }
                    } else {
                        quote! { v.deep_view() }
                    };
                    quote! { #exec_ident::#ident(v) => #spec_ident::#ident(#expr), }
                });

        let deep_view_impl = if self_view {
            quote! {
                impl #exec_generics DeepView for #exec_ident #exec_generics {
                    type V = Self;
                    open spec fn deep_view(&self) -> Self::V {
                        *self
                    }
                }
            }
        } else if !scc_members.is_empty() {
            let view_fn = format_ident!("{}_view", names.dsl);
            quote! {
                pub open spec fn #view_fn(x: &#exec_ident) -> #spec_ident decreases *x, {
                    match x { #(#deep_view_arms)* }
                }
                impl #exec_generics DeepView for #exec_ident #exec_generics {
                    type V = #spec_ident;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        } else {
            quote! {
                impl #exec_generics DeepView for #exec_ident #exec_generics {
                    type V = #spec_ident;
                    open spec fn deep_view(&self) -> Self::V {
                        match self {
                            #(#deep_view_arms)*
                        }
                    }
                }
            }
        };
        render_ts(quote! {
            #[doc = #doc]
            #exec_enum
            #spec_enum
            pub type #inner_ident = #inner_ty;
            #deep_view_impl
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
        let repr_ty = self.render_int_type(inferred);
        let int_spec_ty = self.render_int_type(inferred);
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
                type V = Self;
                open spec fn deep_view(&self) -> Self::V {
                    *self
                }
            }
            impl DeepEq for #exec_ident {
                fn deep_eq(&self, other: &Self) -> bool {
                    *self == *other
                }
            }
            impl SelfView for #exec_ident {
                proof fn self_view(&self) {}
                fn eq(&self, other: &Self) -> bool {
                    *self == *other
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

    pub(crate) fn render_const_value_type(
        &self,
        combinator: &ConstCombinator,
        mode: TypeMode,
    ) -> TokenStream {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(bytes) => match mode {
                TypeMode::Exec => {
                    let n = syn_usize(bytes.len);
                    quote! { [u8; #n] }
                }
                TypeMode::Spec => quote! { Seq<u8> },
            },
            ConstCombinator::ConstInt(int_comb) => self.render_int_type(&int_comb.combinator),
            ConstCombinator::ConstEnum(enum_comb) => {
                self.render_nominal_type(&enum_comb.combinator.func, mode)
            }
            ConstCombinator::ConstCombinatorInvocation(name) => {
                self.render_nominal_type(name, mode)
            }
        }
    }
}
