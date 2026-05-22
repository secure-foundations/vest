use super::common::{int_literal, type_needs_exec_lifetime, Analysis, FormatNames, TypeMode};
use crate::vestir::{
    ChoiceCombinator, Combinator, CombinatorInner, ConstCombinator, EnumCombinator, ParamDefn,
};
use quote::{format_ident, quote};

impl<'a> Analysis<'a> {
    pub(crate) fn gen_value_types(&self, name: &str, combinator: &Combinator) -> String {
        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let doc = format!("data type for `{}`.", name);
        match self.ctx.resolve(combinator) {
            CombinatorInner::Struct(struct_comb) => {
                let exec_fields = self.struct_value_fields(struct_comb, TypeMode::Exec);
                let spec_fields = self.struct_value_fields(struct_comb, TypeMode::Spec);
                let inner_ty = self.render_struct_inner_type(struct_comb, TypeMode::Spec);
                let exec_lifetime = if info.needs_lifetime {
                    quote! { <'i> }
                } else {
                    quote! {}
                };
                let exec_generics = if info.needs_lifetime {
                    quote! { <'i> }
                } else {
                    quote! {}
                };
                let exec_struct = quote! {
                    #[derive(Debug, PartialEq, Eq, Clone)]
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
                quote! {
                    #[doc = #doc]
                    #exec_struct
                    #spec_struct
                    pub type #inner_ident = #inner_ty;
                    impl #exec_generics DeepView for #exec_ident #exec_generics {
                        type V = #spec_ident;
                        open spec fn deep_view(&self) -> Self::V {
                            #spec_ident { #(#deep_view_fields,)* }
                        }
                    }
                }
                .to_string()
            }
            CombinatorInner::Enum(enum_comb) => self.gen_enum_types(enum_comb, &info.names),
            CombinatorInner::Choice(choice_comb) => self.gen_choice_types(choice_comb, &info.names),
            _ => {
                let exec_ty = self.render_value_type(combinator, TypeMode::Exec, true);
                let spec_ty = self.render_value_type(combinator, TypeMode::Spec, true);
                let exec_alias = if info.needs_lifetime {
                    quote! { pub type #exec_ident <'i> = #exec_ty; }
                } else {
                    quote! { pub type #exec_ident = #exec_ty; }
                };
                quote! {
                    #[doc = #doc]
                    #exec_alias
                    pub type #spec_ident = #spec_ty;
                }
                .to_string()
            }
        }
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
        let doc = format!("data type for `{}`.", name);
        let exec_alias = if info.needs_lifetime {
            quote! { pub type #exec_ident <'i> = #ty; }
        } else {
            quote! { pub type #exec_ident = #ty; }
        };
        quote! {
            #[doc = #doc]
            #exec_alias
            pub type #spec_ident = #spec_ty;
        }
        .to_string()
    }

    fn gen_enum_types(&self, enum_comb: &EnumCombinator, names: &FormatNames) -> String {
        let exec_ident = format_ident!("{}", names.exec);
        let spec_ident = format_ident!("{}", names.spec);
        let inner_ident = format_ident!("{}", names.inner);
        let (variants, exhaustive, inferred) = match enum_comb {
            EnumCombinator::Exhaustive { enums, inferred } => (enums, true, inferred),
            EnumCombinator::NonExhaustive { enums, inferred } => (enums, false, inferred),
        };
        let repr_ty = self.int_exec_type(inferred);
        let mut branch_tys = variants
            .iter()
            .map(|_| self.int_spec_type(inferred))
            .collect::<Vec<_>>();
        if !exhaustive {
            branch_tys.push(self.int_spec_type(inferred));
        }
        let inner_ty = self.choice_sum_type(&branch_tys);
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
        quote! {
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
        }
        .to_string()
    }

    fn gen_choice_types(&self, choice_comb: &ChoiceCombinator, names: &FormatNames) -> String {
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
        quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq, Clone)]
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
        }
        .to_string()
    }

    pub(crate) fn gen_wrapper_type(&self, name: &str, param_defns: &[ParamDefn]) -> String {
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
                    let field_ident = format_ident!("{}", name);
                    let ty = self.render_inner_type(combinator, TypeMode::Exec, true);
                    quote! { pub #field_ident: #ty }
                }
            })
            .collect::<Vec<_>>();
        if fields.is_empty() {
            quote! {
                #[doc = #doc]
                pub struct #fmt_ident;
            }
            .to_string()
        } else {
            quote! {
                #[doc = #doc]
                pub struct #fmt_ident #lifetime {
                    #(#fields,)*
                }
            }
            .to_string()
        }
    }
}
