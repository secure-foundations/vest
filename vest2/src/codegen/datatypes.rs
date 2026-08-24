use super::common::{
    int_literal, nested_tuple_pattern_idents, nested_tuple_value_expr_idents, sum_pattern,
    type_needs_exec_lifetime, Analysis, TypeMode,
};
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
        if !scc_members.is_empty() {
            return self.gen_recursive_struct_value_types(name, struct_comb, scc_members);
        }

        let info = self.info(name);
        let exec_ident = format_ident!("{}", info.names.exec);
        let spec_ident = format_ident!("{}", info.names.spec);
        let inner_ident = format_ident!("{}", info.names.inner);
        let doc = Self::type_doc(name);

        let exec_fields: Vec<_> = struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_const_value_type(combinator, TypeMode::Exec);
                    quote! { pub #id: #ty }
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Exec, scc_members);
                    quote! { pub #id: #ty }
                }
            })
            .collect();

        let spec_field_info: Vec<_> = struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_const_value_type(combinator, TypeMode::Spec);
                    (id, ty)
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Spec, scc_members);
                    (id, ty)
                }
            })
            .collect();
        let spec_field_idents = spec_field_info
            .iter()
            .map(|(ident, _)| ident.clone())
            .collect::<Vec<_>>();
        let spec_field_types = spec_field_info
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>();
        let type_params = (0..spec_field_info.len())
            .map(|idx| format_ident!("T{}", idx))
            .collect::<Vec<_>>();
        let generic_defaults = type_params
            .iter()
            .zip(spec_field_types.iter())
            .map(|(param, ty)| quote! { #param = #ty })
            .collect::<Vec<_>>();
        let spec_decl_generics = if generic_defaults.is_empty() {
            quote! {}
        } else {
            quote! { <#(#generic_defaults),*> }
        };
        let spec_impl_generics = if type_params.is_empty() {
            quote! {}
        } else {
            quote! { <#(#type_params),*> }
        };
        let generic_spec_fields = spec_field_idents
            .iter()
            .zip(type_params.iter())
            .map(|(ident, ty)| quote! { pub #ident: #ty })
            .collect::<Vec<_>>();

        let retained = struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { combinator, .. } => {
                    self.render_const_value_type(combinator, TypeMode::Spec)
                }
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    self.render_value_type_scc(combinator, TypeMode::Spec, scc_members)
                }
            })
            .collect::<Vec<_>>();
        let inner_ty = tuple_chain(&retained);

        let exec_lifetime = if info.needs_lifetime {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let derives = if self.is_copyable(name) {
            quote! { #[derive(Debug, PartialEq, Eq, Clone, Copy)] }
        } else {
            quote! { #[derive(Debug, PartialEq, Eq, Clone)] }
        };
        let exec_struct = quote! {
            #derives
            pub struct #exec_ident #exec_lifetime {
                #(#exec_fields,)*
            }
        };
        let spec_struct = quote! {
            #[verifier::ext_equal]
            pub struct #spec_ident #spec_decl_generics {
                #(#generic_spec_fields,)*
            }
        };

        let deep_view_fields: Vec<_> = struct_comb
            .0
            .iter()
            .map(|field| {
                let label = match field {
                    StructField::Const { label, .. }
                    | StructField::Dependent { label, .. }
                    | StructField::Ordinary { label, .. } => label,
                };
                let id = format_ident!("{}", label);
                quote! { #id: self.#id.deep_view() }
            })
            .collect();
        let deep_view_field_ensures = spec_field_idents
            .iter()
            .map(|ident| quote! { self.deep_view().#ident == self.#ident.deep_view() })
            .collect::<Vec<_>>();

        let deep_view_impl = quote! {
            impl #exec_lifetime DeepView for #exec_ident #exec_lifetime {
                type V = #spec_ident;
                #[verifier::opaque]
                open spec fn deep_view(&self) -> Self::V {
                    #spec_ident { #(#deep_view_fields,)* }
                }
            }

            impl #exec_lifetime #exec_ident #exec_lifetime {
                pub proof fn lemma_deep_view_fields(&self)
                    ensures
                        #(#deep_view_field_ensures,)*
                {
                    reveal(<#exec_ident as DeepView>::deep_view);
                }
            }
        };

        let structural_ty = tuple_chain(
            &type_params
                .iter()
                .map(|x| quote! { #x })
                .collect::<Vec<_>>(),
        );
        let structural_pattern = nested_tuple_pattern_idents(&spec_field_idents);
        let structural_expr = nested_tuple_value_expr_idents(&spec_field_idents);
        let forward_ident = format_ident!("{}Forward", info.names.exec);
        let reverse_ident = format_ident!("{}Reverse", info.names.exec);
        let conversions = quote! {
            impl #spec_impl_generics #spec_ident #spec_impl_generics {
                #[verifier::opaque]
                pub open spec fn from_structural(input: #structural_ty) -> Self {
                    let #structural_pattern = input;
                    Self { #(#spec_field_idents),* }
                }

                #[verifier::opaque]
                pub open spec fn into_structural(self) -> #structural_ty {
                    let Self { #(#spec_field_idents),* } = self;
                    #structural_expr
                }

                pub broadcast proof fn lemma_from_into(self)
                    ensures #[trigger] Self::from_structural(Self::into_structural(self)) == self,
                {
                    reveal(#spec_ident::from_structural);
                    reveal(#spec_ident::into_structural);
                }

                pub broadcast proof fn lemma_into_from(input: #structural_ty)
                    ensures #[trigger] Self::into_structural(Self::from_structural(input)) == input,
                {
                    reveal(#spec_ident::from_structural);
                    reveal(#spec_ident::into_structural);
                }

                pub proof fn lemma_into_structural_fields(self)
                    ensures
                        Self::into_structural(self) == match self {
                            Self { #(#spec_field_idents),* } => #structural_expr,
                        },
                {
                    reveal(#spec_ident::into_structural);
                }
            }

            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #forward_ident;
            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #reverse_ident;

            impl SpecMap for #forward_ident {
                type Input = #inner_ident;
                type Output = #spec_ident;

                open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
                    #spec_ident::from_structural(input)
                }
            }

            impl SpecMap for #reverse_ident {
                type Input = #spec_ident;
                type Output = #inner_ident;

                open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
                    value.into_structural()
                }
            }
        };

        render_ts(quote! {
            #[doc = #doc]
            #exec_struct
            #spec_struct
            pub type #inner_ident = #inner_ty;
            #deep_view_impl
            #conversions
        })
    }

    fn gen_recursive_struct_value_types(
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

        let exec_fields = struct_comb.0.iter().filter_map(|field| match field {
            StructField::Const { .. } => None,
            StructField::Dependent { label, combinator }
            | StructField::Ordinary { label, combinator } => {
                let id = format_ident!("{}", label);
                let ty = self.render_value_type_scc(combinator, TypeMode::Exec, scc_members);
                Some(quote! { pub #id: #ty })
            }
        });
        let spec_fields = struct_comb.0.iter().filter_map(|field| match field {
            StructField::Const { .. } => None,
            StructField::Dependent { label, combinator }
            | StructField::Ordinary { label, combinator } => {
                let id = format_ident!("{}", label);
                let ty = self.render_value_type_scc(combinator, TypeMode::Spec, scc_members);
                Some(quote! { pub #id: #ty })
            }
        });
        let retained = struct_comb
            .0
            .iter()
            .map(|field| match field {
                StructField::Const { combinator, .. } => {
                    self.render_const_value_type(combinator, TypeMode::Spec)
                }
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    self.render_value_type_scc(combinator, TypeMode::Spec, scc_members)
                }
            })
            .collect::<Vec<_>>();
        let inner_ty = tuple_chain(&retained);
        let deep_view_fields = struct_comb.0.iter().filter_map(|field| match field {
            StructField::Const { .. } => None,
            StructField::Dependent { label, combinator }
            | StructField::Ordinary { label, combinator } => {
                let id = format_ident!("{}", label);
                let expr = if super::common::is_combinator_in_scc(combinator, scc_members) {
                    let vfn =
                        format_ident!("{}_view", super::common::get_invocation_name(combinator));
                    quote! { Box::new(#vfn(&*x.#id)) }
                } else {
                    quote! { x.#id.deep_view() }
                };
                Some(quote! { #id: #expr })
            }
        });
        let view_fn = format_ident!("{}_view", info.names.dsl);

        render_ts(quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq)]
            pub struct #exec_ident<'i> {
                #(#exec_fields,)*
            }
            #[verifier::ext_equal]
            pub struct #spec_ident {
                #(#spec_fields,)*
            }
            pub type #inner_ident = #inner_ty;
            pub open spec fn #view_fn(x: &#exec_ident) -> #spec_ident decreases *x, {
                #spec_ident { #(#deep_view_fields,)* }
            }
            impl<'i> DeepView for #exec_ident<'i> {
                type V = #spec_ident;
                open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
            }
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
                #[verifier::opaque]
                open spec fn deep_view(&self) -> Self::V {
                    *self
                }
            }
            impl #exec_ident {
                pub proof fn lemma_deep_view(&self)
                    ensures self.deep_view() == *self,
                {
                    reveal(<#exec_ident as DeepView>::deep_view);
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
        if !scc_members.is_empty() {
            return self.gen_recursive_choice_value_types(name, choice_comb, scc_members);
        }

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
        let type_params = (0..branch_spec_types.len())
            .map(|idx| format_ident!("T{}", idx))
            .collect::<Vec<_>>();
        let generic_defaults = type_params
            .iter()
            .zip(branch_spec_types.iter())
            .map(|(param, ty)| quote! { #param = #ty })
            .collect::<Vec<_>>();
        let spec_decl_generics = if generic_defaults.is_empty() {
            quote! {}
        } else {
            quote! { <#(#generic_defaults),*> }
        };
        let spec_impl_generics = if type_params.is_empty() {
            quote! {}
        } else {
            quote! { <#(#type_params),*> }
        };
        let spec_variants = variant_names
            .iter()
            .zip(type_params.iter())
            .map(|(name, ty)| {
                let ident = format_ident!("{}", name);
                quote! { #ident(#ty) }
            });
        let doc = format!("data type for `{}`.", names.dsl);
        let derives = if self.is_copyable(name) {
            quote! { #[derive(Debug, PartialEq, Eq, Clone, Copy)] }
        } else {
            quote! { #[derive(Debug, PartialEq, Eq, Clone)] }
        };
        let exec_enum = quote! {
            #derives
            pub enum #exec_ident #exec_lifetime {
                #(#exec_variants,)*
            }
        };
        let spec_enum = quote! {
            #[verifier::ext_equal]
            pub enum #spec_ident #spec_decl_generics {
                #(#spec_variants,)*
            }
        };

        let deep_view_arms = variant_names
            .iter()
            .zip(&choice_comb.choices)
            .map(|(vn, _)| {
                let ident = format_ident!("{}", vn);
                let expr = quote! { v.deep_view() };
                quote! { #exec_ident::#ident(v) => #spec_ident::#ident(#expr), }
            })
            .collect::<Vec<_>>();

        let deep_view_impl = quote! {
            impl #exec_generics DeepView for #exec_ident #exec_generics {
                type V = #spec_ident;
                #[verifier::opaque]
                open spec fn deep_view(&self) -> Self::V {
                    match self {
                        #(#deep_view_arms)*
                    }
                }
            }

            impl #exec_generics #exec_ident #exec_generics {
                pub proof fn lemma_deep_view_fields(&self)
                    ensures
                        self.deep_view() == match self {
                            #(#deep_view_arms)*
                        },
                {
                    reveal(<#exec_ident as DeepView>::deep_view);
                }
            }
        };

        let generic_sum_ty = self.render_choice_sum_type(
            &type_params
                .iter()
                .map(|ty| quote! { #ty })
                .collect::<Vec<_>>(),
        );
        let from_arms = variant_names.iter().enumerate().map(|(idx, variant)| {
            let pattern = sum_pattern(idx, variant_names.len(), quote! { value });
            let variant = format_ident!("{}", variant);
            quote! { #pattern => Self::#variant(value), }
        });
        let into_arms = variant_names
            .iter()
            .enumerate()
            .map(|(idx, variant)| {
                let value = sum_pattern(idx, variant_names.len(), quote! { value });
                let variant = format_ident!("{}", variant);
                quote! { Self::#variant(value) => #value, }
            })
            .collect::<Vec<_>>();
        let self_proof_arms = variant_names.iter().map(|variant| {
            let variant = format_ident!("{}", variant);
            quote! { Self::#variant(_) => {}, }
        });
        let input_proof_arms = variant_names.iter().enumerate().map(|(idx, _)| {
            let pattern = sum_pattern(idx, variant_names.len(), quote! { _ });
            quote! { #pattern => {}, }
        });
        let forward_ident = format_ident!("{}Forward", names.exec);
        let reverse_ident = format_ident!("{}Reverse", names.exec);
        let conversions = quote! {
            impl #spec_impl_generics #spec_ident #spec_impl_generics {
                #[verifier::opaque]
                pub open spec fn from_structural(input: #generic_sum_ty) -> Self {
                    match input { #(#from_arms)* }
                }

                #[verifier::opaque]
                pub open spec fn into_structural(self) -> #generic_sum_ty {
                    match self { #(#into_arms)* }
                }

                pub broadcast proof fn lemma_from_into(self)
                    ensures #[trigger] Self::from_structural(Self::into_structural(self)) == self,
                {
                    reveal(#spec_ident::from_structural);
                    reveal(#spec_ident::into_structural);
                    match self { #(#self_proof_arms)* }
                }

                pub broadcast proof fn lemma_into_from(input: #generic_sum_ty)
                    ensures #[trigger] Self::into_structural(Self::from_structural(input)) == input,
                {
                    reveal(#spec_ident::from_structural);
                    reveal(#spec_ident::into_structural);
                    match input { #(#input_proof_arms)* }
                }

                pub proof fn lemma_into_structural_variant(self)
                    ensures
                        Self::into_structural(self) == match self {
                            #(#into_arms)*
                        },
                {
                    reveal(#spec_ident::into_structural);
                }
            }

            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #forward_ident;
            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #reverse_ident;

            impl SpecMap for #forward_ident {
                type Input = #inner_ident;
                type Output = #spec_ident;

                open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
                    #spec_ident::from_structural(input)
                }
            }

            impl SpecMap for #reverse_ident {
                type Input = #spec_ident;
                type Output = #inner_ident;

                open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
                    value.into_structural()
                }
            }
        };
        render_ts(quote! {
            #[doc = #doc]
            #exec_enum
            #spec_enum
            pub type #inner_ident = #inner_ty;
            #deep_view_impl
            #conversions
        })
    }

    fn gen_recursive_choice_value_types(
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
        let branch_exec_types = choice_comb
            .choices
            .iter()
            .map(|(_, comb)| self.render_value_type_scc(comb, TypeMode::Exec, scc_members))
            .collect::<Vec<_>>();
        let branch_spec_types = choice_comb
            .choices
            .iter()
            .map(|(_, comb)| self.render_value_type_scc(comb, TypeMode::Spec, scc_members))
            .collect::<Vec<_>>();
        let inner_ty = self.render_choice_sum_type(&branch_spec_types);
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
        let deep_view_arms =
            variant_names
                .iter()
                .zip(&choice_comb.choices)
                .map(|(variant, (_, combinator))| {
                    let variant = format_ident!("{}", variant);
                    let value = if super::common::is_combinator_in_scc(combinator, scc_members) {
                        let view_fn = format_ident!(
                            "{}_view",
                            super::common::get_invocation_name(combinator)
                        );
                        quote! { Box::new(#view_fn(&**v)) }
                    } else {
                        quote! { v.deep_view() }
                    };
                    quote! { #exec_ident::#variant(v) => #spec_ident::#variant(#value), }
                });
        let view_fn = format_ident!("{}_view", names.dsl);
        let doc = format!("data type for `{}`.", names.dsl);

        render_ts(quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq)]
            pub enum #exec_ident<'i> {
                #(#exec_variants,)*
            }
            #[verifier::ext_equal]
            pub enum #spec_ident {
                #(#spec_variants,)*
            }
            pub type #inner_ident = #inner_ty;
            pub open spec fn #view_fn(x: &#exec_ident) -> #spec_ident decreases *x, {
                match x { #(#deep_view_arms)* }
            }
            impl<'i> DeepView for #exec_ident<'i> {
                type V = #spec_ident;
                open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
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
        let forward_ident = format_ident!("{}Forward", names.exec);
        let reverse_ident = format_ident!("{}Reverse", names.exec);
        let known_from_arms = variants
            .iter()
            .map(|variant| {
                let ident = format_ident!("{}", variant.name);
                let value = int_literal(variant.value, inferred);
                quote! { #value => Self::#ident, }
            })
            .collect::<Vec<_>>();
        let known_into_arms = variants
            .iter()
            .map(|variant| {
                let ident = format_ident!("{}", variant.name);
                let value = int_literal(variant.value, inferred);
                if exhaustive {
                    quote! { Self::#ident => #value, }
                } else {
                    quote! { Self::#ident => L(#value), }
                }
            })
            .collect::<Vec<_>>();
        let known_input_proof_arms = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                quote! { #value => {}, }
            })
            .collect::<Vec<_>>();
        let valid_terms = variants
            .iter()
            .map(|variant| {
                let value = int_literal(variant.value, inferred);
                quote! { x == #value }
            })
            .collect::<Vec<_>>();
        let valid_known = valid_terms
            .into_iter()
            .reduce(|left, right| quote! { #left || #right })
            .unwrap_or_else(|| quote! { false });
        let (from_body, into_body, valid_body, from_into_arms, into_from_body) = if exhaustive {
            (
                quote! {
                    match input {
                        #(#known_from_arms)*
                        _ => arbitrary(),
                    }
                },
                quote! { match self { #(#known_into_arms)* } },
                quote! { { let x = input; #valid_known } },
                variants
                    .iter()
                    .map(|variant| {
                        let ident = format_ident!("{}", variant.name);
                        quote! { Self::#ident => {}, }
                    })
                    .collect::<Vec<_>>(),
                quote! { match input { #(#known_input_proof_arms)* _ => { assert(false); } } },
            )
        } else {
            (
                quote! {
                    match input {
                        L(x) => match x {
                            #(#known_from_arms)*
                            _ => arbitrary(),
                        },
                        R(x) => Self::Unknown(x),
                    }
                },
                quote! {
                    match self {
                        #(#known_into_arms)*
                        Self::Unknown(x) => R(x),
                    }
                },
                quote! {
                    match input {
                        L(x) => #valid_known,
                        R(x) => true,
                    }
                },
                variants
                    .iter()
                    .map(|variant| {
                        let ident = format_ident!("{}", variant.name);
                        quote! { Self::#ident => {}, }
                    })
                    .chain(core::iter::once(quote! { Self::Unknown(_) => {}, }))
                    .collect::<Vec<_>>(),
                quote! {
                    match input {
                        L(x) => match x { #(#known_input_proof_arms)* _ => { assert(false); } },
                        R(_) => {},
                    }
                },
            )
        };
        let doc = format!("data type for `{}`.", names.dsl);
        render_ts(quote! {
            #[doc = #doc]
            #[repr(#repr_ty)]
            #[derive(Debug, PartialEq, Eq, Clone, Copy, StructuralEq)]
            pub enum #exec_ident {
                #(#exec_variants,)*
                #extra_exec
            }
            pub type #spec_ident = #exec_ident;
            pub type #inner_ident = #inner_ty;
            impl DeepView for #exec_ident {
                type V = Self;
                #[verifier::opaque]
                open spec fn deep_view(&self) -> Self::V {
                    *self
                }
            }

            impl #exec_ident {
                pub proof fn lemma_deep_view(&self)
                    ensures self.deep_view() == *self,
                {
                    reveal(<#exec_ident as DeepView>::deep_view);
                }

                pub open spec fn structural_valid(input: #inner_ident) -> bool {
                    #valid_body
                }

                #[verifier::opaque]
                pub open spec fn from_structural(input: #inner_ident) -> Self {
                    #from_body
                }

                #[verifier::opaque]
                pub open spec fn into_structural(self) -> #inner_ident {
                    #into_body
                }

                pub broadcast proof fn lemma_from_into(self)
                    ensures #[trigger] Self::from_structural(Self::into_structural(self)) == self,
                {
                    reveal(#exec_ident::from_structural);
                    reveal(#exec_ident::into_structural);
                    match self { #(#from_into_arms)* }
                }

                pub broadcast proof fn lemma_into_from(input: #inner_ident)
                    requires Self::structural_valid(input),
                    ensures #[trigger] Self::into_structural(Self::from_structural(input)) == input,
                {
                    reveal(#exec_ident::from_structural);
                    reveal(#exec_ident::into_structural);
                    #into_from_body
                }
            }

            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #forward_ident;
            #[derive(Clone, Copy)]
            #[doc(hidden)]
            pub struct #reverse_ident;

            impl SpecMap for #forward_ident {
                type Input = #inner_ident;
                type Output = #spec_ident;

                open spec fn spec_map(&self, input: Self::Input) -> Self::Output {
                    #exec_ident::from_structural(input)
                }
            }

            impl SpecMap for #reverse_ident {
                type Input = #spec_ident;
                type Output = #inner_ident;

                open spec fn spec_map(&self, value: Self::Input) -> Self::Output {
                    value.into_structural()
                }
            }
            #[cfg(not(verus_keep_ghost))]
            unsafe impl Structural for #exec_ident {}
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
