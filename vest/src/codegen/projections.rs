//! Length and consistency specs over the public nominal model's fields.
//!
//! These projections only bypass the outer mapper. The backend still defines
//! encoding lengths and validity. Nominal child views and lengths stay closed;
//! expanded specs for non-self-view parameters are bridged separately.
use super::common::{definition_dependencies, sum_pattern, tuple_chain, Analysis};
use crate::vestir::{Definition, StructField};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

impl<'a> Analysis<'a> {
    pub(crate) fn definition(&self, name: &str) -> &Definition {
        self.defs
            .iter()
            .find(|definition| definition.name() == Some(name))
            .expect("generated definition exists")
    }

    pub(crate) fn has_opaque_value_view(&self, name: &str) -> bool {
        match self.definition(name) {
            Definition::StructDef { .. } | Definition::ChoiceDef { .. } => true,
            Definition::CombinatorDef { combinator, .. } => {
                self.direct_alias(combinator).is_some_and(|invocation| {
                    self.recursive_member_for(&invocation.func).is_none()
                        && self.has_opaque_value_view(&invocation.func)
                })
            }
            _ => false,
        }
    }

    pub(crate) fn model_spec_body(
        &self,
        name: &str,
        args: &[TokenStream],
        method: &str,
    ) -> TokenStream {
        let method = format_ident!("{}", method);
        let original = quote! { Self::spec_inner(#(#args),*).#method(v) };
        if self.recursive_member_for(name).is_some() {
            return original;
        }
        let structural = match self.definition(name) {
            Definition::StructDef { combinator, .. } => {
                let fields = combinator
                    .0
                    .iter()
                    .map(|field| {
                        let label = match field {
                            StructField::Ordinary { label, .. }
                            | StructField::Dependent { label, .. }
                            | StructField::Const { label, .. } => format_ident!("{}", label),
                        };
                        quote! { v.#label }
                    })
                    .collect::<Vec<_>>();
                tuple_chain(&fields)
            }
            Definition::ChoiceDef { combinator, .. } => {
                let spec = format_ident!("{}", self.info(name).names.spec);
                let count = combinator.choices.len();
                let arms = self
                    .choice_variant_names(combinator)
                    .into_iter()
                    .enumerate()
                    .map(|(index, variant)| {
                        let variant = format_ident!("{}", variant);
                        let structural = sum_pattern(index, count, quote! { item });
                        quote! { #spec::#variant(item) => #structural, }
                    });
                quote! { match v { #(#arms)* } }
            }
            _ => return original,
        };
        quote! { Self::spec_inner(#(#args),*).1.inner.#method(#structural) }
    }

    /// Connect the public field projections to the mapper only inside proofs.
    pub(crate) fn model_projection_reveal(&self, format: &proc_macro2::Ident) -> TokenStream {
        let format = format.to_string();
        let info = self
            .infos
            .values()
            .find(|info| info.names.fmt == format)
            .expect("generated format exists");
        if self.recursive_member_for(&info.names.dsl).is_some() {
            return TokenStream::new();
        }
        let mut names = vec![info.names.dsl.clone()];
        names.extend(self.unsealed_projection_dependencies(&info.names.dsl));
        let reveals = names.iter().filter_map(|name| match self.definition(name) {
            Definition::StructDef { .. } | Definition::ChoiceDef { .. } => {
                let spec = format_ident!("{}", self.info(name).names.spec);
                Some(quote! { reveal(#spec::into_structural); })
            }
            _ => None,
        });
        quote! { #(#reveals)* }
    }

    pub(crate) fn uses_nominal_spec(&self, name: &str) -> bool {
        self.param_defns_for(name).iter().all(|param| match param {
            crate::vestir::ParamDefn::Dependent { combinator, .. } => {
                self.combinator_is_selfview(combinator)
            }
        })
    }

    /// Non-self-view parameters are represented by an expanded spec combinator,
    /// not an executable nominal format. Its mapper must be opened when bridging
    /// back to the nominal APIs; ordinary child boundaries stay closed.
    pub(crate) fn unsealed_projection_dependencies(&self, name: &str) -> Vec<String> {
        let mut pending = definition_dependencies(self.definition(name));
        let mut result = Vec::new();
        while let Some(child) = pending.pop() {
            if self.uses_nominal_spec(&child)
                || self.recursive_member_for(&child).is_some()
                || result.contains(&child)
            {
                continue;
            }
            pending.extend(definition_dependencies(self.definition(&child)));
            result.push(child);
        }
        result
    }
}
