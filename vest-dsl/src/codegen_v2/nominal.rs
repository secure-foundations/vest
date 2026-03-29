//! Nominal type generation for vest combinators.
//!
//! This module generates nominal Rust types from combinator definitions:
//!
//! - **Nominal struct types** for vest struct formats (e.g., `struct Foo { ... }`)
//! - **Nominal enum types** for vest choice/dispatch formats (e.g., `enum Bar { ... }`)
//! - **Owned variants** for generated data that needs ownership
//! - **`From` impls** for struct <-> tuple conversions
//! - **`Mapper` structs** for use with the `Mapped` combinator
//!
//! The generated nominal types provide a more ergonomic API compared to raw
//! tuple/nested types from the combinator structure.

use proc_macro2::{Ident, Literal, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;

use super::combir::{CombDef, CombIR, DepCombIR, TagValue};

/// Field information extracted from combinator structure.
#[derive(Debug, Clone)]
pub struct FieldInfo {
    /// Field name (from struct definition or generated).
    pub name: String,
    /// Whether this is a dependent field (prefixed with @).
    pub is_dependent: bool,
    /// The field's combinator type.
    pub comb: CombIR,
}

/// Variant information for enum types.
#[derive(Debug, Clone)]
pub struct VariantInfo {
    /// Variant name.
    pub name: String,
    /// Tag value for dispatch.
    pub tag: TagValue,
    /// Inner combinator for this variant.
    pub comb: CombIR,
}

/// Context for generating nominal types from combinator definitions.
pub struct NominalTypeGen<'a> {
    /// The combinator definition being processed.
    pub def: &'a CombDef,
    /// Map of all definitions for reference lookups.
    pub defs: &'a HashMap<String, &'a CombDef>,
    /// Generated type items (accumulated).
    pub type_items: Vec<TokenStream>,
    /// Generated From impls (accumulated).
    pub from_impls: Vec<TokenStream>,
    /// Generated Mapper structs (accumulated).
    pub mapper_items: Vec<TokenStream>,
}

pub struct NominalSections {
    pub type_items: TokenStream,
    pub support_items: TokenStream,
}

enum TopLevelNominalKind {
    Struct {
        needs_lifetime: bool,
        borrow_by_value: bool,
    },
    Enum {
        needs_lifetime: bool,
    },
    Alias,
}

impl<'a> NominalTypeGen<'a> {
    pub fn new(def: &'a CombDef, defs: &'a HashMap<String, &'a CombDef>) -> Self {
        Self {
            def,
            defs,
            type_items: Vec::new(),
            from_impls: Vec::new(),
            mapper_items: Vec::new(),
        }
    }

    /// Generate all nominal types for this definition.
    pub fn generate(&mut self) -> TokenStream {
        let sections = self.generate_sections();
        let type_items = sections.type_items;
        let support_items = sections.support_items;

        quote! {
            #type_items
            #support_items
        }
    }

    /// Generate nominal types and return them split into type and support sections.
    pub fn generate_sections(&mut self) -> NominalSections {
        self.generate_for_comb(&self.def.body.clone(), &self.def.name);

        let type_items = &self.type_items;
        let from_impls = &self.from_impls;
        let mapper_items = &self.mapper_items;

        NominalSections {
            type_items: quote! {
                #(#type_items)*
            },
            support_items: quote! {
                #(#from_impls)*
                #(#mapper_items)*
            },
        }
    }

    fn top_level_nominal_kind(&self, comb: &CombIR) -> TopLevelNominalKind {
        match comb {
            CombIR::Tuple(elems) if !elems.is_empty() => TopLevelNominalKind::Struct {
                needs_lifetime: self.comb_needs_lifetime(comb),
                borrow_by_value: self.comb_borrow_by_value(comb),
            },
            CombIR::Pair { .. } => TopLevelNominalKind::Struct {
                needs_lifetime: self.comb_needs_lifetime(comb),
                borrow_by_value: self.comb_borrow_by_value(comb),
            },
            CombIR::Dispatch { branches, .. } => TopLevelNominalKind::Enum {
                needs_lifetime: branches
                    .iter()
                    .any(|(_, branch)| self.comb_needs_lifetime(branch)),
            },
            CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::AndThen { inner, .. } => self.top_level_nominal_kind(inner),
            _ => TopLevelNominalKind::Alias,
        }
    }

    /// Generate nominal types for a combinator.
    fn generate_for_comb(&mut self, comb: &CombIR, name: &str) {
        match comb {
            // Struct-like: Tuple or Pair with named fields
            CombIR::Tuple(elems) if !elems.is_empty() => {
                let mut fields = Vec::new();
                self.extract_fields_recursive(comb, &mut fields, &[]);
                self.generate_struct_type(name, comb, &fields);
            }

            CombIR::Pair { fst, snd } => {
                // Dependent pair - extract field info from structure
                let fields = self.extract_pair_fields(fst, snd);
                if !fields.is_empty() {
                    self.generate_struct_type(name, comb, &fields);
                }
            }

            CombIR::Dispatch { tag: _, branches } => {
                // Dispatch/choice - generate enum type
                let variants: Vec<VariantInfo> = branches
                    .iter()
                    .enumerate()
                    .map(|(i, (tag, c))| VariantInfo {
                        name: self.variant_name_from_tag(tag, i),
                        tag: tag.clone(),
                        comb: c.clone(),
                    })
                    .collect();
                self.generate_enum_type(name, &variants);
            }

            // Named reference - emit a nominal alias for this definition.
            CombIR::Named { .. } => self.generate_alias_type(name, comb),

            // Modifiers - generate for inner
            CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::AndThen { inner, .. } => {
                self.generate_for_comb(inner, name);
            }

            // Primitive and wrapper aliases still need a nominal name so other generated
            // types can reference them.
            _ => self.generate_alias_type(name, comb),
        }
    }

    /// Extract field information from a Pair structure.
    fn extract_pair_fields(&self, fst: &CombIR, snd: &DepCombIR) -> Vec<FieldInfo> {
        let mut fields = Vec::new();

        // Extract fields from first component
        self.extract_fields_recursive(fst, &mut fields, &snd.dep_names);

        // Extract fields from second component
        self.extract_fields_recursive(&snd.comb, &mut fields, &[]);

        fields
    }

    /// Recursively extract fields from combinator structure.
    fn extract_fields_recursive(
        &self,
        comb: &CombIR,
        fields: &mut Vec<FieldInfo>,
        dep_names: &[String],
    ) {
        match comb {
            CombIR::Tuple(elems) => {
                for (i, (opt_name, elem)) in elems.iter().enumerate() {
                    // Check if this position corresponds to a dependent name
                    let is_dep = i < dep_names.len();
                    if !is_dep
                        && opt_name.is_none()
                        && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. })
                    {
                        self.extract_fields_recursive(elem, fields, &[]);
                        continue;
                    }
                    let name = if is_dep {
                        dep_names[i].clone()
                    } else if let Some(stored_name) = opt_name {
                        stored_name.clone()
                    } else {
                        format!("field{}", fields.len())
                    };
                    fields.push(FieldInfo {
                        name,
                        is_dependent: is_dep,
                        comb: elem.clone(),
                    });
                }
            }
            CombIR::Pair { fst, snd } => {
                self.extract_fields_recursive(fst, fields, dep_names);
                self.extract_fields_recursive(&snd.comb, fields, &[]);
            }
            // For other types, add as single field
            _ => {
                let name = if !dep_names.is_empty() {
                    dep_names[0].clone()
                } else {
                    format!("field{}", fields.len())
                };
                fields.push(FieldInfo {
                    name,
                    is_dependent: !dep_names.is_empty(),
                    comb: comb.clone(),
                });
            }
        }
    }

    /// Generate a variant name from a tag value and its index in the branch list.
    /// For integer tags, we use 0-indexed "Variant{i}" names for consistency with old codegen.
    fn variant_name_from_tag(&self, tag: &TagValue, index: usize) -> String {
        match tag {
            TagValue::Int(_) => format!("Variant{}", index),
            TagValue::Enum { variant, .. } => variant.clone(),
            TagValue::Bytes(bytes) => {
                format!("Bytes{:02X?}", bytes).replace(['[', ']', ',', ' '], "")
            }
            TagValue::Wildcard => "Default".to_string(),
        }
    }

    fn generate_alias_type(&mut self, name: &str, comb: &CombIR) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
        let ty = self.nominal_type_tokens(comb, false);

        if self.comb_needs_lifetime(comb) {
            let owned_ty = self.nominal_type_tokens(comb, true);
            self.type_items
                .push(quote! { pub type #type_name<'a> = #ty; });
            self.type_items
                .push(quote! { pub type #owned_name = #owned_ty; });
        } else {
            self.type_items.push(quote! { pub type #type_name = #ty; });
        }
    }

    fn def_needs_lifetime(&self, name: &str) -> bool {
        self.defs
            .get(name)
            .map(|def| self.comb_needs_lifetime(&def.body))
            .unwrap_or(false)
    }

    fn def_borrow_by_value(&self, name: &str) -> bool {
        self.defs
            .get(name)
            .map(|def| self.comb_borrow_by_value(&def.body))
            .unwrap_or(false)
    }

    fn comb_borrow_by_value(&self, comb: &CombIR) -> bool {
        match comb {
            CombIR::U8
            | CombIR::U16(_)
            | CombIR::U24(_)
            | CombIR::U32(_)
            | CombIR::U64(_)
            | CombIR::Fixed { .. }
            | CombIR::Variable { .. }
            | CombIR::Tail
            | CombIR::End
            | CombIR::Success
            | CombIR::Fail(_) => true,
            CombIR::Tuple(elems) => {
                !elems.is_empty()
                    && elems
                        .iter()
                        .all(|(_, elem)| self.comb_borrow_by_value(elem))
            }
            CombIR::Opt(inner) => self.comb_borrow_by_value(inner),
            CombIR::OptThen { fst, snd } => {
                self.comb_borrow_by_value(fst) && self.comb_borrow_by_value(snd)
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                self.comb_borrow_by_value(inner)
            }
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. }
            | CombIR::Tag { inner, .. } => self.comb_borrow_by_value(inner),
            CombIR::Named { name, .. } => self.def_borrow_by_value(name),
            CombIR::Pair { .. } | CombIR::Dispatch { .. } | CombIR::Choice(_) => false,
        }
    }

    fn named_type_tokens(&self, name: &str, lt: Option<TokenStream>, owned: bool) -> TokenStream {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        if owned && self.def_needs_lifetime(name) {
            let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
            quote! { #owned_name }
        } else if self.def_needs_lifetime(name) {
            let lt = lt.unwrap_or_else(|| quote! { 'a });
            quote! { #type_name<#lt> }
        } else {
            quote! { #type_name }
        }
    }

    fn named_borrow_type_tokens(&self, name: &str) -> TokenStream {
        let ty = self.named_type_tokens(name, Some(quote! { 's }), false);
        if self.def_borrow_by_value(name) {
            ty
        } else {
            quote! { &'s #ty }
        }
    }

    fn comb_needs_lifetime(&self, comb: &CombIR) -> bool {
        match comb {
            CombIR::Variable { .. } | CombIR::Tail | CombIR::Fixed { .. } => true,
            CombIR::Tuple(elems) => elems.iter().any(|(_, elem)| self.comb_needs_lifetime(elem)),
            CombIR::Choice(elems) => elems.iter().any(|elem| self.comb_needs_lifetime(elem)),
            CombIR::Pair { fst, snd } => {
                self.comb_needs_lifetime(fst) || self.comb_needs_lifetime(&snd.comb)
            }
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Opt(inner)
            | CombIR::Repeat(inner)
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. }
            | CombIR::Tag { inner, .. } => self.comb_needs_lifetime(inner),
            CombIR::OptThen { fst, snd } => {
                self.comb_needs_lifetime(fst) || self.comb_needs_lifetime(snd)
            }
            CombIR::RepeatN { inner, .. } => self.comb_needs_lifetime(inner),
            CombIR::Dispatch { branches, .. } => branches
                .iter()
                .any(|(_, comb)| self.comb_needs_lifetime(comb)),
            CombIR::Named { name, .. } => self.def_needs_lifetime(name),
            CombIR::U8
            | CombIR::U16(_)
            | CombIR::U24(_)
            | CombIR::U32(_)
            | CombIR::U64(_)
            | CombIR::End
            | CombIR::Success
            | CombIR::Fail(_) => false,
        }
    }

    fn nominal_type_tokens(&self, comb: &CombIR, owned: bool) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { u8 },
            CombIR::U16(_) => quote! { u16 },
            CombIR::U24(_) => quote! { u24 },
            CombIR::U32(_) => quote! { u32 },
            CombIR::U64(_) => quote! { u64 },
            CombIR::Fixed { .. } => {
                if owned {
                    quote! { Vec<u8> }
                } else {
                    quote! { &'a [u8] }
                }
            }
            CombIR::Variable { .. } | CombIR::Tail => {
                if owned {
                    quote! { Vec<u8> }
                } else {
                    quote! { &'a [u8] }
                }
            }
            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.nominal_type_tokens(&elems[0].1, owned)
                } else {
                    let types: Vec<TokenStream> = elems
                        .iter()
                        .map(|(_, elem)| self.nominal_type_tokens(elem, owned))
                        .collect();
                    build_nested_pair_type_from_tokens(&types)
                }
            }
            CombIR::Pair { fst, snd } => {
                let fst_ty = self.nominal_type_tokens(fst, owned);
                let snd_ty = self.nominal_type_tokens(&snd.comb, owned);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.nominal_type_tokens(inner, owned);
                quote! { Option<#inner_ty> }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_ty = self.nominal_type_tokens(fst, owned);
                let snd_ty = self.nominal_type_tokens(snd, owned);
                quote! { (Option<#fst_ty>, #snd_ty) }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.nominal_type_tokens(inner, owned);
                quote! { Vec<#inner_ty> }
            }
            CombIR::Choice(choices) => {
                let types: Vec<TokenStream> = choices
                    .iter()
                    .map(|choice| self.nominal_type_tokens(choice, owned))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Dispatch { branches, .. } => {
                let types: Vec<TokenStream> = branches
                    .iter()
                    .map(|(_, branch)| self.nominal_type_tokens(branch, owned))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Named { name, .. } => self.named_type_tokens(name, Some(quote! { 'a }), owned),
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.nominal_type_tokens(inner, owned),
            CombIR::Tag { inner, value } => self
                .nominal_tag_type_tokens(inner, value, owned)
                .unwrap_or_else(|| quote! { () }),
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        }
    }

    fn nominal_tag_type_tokens(
        &self,
        inner: &CombIR,
        value: &TagValue,
        owned: bool,
    ) -> Option<TokenStream> {
        match value {
            TagValue::Int(_) | TagValue::Enum { .. } => {
                Some(self.nominal_type_tokens(inner, owned))
            }
            TagValue::Bytes(_) | TagValue::Wildcard => None,
        }
    }

    fn nominal_tag_value_tokens(&self, value: &TagValue) -> Option<TokenStream> {
        match value {
            TagValue::Int(v) => {
                if let Some(const_ident) = self.const_ident_for_int(*v) {
                    Some(quote! { #const_ident })
                } else {
                    let lit = Literal::i128_unsuffixed(*v);
                    Some(quote! { #lit })
                }
            }
            TagValue::Enum { ty, variant } => {
                let ty_ident = format_ident!("{}", snake_to_upper_camel(ty));
                let variant_ident = format_ident!("{}", variant);
                Some(quote! { #ty_ident::#variant_ident })
            }
            TagValue::Bytes(_) | TagValue::Wildcard => None,
        }
    }

    fn const_ident_for_int(&self, value: i128) -> Option<Ident> {
        let mut matches = self
            .def
            .const_defs
            .iter()
            .filter(|const_def| const_def.value == value)
            .map(|const_def| format_ident!("{}", const_def.name));
        let first = matches.next()?;
        if matches.next().is_some() {
            None
        } else {
            Some(first)
        }
    }

    fn parse_type_tokens_with_lt(&self, comb: &CombIR, lt: TokenStream) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { u8 },
            CombIR::U16(_) => quote! { u16 },
            CombIR::U24(_) => quote! { u24 },
            CombIR::U32(_) => quote! { u32 },
            CombIR::U64(_) => quote! { u64 },
            CombIR::Fixed { .. } => quote! { &#lt [u8] },
            CombIR::Variable { .. } | CombIR::Tail => quote! { &#lt [u8] },
            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.parse_type_tokens_with_lt(&elems[0].1, lt)
                } else {
                    let types: Vec<TokenStream> = elems
                        .iter()
                        .map(|(_, elem)| self.parse_type_tokens_with_lt(elem, lt.clone()))
                        .collect();
                    build_nested_pair_type_from_tokens(&types)
                }
            }
            CombIR::Pair { fst, snd } => {
                let fst_ty = self.parse_type_tokens_with_lt(fst, lt.clone());
                let snd_ty = self.parse_type_tokens_with_lt(&snd.comb, lt);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.parse_type_tokens_with_lt(inner, lt);
                quote! { Option<#inner_ty> }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_ty = self.parse_type_tokens_with_lt(fst, lt.clone());
                let snd_ty = self.parse_type_tokens_with_lt(snd, lt);
                quote! { (Option<#fst_ty>, #snd_ty) }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.parse_type_tokens_with_lt(inner, lt);
                quote! { Vec<#inner_ty> }
            }
            CombIR::Choice(choices) => {
                let types: Vec<TokenStream> = choices
                    .iter()
                    .map(|choice| self.parse_type_tokens_with_lt(choice, lt.clone()))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Dispatch { branches, .. } => {
                let types: Vec<TokenStream> = branches
                    .iter()
                    .map(|(_, branch)| self.parse_type_tokens_with_lt(branch, lt.clone()))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Named { name, .. } => self.named_type_tokens(name, Some(lt), false),
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.parse_type_tokens_with_lt(inner, lt),
            CombIR::Tag { .. } => quote! { () },
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        }
    }

    fn owned_type_tokens(&self, comb: &CombIR) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { u8 },
            CombIR::U16(_) => quote! { u16 },
            CombIR::U24(_) => quote! { u24 },
            CombIR::U32(_) => quote! { u32 },
            CombIR::U64(_) => quote! { u64 },
            CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => quote! { Vec<u8> },
            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.owned_type_tokens(&elems[0].1)
                } else {
                    let types: Vec<TokenStream> = elems
                        .iter()
                        .map(|(_, elem)| self.owned_type_tokens(elem))
                        .collect();
                    build_nested_pair_type_from_tokens(&types)
                }
            }
            CombIR::Pair { fst, snd } => {
                let fst_ty = self.owned_type_tokens(fst);
                let snd_ty = self.owned_type_tokens(&snd.comb);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.owned_type_tokens(inner);
                quote! { Option<#inner_ty> }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_ty = self.owned_type_tokens(fst);
                let snd_ty = self.owned_type_tokens(snd);
                quote! { (Option<#fst_ty>, #snd_ty) }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.owned_type_tokens(inner);
                quote! { Vec<#inner_ty> }
            }
            CombIR::Choice(choices) => {
                let types: Vec<TokenStream> = choices
                    .iter()
                    .map(|choice| self.owned_type_tokens(choice))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Dispatch { branches, .. } => {
                let types: Vec<TokenStream> = branches
                    .iter()
                    .map(|(_, branch)| self.owned_type_tokens(branch))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Named { name, .. } => self.named_type_tokens(name, None, true),
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.owned_type_tokens(inner),
            CombIR::Tag { .. } => quote! { () },
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        }
    }

    fn borrow_type_tokens(&self, comb: &CombIR) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { u8 },
            CombIR::U16(_) => quote! { u16 },
            CombIR::U24(_) => quote! { u24 },
            CombIR::U32(_) => quote! { u32 },
            CombIR::U64(_) => quote! { u64 },
            CombIR::Fixed { .. } => quote! { &'s [u8] },
            CombIR::Variable { .. } | CombIR::Tail => quote! { &'s [u8] },
            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.borrow_type_tokens(&elems[0].1)
                } else {
                    let types: Vec<TokenStream> = elems
                        .iter()
                        .map(|(_, elem)| self.borrow_type_tokens(elem))
                        .collect();
                    build_nested_pair_type_from_tokens(&types)
                }
            }
            CombIR::Pair { fst, snd } => {
                let fst_ty = self.borrow_type_tokens(fst);
                let snd_ty = self.borrow_type_tokens(&snd.comb);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.borrow_type_tokens(inner);
                quote! { Option<#inner_ty> }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_ty = self.borrow_type_tokens(fst);
                let snd_ty = self.borrow_type_tokens(snd);
                quote! { (Option<#fst_ty>, #snd_ty) }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.borrow_type_tokens(inner);
                quote! { &'s [#inner_ty] }
            }
            CombIR::Choice(choices) => {
                let types: Vec<TokenStream> = choices
                    .iter()
                    .map(|choice| self.borrow_type_tokens(choice))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Dispatch { branches, .. } => {
                let types: Vec<TokenStream> = branches
                    .iter()
                    .map(|(_, branch)| self.borrow_type_tokens(branch))
                    .collect();
                build_nested_either_type_from_tokens(&types)
            }
            CombIR::Named { name, .. } => self.named_borrow_type_tokens(name),
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.borrow_type_tokens(inner),
            CombIR::Tag { .. } => quote! { () },
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        }
    }

    fn collect_field_exprs(&self, comb: &CombIR, access: TokenStream) -> Vec<TokenStream> {
        let mut exprs = Vec::new();
        self.collect_field_exprs_inner(comb, access, &[], &mut exprs);
        exprs
    }

    fn collect_field_exprs_inner(
        &self,
        comb: &CombIR,
        access: TokenStream,
        dep_names: &[String],
        exprs: &mut Vec<TokenStream>,
    ) {
        match comb {
            CombIR::Tuple(elems) => {
                for (idx, (opt_name, elem)) in elems.iter().enumerate() {
                    let child_access = tuple_field_access(&access, elems.len(), idx);
                    let is_dep = idx < dep_names.len();
                    if !is_dep
                        && opt_name.is_none()
                        && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. })
                    {
                        self.collect_field_exprs_inner(elem, child_access, &[], exprs);
                    } else {
                        exprs.push(child_access);
                    }
                }
            }
            CombIR::Pair { fst, snd } => {
                self.collect_field_exprs_inner(
                    fst,
                    tuple_field_access(&access, 2, 0),
                    &snd.dep_names,
                    exprs,
                );
                self.collect_field_exprs_inner(
                    &snd.comb,
                    tuple_field_access(&access, 2, 1),
                    &[],
                    exprs,
                );
            }
            _ => exprs.push(access),
        }
    }

    fn build_raw_expr_from_fields(
        &self,
        comb: &CombIR,
        field_exprs: &[TokenStream],
    ) -> TokenStream {
        let mut next = 0;
        let expr = self.build_raw_expr_from_fields_inner(comb, field_exprs, &mut next, &[]);
        debug_assert_eq!(next, field_exprs.len());
        expr
    }

    fn build_raw_expr_from_fields_inner(
        &self,
        comb: &CombIR,
        field_exprs: &[TokenStream],
        next: &mut usize,
        dep_names: &[String],
    ) -> TokenStream {
        match comb {
            CombIR::Tuple(elems) => {
                let exprs: Vec<TokenStream> = elems
                    .iter()
                    .enumerate()
                    .map(|(idx, (opt_name, elem))| {
                        let is_dep = idx < dep_names.len();
                        if !is_dep
                            && opt_name.is_none()
                            && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. })
                        {
                            self.build_raw_expr_from_fields_inner(elem, field_exprs, next, &[])
                        } else {
                            let expr = field_exprs[*next].clone();
                            *next += 1;
                            expr
                        }
                    })
                    .collect();
                build_nested_pair_expr(&exprs)
            }
            CombIR::Pair { fst, snd } => build_nested_pair_expr(&[
                self.build_raw_expr_from_fields_inner(fst, field_exprs, next, &snd.dep_names),
                self.build_raw_expr_from_fields_inner(&snd.comb, field_exprs, next, &[]),
            ]),
            _ => {
                let expr = field_exprs[*next].clone();
                *next += 1;
                expr
            }
        }
    }

    fn field_borrow_expr(&self, access: TokenStream, comb: &CombIR) -> TokenStream {
        match comb {
            CombIR::Tag { .. } => quote! { () },
            CombIR::Tuple(elems) => {
                let exprs: Vec<TokenStream> = elems
                    .iter()
                    .enumerate()
                    .map(|(idx, (_, elem))| {
                        self.field_borrow_expr(tuple_field_access(&access, elems.len(), idx), elem)
                    })
                    .collect();
                build_nested_pair_expr(&exprs)
            }
            CombIR::Pair { fst, snd } => build_nested_pair_expr(&[
                self.field_borrow_expr(tuple_field_access(&access, 2, 0), fst),
                self.field_borrow_expr(tuple_field_access(&access, 2, 1), &snd.comb),
            ]),
            CombIR::RepeatN { .. } | CombIR::Repeat(..) => quote! { #access.as_slice() },
            CombIR::Named { name, .. } if self.defs.contains_key(name) => {
                if self.def_borrow_by_value(name) {
                    access
                } else {
                    quote! { &#access }
                }
            }
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.field_borrow_expr(access, inner),
            _ => access,
        }
    }

    fn field_from_expr(&self, expr: TokenStream, comb: &CombIR) -> TokenStream {
        match comb {
            CombIR::Tag { value, .. } => self
                .nominal_tag_value_tokens(value)
                .unwrap_or_else(|| quote! { () }),
            CombIR::Named { .. } => expr,
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.field_from_expr(expr, inner),
            _ => expr,
        }
    }

    fn variant_borrow_expr(&self, binding: &Ident, comb: &CombIR) -> TokenStream {
        match comb {
            CombIR::Tag { .. } => quote! { () },
            CombIR::Named { name, .. } if self.defs.contains_key(name) => {
                if self.def_borrow_by_value(name) {
                    quote! { *#binding }
                } else {
                    quote! { #binding }
                }
            }
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.variant_borrow_expr(binding, inner),
            _ => quote! { *#binding },
        }
    }

    /// Generate a struct type and its conversions.
    fn generate_struct_type(&mut self, name: &str, comb: &CombIR, fields: &[FieldInfo]) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
        let borrow_by_value = self.comb_borrow_by_value(comb);

        // Generate field definitions
        let field_defs: Vec<TokenStream> = fields
            .iter()
            .map(|f| {
                let fname = format_ident!("{}", f.name);
                let ftype = self.nominal_type_tokens(&f.comb, false);
                quote! { pub #fname: #ftype }
            })
            .collect();

        let field_defs_owned: Vec<TokenStream> = fields
            .iter()
            .map(|f| {
                let fname = format_ident!("{}", f.name);
                let ftype = self.nominal_type_tokens(&f.comb, true);
                quote! { pub #fname: #ftype }
            })
            .collect();

        // Check if we need lifetime (if any field contains a byte slice)
        let needs_lifetime = fields.iter().any(|f| self.comb_needs_lifetime(&f.comb));

        // Borrowed struct
        let struct_def = if needs_lifetime {
            let derives = if borrow_by_value {
                quote! { #[derive(Debug, Clone, Copy, PartialEq, Eq)] }
            } else {
                quote! { #[derive(Debug, Clone, PartialEq, Eq)] }
            };
            quote! {
                #derives
                pub struct #type_name<'a> {
                    #(#field_defs),*
                }
            }
        } else {
            let derives = if borrow_by_value {
                quote! { #[derive(Debug, Clone, Copy, PartialEq, Eq)] }
            } else {
                quote! { #[derive(Debug, Clone, PartialEq, Eq)] }
            };
            quote! {
                #derives
                pub struct #type_name {
                    #(#field_defs),*
                }
            }
        };

        // Owned struct (for generation)
        let owned_struct_def = if needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub struct #owned_name {
                    #(#field_defs_owned),*
                }
            }
        } else {
            // If no lifetime needed, owned type is same as borrowed
            quote! {}
        };

        self.type_items.push(struct_def);
        if needs_lifetime {
            self.type_items.push(owned_struct_def);
        }

        // Generate From impls
        self.generate_struct_from_impls(name, comb, fields, needs_lifetime, borrow_by_value);

        // Generate Mapper
        self.generate_struct_mapper(name, comb, needs_lifetime, borrow_by_value);
    }

    /// Generate From implementations for struct <-> tuple conversion.
    fn generate_struct_from_impls(
        &mut self,
        name: &str,
        comb: &CombIR,
        fields: &[FieldInfo],
        needs_lifetime: bool,
        borrow_by_value: bool,
    ) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));

        let field_names: Vec<Ident> = fields.iter().map(|f| format_ident!("{}", f.name)).collect();

        let tuple_type = self.parse_type_tokens_with_lt(comb, quote! { 'a });
        let tuple_type_borrow = self.borrow_type_tokens(comb);
        let tuple_type_owned = self.owned_type_tokens(comb);
        let tuple_exprs = self.collect_field_exprs(comb, quote! { src });

        // From<tuple> for Struct (forward conversion for parsing)
        let from_tuple = if needs_lifetime {
            let field_assigns: Vec<TokenStream> = field_names
                .iter()
                .zip(fields.iter())
                .zip(tuple_exprs.iter())
                .map(|((fname, field), expr)| {
                    let value = self.field_from_expr(expr.clone(), &field.comb);
                    quote! { #fname: #value }
                })
                .collect();

            quote! {
                impl<'a> From<#tuple_type> for #type_name<'a> {
                    fn from(src: #tuple_type) -> Self {
                        Self { #(#field_assigns),* }
                    }
                }
            }
        } else {
            let field_assigns: Vec<TokenStream> = field_names
                .iter()
                .zip(fields.iter())
                .zip(tuple_exprs.iter())
                .map(|((fname, field), expr)| {
                    let value = self.field_from_expr(expr.clone(), &field.comb);
                    quote! { #fname: #value }
                })
                .collect();

            quote! {
                impl From<#tuple_type> for #type_name {
                    fn from(src: #tuple_type) -> Self {
                        Self { #(#field_assigns),* }
                    }
                }
            }
        };

        // From<&Struct> for tuple (backward conversion for serialization)
        let from_struct = if needs_lifetime && !borrow_by_value {
            let field_exprs: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
                .collect();
            let tuple_expr = self.build_raw_expr_from_fields(comb, &field_exprs);
            quote! {
                impl<'s, 'a: 's> From<&'s #type_name<'a>> for #tuple_type_borrow {
                    fn from(v: &'s #type_name<'a>) -> Self {
                        #tuple_expr
                    }
                }
            }
        } else if !borrow_by_value {
            let field_exprs: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
                .collect();
            let tuple_expr = self.build_raw_expr_from_fields(comb, &field_exprs);
            quote! {
                impl<'s> From<&'s #type_name> for #tuple_type_borrow {
                    fn from(v: &'s #type_name) -> Self {
                        #tuple_expr
                    }
                }
            }
        } else if needs_lifetime {
            let field_exprs: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
                .collect();
            let tuple_expr = self.build_raw_expr_from_fields(comb, &field_exprs);
            quote! {
                impl<'s> From<#type_name<'s>> for #tuple_type_borrow {
                    fn from(v: #type_name<'s>) -> Self {
                        #tuple_expr
                    }
                }
            }
        } else {
            let field_exprs: Vec<TokenStream> = fields
                .iter()
                .zip(field_names.iter())
                .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
                .collect();
            let tuple_expr = self.build_raw_expr_from_fields(comb, &field_exprs);
            quote! {
                impl<'s> From<#type_name> for #tuple_type_borrow {
                    fn from(v: #type_name) -> Self {
                        #tuple_expr
                    }
                }
            }
        };

        self.from_impls.push(from_tuple);
        self.from_impls.push(from_struct);

        // Owned conversions
        if needs_lifetime {
            let field_assigns_owned: Vec<TokenStream> = field_names
                .iter()
                .zip(fields.iter())
                .zip(tuple_exprs.iter())
                .map(|((fname, field), expr)| {
                    let value = self.field_from_expr(expr.clone(), &field.comb);
                    quote! { #fname: #value }
                })
                .collect();

            let from_tuple_owned = quote! {
                impl From<#tuple_type_owned> for #owned_name {
                    fn from(src: #tuple_type_owned) -> Self {
                        Self { #(#field_assigns_owned),* }
                    }
                }
            };
            self.from_impls.push(from_tuple_owned);
        }
    }

    /// Generate a Mapper struct for the type.
    fn generate_struct_mapper(
        &mut self,
        name: &str,
        comb: &CombIR,
        needs_lifetime: bool,
        borrow_by_value: bool,
    ) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
        let mapper_name = format_ident!("{}Mapper", snake_to_upper_camel(name));

        let tuple_type = self.parse_type_tokens_with_lt(comb, quote! { 'p });
        let tuple_type_borrow = self.borrow_type_tokens(comb);
        let tuple_type_owned = self.owned_type_tokens(comb);

        let mapper_impl = if needs_lifetime {
            let dst_borrow = if borrow_by_value {
                quote! { #type_name<'s> }
            } else {
                quote! { &'s #type_name<'s> }
            };
            quote! {
                pub struct #mapper_name;

                impl Mapper for #mapper_name {
                    type Src<'p> = #tuple_type;
                    type Dst<'p> = #type_name<'p>;
                    type SrcBorrow<'s> = #tuple_type_borrow;
                    type DstBorrow<'s> = #dst_borrow;
                    type SrcOwned = #tuple_type_owned;
                    type DstOwned = #owned_name;
                }
            }
        } else {
            let dst_borrow = if borrow_by_value {
                quote! { #type_name }
            } else {
                quote! { &'s #type_name }
            };
            quote! {
                pub struct #mapper_name;

                impl Mapper for #mapper_name {
                    type Src<'p> = #tuple_type;
                    type Dst<'p> = #type_name;
                    type SrcBorrow<'s> = #tuple_type_borrow;
                    type DstBorrow<'s> = #dst_borrow;
                    type SrcOwned = #tuple_type_owned;
                    type DstOwned = #type_name;
                }
            }
        };

        self.mapper_items.push(mapper_impl);
    }

    /// Generate an enum type for dispatch variants.
    fn generate_enum_type(&mut self, name: &str, variants: &[VariantInfo]) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));

        // Check if we need lifetime
        let needs_lifetime = variants.iter().any(|v| self.comb_needs_lifetime(&v.comb));

        // Generate variant definitions
        let variant_defs: Vec<TokenStream> = variants
            .iter()
            .map(|v| {
                let vname = format_ident!("{}", v.name);
                let vtype = self.nominal_type_tokens(&v.comb, false);
                quote! { #vname(#vtype) }
            })
            .collect();

        let variant_defs_owned: Vec<TokenStream> = variants
            .iter()
            .map(|v| {
                let vname = format_ident!("{}", v.name);
                let vtype = self.nominal_type_tokens(&v.comb, true);
                quote! { #vname(#vtype) }
            })
            .collect();

        // Borrowed enum
        let enum_def = if needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #type_name<'a> {
                    #(#variant_defs),*
                }
            }
        } else {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #type_name {
                    #(#variant_defs),*
                }
            }
        };

        // Owned enum
        let owned_enum_def = if needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #owned_name {
                    #(#variant_defs_owned),*
                }
            }
        } else {
            quote! {}
        };

        self.type_items.push(enum_def);
        if needs_lifetime {
            self.type_items.push(owned_enum_def);
        }

        // Generate From impls for enum
        self.generate_enum_from_impls(name, variants, needs_lifetime);
        self.generate_enum_mapper(name, variants, needs_lifetime);
    }

    /// Generate From implementations for enum <-> Either conversion.
    fn generate_enum_from_impls(
        &mut self,
        name: &str,
        variants: &[VariantInfo],
        needs_lifetime: bool,
    ) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));

        // Build nested Either type
        let either_type = build_nested_variant_type_with(variants, |variant| {
            self.parse_type_tokens_with_lt(&variant.comb, quote! { 'a })
        });
        let either_type_borrow = build_nested_variant_type_with(variants, |variant| {
            self.borrow_type_tokens(&variant.comb)
        });
        let either_type_owned = build_nested_variant_type_with(variants, |variant| {
            self.owned_type_tokens(&variant.comb)
        });

        // Generate From<Either<...>> for Enum
        let from_either_arms: Vec<TokenStream> = variants
            .iter()
            .enumerate()
            .map(|(idx, v)| {
                let vname = format_ident!("{}", v.name);
                let pattern = either_pattern(idx, variants.len());
                let value = self.field_from_expr(quote! { v }, &v.comb);
                quote! { #pattern => #type_name::#vname(#value) }
            })
            .collect();

        let from_either = if needs_lifetime {
            quote! {
                impl<'a> From<#either_type> for #type_name<'a> {
                    fn from(e: #either_type) -> Self {
                        match e {
                            #(#from_either_arms),*
                        }
                    }
                }
            }
        } else {
            quote! {
                impl From<#either_type> for #type_name {
                    fn from(e: #either_type) -> Self {
                        match e {
                            #(#from_either_arms),*
                        }
                    }
                }
            }
        };

        // Generate From<&Enum> for Either
        let to_either_arms: Vec<TokenStream> = variants
            .iter()
            .enumerate()
            .map(|(idx, v)| {
                let vname = format_ident!("{}", v.name);
                let wrap = either_wrap_expr(
                    idx,
                    variants.len(),
                    self.variant_borrow_expr(&format_ident!("v"), &v.comb),
                );
                quote! { #type_name::#vname(v) => #wrap }
            })
            .collect();

        let to_either = if needs_lifetime {
            quote! {
                impl<'s, 'a: 's> From<&'s #type_name<'a>> for #either_type_borrow {
                    fn from(e: &'s #type_name<'a>) -> Self {
                        match e {
                            #(#to_either_arms),*
                        }
                    }
                }
            }
        } else {
            quote! {
                impl<'s> From<&'s #type_name> for #either_type_borrow {
                    fn from(e: &'s #type_name) -> Self {
                        match e {
                            #(#to_either_arms),*
                        }
                    }
                }
            }
        };

        self.from_impls.push(from_either);
        self.from_impls.push(to_either);

        // Owned conversion
        if needs_lifetime {
            let from_either_arms_owned: Vec<TokenStream> = variants
                .iter()
                .enumerate()
                .map(|(idx, v)| {
                    let vname = format_ident!("{}", v.name);
                    let pattern = either_pattern(idx, variants.len());
                    let value = self.field_from_expr(quote! { v }, &v.comb);
                    quote! { #pattern => #owned_name::#vname(#value) }
                })
                .collect();

            let from_either_owned = quote! {
                impl From<#either_type_owned> for #owned_name {
                    fn from(e: #either_type_owned) -> Self {
                        match e {
                            #(#from_either_arms_owned),*
                        }
                    }
                }
            };
            self.from_impls.push(from_either_owned);
        }
    }

    fn generate_enum_mapper(&mut self, name: &str, variants: &[VariantInfo], needs_lifetime: bool) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
        let mapper_name = format_ident!("{}Mapper", snake_to_upper_camel(name));

        let either_type = build_nested_variant_type_with(variants, |variant| {
            self.parse_type_tokens_with_lt(&variant.comb, quote! { 'p })
        });
        let either_type_borrow = build_nested_variant_type_with(variants, |variant| {
            self.borrow_type_tokens(&variant.comb)
        });
        let either_type_owned = build_nested_variant_type_with(variants, |variant| {
            self.owned_type_tokens(&variant.comb)
        });

        let mapper_impl = if needs_lifetime {
            quote! {
                pub struct #mapper_name;

                impl Mapper for #mapper_name {
                    type Src<'p> = #either_type;
                    type Dst<'p> = #type_name<'p>;
                    type SrcBorrow<'s> = #either_type_borrow;
                    type DstBorrow<'s> = &'s #type_name<'s>;
                    type SrcOwned = #either_type_owned;
                    type DstOwned = #owned_name;
                }
            }
        } else {
            quote! {
                pub struct #mapper_name;

                impl Mapper for #mapper_name {
                    type Src<'p> = #either_type;
                    type Dst<'p> = #type_name;
                    type SrcBorrow<'s> = #either_type_borrow;
                    type DstBorrow<'s> = &'s #type_name;
                    type SrcOwned = #either_type_owned;
                    type DstOwned = #type_name;
                }
            }
        };

        self.mapper_items.push(mapper_impl);
    }
}

pub(crate) fn concrete_parse_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    comb: &CombIR,
    lt: TokenStream,
) -> TokenStream {
    NominalTypeGen::new(def, defs).parse_type_tokens_with_lt(comb, lt)
}

pub(crate) fn concrete_borrow_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    comb: &CombIR,
) -> TokenStream {
    NominalTypeGen::new(def, defs).borrow_type_tokens(comb)
}

pub(crate) fn concrete_owned_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    comb: &CombIR,
) -> TokenStream {
    NominalTypeGen::new(def, defs).owned_type_tokens(comb)
}

pub(crate) fn public_parse_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    lt: TokenStream,
) -> TokenStream {
    let gen = NominalTypeGen::new(def, defs);
    let type_name = format_ident!("{}", snake_to_upper_camel(&def.name));

    if gen.comb_needs_lifetime(&def.body) {
        quote! { #type_name<#lt> }
    } else {
        quote! { #type_name }
    }
}

pub(crate) fn public_borrow_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
) -> TokenStream {
    let gen = NominalTypeGen::new(def, defs);
    let type_name = format_ident!("{}", snake_to_upper_camel(&def.name));

    match gen.top_level_nominal_kind(&def.body) {
        TopLevelNominalKind::Struct {
            needs_lifetime,
            borrow_by_value,
        } => {
            if borrow_by_value {
                if needs_lifetime {
                    quote! { #type_name<'s> }
                } else {
                    quote! { #type_name }
                }
            } else if needs_lifetime {
                quote! { &'s #type_name<'s> }
            } else {
                quote! { &'s #type_name }
            }
        }
        TopLevelNominalKind::Enum { needs_lifetime } => {
            if needs_lifetime {
                quote! { &'s #type_name<'s> }
            } else {
                quote! { &'s #type_name }
            }
        }
        TopLevelNominalKind::Alias => concrete_borrow_type_tokens(def, defs, &def.body),
    }
}

pub(crate) fn public_owned_type_tokens(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
) -> TokenStream {
    let gen = NominalTypeGen::new(def, defs);
    let type_name = format_ident!("{}", snake_to_upper_camel(&def.name));
    let owned_name = format_ident!("{}Owned", snake_to_upper_camel(&def.name));

    if gen.comb_needs_lifetime(&def.body) {
        quote! { #owned_name }
    } else {
        quote! { #type_name }
    }
}

// ===== Helper Functions =====

/// Convert a snake_case name to UpperCamelCase.
pub(crate) fn snake_to_upper_camel(s: &str) -> String {
    s.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().chain(chars).collect(),
                None => String::new(),
            }
        })
        .collect()
}

fn build_nested_pair_type_from_tokens(types: &[TokenStream]) -> TokenStream {
    if types.is_empty() {
        quote! { () }
    } else if types.len() == 1 {
        types[0].clone()
    } else {
        let first = &types[0];
        let rest = build_nested_pair_type_from_tokens(&types[1..]);
        quote! { (#first, #rest) }
    }
}

fn build_nested_pair_expr(exprs: &[TokenStream]) -> TokenStream {
    if exprs.is_empty() {
        quote! { () }
    } else if exprs.len() == 1 {
        exprs[0].clone()
    } else {
        let first = &exprs[0];
        let rest = build_nested_pair_expr(&exprs[1..]);
        quote! { (#first, #rest) }
    }
}

fn tuple_field_access(base: &TokenStream, total: usize, index: usize) -> TokenStream {
    if total <= 1 {
        return base.clone();
    }
    if index == 0 {
        quote! { #base.0 }
    } else {
        let mut access = quote! { #base.1 };
        for _ in 1..index {
            access = quote! { #access.1 };
        }
        if index < total - 1 {
            quote! { #access.0 }
        } else {
            access
        }
    }
}

fn build_nested_variant_type_with<F>(variants: &[VariantInfo], mut f: F) -> TokenStream
where
    F: FnMut(&VariantInfo) -> TokenStream,
{
    if variants.is_empty() {
        return quote! { () };
    }
    if variants.len() == 1 {
        return f(&variants[0]);
    }

    let types: Vec<TokenStream> = variants.iter().map(&mut f).collect();
    build_nested_either_type_from_tokens(&types)
}

/// Generate Either pattern for matching nth variant.
fn either_pattern(idx: usize, total: usize) -> TokenStream {
    if total == 1 {
        return quote! { v };
    }

    // For index 0: Either::Left(v)
    // For index 1 with 2 total: Either::Right(v)
    // For index 1 with 3 total: Either::Right(Either::Left(v))
    // For index 2 with 3 total: Either::Right(Either::Right(v))

    if idx == 0 {
        quote! { Either::Left(v) }
    } else if idx == total - 1 {
        // Last element: nested Rights then the value
        let mut pattern = quote! { v };
        for _ in 0..idx {
            pattern = quote! { Either::Right(#pattern) };
        }
        pattern
    } else {
        // Middle element: Rights then Left
        let mut pattern = quote! { Either::Left(v) };
        for _ in 0..idx {
            pattern = quote! { Either::Right(#pattern) };
        }
        pattern
    }
}

/// Generate Either wrapper expression for nth variant.
fn either_wrap_expr(idx: usize, total: usize, expr: TokenStream) -> TokenStream {
    if total == 1 {
        return expr;
    }

    if idx == 0 {
        quote! { Either::Left(#expr) }
    } else if idx == total - 1 {
        let mut wrap = expr;
        for _ in 0..idx {
            wrap = quote! { Either::Right(#wrap) };
        }
        wrap
    } else {
        let mut wrap = quote! { Either::Left(#expr) };
        for _ in 0..idx {
            wrap = quote! { Either::Right(#wrap) };
        }
        wrap
    }
}

// ===== Dispatch Value Enum Generation =====

/// Generate named dispatch value enums for use with `enum_combinator!` macro.
///
/// This generates:
/// - `{dispatch_name}Value<'p>` - enum with lifetime for parsed values
/// - `{dispatch_name}ValueOwned` - enum without lifetime for generated/owned values
///
/// The variant names come from the dispatch case identifiers, and the inner types
/// are derived from the inner combinator's Type/GType.
///
/// # Example Output
/// ```ignore
/// pub enum MsgValue<'p> {
///     Msg1(&'p [u8; 32]),
///     Msg2(Msg2<'p>),
///     Msg3(Msg3),
/// }
///
/// pub enum MsgValueOwned {
///     Msg1(Vec<u8>),
///     Msg2(Msg2Owned),
///     Msg3(Msg3),
/// }
/// ```
pub fn generate_dispatch_value_enums(
    dispatch_name: &str,
    cases: &[(String, CombIR)],
    def_map: &HashMap<String, &CombDef>,
) -> TokenStream {
    if cases.is_empty() {
        return quote! {};
    }

    let type_name = format_ident!("{}Value", snake_to_upper_camel(dispatch_name));
    let owned_name = format_ident!("{}ValueOwned", snake_to_upper_camel(dispatch_name));

    // Check if any variant needs a lifetime
    let needs_lifetime = cases
        .iter()
        .any(|(_, comb)| comb_needs_lifetime(comb, def_map));

    // Generate variant definitions for borrowed enum
    let variant_defs: Vec<TokenStream> = cases
        .iter()
        .map(|(name, comb)| {
            let vname = format_ident!("{}", snake_to_upper_camel(name));
            let vtype = dispatch_value_type_tokens(comb, def_map, false);
            quote! { #vname(#vtype) }
        })
        .collect();

    // Generate variant definitions for owned enum
    let variant_defs_owned: Vec<TokenStream> = cases
        .iter()
        .map(|(name, comb)| {
            let vname = format_ident!("{}", snake_to_upper_camel(name));
            let vtype = dispatch_value_type_tokens(comb, def_map, true);
            quote! { #vname(#vtype) }
        })
        .collect();

    // Borrowed enum
    let enum_def = if needs_lifetime {
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum #type_name<'a> {
                #(#variant_defs),*
            }
        }
    } else {
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum #type_name {
                #(#variant_defs),*
            }
        }
    };

    // Owned enum (only if we need lifetime, otherwise borrowed and owned are the same)
    let owned_enum_def = if needs_lifetime {
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq)]
            pub enum #owned_name {
                #(#variant_defs_owned),*
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #enum_def
        #owned_enum_def
    }
}

/// Generate the value type tokens for a dispatch variant's inner combinator.
///
/// This determines the appropriate Rust type for the parsed/generated value:
/// - Primitives (u8, u16, etc.) -> use the type directly
/// - Fixed bytes -> `&'a [u8]` (borrowed) or `Vec<u8>` (owned)
/// - Variable bytes -> `&'a [u8]` (borrowed) or `Vec<u8>` (owned)
/// - Named references -> `XxxType<'a>` (borrowed) or `XxxTypeOwned` (owned)
fn dispatch_value_type_tokens(
    comb: &CombIR,
    def_map: &HashMap<String, &CombDef>,
    owned: bool,
) -> TokenStream {
    match comb {
        // Primitive integers - no lifetime needed
        CombIR::U8 => quote! { u8 },
        CombIR::U16(_) => quote! { u16 },
        CombIR::U24(_) => quote! { u24 },
        CombIR::U32(_) => quote! { u32 },
        CombIR::U64(_) => quote! { u64 },

        // Fixed-length bytes
        CombIR::Fixed { .. } => {
            if owned {
                quote! { Vec<u8> }
            } else {
                quote! { &'a [u8] }
            }
        }

        // Variable-length bytes
        CombIR::Variable { .. } | CombIR::Tail => {
            if owned {
                quote! { Vec<u8> }
            } else {
                quote! { &'a [u8] }
            }
        }

        // Tuple types
        CombIR::Tuple(elems) => {
            if elems.is_empty() {
                quote! { () }
            } else if elems.len() == 1 {
                dispatch_value_type_tokens(&elems[0].1, def_map, owned)
            } else {
                let types: Vec<TokenStream> = elems
                    .iter()
                    .map(|(_, elem)| dispatch_value_type_tokens(elem, def_map, owned))
                    .collect();
                quote! { (#(#types),*) }
            }
        }

        // Optional type
        CombIR::Opt(inner) => {
            let inner_ty = dispatch_value_type_tokens(inner, def_map, owned);
            quote! { Option<#inner_ty> }
        }

        // Repetition types
        CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
            let inner_ty = dispatch_value_type_tokens(inner, def_map, owned);
            quote! { Vec<#inner_ty> }
        }

        // Named reference - look up the referenced type
        CombIR::Named { name, .. } => {
            let type_name = format_ident!("{}", snake_to_upper_camel(name));
            // Check if the referenced type needs a lifetime
            let ref_needs_lt = def_map
                .get(name)
                .map(|def| comb_needs_lifetime(&def.body, def_map))
                .unwrap_or(false);

            if owned && ref_needs_lt {
                let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
                quote! { #owned_name }
            } else if ref_needs_lt {
                quote! { #type_name<'a> }
            } else {
                quote! { #type_name }
            }
        }

        // Modifiers - pass through to inner
        CombIR::Refined { inner, .. }
        | CombIR::Tag { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::AndThen { inner, .. } => dispatch_value_type_tokens(inner, def_map, owned),

        // Mapped types - use the inner combinator's type
        CombIR::Mapped { inner, .. } => dispatch_value_type_tokens(inner, def_map, owned),

        // Pair types - build nested tuple
        CombIR::Pair { fst, snd } => {
            let fst_ty = dispatch_value_type_tokens(fst, def_map, owned);
            let snd_ty = dispatch_value_type_tokens(&snd.comb, def_map, owned);
            quote! { (#fst_ty, #snd_ty) }
        }

        // Dispatch/Choice - nested Either types
        CombIR::Dispatch { branches, .. } => {
            let types: Vec<TokenStream> = branches
                .iter()
                .map(|(_, c)| dispatch_value_type_tokens(c, def_map, owned))
                .collect();
            build_nested_either_type_from_tokens(&types)
        }

        CombIR::Choice(choices) => {
            let types: Vec<TokenStream> = choices
                .iter()
                .map(|c| dispatch_value_type_tokens(c, def_map, owned))
                .collect();
            build_nested_either_type_from_tokens(&types)
        }

        // Other cases
        _ => quote! { () },
    }
}

/// Check if a combinator needs a lifetime parameter (for dispatch value enum generation).
fn comb_needs_lifetime(comb: &CombIR, def_map: &HashMap<String, &CombDef>) -> bool {
    match comb {
        // Byte types always need lifetime (they borrow from input)
        CombIR::Variable { .. } | CombIR::Tail | CombIR::Fixed { .. } => true,

        // Recurse into container types
        CombIR::Tuple(elems) => elems
            .iter()
            .any(|(_, elem)| comb_needs_lifetime(elem, def_map)),
        CombIR::Pair { fst, snd } => {
            comb_needs_lifetime(fst, def_map) || comb_needs_lifetime(&snd.comb, def_map)
        }
        CombIR::Opt(inner) | CombIR::Repeat(inner) | CombIR::RepeatN { inner, .. } => {
            comb_needs_lifetime(inner, def_map)
        }
        CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::Tag { inner, .. } => comb_needs_lifetime(inner, def_map),
        CombIR::Dispatch { branches, .. } => branches
            .iter()
            .any(|(_, c)| comb_needs_lifetime(c, def_map)),
        CombIR::Choice(choices) => choices.iter().any(|c| comb_needs_lifetime(c, def_map)),

        // Named references - look up the definition
        CombIR::Named { name, .. } => def_map
            .get(name)
            .map(|def| comb_needs_lifetime(&def.body, def_map))
            .unwrap_or(false),

        // Primitives don't need lifetime
        _ => false,
    }
}

/// Build nested Either type from a list of type tokens.
fn build_nested_either_type_from_tokens(types: &[TokenStream]) -> TokenStream {
    if types.is_empty() {
        return quote! { () };
    }
    if types.len() == 1 {
        return types[0].clone();
    }

    // Build right-nested Either: Either<A, Either<B, Either<C, D>>>
    let mut result = types.last().unwrap().clone();
    for ty in types.iter().rev().skip(1) {
        result = quote! { Either<#ty, #result> };
    }
    result
}

/// Extract case names and combinators from dispatch branches.
///
/// This converts `(TagValue, CombIR)` pairs into `(String, CombIR)` pairs
/// where the string is a suitable variant name derived from the tag value.
/// For integer tags, we use 0-indexed "Variant{i}" names for consistency with old codegen.
pub fn extract_dispatch_cases(branches: &[(TagValue, CombIR)]) -> Vec<(String, CombIR)> {
    branches
        .iter()
        .enumerate()
        .map(|(i, (tag, comb))| {
            let name = match tag {
                TagValue::Int(_) => format!("Variant{}", i),
                TagValue::Enum { variant, .. } => variant.clone(),
                TagValue::Bytes(bytes) => {
                    format!("Bytes{:02X?}", bytes).replace(['[', ']', ',', ' '], "")
                }
                TagValue::Wildcard => "Default".to_string(),
            };
            (name, comb.clone())
        })
        .collect()
}
