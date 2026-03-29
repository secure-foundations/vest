use proc_macro2::{Ident, Literal, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;

use super::builders::{
    build_nested_pair_expr, build_nested_pair_type as build_nested_pair_type_from_tokens,
};
use super::combir::{
    comb_needs_lifetime as shared_comb_needs_lifetime, CombDef, CombIR, DepCombIR, TagValue,
};

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub comb: CombIR,
}

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub tag: TagValue,
    pub comb: CombIR,
}

pub struct NominalTypeGen<'a> {
    pub def: &'a CombDef,
    pub defs: &'a HashMap<String, &'a CombDef>,
    pub type_items: Vec<TokenStream>,
    pub from_impls: Vec<TokenStream>,
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
    ValueEnum,
    Enum {
        needs_lifetime: bool,
    },
    Alias,
}

enum TypeFlavor {
    Nominal { owned: bool },
    Parse(TokenStream),
    Owned,
    Borrow,
}

fn nominal_wrapper_inner(comb: &CombIR) -> Option<&CombIR> {
    match comb {
        CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::AndThen { inner, .. } => Some(inner),
        _ => None,
    }
}

fn transparent_inner(comb: &CombIR) -> Option<&CombIR> {
    match comb {
        CombIR::Preceded { inner, .. }
        | CombIR::Terminated { inner, .. }
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. } => Some(inner),
        _ => None,
    }
}

fn borrowed_derives(copy: bool) -> TokenStream {
    if copy {
        quote! { #[derive(Debug, Clone, Copy, PartialEq, Eq)] }
    } else {
        quote! { #[derive(Debug, Clone, PartialEq, Eq)] }
    }
}

fn emit_mapper_item(
    mapper_name: &Ident,
    src: TokenStream,
    dst: TokenStream,
    src_borrow: TokenStream,
    dst_borrow: TokenStream,
    src_owned: TokenStream,
    dst_owned: TokenStream,
) -> TokenStream {
    quote! {
        pub struct #mapper_name;

        impl Mapper for #mapper_name {
            type Src<'p> = #src;
            type Dst<'p> = #dst;
            type SrcBorrow<'s> = #src_borrow;
            type DstBorrow<'s> = #dst_borrow;
            type SrcOwned = #src_owned;
            type DstOwned = #dst_owned;
        }
    }
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

    pub fn generate(&mut self) -> TokenStream {
        let sections = self.generate_sections();
        let type_items = sections.type_items;
        let support_items = sections.support_items;

        quote! {
            #type_items
            #support_items
        }
    }

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
            CombIR::Enum { .. } => TopLevelNominalKind::ValueEnum,
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

    fn generate_for_comb(&mut self, comb: &CombIR, name: &str) {
        match comb {
            CombIR::Tuple(elems) if !elems.is_empty() => {
                let mut fields = Vec::new();
                self.extract_fields_recursive(comb, &mut fields, &[]);
                self.generate_struct_type(name, comb, &fields);
            }

            CombIR::Pair { fst, snd } => {
                let fields = self.extract_pair_fields(fst, snd);
                if !fields.is_empty() {
                    self.generate_struct_type(name, comb, &fields);
                }
            }

            CombIR::Dispatch { tag: _, branches } => {
                let variants: Vec<VariantInfo> = branches
                    .iter()
                    .enumerate()
                    .map(|(i, (tag, c))| VariantInfo {
                        name: variant_name_from_tag(tag, i),
                        tag: tag.clone(),
                        comb: c.clone(),
                    })
                    .collect();
                self.generate_enum_type(name, &variants);
            }

            CombIR::Enum { variants, inner } => {
                self.generate_value_enum_type(name, inner, variants);
            }

            CombIR::Named { .. } => self.generate_alias_type(name, comb),

            _ if nominal_wrapper_inner(comb).is_some() => {
                let inner = nominal_wrapper_inner(comb).expect("checked above");
                self.generate_for_comb(inner, name);
            }

            _ => self.generate_alias_type(name, comb),
        }
    }

    fn extract_pair_fields(&self, fst: &CombIR, snd: &DepCombIR) -> Vec<FieldInfo> {
        let mut fields = Vec::new();
        self.extract_fields_recursive(fst, &mut fields, &snd.dep_names);
        self.extract_fields_recursive(&snd.comb, &mut fields, &[]);

        fields
    }

    fn extract_fields_recursive(
        &self,
        comb: &CombIR,
        fields: &mut Vec<FieldInfo>,
        dep_names: &[String],
    ) {
        match comb {
            CombIR::Tuple(elems) => {
                for (i, (opt_name, elem)) in elems.iter().enumerate() {
                    let is_dep = i < dep_names.len();
                    if !is_dep && opt_name.is_empty() && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. }) {
                        self.extract_fields_recursive(elem, fields, &[]);
                        continue;
                    }
                    let name = if is_dep {
                        dep_names[i].clone()
                    } else if !opt_name.is_empty() {
                        opt_name.clone()
                    } else {
                        format!("field{}", fields.len())
                    };
                    fields.push(FieldInfo {
                        name,
                        comb: elem.clone(),
                    });
                }
            }
            CombIR::Pair { fst, snd } => {
                self.extract_fields_recursive(fst, fields, &snd.dep_names);
                self.extract_fields_recursive(&snd.comb, fields, &[]);
            }
            _ => {
                let name = if !dep_names.is_empty() {
                    dep_names[0].clone()
                } else {
                    format!("field{}", fields.len())
                };
                fields.push(FieldInfo {
                    name,
                    comb: comb.clone(),
                });
            }
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
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                self.comb_borrow_by_value(inner)
            }
            CombIR::Preceded { .. }
            | CombIR::Terminated { .. }
            | CombIR::Refined { .. }
            | CombIR::Mapped { .. }
            | CombIR::AndThen { .. }
            | CombIR::FixedLen { .. } => {
                self.comb_borrow_by_value(transparent_inner(comb).expect("transparent wrapper"))
            }
            CombIR::Tag { inner, .. } => self.comb_borrow_by_value(inner),
            CombIR::Enum { .. } => true,
            CombIR::Named { name, .. } => self.def_borrow_by_value(name),
            CombIR::Pair { .. } | CombIR::Dispatch { .. } => false,
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
        shared_comb_needs_lifetime(comb, self.defs)
    }

    fn nominal_type_tokens(&self, comb: &CombIR, owned: bool) -> TokenStream {
        self.type_tokens_with_flavor(comb, &TypeFlavor::Nominal { owned })
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
        self.type_tokens_with_flavor(comb, &TypeFlavor::Parse(lt))
    }

    fn owned_type_tokens(&self, comb: &CombIR) -> TokenStream {
        self.type_tokens_with_flavor(comb, &TypeFlavor::Owned)
    }

    fn borrow_type_tokens(&self, comb: &CombIR) -> TokenStream {
        self.type_tokens_with_flavor(comb, &TypeFlavor::Borrow)
    }

    fn type_tokens_with_flavor(&self, comb: &CombIR, flavor: &TypeFlavor) -> TokenStream {
        if let Some(inner) = transparent_inner(comb) {
            return self.type_tokens_with_flavor(inner, flavor);
        }

        match comb {
            CombIR::U8 => quote! { u8 },
            CombIR::U16(_) => quote! { u16 },
            CombIR::U24(_) => quote! { u24 },
            CombIR::U32(_) => quote! { u32 },
            CombIR::U64(_) => quote! { u64 },
            CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => {
                self.bytes_type_tokens(flavor)
            }
            CombIR::Tuple(elems) => self.tuple_type_tokens(elems, flavor),
            CombIR::Pair { fst, snd } => {
                let fst_ty = self.type_tokens_with_flavor(fst, flavor);
                let snd_ty = self.type_tokens_with_flavor(&snd.comb, flavor);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.type_tokens_with_flavor(inner, flavor);
                quote! { Option<#inner_ty> }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.type_tokens_with_flavor(inner, flavor);
                match flavor {
                    TypeFlavor::Borrow => quote! { &'s [#inner_ty] },
                    _ => quote! { Vec<#inner_ty> },
                }
            }
            CombIR::Dispatch { .. } => self.dispatch_type_tokens_for_flavor(flavor),
            CombIR::Enum { inner, .. } => self.type_tokens_with_flavor(inner, flavor),
            CombIR::Named { name, .. } => self.named_type_tokens_for_flavor(name, flavor),
            CombIR::Preceded { .. }
            | CombIR::Terminated { .. }
            | CombIR::Refined { .. }
            | CombIR::Mapped { .. }
            | CombIR::AndThen { .. }
            | CombIR::FixedLen { .. } => self.type_tokens_with_flavor(
                transparent_inner(comb).expect("transparent wrapper"),
                flavor,
            ),
            CombIR::Tag { inner, value } => self.tag_type_tokens_for_flavor(inner, value, flavor),
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        }
    }

    fn tuple_type_tokens(
        &self,
        elems: &[(String, CombIR)],
        flavor: &TypeFlavor,
    ) -> TokenStream {
        match elems {
            [] => quote! { () },
            [(_, only)] => self.type_tokens_with_flavor(only, flavor),
            _ => {
                let types: Vec<TokenStream> = elems
                    .iter()
                    .map(|(_, elem)| self.type_tokens_with_flavor(elem, flavor))
                    .collect();
                build_nested_pair_type_from_tokens(&types)
            }
        }
    }

    fn bytes_type_tokens(&self, flavor: &TypeFlavor) -> TokenStream {
        match flavor {
            TypeFlavor::Nominal { owned: true } | TypeFlavor::Owned => quote! { Vec<u8> },
            TypeFlavor::Nominal { owned: false } => quote! { &'a [u8] },
            TypeFlavor::Parse(lt) => quote! { &#lt [u8] },
            TypeFlavor::Borrow => quote! { &'s [u8] },
        }
    }

    fn dispatch_type_tokens_for_flavor(&self, flavor: &TypeFlavor) -> TokenStream {
        let type_name = format_ident!("{}", snake_to_upper_camel(&self.def.name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(&self.def.name));
        let needs_lifetime = self.comb_needs_lifetime(&self.def.body);

        match flavor {
            TypeFlavor::Nominal { owned: false } => {
                if needs_lifetime {
                    quote! { #type_name<'a> }
                } else {
                    quote! { #type_name }
                }
            }
            TypeFlavor::Nominal { owned: true } | TypeFlavor::Owned => {
                if needs_lifetime {
                    quote! { #owned_name }
                } else {
                    quote! { #type_name }
                }
            }
            TypeFlavor::Parse(lt) => {
                if needs_lifetime {
                    quote! { #type_name<#lt> }
                } else {
                    quote! { #type_name }
                }
            }
            TypeFlavor::Borrow => {
                if needs_lifetime {
                    quote! { &'s #type_name<'s> }
                } else {
                    quote! { &'s #type_name }
                }
            }
        }
    }

    fn named_type_tokens_for_flavor(&self, name: &str, flavor: &TypeFlavor) -> TokenStream {
        match flavor {
            TypeFlavor::Nominal { owned } => {
                self.named_type_tokens(name, Some(quote! { 'a }), *owned)
            }
            TypeFlavor::Parse(lt) => self.named_type_tokens(name, Some(lt.clone()), false),
            TypeFlavor::Owned => self.named_type_tokens(name, None, true),
            TypeFlavor::Borrow => self.named_borrow_type_tokens(name),
        }
    }

    fn tag_type_tokens_for_flavor(
        &self,
        inner: &CombIR,
        value: &TagValue,
        flavor: &TypeFlavor,
    ) -> TokenStream {
        match flavor {
            TypeFlavor::Nominal { owned } => self
                .nominal_tag_type_tokens(inner, value, *owned)
                .unwrap_or_else(|| quote! { () }),
            TypeFlavor::Parse(_) | TypeFlavor::Owned | TypeFlavor::Borrow => quote! { () },
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
                    if !is_dep && opt_name.is_empty() && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. }) {
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
                        if !is_dep && opt_name.is_empty() && matches!(elem, CombIR::Tuple(_) | CombIR::Pair { .. }) {
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
        if let Some(inner) = transparent_inner(comb) {
            return self.field_borrow_expr(access, inner);
        }

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
            _ => access,
        }
    }

    fn field_from_expr(&self, expr: TokenStream, comb: &CombIR) -> TokenStream {
        if let Some(inner) = transparent_inner(comb) {
            return self.field_from_expr(expr, inner);
        }

        match comb {
            CombIR::Tag { value, .. } => self
                .nominal_tag_value_tokens(value)
                .unwrap_or_else(|| quote! { () }),
            CombIR::Named { .. } => expr,
            _ => expr,
        }
    }

    fn generate_struct_type(&mut self, name: &str, comb: &CombIR, fields: &[FieldInfo]) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));
        let borrow_by_value = self.comb_borrow_by_value(comb);

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

        let needs_lifetime = fields.iter().any(|f| self.comb_needs_lifetime(&f.comb));

        let derives = borrowed_derives(borrow_by_value);
        let struct_def = if needs_lifetime {
            quote! {
                #derives
                pub struct #type_name<'a> {
                    #(#field_defs),*
                }
            }
        } else {
            quote! {
                #derives
                pub struct #type_name {
                    #(#field_defs),*
                }
            }
        };

        let owned_struct_def = if needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub struct #owned_name {
                    #(#field_defs_owned),*
                }
            }
        } else {
            quote! {}
        };

        self.type_items.push(struct_def);
        if needs_lifetime {
            self.type_items.push(owned_struct_def);
        }

        self.generate_struct_from_impls(name, comb, fields, needs_lifetime, borrow_by_value);
        self.generate_struct_mapper(name, comb, needs_lifetime, borrow_by_value);
    }

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
        let field_assigns = self.build_field_assigns(&field_names, fields, &tuple_exprs);

        let from_tuple = if needs_lifetime {
            quote! {
                impl<'a> From<#tuple_type> for #type_name<'a> {
                    fn from(src: #tuple_type) -> Self {
                        Self { #(#field_assigns),* }
                    }
                }
            }
        } else {
            quote! {
                impl From<#tuple_type> for #type_name {
                    fn from(src: #tuple_type) -> Self {
                        Self { #(#field_assigns),* }
                    }
                }
            }
        };

        let field_exprs: Vec<TokenStream> = fields
            .iter()
            .zip(field_names.iter())
            .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
            .collect();
        let tuple_expr = self.build_raw_expr_from_fields(comb, &field_exprs);
        let from_struct = self.struct_to_tuple_impl(
            &type_name,
            &tuple_type_borrow,
            tuple_expr,
            needs_lifetime,
            borrow_by_value,
        );

        self.from_impls.push(from_tuple);
        self.from_impls.push(from_struct);

        if needs_lifetime {
            let field_assigns_owned = self.build_field_assigns(&field_names, fields, &tuple_exprs);

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

    fn build_field_assigns(
        &self,
        field_names: &[Ident],
        fields: &[FieldInfo],
        tuple_exprs: &[TokenStream],
    ) -> Vec<TokenStream> {
        field_names
            .iter()
            .zip(fields.iter())
            .zip(tuple_exprs.iter())
            .map(|((fname, field), expr)| {
                let value = self.field_from_expr(expr.clone(), &field.comb);
                quote! { #fname: #value }
            })
            .collect()
    }

    fn struct_to_tuple_impl(
        &self,
        type_name: &Ident,
        tuple_type_borrow: &TokenStream,
        tuple_expr: TokenStream,
        needs_lifetime: bool,
        borrow_by_value: bool,
    ) -> TokenStream {
        match (needs_lifetime, borrow_by_value) {
            (true, false) => quote! {
                impl<'s, 'a: 's> From<&'s #type_name<'a>> for #tuple_type_borrow {
                    fn from(v: &'s #type_name<'a>) -> Self {
                        #tuple_expr
                    }
                }
            },
            (false, false) => quote! {
                impl<'s> From<&'s #type_name> for #tuple_type_borrow {
                    fn from(v: &'s #type_name) -> Self {
                        #tuple_expr
                    }
                }
            },
            (true, true) => quote! {
                impl<'s> From<#type_name<'s>> for #tuple_type_borrow {
                    fn from(v: #type_name<'s>) -> Self {
                        #tuple_expr
                    }
                }
            },
            (false, true) => quote! {
                impl<'s> From<#type_name> for #tuple_type_borrow {
                    fn from(v: #type_name) -> Self {
                        #tuple_expr
                    }
                }
            },
        }
    }

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
            emit_mapper_item(
                &mapper_name,
                tuple_type,
                quote! { #type_name<'p> },
                tuple_type_borrow,
                dst_borrow,
                tuple_type_owned,
                quote! { #owned_name },
            )
        } else {
            let dst_borrow = if borrow_by_value {
                quote! { #type_name }
            } else {
                quote! { &'s #type_name }
            };
            emit_mapper_item(
                &mapper_name,
                tuple_type,
                quote! { #type_name },
                tuple_type_borrow,
                dst_borrow,
                tuple_type_owned,
                quote! { #type_name },
            )
        };

        self.mapper_items.push(mapper_impl);
    }

    fn generate_value_enum_type(
        &mut self,
        name: &str,
        inner: &CombIR,
        variants: &[(String, i128)],
    ) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let mapper_name = format_ident!("{}Mapper", snake_to_upper_camel(name));
        let raw_type = self.parse_type_tokens_with_lt(inner, quote! { 'p });

        let variant_defs: Vec<_> = variants
            .iter()
            .map(|(variant, value)| {
                let variant = format_ident!("{}", variant);
                let value = Literal::i128_unsuffixed(*value);
                quote! { #variant = #value }
            })
            .collect();
        let from_raw_arms: Vec<_> = variants
            .iter()
            .map(|(variant, value)| {
                let variant = format_ident!("{}", variant);
                let value = Literal::i128_unsuffixed(*value);
                quote! { #value => Self::#variant }
            })
            .collect();

        self.type_items.push(quote! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum #type_name {
                #(#variant_defs),*
            }
        });

        self.from_impls.push(quote! {
            impl From<#raw_type> for #type_name {
                fn from(src: #raw_type) -> Self {
                    match src as i128 {
                        #(#from_raw_arms,)*
                        _ => unreachable!("validated by combinator"),
                    }
                }
            }
        });
        self.from_impls.push(quote! {
            impl From<#type_name> for #raw_type {
                fn from(v: #type_name) -> Self {
                    v as #raw_type
                }
            }
        });

        self.mapper_items.push(emit_mapper_item(
            &mapper_name,
            raw_type.clone(),
            quote! { #type_name },
            raw_type.clone(),
            quote! { #type_name },
            raw_type,
            quote! { #type_name },
        ));
    }

    fn generate_enum_type(&mut self, name: &str, variants: &[VariantInfo]) {
        let type_name = format_ident!("{}", snake_to_upper_camel(name));
        let owned_name = format_ident!("{}Owned", snake_to_upper_camel(name));

        let needs_lifetime = variants.iter().any(|v| self.comb_needs_lifetime(&v.comb));

        let variant_defs: Vec<_> = variants
            .iter()
            .map(|variant| {
                let vname = format_ident!("{}", variant.name);
                let vtype = self.nominal_type_tokens(&variant.comb, false);
                quote! { #vname(#vtype) }
            })
            .collect();
        let variant_defs_owned: Vec<_> = variants
            .iter()
            .map(|variant| {
                let vname = format_ident!("{}", variant.name);
                let vtype = self.nominal_type_tokens(&variant.comb, true);
                quote! { #vname(#vtype) }
            })
            .collect();

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

pub(crate) fn concrete_field_from_expr(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    expr: TokenStream,
    comb: &CombIR,
) -> TokenStream {
    NominalTypeGen::new(def, defs).field_from_expr(expr, comb)
}

pub(crate) fn concrete_variant_borrow_expr(
    def: &CombDef,
    defs: &HashMap<String, &CombDef>,
    binding: &Ident,
    comb: &CombIR,
) -> TokenStream {
    NominalTypeGen::new(def, defs).field_borrow_expr(quote! { (*#binding) }, comb)
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
        TopLevelNominalKind::ValueEnum => quote! { #type_name },
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

pub(crate) fn variant_name_from_tag(tag: &TagValue, index: usize) -> String {
    match tag {
        TagValue::Int(_) => format!("Variant{}", index),
        TagValue::Enum { variant, .. } => variant.clone(),
        TagValue::Bytes(bytes) => format!("Bytes{:02X?}", bytes).replace(['[', ']', ',', ' '], ""),
        TagValue::Wildcard => "Default".to_string(),
    }
}
