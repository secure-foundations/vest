use std::collections::HashMap;

use proc_macro2::{Ident, Literal, TokenStream};
use quote::{format_ident, quote};

use super::super::{
    peel_wrappers_for, wrapper_inner_for, Analysis, AnalysisMap, CombDef, CombIR, WrapperUse,
};
use super::super::{DefinitionNames, EnumVariantIR, NamesMap, TagValue};
use super::module_emit::{
    build_nested_pair_expr, build_nested_pair_type, tuple_field_access, value_shape_borrow_expr_tokens,
    value_shape_field_expr_tokens,
};

#[derive(Debug, Clone)]
struct FieldInfo<'a> {
    name: String,
    comb: &'a CombIR,
}

#[derive(Debug, Clone)]
struct VariantInfo<'a> {
    name: String,
    comb: &'a CombIR,
}

#[derive(Debug, Clone)]
enum FieldShape<'a> {
    Leaf {
        name: Option<String>,
        comb: &'a CombIR,
    },
    Group(Vec<FieldShape<'a>>),
}

pub struct NominalSections {
    pub type_items: TokenStream,
    pub support_items: TokenStream,
}

enum TypeView {
    NominalBorrowed,
    NominalOwned,
    Parse(TokenStream),
    Owned,
    Borrow,
}

struct NominalCtx<'a> {
    def: &'a CombDef,
    defs: &'a HashMap<String, &'a CombDef>,
    analysis: &'a AnalysisMap,
    names: &'a NamesMap,
    type_items: Vec<TokenStream>,
    from_impls: Vec<TokenStream>,
    mapper_items: Vec<TokenStream>,
}

pub fn generate_nominal_sections(
    defs: &[CombDef],
    names: &NamesMap,
    analysis: &AnalysisMap,
) -> NominalSections {
    let def_map: HashMap<String, &CombDef> =
        defs.iter().map(|def| (def.name.clone(), def)).collect();
    let mut type_items = TokenStream::new();
    let mut support_items = TokenStream::new();

    for def in defs {
        let mut ctx = NominalCtx::new(def, &def_map, analysis, names);
        let sections = ctx.generate_sections();
        type_items.extend(sections.type_items);
        support_items.extend(sections.support_items);
    }

    NominalSections {
        type_items,
        support_items,
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

impl<'a> FieldShape<'a> {
    fn collect_fields(&self, fields: &mut Vec<FieldInfo<'a>>) {
        match self {
            FieldShape::Leaf { name, comb } => fields.push(FieldInfo {
                name: name
                    .clone()
                    .unwrap_or_else(|| format!("field{}", fields.len())),
                comb,
            }),
            FieldShape::Group(children) => {
                for child in children {
                    child.collect_fields(fields);
                }
            }
        }
    }

    fn collect_exprs(&self, access: TokenStream, exprs: &mut Vec<TokenStream>) {
        match self {
            FieldShape::Leaf { .. } => exprs.push(access),
            FieldShape::Group(children) => {
                for (idx, child) in children.iter().enumerate() {
                    child.collect_exprs(tuple_field_access(&access, children.len(), idx), exprs);
                }
            }
        }
    }

    fn build_expr(&self, field_exprs: &[TokenStream], next: &mut usize) -> TokenStream {
        match self {
            FieldShape::Leaf { .. } => {
                let expr = field_exprs[*next].clone();
                *next += 1;
                expr
            }
            FieldShape::Group(children) => {
                let exprs: Vec<_> = children
                    .iter()
                    .map(|child| child.build_expr(field_exprs, next))
                    .collect();
                build_nested_pair_expr(&exprs)
            }
        }
    }
}

impl<'a> NominalCtx<'a> {
    fn new(
        def: &'a CombDef,
        defs: &'a HashMap<String, &'a CombDef>,
        analysis: &'a AnalysisMap,
        names: &'a NamesMap,
    ) -> Self {
        Self {
            def,
            defs,
            analysis,
            names,
            type_items: Vec::new(),
            from_impls: Vec::new(),
            mapper_items: Vec::new(),
        }
    }

    fn generate_sections(&mut self) -> NominalSections {
        self.generate_for_comb(peel_wrappers_for(&self.def.body, WrapperUse::NominalRoot));
        let type_items = &self.type_items;
        let from_impls = &self.from_impls;
        let mapper_items = &self.mapper_items;

        NominalSections {
            type_items: quote! { #(#type_items)* },
            support_items: quote! { #(#from_impls)* #(#mapper_items)* },
        }
    }

    fn analysis_for(&self, name: &str) -> &Analysis {
        self.analysis
            .get(name)
            .expect("every named definition should have analysis")
    }

    fn names_for(&self, name: &str) -> &DefinitionNames {
        self.names
            .get(name)
            .expect("every named definition should have names")
    }

    fn generate_for_comb(&mut self, comb: &CombIR) {
        match comb {
            CombIR::Struct(_) | CombIR::Seq(_) | CombIR::DepPair { .. } => {
                let field_shape = self.field_shape(comb, &[]);
                let mut fields = Vec::new();
                field_shape.collect_fields(&mut fields);
                if !fields.is_empty() {
                    self.generate_struct_type(comb, &fields, &field_shape);
                } else {
                    self.generate_alias_type(comb);
                }
            }
            CombIR::Dispatch { branches, .. } => {
                let variants: Vec<_> = branches
                    .iter()
                    .map(|branch| VariantInfo {
                        name: branch.variant_name.clone(),
                        comb: &branch.comb,
                    })
                    .collect();
                self.generate_enum_type(&variants);
            }
            CombIR::Enum {
                inner, variants, ..
            } => self.generate_value_enum_type(inner, variants),
            _ => self.generate_alias_type(comb),
        }
    }

    fn generate_alias_type(&mut self, comb: &CombIR) {
        let names = self.names_for(&self.def.name).clone();
        let ty = self.nominal_type_tokens(comb, false);
        let needs_lifetime = self.analysis_for(&self.def.name).needs_lifetime;

        if needs_lifetime {
            let owned_ty = self.nominal_type_tokens(comb, true);
            let type_name = names.type_ident;
            let owned_name = names.owned_ident;
            self.type_items
                .push(quote! { pub type #type_name<'a> = #ty; });
            self.type_items
                .push(quote! { pub type #owned_name = #owned_ty; });
        } else {
            let type_name = names.type_ident;
            self.type_items.push(quote! { pub type #type_name = #ty; });
        }
    }

    fn field_shape<'b>(&self, comb: &'b CombIR, dep_names: &[String]) -> FieldShape<'b> {
        match comb {
            CombIR::Struct(items) => FieldShape::Group(
                items
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| FieldShape::Leaf {
                        name: Some(
                            dep_names
                                .get(idx)
                                .cloned()
                                .unwrap_or_else(|| field.name.clone()),
                        ),
                        comb: &field.comb,
                    })
                    .collect(),
            ),
            CombIR::Seq(items) => FieldShape::Group(
                items
                    .iter()
                    .map(|item| {
                        if is_nominal_field_group(item) {
                            self.field_shape(item, &[])
                        } else {
                            FieldShape::Leaf {
                                name: dep_names.first().cloned(),
                                comb: item,
                            }
                        }
                    })
                    .collect(),
            ),
            CombIR::DepPair {
                fst,
                fst_bindings,
                snd,
            } => FieldShape::Group(vec![
                self.field_shape(fst, fst_bindings),
                self.field_shape(snd, &[]),
            ]),
            _ => FieldShape::Leaf {
                name: dep_names.first().cloned(),
                comb,
            },
        }
    }

    fn nominal_type_tokens(&self, comb: &CombIR, owned: bool) -> TokenStream {
        let view = if owned {
            TypeView::NominalOwned
        } else {
            TypeView::NominalBorrowed
        };
        self.type_tokens_with_view(comb, &view)
    }

    fn parse_type_tokens_with_lt(&self, comb: &CombIR, lt: TokenStream) -> TokenStream {
        self.type_tokens_with_view(comb, &TypeView::Parse(lt))
    }

    fn owned_type_tokens(&self, comb: &CombIR) -> TokenStream {
        self.type_tokens_with_view(comb, &TypeView::Owned)
    }

    fn borrow_type_tokens(&self, comb: &CombIR) -> TokenStream {
        self.type_tokens_with_view(comb, &TypeView::Borrow)
    }

    fn named_type_tokens(&self, name: &str, lt: Option<TokenStream>, owned: bool) -> TokenStream {
        let names = self.names_for(name);
        let analysis = self.analysis_for(name);

        if owned && analysis.needs_lifetime {
            let owned_name = &names.owned_ident;
            quote! { #owned_name }
        } else if analysis.needs_lifetime {
            let type_name = &names.type_ident;
            let lt = lt.unwrap_or_else(|| quote! { 'a });
            quote! { #type_name<#lt> }
        } else {
            let type_name = &names.type_ident;
            quote! { #type_name }
        }
    }

    fn named_borrow_type_tokens(&self, name: &str) -> TokenStream {
        let ty = self.named_type_tokens(name, Some(quote! { 's }), false);
        if self.analysis_for(name).borrow_by_value {
            ty
        } else {
            quote! { &'s #ty }
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

    fn type_tokens_with_view(&self, comb: &CombIR, view: &TypeView) -> TokenStream {
        if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
            return self.type_tokens_with_view(inner, view);
        }

        match comb {
            CombIR::UInt(uint) => uint.rust_type_tokens(),
            CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => {
                self.bytes_type_tokens(view)
            }
            CombIR::Struct(fields) => self.seq_like_type_tokens(
                fields.iter().map(|field| &field.comb).collect(),
                view,
            ),
            CombIR::Seq(items) => self.seq_like_type_tokens(items.iter().collect(), view),
            CombIR::DepPair { fst, snd, .. } => {
                let fst_ty = self.type_tokens_with_view(fst, view);
                let snd_ty = self.type_tokens_with_view(snd, view);
                quote! { (#fst_ty, #snd_ty) }
            }
            CombIR::Opt(inner) => {
                let inner_ty = self.type_tokens_with_view(inner, view);
                quote! { Option<#inner_ty> }
            }
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                let inner_ty = self.type_tokens_with_view(inner, view);
                match view {
                    TypeView::Borrow => quote! { &'s [#inner_ty] },
                    _ => quote! { Vec<#inner_ty> },
                }
            }
            CombIR::Dispatch { .. } => self.dispatch_type_tokens_for_view(view),
            CombIR::Enum { inner, .. } => self.type_tokens_with_view(inner, view),
            CombIR::Named { name, .. } => self.named_type_tokens_for_view(name, view),
            CombIR::Tag { inner, value } => self.tag_type_tokens_for_view(inner, value, view),
            CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
            CombIR::Preceded { .. }
            | CombIR::Terminated { .. }
            | CombIR::Refined { .. }
            | CombIR::Mapped { .. }
            | CombIR::AndThen { .. }
            | CombIR::FixedLen { .. } => unreachable!("transparent wrappers handled above"),
        }
    }

    fn seq_like_type_tokens(&self, items: Vec<&CombIR>, view: &TypeView) -> TokenStream {
        if items.is_empty() {
            return quote! { () };
        }
        if items.len() == 1 {
            return self.type_tokens_with_view(items[0], view);
        }
        let types: Vec<_> = items
            .into_iter()
            .map(|item| self.type_tokens_with_view(item, view))
            .collect();
        build_nested_pair_type(&types)
    }

    fn bytes_type_tokens(&self, view: &TypeView) -> TokenStream {
        match view {
            TypeView::NominalOwned | TypeView::Owned => quote! { Vec<u8> },
            TypeView::NominalBorrowed => quote! { &'a [u8] },
            TypeView::Parse(lt) => quote! { &#lt [u8] },
            TypeView::Borrow => quote! { &'s [u8] },
        }
    }

    fn dispatch_type_tokens_for_view(&self, view: &TypeView) -> TokenStream {
        let names = self.names_for(&self.def.name);
        let analysis = self.analysis_for(&self.def.name);
        let type_name = &names.type_ident;
        let owned_name = &names.owned_ident;

        match view {
            TypeView::NominalBorrowed => {
                if analysis.needs_lifetime {
                    quote! { #type_name<'a> }
                } else {
                    quote! { #type_name }
                }
            }
            TypeView::NominalOwned | TypeView::Owned => {
                if analysis.needs_lifetime {
                    quote! { #owned_name }
                } else {
                    quote! { #type_name }
                }
            }
            TypeView::Parse(lt) => {
                if analysis.needs_lifetime {
                    quote! { #type_name<#lt> }
                } else {
                    quote! { #type_name }
                }
            }
            TypeView::Borrow => {
                if analysis.needs_lifetime {
                    quote! { &'s #type_name<'s> }
                } else {
                    quote! { &'s #type_name }
                }
            }
        }
    }

    fn named_type_tokens_for_view(&self, name: &str, view: &TypeView) -> TokenStream {
        match view {
            TypeView::NominalBorrowed => self.named_type_tokens(name, Some(quote! { 'a }), false),
            TypeView::NominalOwned => self.named_type_tokens(name, Some(quote! { 'a }), true),
            TypeView::Parse(lt) => self.named_type_tokens(name, Some(lt.clone()), false),
            TypeView::Owned => self.named_type_tokens(name, None, true),
            TypeView::Borrow => self.named_borrow_type_tokens(name),
        }
    }

    fn tag_type_tokens_for_view(
        &self,
        inner: &CombIR,
        value: &TagValue,
        view: &TypeView,
    ) -> TokenStream {
        match view {
            TypeView::NominalBorrowed => self
                .nominal_tag_type_tokens(inner, value, false)
                .unwrap_or_else(|| quote! { () }),
            TypeView::NominalOwned => self
                .nominal_tag_type_tokens(inner, value, true)
                .unwrap_or_else(|| quote! { () }),
            TypeView::Parse(_) | TypeView::Owned | TypeView::Borrow => quote! { () },
        }
    }

    fn collect_field_exprs(&self, shape: &FieldShape<'_>, access: TokenStream) -> Vec<TokenStream> {
        let mut exprs = Vec::new();
        shape.collect_exprs(access, &mut exprs);
        exprs
    }

    fn build_raw_expr_from_fields(
        &self,
        shape: &FieldShape<'_>,
        field_exprs: &[TokenStream],
    ) -> TokenStream {
        let mut next = 0;
        let expr = shape.build_expr(field_exprs, &mut next);
        debug_assert_eq!(next, field_exprs.len());
        expr
    }

    fn field_borrow_expr(&self, access: TokenStream, comb: &CombIR) -> TokenStream {
        value_shape_borrow_expr_tokens(access, comb, self.defs, self.analysis)
    }

    fn field_from_expr(&self, expr: TokenStream, comb: &CombIR) -> TokenStream {
        value_shape_field_expr_tokens(expr, comb, self.def, self.names)
    }

    fn generate_struct_type(
        &mut self,
        comb: &CombIR,
        fields: &[FieldInfo],
        field_shape: &FieldShape<'_>,
    ) {
        let names = self.names_for(&self.def.name).clone();
        let type_name = names.type_ident;
        let owned_name = names.owned_ident;
        let analysis = self.analysis_for(&self.def.name).clone();
        let borrow_by_value = analysis.borrow_by_value;

        let field_defs: Vec<_> = fields
            .iter()
            .map(|f| {
                let fname = format_ident!("{}", f.name);
                let ftype = self.nominal_type_tokens(&f.comb, false);
                quote! { pub #fname: #ftype }
            })
            .collect();
        let field_defs_owned: Vec<_> = fields
            .iter()
            .map(|f| {
                let fname = format_ident!("{}", f.name);
                let ftype = self.nominal_type_tokens(&f.comb, true);
                quote! { pub #fname: #ftype }
            })
            .collect();

        let derives = borrowed_derives(borrow_by_value);
        let struct_def = if analysis.needs_lifetime {
            quote! {
                #derives
                pub struct #type_name<'a> { #(#field_defs),* }
            }
        } else {
            quote! {
                #derives
                pub struct #type_name { #(#field_defs),* }
            }
        };
        let owned_struct_def = if analysis.needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub struct #owned_name { #(#field_defs_owned),* }
            }
        } else {
            quote! {}
        };

        self.type_items.push(struct_def);
        if analysis.needs_lifetime {
            self.type_items.push(owned_struct_def);
        }

        self.generate_struct_from_impls(comb, fields, field_shape);
        self.generate_struct_mapper(comb);
    }

    fn generate_struct_from_impls(
        &mut self,
        comb: &CombIR,
        fields: &[FieldInfo],
        field_shape: &FieldShape<'_>,
    ) {
        let names = self.names_for(&self.def.name).clone();
        let type_name = names.type_ident;
        let owned_name = names.owned_ident;
        let analysis = self.analysis_for(&self.def.name).clone();
        let field_names: Vec<Ident> = fields.iter().map(|f| format_ident!("{}", f.name)).collect();

        let tuple_type = self.parse_type_tokens_with_lt(comb, quote! { 'a });
        let tuple_type_borrow = self.borrow_type_tokens(comb);
        let tuple_type_owned = self.owned_type_tokens(comb);
        let tuple_exprs = self.collect_field_exprs(field_shape, quote! { src });
        let field_assigns = self.build_field_assigns(&field_names, fields, &tuple_exprs);

        let from_tuple = if analysis.needs_lifetime {
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

        let field_exprs: Vec<_> = fields
            .iter()
            .zip(field_names.iter())
            .map(|(field, name)| self.field_borrow_expr(quote! { v.#name }, &field.comb))
            .collect();
        let tuple_expr = self.build_raw_expr_from_fields(field_shape, &field_exprs);
        let from_struct = self.struct_to_tuple_impl(&type_name, &tuple_type_borrow, tuple_expr);

        self.from_impls.push(from_tuple);
        self.from_impls.push(from_struct);

        if analysis.needs_lifetime {
            let field_assigns_owned = self.build_field_assigns(&field_names, fields, &tuple_exprs);
            self.from_impls.push(quote! {
                impl From<#tuple_type_owned> for #owned_name {
                    fn from(src: #tuple_type_owned) -> Self {
                        Self { #(#field_assigns_owned),* }
                    }
                }
            });
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
    ) -> TokenStream {
        let analysis = self.analysis_for(&self.def.name);
        match (analysis.needs_lifetime, analysis.borrow_by_value) {
            (true, false) => quote! {
                impl<'s, 'a: 's> From<&'s #type_name<'a>> for #tuple_type_borrow {
                    fn from(v: &'s #type_name<'a>) -> Self { #tuple_expr }
                }
            },
            (false, false) => quote! {
                impl<'s> From<&'s #type_name> for #tuple_type_borrow {
                    fn from(v: &'s #type_name) -> Self { #tuple_expr }
                }
            },
            (true, true) => quote! {
                impl<'s> From<#type_name<'s>> for #tuple_type_borrow {
                    fn from(v: #type_name<'s>) -> Self { #tuple_expr }
                }
            },
            (false, true) => quote! {
                impl<'s> From<#type_name> for #tuple_type_borrow {
                    fn from(v: #type_name) -> Self { #tuple_expr }
                }
            },
        }
    }

    fn generate_struct_mapper(&mut self, comb: &CombIR) {
        let names = self.names_for(&self.def.name).clone();
        let type_name = names.type_ident;
        let owned_name = names.owned_ident;
        let mapper_name = names.mapper_ident;
        let analysis = self.analysis_for(&self.def.name).clone();

        let tuple_type = self.parse_type_tokens_with_lt(comb, quote! { 'p });
        let tuple_type_borrow = self.borrow_type_tokens(comb);
        let tuple_type_owned = self.owned_type_tokens(comb);

        let mapper_impl = if analysis.needs_lifetime {
            let dst_borrow = if analysis.borrow_by_value {
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
            let dst_borrow = if analysis.borrow_by_value {
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

    fn generate_value_enum_type(&mut self, inner: &CombIR, variants: &[EnumVariantIR]) {
        let names = self.names_for(&self.def.name).clone();
        let type_name = names.type_ident;
        let mapper_name = names.mapper_ident;
        let raw_type = self.parse_type_tokens_with_lt(inner, quote! { 'p });

        let variant_defs: Vec<_> = variants
            .iter()
            .map(|variant| {
                let variant_ident = format_ident!("{}", variant.name);
                let value = Literal::i128_unsuffixed(variant.value);
                quote! { #variant_ident = #value }
            })
            .collect();
        let from_raw_arms: Vec<_> = variants
            .iter()
            .map(|variant| {
                let variant_name = format_ident!("{}", variant.name);
                let value = Literal::i128_unsuffixed(variant.value);
                quote! { #value => Self::#variant_name }
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

    fn generate_enum_type(&mut self, variants: &[VariantInfo]) {
        let names = self.names_for(&self.def.name).clone();
        let type_name = names.type_ident;
        let owned_name = names.owned_ident;
        let analysis = self.analysis_for(&self.def.name).clone();

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

        let enum_def = if analysis.needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #type_name<'a> { #(#variant_defs),* }
            }
        } else {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #type_name { #(#variant_defs),* }
            }
        };
        let owned_enum_def = if analysis.needs_lifetime {
            quote! {
                #[derive(Debug, Clone, PartialEq, Eq)]
                pub enum #owned_name { #(#variant_defs_owned),* }
            }
        } else {
            quote! {}
        };

        self.type_items.push(enum_def);
        if analysis.needs_lifetime {
            self.type_items.push(owned_enum_def);
        }
    }
}

fn is_nominal_field_group(comb: &CombIR) -> bool {
    matches!(
        comb,
        CombIR::Struct(_) | CombIR::Seq(_) | CombIR::DepPair { .. }
    )
}
