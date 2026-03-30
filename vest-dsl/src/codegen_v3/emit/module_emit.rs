use std::collections::{HashMap, HashSet};
use std::error::Error;

use proc_macro2::{Ident, Literal, TokenStream};
use quote::{format_ident, quote};

use super::super::analysis::value_kind_for_comb;
use super::super::helper_specs::{self, collect_helper_specs, scoped_helper_ident, BindingEnv};
use super::super::rust_format::format_rust_code;
use super::super::{
    const_ident_for_int, peel_wrappers_for, snake_to_upper_camel, wrapper_inner_for, Analysis,
    AnalysisMap, CodegenPlan, CombDef, CombIR, ConstDef, DefinitionNames, EnumConstraintIR,
    IntConstraintIR, NamesMap, ParamRef, PredicateIR, TagValue, UIntIR, UIntWidth, ValType,
    WrapperUse,
};
use super::generate_nominal_sections;

#[derive(Default)]
pub struct ModuleSections {
    pub imports: TokenStream,
    pub nominal_type_items: TokenStream,
    pub nominal_support_items: TokenStream,
    pub const_items: TokenStream,
    pub combinator_type_items: TokenStream,
    pub constructor_items: TokenStream,
    pub helper_items: TokenStream,
    pub public_items: TokenStream,
    pub wrapper_impl_items: TokenStream,
    pub constructor_helper_items: TokenStream,
}

impl ModuleSections {
    pub fn to_tokens(self) -> TokenStream {
        let Self {
            imports,
            nominal_type_items,
            nominal_support_items,
            const_items,
            combinator_type_items,
            constructor_items,
            helper_items,
            public_items,
            wrapper_impl_items,
            constructor_helper_items,
        } = self;

        quote! {
            #imports

            // ========== Nominal Types ==========
            #nominal_type_items
            #nominal_support_items

            // ========== Combinator Definitions ==========
            #const_items
            #combinator_type_items
            #constructor_items
            #helper_items

            // ========== Public API ==========
            #public_items

            // ========== Wrapper Impls ==========
            #wrapper_impl_items
            #constructor_helper_items
        }
    }
}

#[derive(Clone, Copy)]
pub(super) struct DefinitionEmitContext<'a> {
    pub(super) def: &'a CombDef,
    pub(super) names: &'a DefinitionNames,
    pub(super) analysis: &'a Analysis,
}

#[derive(Clone)]
pub(super) struct EmitParam {
    pub(super) name: String,
    pub(super) ident: Ident,
    pub(super) kind: ValType,
    pub(super) needs_generate_ref: bool,
    pub(super) needs_length_param: bool,
}

impl EmitParam {
    pub(super) fn ctor_generic_ident(&self) -> Ident {
        format_ident!("{}Arg", snake_to_upper_camel(&self.name))
    }
}

#[derive(Clone)]
pub(super) struct DispatchBranchTypes {
    pub(super) param: Ident,
    pub(super) variant: Ident,
    pub(super) nominal_variant: Ident,
    pub(super) default_type: TokenStream,
    pub(super) parse_type: TokenStream,
    pub(super) borrow_type: TokenStream,
    pub(super) owned_type: TokenStream,
}

pub fn generate_module(plan: &CodegenPlan) -> Result<String, Box<dyn Error>> {
    ModuleEmitter::new(plan).generate_module()
}

pub fn generate_module_tokens(plan: &CodegenPlan) -> TokenStream {
    ModuleEmitter::new(plan).generate_module_tokens()
}

struct ModuleEmitter<'a> {
    plan: &'a CodegenPlan,
}

impl<'a> ModuleEmitter<'a> {
    fn new(plan: &'a CodegenPlan) -> Self {
        Self { plan }
    }

    fn generate_module(&self) -> Result<String, Box<dyn Error>> {
        let tokens = self.generate_module_tokens();
        format_rust_code(tokens).map_err(|e| Box::new(e) as Box<dyn Error>)
    }

    fn generate_module_tokens(&self) -> TokenStream {
        self.bootstrap_sections().to_tokens()
    }

    fn bootstrap_sections(&self) -> ModuleSections {
        let def_ctxs: Vec<_> = self.definition_contexts().collect();
        debug_assert_eq!(def_ctxs.len(), self.plan.defs.len());
        debug_assert!(def_ctxs.iter().all(|ctx| !ctx.names.raw.is_empty()));
        debug_assert!(def_ctxs.iter().all(|ctx| {
            let _ = &ctx.analysis.value_kind;
            true
        }));

        let nominal_sections =
            generate_nominal_sections(&self.plan.defs, &self.plan.names, &self.plan.analysis);

        ModuleSections {
            imports: generate_imports(),
            nominal_type_items: nominal_sections.type_items,
            nominal_support_items: nominal_sections.support_items,
            const_items: self.generate_const_definitions(),
            combinator_type_items: self.generate_combinator_type_items(),
            constructor_items: self.generate_constructor_items(),
            helper_items: self.generate_helper_items(),
            public_items: self.generate_public_items(),
            wrapper_impl_items: self.generate_wrapper_impl_items(),
            constructor_helper_items: generate_constructor_param_helpers(),
            ..ModuleSections::default()
        }
    }

    fn definition_contexts(&self) -> impl Iterator<Item = DefinitionEmitContext<'a>> + 'a {
        self.plan.defs.iter().map(|def| DefinitionEmitContext {
            def,
            names: self
                .plan
                .names
                .get(&def.name)
                .expect("every v3 definition should have a nameset"),
            analysis: self
                .plan
                .analysis
                .get(&def.name)
                .expect("every v3 definition should have analysis"),
        })
    }

    fn generate_const_definitions(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            for const_def in &def_ctx.def.const_defs {
                tokens.extend(generate_const_definition(const_def));
            }
        }
        tokens
    }

    fn generate_combinator_type_items(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            tokens.extend(DefinitionEmitter::new(self.plan, def_ctx).comb_type_item());
        }
        tokens
    }

    fn generate_constructor_items(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            tokens.extend(DefinitionEmitter::new(self.plan, def_ctx).constructor_item());
        }
        tokens
    }

    fn generate_public_items(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            tokens.extend(DefinitionEmitter::new(self.plan, def_ctx).public_items());
        }
        tokens
    }

    fn generate_helper_items(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            let emitter = DefinitionEmitter::new(self.plan, def_ctx);
            tokens.extend(emitter.helper_items());
        }
        tokens
    }

    fn generate_wrapper_impl_items(&self) -> TokenStream {
        let mut tokens = TokenStream::new();
        for def_ctx in self.definition_contexts() {
            tokens.extend(DefinitionEmitter::new(self.plan, def_ctx).wrapper_impl_item());
        }
        tokens
    }
}

pub(super) struct DefinitionEmitter<'a> {
    pub(super) plan: &'a CodegenPlan,
    pub(super) def_ctx: DefinitionEmitContext<'a>,
    pub(super) defs: HashMap<String, &'a CombDef>,
    pub(super) param_specs: Vec<EmitParam>,
    pub(super) needs_runtime_ref: bool,
}

impl<'a> DefinitionEmitter<'a> {
    fn new(plan: &'a CodegenPlan, def_ctx: DefinitionEmitContext<'a>) -> Self {
        let defs: HashMap<String, &'a CombDef> = plan
            .defs
            .iter()
            .map(|def| (def.name.clone(), def))
            .collect();
        let param_specs: Vec<EmitParam> = def_ctx
            .def
            .params
            .iter()
            .map(|param| EmitParam {
                name: param.name.clone(),
                ident: format_ident!("{}", param.name),
                kind: value_kind_for_comb(&param.ty, &defs, &plan.analysis),
                needs_generate_ref: param_needs_generate_ref(&def_ctx.def.body, &param.name, &defs),
                needs_length_param: param_usage_inner(
                    &def_ctx.def.body,
                    &param.name,
                    &defs,
                    &mut HashSet::new(),
                    ParamUsageMode::LengthParam,
                ),
            })
            .collect();
        let needs_runtime_ref = param_specs.iter().any(|param| param.needs_generate_ref);

        Self {
            plan,
            def_ctx,
            defs,
            param_specs,
            needs_runtime_ref,
        }
    }

    fn comb_type_item(&self) -> TokenStream {
        let env = self.top_level_env();
        let body_type_raw =
            self.top_level_body_type_tokens_with_options(&self.def_ctx.def.body, &env, None, false);
        let body_type = self.wrap_top_level_mapper_type(body_type_raw);
        let body_type_gen = self.top_level_generate_alias_body_type_tokens();

        let alias_name = &self.def_ctx.names.alias_ident;
        let combinator_type_name = &self.def_ctx.names.combinator_ident;
        let type_doc = format!("Type alias for {} combinator", self.def_ctx.def.name);
        let struct_doc = format!("Wrapper struct for {} combinator", self.def_ctx.def.name);

        match body_type_gen {
            Some(body_type_gen) => quote! {
                #[doc = #type_doc]
                pub type #alias_name<'x> = #body_type_gen;

                #[doc = #struct_doc]
                pub struct #combinator_type_name<C = #alias_name<'static>>(pub C);
            },
            None => quote! {
                #[doc = #type_doc]
                pub type #alias_name = #body_type;

                #[doc = #struct_doc]
                pub struct #combinator_type_name<C = #alias_name>(pub C);
            },
        }
    }

    fn wrapper_impl_item(&self) -> TokenStream {
        let combinator_type_name = &self.def_ctx.names.combinator_ident;

        quote! {
            impl<C> Combinator<[u8], Vec<u8>> for #combinator_type_name<C>
            where
                C: Combinator<[u8], Vec<u8>>,
            {
                type Type<'p> = C::Type<'p>;
                type SType<'s> = C::SType<'s>;
                type GType = C::GType;

                fn length<'s>(&self, v: Self::SType<'s>) -> usize
                where
                    [u8]: 's,
                {
                    self.0.length(v)
                }

                fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
                where
                    [u8]: 'p,
                {
                    self.0.parse(s)
                }

                fn serialize<'s>(
                    &self,
                    v: Self::SType<'s>,
                    data: &mut Vec<u8>,
                    pos: usize,
                ) -> Result<usize, SerializeError>
                where
                    [u8]: 's,
                {
                    self.0.serialize(v, data, pos)
                }

                fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
                    self.0.generate(g)
                }

                fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
                where
                    [u8]: 's,
                {
                    self.0.well_formed(v)
                }
            }
        }
    }

    pub(super) fn helper_ident(&self, path: &[usize]) -> Ident {
        scoped_helper_ident(&format!("{}Dep", self.def_ctx.names.type_ident), path)
    }

    pub(super) fn dispatch_helper_ident(&self, path: &[usize]) -> Ident {
        scoped_helper_ident(
            &format!("{}DispatchCase", self.def_ctx.names.type_ident),
            path,
        )
    }

    pub(super) fn helper_collection(&self) -> helper_specs::CollectedHelperSpecs<'a> {
        let env = self.top_level_env();
        let body: &'a CombIR = &self.def_ctx.def.body;
        collect_helper_specs(body, &env, &self.defs, &self.plan.analysis)
    }
}

fn generate_const_definition(const_def: &ConstDef) -> TokenStream {
    let name = format_ident!("{}", const_def.name);
    let ty = const_def.ty.rust_type_tokens();
    let value = Literal::i128_unsuffixed(const_def.value);
    quote! {
        pub const #name: #ty = #value;
    }
}

fn generate_imports() -> TokenStream {
    quote! {
        #![allow(unused_imports)]
        #![allow(dead_code)]
        #![allow(unused_variables)]
        #![allow(non_camel_case_types)]

        use vest_lib::properties::*;
        use vest_lib::errors::*;
        use vest_lib::regular::*;
        use vest_lib::regular::sequence::{Pair, Preceded, Terminated, DepCombinator};
        use vest_lib::regular::variant::{Dispatch, Opt, OptThen, Choice};
        use vest_lib::regular::repetition::{Repeat, RepeatN};
        use vest_lib::regular::modifier::{Refined, Mapped, FixedLen, Length, RuntimeValue, AndThen, CondEq, Mapper};
        use vest_lib::regular::tag::Tag;
        use vest_lib::regular::bytes::{Fixed, Variable, Tail};
        use vest_lib::regular::success::Success;
        use vest_lib::regular::fail::Fail;
        use vest_lib::regular::end::End;
        use vest_lib::regular::uints::*;
        use vest_lib::buf_traits::{VestInput, VestOutput};
    }
}

fn generate_constructor_param_helpers() -> TokenStream {
    let length_plain_specs = [
        (quote! { u8 }, quote! { Length::from_value(self as usize) }),
        (quote! { u16 }, quote! { Length::from_value(self as usize) }),
        (
            quote! { u24 },
            quote! { Length::from_value(self.as_u32() as usize) },
        ),
        (quote! { u32 }, quote! { Length::from_value(self as usize) }),
        (quote! { u64 }, quote! { Length::from_value(self as usize) }),
    ];
    let length_ref_specs = [
        (quote! { u8 }, quote! { Length::from_u8_mut(self) }),
        (quote! { u16 }, quote! { Length::from_u16_mut(self) }),
        (
            quote! { u24 },
            quote! { Length::from_value(self.as_u32() as usize) },
        ),
        (quote! { u32 }, quote! { Length::from_u32_mut(self) }),
        (quote! { u64 }, quote! { Length::from_u64_mut(self) }),
    ];
    let length_plain_impls: Vec<_> = length_plain_specs
        .into_iter()
        .map(|(ty, length)| {
            quote! {
                impl LengthParam<'static, #ty> for #ty {
                    fn into_length(self) -> Length<'static> { #length }
                }
            }
        })
        .collect();
    let length_ref_impls: Vec<_> = length_ref_specs
        .into_iter()
        .map(|(ty, length)| {
            quote! {
                impl<'a> LengthParam<'a, #ty> for &'a mut #ty {
                    fn into_length(self) -> Length<'a> { #length }
                }
            }
        })
        .collect();

    quote! {
        pub trait RuntimeValParam<'a, T: Copy> {
            fn into_runtime_value(self) -> RuntimeValue<'a, T>;
        }

        pub trait LengthParam<'a, T: Copy> {
            fn into_length(self) -> Length<'a>;
        }

        impl<T: Copy> RuntimeValParam<'static, T> for T {
            fn into_runtime_value(self) -> RuntimeValue<'static, T> {
                RuntimeValue::from_value(self)
            }
        }

        impl<'a, T: Copy> RuntimeValParam<'a, T> for &'a mut T {
            fn into_runtime_value(self) -> RuntimeValue<'a, T> {
                RuntimeValue::from_mut(self)
            }
        }

        #(#length_plain_impls)*
        #(#length_ref_impls)*
    }
}

pub(super) fn param_needs_generate_ref(
    comb: &CombIR,
    name: &str,
    defs: &HashMap<String, &CombDef>,
) -> bool {
    let mut seen = HashSet::new();
    param_usage_inner(comb, name, defs, &mut seen, ParamUsageMode::GenerateRef)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ParamUsageMode {
    GenerateRef,
    LengthParam,
}

fn param_usage_inner(
    comb: &CombIR,
    name: &str,
    defs: &HashMap<String, &CombDef>,
    seen: &mut HashSet<String>,
    mode: ParamUsageMode,
) -> bool {
    match comb {
        CombIR::Variable { len } => {
            mode == ParamUsageMode::LengthParam && len_uses_dependent_name(len, name)
        }
        CombIR::Struct(fields) => fields
            .iter()
            .any(|field| param_usage_inner(&field.comb, name, defs, seen, mode)),
        CombIR::Seq(items) => items
            .iter()
            .any(|item| param_usage_inner(item, name, defs, seen, mode)),
        CombIR::DepPair { fst, snd, .. } => {
            param_usage_inner(fst, name, defs, seen, mode)
                || param_usage_inner(snd, name, defs, seen, mode)
        }
        CombIR::Preceded { prefix, inner } => {
            param_usage_inner(prefix, name, defs, seen, mode)
                || param_usage_inner(inner, name, defs, seen, mode)
        }
        CombIR::Terminated { inner, suffix } => {
            param_usage_inner(inner, name, defs, seen, mode)
                || param_usage_inner(suffix, name, defs, seen, mode)
        }
        CombIR::Dispatch { tag, branches } => {
            (mode == ParamUsageMode::GenerateRef && tag == name)
                || branches
                    .iter()
                    .any(|branch| param_usage_inner(&branch.comb, name, defs, seen, mode))
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::Tag { inner, .. } => param_usage_inner(inner, name, defs, seen, mode),
        CombIR::RepeatN { inner, count } => {
            (mode == ParamUsageMode::LengthParam && len_uses_dependent_name(count, name))
                || param_usage_inner(inner, name, defs, seen, mode)
        }
        CombIR::FixedLen { len, inner } => {
            len_uses_dependent_name(len, name) || param_usage_inner(inner, name, defs, seen, mode)
        }
        CombIR::Named {
            name: def_name,
            args,
        } => {
            let Some(def) = defs.get(def_name) else {
                return false;
            };
            if !seen.insert(def_name.clone()) {
                return false;
            }
            let result = def
                .params
                .iter()
                .zip(args.iter())
                .any(|(param, arg)| match arg {
                    ParamRef::Dependent(arg_name) if arg_name == name => {
                        param_usage_inner(&def.body, &param.name, defs, seen, mode)
                    }
                    _ => false,
                });
            seen.remove(def_name);
            result
        }
        CombIR::Tail
        | CombIR::UInt(_)
        | CombIR::Fixed { .. }
        | CombIR::End
        | CombIR::Success
        | CombIR::Fail(_) => false,
    }
}

fn len_uses_dependent_name(len: &crate::vestir::LengthExpr, name: &str) -> bool {
    match len {
        crate::vestir::LengthExpr::Const(_) | crate::vestir::LengthExpr::SizeOf(_) => false,
        crate::vestir::LengthExpr::Dependent(dep) => dep == name,
        crate::vestir::LengthExpr::BinOp { left, right, .. } => {
            len_uses_dependent_name(left, name) || len_uses_dependent_name(right, name)
        }
    }
}

pub(super) fn dispatch_tag_type_tokens_for_ref(
    tag_ref: &str,
    env: &BindingEnv,
    names: &NamesMap,
) -> TokenStream {
    if let Some(binding) = env.get(tag_ref) {
        match &binding.kind {
            ValType::Named(name) => {
                let ident = &names.get(name).expect("names for tag ref").type_ident;
                quote! { #ident }
            }
            ValType::UInt(width) => {
                UIntIR::new(*width, crate::vestir::Endianess::Little).rust_type_tokens()
            }
            _ => quote! { i128 },
        }
    } else {
        quote! { i128 }
    }
}

pub(super) fn tag_value_type_tokens(
    tag_value: &TagValue,
    inner: &CombIR,
    names: &NamesMap,
) -> TokenStream {
    match tag_value {
        TagValue::Int(_) => match inner {
            CombIR::UInt(uint) => uint.rust_type_tokens(),
            CombIR::Enum { inner, .. } => match inner.as_ref() {
                CombIR::UInt(uint) => uint.rust_type_tokens(),
                _ => quote! { i128 },
            },
            _ => quote! { i128 },
        },
        TagValue::Enum { ty, .. } => {
            let ident = &names.get(ty).expect("names for enum tag").type_ident;
            quote! { #ident }
        }
        TagValue::Bytes(bytes) => {
            let n = Literal::usize_unsuffixed(bytes.len());
            quote! { [u8; #n] }
        }
        TagValue::Wildcard => quote! { i128 },
    }
}

pub(super) fn refined_pred_fn_type_tokens(inner: &CombIR, names: &NamesMap) -> TokenStream {
    let arg_ty = predicate_arg_type_tokens(inner, names);
    quote! { fn(#arg_ty) -> bool }
}

pub(super) fn build_nested_pair_type(types: &[TokenStream]) -> TokenStream {
    match types {
        [] => quote! { () },
        [only] => only.clone(),
        [head, tail @ ..] => {
            let tail_ty = build_nested_pair_type(tail);
            quote! { (#head, #tail_ty) }
        }
    }
}

pub(super) fn build_nested_pair_expr(exprs: &[TokenStream]) -> TokenStream {
    match exprs {
        [] => quote! { () },
        [only] => only.clone(),
        [head, tail @ ..] => {
            let tail_expr = build_nested_pair_expr(tail);
            quote! { (#head, #tail_expr) }
        }
    }
}

pub(super) fn build_nested_tuple_pattern(items: &[Ident]) -> TokenStream {
    match items {
        [] => quote! { () },
        [only] => quote! { #only },
        [head, rest @ ..] => {
            let rest = build_nested_tuple_pattern(rest);
            quote! { (#head, #rest) }
        }
    }
}

pub(super) fn tuple_field_access(base: &TokenStream, total: usize, index: usize) -> TokenStream {
    if total <= 1 {
        return base.clone();
    }
    if index == 0 {
        quote! { #base.0 }
    } else {
        let rest = quote! { #base.1 };
        tuple_field_access(&rest, total - 1, index - 1)
    }
}

pub(super) fn nominal_tag_value_expr_tokens(
    value: &TagValue,
    def: &CombDef,
    names: &NamesMap,
) -> Option<TokenStream> {
    match value {
        TagValue::Int(v) => {
            if let Some(const_ident) = const_ident_for_int(def, *v) {
                Some(quote! { #const_ident })
            } else {
                let lit = Literal::i128_unsuffixed(*v);
                Some(quote! { #lit })
            }
        }
        TagValue::Enum { ty, variant } => {
            let ty_ident = &names.get(ty).expect("enum tag names").type_ident;
            let variant_ident = format_ident!("{}", variant);
            Some(quote! { #ty_ident::#variant_ident })
        }
        TagValue::Bytes(_) | TagValue::Wildcard => None,
    }
}

pub(super) fn value_shape_field_expr_tokens(
    expr: TokenStream,
    comb: &CombIR,
    def: &CombDef,
    names: &NamesMap,
) -> TokenStream {
    if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
        return value_shape_field_expr_tokens(expr, inner, def, names);
    }

    match comb {
        CombIR::Tag { value, .. } => {
            nominal_tag_value_expr_tokens(value, def, names).unwrap_or_else(|| quote! { () })
        }
        _ => expr,
    }
}

pub(super) fn value_shape_borrow_expr_tokens(
    access: TokenStream,
    comb: &CombIR,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
) -> TokenStream {
    if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
        return value_shape_borrow_expr_tokens(access, inner, defs, analysis);
    }

    match comb {
        CombIR::Tag { .. } => quote! { () },
        CombIR::Struct(fields) => {
            let exprs: Vec<_> = fields
                .iter()
                .enumerate()
                .map(|(idx, field)| {
                    value_shape_borrow_expr_tokens(
                        tuple_field_access(&access, fields.len(), idx),
                        &field.comb,
                        defs,
                        analysis,
                    )
                })
                .collect();
            build_nested_pair_expr(&exprs)
        }
        CombIR::Seq(items) => {
            let exprs: Vec<_> = items
                .iter()
                .enumerate()
                .map(|(idx, item)| {
                    value_shape_borrow_expr_tokens(
                        tuple_field_access(&access, items.len(), idx),
                        item,
                        defs,
                        analysis,
                    )
                })
                .collect();
            build_nested_pair_expr(&exprs)
        }
        CombIR::DepPair { fst, snd, .. } => build_nested_pair_expr(&[
            value_shape_borrow_expr_tokens(tuple_field_access(&access, 2, 0), fst, defs, analysis),
            value_shape_borrow_expr_tokens(tuple_field_access(&access, 2, 1), snd, defs, analysis),
        ]),
        CombIR::RepeatN { .. } | CombIR::Repeat(..) => quote! { #access.as_slice() },
        CombIR::Named { name, .. } if defs.contains_key(name) => {
            if analysis
                .get(name)
                .expect("analysis for borrow expr")
                .borrow_by_value
            {
                access
            } else {
                quote! { &#access }
            }
        }
        _ => access,
    }
}

pub(super) fn emit_function_item(
    doc: String,
    name: Ident,
    generics: Option<TokenStream>,
    params: Vec<TokenStream>,
    ret: TokenStream,
    body: TokenStream,
) -> TokenStream {
    match generics {
        Some(generics) => quote! {
            #[doc = #doc]
            pub fn #name #generics (#(#params),*) -> #ret {
                #body
            }
        },
        None => quote! {
            #[doc = #doc]
            pub fn #name(#(#params),*) -> #ret {
                #body
            }
        },
    }
}

pub(super) fn call_tokens(fn_name: &Ident, args: &[TokenStream]) -> TokenStream {
    if args.is_empty() {
        quote! { #fn_name() }
    } else {
        quote! { #fn_name(#(#args),*) }
    }
}

pub(super) fn public_parse_type_tokens(
    def_ctx: DefinitionEmitContext<'_>,
    lt: TokenStream,
) -> TokenStream {
    let name = &def_ctx.names.type_ident;
    if def_ctx.analysis.needs_lifetime {
        quote! { #name<#lt> }
    } else {
        quote! { #name }
    }
}

pub(super) fn public_borrow_type_tokens(
    def_ctx: DefinitionEmitContext<'_>,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
    names: &NamesMap,
) -> TokenStream {
    let name = &def_ctx.names.type_ident;
    match top_level_nominal_kind(&def_ctx.def.body) {
        TopLevelNominalKind::Struct => {
            if def_ctx.analysis.borrow_by_value {
                if def_ctx.analysis.needs_lifetime {
                    quote! { #name<'s> }
                } else {
                    quote! { #name }
                }
            } else if def_ctx.analysis.needs_lifetime {
                quote! { &'s #name<'s> }
            } else {
                quote! { &'s #name }
            }
        }
        TopLevelNominalKind::Enum => {
            if def_ctx.analysis.needs_lifetime {
                quote! { &'s #name<'s> }
            } else {
                quote! { &'s #name }
            }
        }
        TopLevelNominalKind::ValueEnum => quote! { #name },
        TopLevelNominalKind::Alias => {
            concrete_borrow_type_tokens(&def_ctx.def.body, defs, analysis, names)
        }
    }
}

pub(super) fn public_owned_type_tokens(def_ctx: DefinitionEmitContext<'_>) -> TokenStream {
    if def_ctx.analysis.needs_lifetime {
        let owned = &def_ctx.names.owned_ident;
        quote! { #owned }
    } else {
        let name = &def_ctx.names.type_ident;
        quote! { #name }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TopLevelNominalKind {
    Struct,
    Enum,
    ValueEnum,
    Alias,
}

fn top_level_nominal_kind(comb: &CombIR) -> TopLevelNominalKind {
    let comb = peel_wrappers_for(comb, WrapperUse::NominalRoot);
    match comb {
        CombIR::Struct(_) | CombIR::Seq(_) | CombIR::DepPair { .. } => TopLevelNominalKind::Struct,
        CombIR::Dispatch { .. } => TopLevelNominalKind::Enum,
        CombIR::Enum { .. } => TopLevelNominalKind::ValueEnum,
        _ => TopLevelNominalKind::Alias,
    }
}

pub(super) fn concrete_borrow_type_tokens(
    comb: &CombIR,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
    names: &NamesMap,
) -> TokenStream {
    if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
        return concrete_borrow_type_tokens(inner, defs, analysis, names);
    }

    match comb {
        CombIR::UInt(uint) => uint.rust_type_tokens(),
        CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => quote! { &'s [u8] },
        CombIR::Struct(fields) => {
            let field_tys: Vec<_> = fields
                .iter()
                .map(|field| concrete_borrow_type_tokens(&field.comb, defs, analysis, names))
                .collect();
            build_nested_pair_type(&field_tys)
        }
        CombIR::Preceded { inner, .. }
        | CombIR::Terminated { inner, .. }
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. } => {
            concrete_borrow_type_tokens(inner, defs, analysis, names)
        }
        CombIR::Seq(items) => {
            let item_tys: Vec<_> = items
                .iter()
                .map(|item| concrete_borrow_type_tokens(item, defs, analysis, names))
                .collect();
            build_nested_pair_type(&item_tys)
        }
        CombIR::DepPair { fst, snd, .. } => {
            let fst = concrete_borrow_type_tokens(fst, defs, analysis, names);
            let snd = concrete_borrow_type_tokens(snd, defs, analysis, names);
            build_nested_pair_type(&[fst, snd])
        }
        CombIR::Dispatch { .. } => {
            quote! { todo!("dispatch borrow type outside top-level enum is unsupported") }
        }
        CombIR::Opt(inner) => {
            let inner = concrete_borrow_type_tokens(inner, defs, analysis, names);
            quote! { Option<#inner> }
        }
        CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
            let inner = concrete_borrow_type_tokens(inner, defs, analysis, names);
            quote! { &'s [#inner] }
        }
        CombIR::Enum { inner, .. } => concrete_borrow_type_tokens(inner, defs, analysis, names),
        CombIR::Tag { .. } | CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        CombIR::Named { name, .. } => named_borrow_type_tokens(name, analysis, names),
        CombIR::AndThen { len_comb, inner } => {
            let pair = [
                concrete_borrow_type_tokens(len_comb, defs, analysis, names),
                concrete_borrow_type_tokens(inner, defs, analysis, names),
            ];
            build_nested_pair_type(&pair)
        }
    }
}

fn named_borrow_type_tokens(name: &str, analysis: &AnalysisMap, names: &NamesMap) -> TokenStream {
    let type_name = &names.get(name).expect("names for borrow type").type_ident;
    let needs_lifetime = analysis
        .get(name)
        .expect("analysis for borrow type")
        .needs_lifetime;
    let borrow_by_value = analysis
        .get(name)
        .expect("analysis for borrow type")
        .borrow_by_value;
    let ty = if needs_lifetime {
        quote! { #type_name<'s> }
    } else {
        quote! { #type_name }
    };
    if borrow_by_value {
        ty
    } else {
        quote! { &'s #ty }
    }
}

pub(super) fn concrete_owned_type_tokens(
    comb: &CombIR,
    defs: &HashMap<String, &CombDef>,
    analysis: &AnalysisMap,
    names: &NamesMap,
) -> TokenStream {
    if let Some(inner) = wrapper_inner_for(comb, WrapperUse::ValueShape) {
        return concrete_owned_type_tokens(inner, defs, analysis, names);
    }

    match comb {
        CombIR::UInt(uint) => uint.rust_type_tokens(),
        CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => quote! { Vec<u8> },
        CombIR::Struct(fields) => {
            let field_tys: Vec<_> = fields
                .iter()
                .map(|field| concrete_owned_type_tokens(&field.comb, defs, analysis, names))
                .collect();
            build_nested_pair_type(&field_tys)
        }
        CombIR::Seq(items) => {
            let item_tys: Vec<_> = items
                .iter()
                .map(|item| concrete_owned_type_tokens(item, defs, analysis, names))
                .collect();
            build_nested_pair_type(&item_tys)
        }
        CombIR::DepPair { fst, snd, .. } => {
            let fst = concrete_owned_type_tokens(fst, defs, analysis, names);
            let snd = concrete_owned_type_tokens(snd, defs, analysis, names);
            build_nested_pair_type(&[fst, snd])
        }
        CombIR::Preceded { inner, .. }
        | CombIR::Terminated { inner, .. }
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::Enum { inner, .. } => concrete_owned_type_tokens(inner, defs, analysis, names),
        CombIR::Dispatch { .. } => {
            quote! { todo!("dispatch owned type outside top-level enum is unsupported") }
        }
        CombIR::Opt(inner) => {
            let inner = concrete_owned_type_tokens(inner, defs, analysis, names);
            quote! { Option<#inner> }
        }
        CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
            let inner = concrete_owned_type_tokens(inner, defs, analysis, names);
            quote! { Vec<#inner> }
        }
        CombIR::AndThen { len_comb, inner } => {
            let pair = [
                concrete_owned_type_tokens(len_comb, defs, analysis, names),
                concrete_owned_type_tokens(inner, defs, analysis, names),
            ];
            build_nested_pair_type(&pair)
        }
        CombIR::Tag { .. } | CombIR::End | CombIR::Success | CombIR::Fail(_) => quote! { () },
        CombIR::Named { name, .. } => named_owned_type_tokens(name, analysis, names),
    }
}

fn named_owned_type_tokens(name: &str, analysis: &AnalysisMap, names: &NamesMap) -> TokenStream {
    let name_set = names.get(name).expect("names for owned type");
    if analysis
        .get(name)
        .expect("analysis for owned type")
        .needs_lifetime
    {
        let owned = &name_set.owned_ident;
        quote! { #owned }
    } else {
        let ident = &name_set.type_ident;
        quote! { #ident }
    }
}

pub(super) fn value_kind_type_tokens(kind: &ValType, names: &NamesMap) -> TokenStream {
    match kind {
        ValType::UInt(width) => {
            UIntIR::new(*width, crate::vestir::Endianess::Little).rust_type_tokens()
        }
        ValType::Named(name) => {
            let ident = &names.get(name).expect("names for value kind").type_ident;
            quote! { #ident }
        }
        ValType::ByteSlice => quote! { &[u8] },
        ValType::Unit => quote! { () },
        ValType::Tuple(items) => {
            let item_tys: Vec<_> = items
                .iter()
                .map(|item| value_kind_type_tokens(item, names))
                .collect();
            build_nested_pair_type(&item_tys)
        }
        ValType::Option(inner) => {
            let inner = value_kind_type_tokens(inner, names);
            quote! { Option<#inner> }
        }
        ValType::Vec(inner) => {
            let inner = value_kind_type_tokens(inner, names);
            quote! { Vec<#inner> }
        }
    }
}

pub(super) fn value_kind_to_usize_tokens(kind: &ValType, value: TokenStream) -> TokenStream {
    match kind {
        ValType::UInt(UIntWidth::U24) => quote! { #value.as_u32() as usize },
        _ => quote! { #value as usize },
    }
}

pub(super) fn predicate_to_tokens(
    pred: &PredicateIR,
    inner: Option<&CombIR>,
    names: &NamesMap,
) -> TokenStream {
    match pred {
        PredicateIR::Int(pred) => {
            let arg_ty = inner
                .map(|inner| predicate_arg_type_tokens(inner, names))
                .unwrap_or_else(|| quote! { i128 });
            let var_expr = refined_pred_value_as_i128(inner);
            let check = int_constraint_to_check(pred, var_expr);
            quote! { |v: #arg_ty| #check }
        }
        PredicateIR::Enum(pred) => {
            let inner = inner.expect("enum predicate requires inner combinator");
            let arg_ty = predicate_arg_type_tokens(inner, names);
            let check = enum_constraint_to_check(pred, inner, names, quote! { v });
            quote! { |v: #arg_ty| #check }
        }
    }
}

fn predicate_arg_type_tokens(inner: &CombIR, names: &NamesMap) -> TokenStream {
    match peel_wrappers_for(inner, WrapperUse::ValueShape) {
        CombIR::UInt(uint) => uint.rust_type_tokens(),
        CombIR::Named { name, .. } => {
            let ident = &names
                .get(name)
                .expect("names for predicate type")
                .type_ident;
            quote! { #ident }
        }
        _ => quote! { i128 },
    }
}

fn refined_pred_value_as_i128(inner: Option<&CombIR>) -> TokenStream {
    match inner {
        Some(CombIR::UInt(uint)) if uint.is_u24() => quote! { v.as_u32() as i128 },
        _ => quote! { v as i128 },
    }
}

fn int_constraint_to_check(constraint: &IntConstraintIR, var: TokenStream) -> TokenStream {
    match constraint {
        IntConstraintIR::Single(elem) => constraint_elem_to_check(elem, var),
        IntConstraintIR::Set(elems) => {
            let checks: Vec<_> = elems
                .iter()
                .map(|elem| constraint_elem_to_check(elem, var.clone()))
                .collect();
            if checks.is_empty() {
                quote! { false }
            } else {
                quote! { (#(#checks)||*) }
            }
        }
        IntConstraintIR::Neg(inner) => {
            let inner = int_constraint_to_check(inner, var);
            quote! { !(#inner) }
        }
    }
}

fn enum_constraint_to_check(
    constraint: &EnumConstraintIR,
    inner: &CombIR,
    names: &NamesMap,
    var: TokenStream,
) -> TokenStream {
    let enum_type = enum_predicate_type_ident(inner, names);
    match constraint {
        EnumConstraintIR::Single(variant) => {
            let variant = format_ident!("{}", variant);
            quote! { matches!(#var, #enum_type::#variant) }
        }
        EnumConstraintIR::Set(variants) => {
            if variants.is_empty() {
                quote! { false }
            } else {
                let variants: Vec<_> = variants
                    .iter()
                    .map(|variant| {
                        let variant = format_ident!("{}", variant);
                        quote! { #enum_type::#variant }
                    })
                    .collect();
                quote! { matches!(#var, #(#variants)|*) }
            }
        }
        EnumConstraintIR::Neg(negated) => {
            let inner = enum_constraint_to_check(negated, inner, names, var);
            quote! { !(#inner) }
        }
    }
}

fn enum_predicate_type_ident(inner: &CombIR, names: &NamesMap) -> Ident {
    match peel_wrappers_for(inner, WrapperUse::ValueShape) {
        CombIR::Named { name, .. } => names
            .get(name)
            .expect("names for enum predicate")
            .type_ident
            .clone(),
        other => panic!(
            "enum predicate requires named enum combinator, got {:?}",
            other
        ),
    }
}

fn constraint_elem_to_check(elem: &crate::vestir::ConstraintElem, var: TokenStream) -> TokenStream {
    match elem {
        crate::vestir::ConstraintElem::Single(v) => {
            let lit = Literal::i128_unsuffixed(*v);
            quote! { #var == #lit }
        }
        crate::vestir::ConstraintElem::Range { start, end } => match (start, end) {
            (Some(start), Some(end)) => {
                let start = Literal::i128_unsuffixed(*start);
                let end = Literal::i128_unsuffixed(*end);
                quote! { #var >= #start && #var <= #end }
            }
            (Some(start), None) => {
                let start = Literal::i128_unsuffixed(*start);
                quote! { #var >= #start }
            }
            (None, Some(end)) => {
                let end = Literal::i128_unsuffixed(*end);
                quote! { #var <= #end }
            }
            (None, None) => quote! { true },
        },
    }
}

pub(super) fn dispatch_variant_ident(index: usize) -> Ident {
    format_ident!("V{}", index + 1)
}
