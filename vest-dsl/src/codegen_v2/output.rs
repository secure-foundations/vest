//! This module combines all the generated pieces (types, combinators, wrappers)
//! into a complete Rust module.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use proc_macro2::{Ident, Literal, TokenStream};
use quote::{format_ident, quote};

use crate::vestir::ConstraintElem;

use super::builders::{
    build_nested_either_type, build_right_nested_tokens, wrap_right_nested_either,
};
use super::combir::{
    comb_uint_or_i128_type_tokens, comb_uint_type_tokens, tag_literal_type_tokens, ArithOp,
    CodegenCtx, CombDef, CombIR, ConstDef, DepCombIR, Endian, IntConstraintIR, LenExpr, ParamRef,
    PredicateIR, TagRef, TagValue,
};
use super::format::{format_rust_code, FormatError};
use super::nominal::{
    concrete_borrow_type_tokens, concrete_owned_type_tokens, concrete_parse_type_tokens,
    public_borrow_type_tokens, public_owned_type_tokens, public_parse_type_tokens,
    snake_to_upper_camel, NominalTypeGen,
};

/// Context for token generation.
pub struct TokenCtx<'a> {
    /// Reference to the codegen context.
    pub ctx: &'a CodegenCtx,
}

impl<'a> TokenCtx<'a> {
    pub fn new(ctx: &'a CodegenCtx) -> Self {
        Self { ctx }
    }
}

/// Generate a complete Rust module from combinator definitions.
pub fn generate_module(defs: &[CombDef], ctx: &CodegenCtx) -> Result<String, FormatError> {
    let token_ctx = TokenCtx::new(ctx);
    let tokens = generate_module_tokens(defs, &token_ctx);
    format_rust_code(tokens)
}

/// Generate module tokens (before formatting).
pub fn generate_module_tokens(defs: &[CombDef], ctx: &TokenCtx) -> TokenStream {
    let imports = generate_imports();
    let def_map: HashMap<String, &CombDef> =
        defs.iter().map(|def| (def.name.clone(), def)).collect();
    let constructor_param_helpers = generate_constructor_param_helpers();

    // Generate const definitions for all defs
    let const_defs = generate_const_definitions(defs);

    let mut type_items = TokenStream::new();
    let mut constructor_items = TokenStream::new();
    let mut helper_items = TokenStream::new();
    let mut public_items = TokenStream::new();
    let mut wrapper_impls = TokenStream::new();
    for def in defs {
        let bundle = generate_definition_bundle(def, &def_map, ctx);
        type_items.extend(bundle.type_items);
        constructor_items.extend(bundle.constructor_items);
        helper_items.extend(bundle.helper_items);
        public_items.extend(bundle.public_items);
        wrapper_impls.extend(bundle.wrapper_impls);
    }

    // Generate nominal types (structs, enums) first, then From impls and Mappers.
    let mut nominal_type_items = TokenStream::new();
    let mut nominal_support_items = TokenStream::new();
    for def in defs {
        let mut nominal_gen = NominalTypeGen::new(def, &def_map);
        let sections = nominal_gen.generate_sections();
        nominal_type_items.extend(sections.type_items);
        nominal_support_items.extend(sections.support_items);
    }

    quote! {
        #imports

        // ========== Nominal Types ==========
        #nominal_type_items
        #nominal_support_items

        // ========== Combinator Definitions ==========
        #constructor_param_helpers
        #const_defs
        #type_items
        #constructor_items
        #helper_items

        // ========== Public API ==========
        #public_items

        // ========== Wrapper Impls ==========
        #wrapper_impls
    }
}

/// Generate const definitions for all combinators.
fn generate_const_definitions(defs: &[CombDef]) -> TokenStream {
    let mut tokens = TokenStream::new();
    for def in defs {
        for const_def in &def.const_defs {
            tokens.extend(generate_const_definition(const_def));
        }
    }
    tokens
}

/// Generate a single const definition.
fn generate_const_definition(const_def: &ConstDef) -> TokenStream {
    let name = format_ident!("{}", const_def.name);
    let ty: TokenStream = const_def.ty.parse().expect("valid type");
    let value = Literal::i128_unsuffixed(const_def.value);
    quote! {
        pub const #name: #ty = #value;
    }
}

/// Generate import statements.
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
        use vest_lib::regular::variant::{Either, Dispatch, Opt, OptThen, Choice};
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
    quote! {
        pub trait CombinatorParam<'a, T: Copy> {
            fn into_runtime_value(self) -> RuntimeValue<'a, T>;
            fn into_length(self) -> Length<'a>;
        }

        impl CombinatorParam<'static, u8> for u8 {
            fn into_runtime_value(self) -> RuntimeValue<'static, u8> { RuntimeValue::from_value(self) }
            fn into_length(self) -> Length<'static> { Length::from_value(self as usize) }
        }

        impl CombinatorParam<'static, u16> for u16 {
            fn into_runtime_value(self) -> RuntimeValue<'static, u16> { RuntimeValue::from_value(self) }
            fn into_length(self) -> Length<'static> { Length::from_value(self as usize) }
        }

        impl CombinatorParam<'static, u24> for u24 {
            fn into_runtime_value(self) -> RuntimeValue<'static, u24> { RuntimeValue::from_value(self) }
            fn into_length(self) -> Length<'static> { Length::from_value(self.as_u32() as usize) }
        }

        impl CombinatorParam<'static, u32> for u32 {
            fn into_runtime_value(self) -> RuntimeValue<'static, u32> { RuntimeValue::from_value(self) }
            fn into_length(self) -> Length<'static> { Length::from_value(self as usize) }
        }

        impl CombinatorParam<'static, u64> for u64 {
            fn into_runtime_value(self) -> RuntimeValue<'static, u64> { RuntimeValue::from_value(self) }
            fn into_length(self) -> Length<'static> { Length::from_value(self as usize) }
        }

        impl<'a> CombinatorParam<'a, u8> for &'a mut u8 {
            fn into_runtime_value(self) -> RuntimeValue<'a, u8> { RuntimeValue::from_mut(self) }
            fn into_length(self) -> Length<'a> { Length::from_u8_mut(self) }
        }

        impl<'a> CombinatorParam<'a, u16> for &'a mut u16 {
            fn into_runtime_value(self) -> RuntimeValue<'a, u16> { RuntimeValue::from_mut(self) }
            fn into_length(self) -> Length<'a> { Length::from_u16_mut(self) }
        }

        impl<'a> CombinatorParam<'a, u24> for &'a mut u24 {
            fn into_runtime_value(self) -> RuntimeValue<'a, u24> { RuntimeValue::from_mut(self) }
            fn into_length(self) -> Length<'a> { Length::from_value(self.as_u32() as usize) }
        }

        impl<'a> CombinatorParam<'a, u32> for &'a mut u32 {
            fn into_runtime_value(self) -> RuntimeValue<'a, u32> { RuntimeValue::from_mut(self) }
            fn into_length(self) -> Length<'a> { Length::from_u32_mut(self) }
        }

        impl<'a> CombinatorParam<'a, u64> for &'a mut u64 {
            fn into_runtime_value(self) -> RuntimeValue<'a, u64> { RuntimeValue::from_mut(self) }
            fn into_length(self) -> Length<'a> { Length::from_u64_mut(self) }
        }
    }
}

fn generate_definition_bundle<'a>(
    def: &'a CombDef,
    defs: &'a HashMap<String, &'a CombDef>,
    ctx: &'a TokenCtx<'a>,
) -> DefinitionBundle {
    let mut emitter = DefEmitter::new(def, defs, ctx);
    let env = emitter.top_level_env();
    let ctor_env = emitter.top_level_ctor_env();
    let body_expr_raw =
        emitter.top_level_body_expr_tokens_mode(&def.body, &ctor_env, EmitMode::Unified);
    let body_type_raw = emitter.top_level_body_type_tokens(&def.body, &env);
    let (body_expr, body_type) = emitter.wrap_top_level_mapper_tokens(body_expr_raw, body_type_raw);
    let body_type_gen = emitter.top_level_generate_alias_body_type_tokens();
    let type_item = emitter.type_item(body_type, body_type_gen);
    let ctor_fn = emitter.constructor_fn(body_expr);
    let parse_fn = emitter.parse_fn();
    let serialize_fn = emitter.serialize_fn();
    let length_fn = emitter.length_fn();
    let generate_fn = emitter.generate_fn();
    let wrapper_impl = emitter.wrapper_impl_item();
    let helper_items = emitter.helper_items();

    DefinitionBundle {
        type_items: type_item,
        constructor_items: quote! {
            #ctor_fn
        },
        helper_items,
        public_items: quote! {
            #parse_fn
            #serialize_fn
            #length_fn
            #generate_fn
        },
        wrapper_impls: wrapper_impl,
    }
}

struct DefinitionBundle {
    type_items: TokenStream,
    constructor_items: TokenStream,
    helper_items: TokenStream,
    public_items: TokenStream,
    wrapper_impls: TokenStream,
}

#[derive(Clone)]
struct ParamSpec {
    name: String,
    ident: Ident,
    ty: ValueType,
    needs_generate_ref: bool,
}

impl ParamSpec {
    fn ctor_generic_ident(&self) -> Ident {
        format_ident!("{}Arg", snake_to_upper_camel(&self.name))
    }
}

#[derive(Clone)]
struct Binding {
    ident: Ident,
    ty: ValueType,
    is_mut_ref: bool,
    is_generic_int_param: bool,
}

type ValueEnv = BTreeMap<String, Binding>;

#[derive(Clone, Debug)]
enum ValueType {
    U8,
    U16,
    U24,
    U32,
    U64,
    ByteSlice,
    Unit,
    Tuple(Vec<ValueType>),
    Either(Box<ValueType>, Box<ValueType>),
    Option(Box<ValueType>),
    Slice(Box<ValueType>),
}

impl ValueType {
    fn to_tokens(&self) -> TokenStream {
        match self {
            ValueType::U8 => quote! { u8 },
            ValueType::U16 => quote! { u16 },
            ValueType::U24 => quote! { u24 },
            ValueType::U32 => quote! { u32 },
            ValueType::U64 => quote! { u64 },
            ValueType::ByteSlice => quote! { &'static [u8] },
            ValueType::Unit => quote! { () },
            ValueType::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    elems[0].to_tokens()
                } else {
                    let elem_tokens: Vec<TokenStream> =
                        elems.iter().map(ValueType::to_tokens).collect();
                    build_nested_pair_type(&elem_tokens)
                }
            }
            ValueType::Either(left, right) => {
                let left = left.to_tokens();
                let right = right.to_tokens();
                quote! { Either<#left, #right> }
            }
            ValueType::Option(inner) => {
                let inner = inner.to_tokens();
                quote! { Option<#inner> }
            }
            ValueType::Slice(inner) => {
                let inner = inner.to_tokens();
                quote! { &[#inner] }
            }
        }
    }

    fn to_usize_tokens(&self, expr: TokenStream) -> TokenStream {
        match self {
            ValueType::U24 => quote! { (#expr).as_u32() as usize },
            _ => quote! { #expr as usize },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PublicFnKind {
    Parse,
    Serialize,
    Length,
    Generate,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EmitMode {
    Parse,
    Generate,
    Unified,
}

struct DefEmitter<'a> {
    def: &'a CombDef,
    defs: &'a HashMap<String, &'a CombDef>,
    ctx: &'a TokenCtx<'a>,
    param_specs: Vec<ParamSpec>,
    needs_runtime_ref: bool,
    helpers: Vec<TokenStream>,
    emitted_helpers: HashSet<String>,
}

impl<'a> DefEmitter<'a> {
    fn new(
        def: &'a CombDef,
        defs: &'a HashMap<String, &'a CombDef>,
        ctx: &'a TokenCtx<'a>,
    ) -> Self {
        let mut emitter = Self {
            def,
            defs,
            ctx,
            param_specs: Vec::new(),
            needs_runtime_ref: false,
            helpers: Vec::new(),
            emitted_helpers: HashSet::new(),
        };
        let param_specs: Vec<ParamSpec> = def
            .params
            .iter()
            .map(|param| ParamSpec {
                name: param.name.clone(),
                ident: format_ident!("{}", param.name),
                ty: emitter.value_type_of_comb(&param.ty),
                needs_generate_ref: emitter.param_needs_generate_ref(&def.body, &param.name),
            })
            .collect();
        emitter.needs_runtime_ref = param_specs.iter().any(|param| param.needs_generate_ref);
        emitter.param_specs = param_specs;
        emitter
    }

    fn top_level_env(&self) -> ValueEnv {
        self.build_top_level_env(false)
    }

    fn top_level_ctor_env(&self) -> ValueEnv {
        self.build_top_level_env(true)
    }

    fn build_top_level_env(&self, ctor_mode: bool) -> ValueEnv {
        self.param_specs
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    Binding {
                        ident: param.ident.clone(),
                        ty: param.ty.clone(),
                        is_mut_ref: false,
                        is_generic_int_param: ctor_mode && param.needs_generate_ref,
                    },
                )
            })
            .collect()
    }

    fn public_parse_type_tokens(&self, lt: TokenStream) -> TokenStream {
        public_parse_type_tokens(self.def, self.defs, lt)
    }

    fn public_borrow_type_tokens(&self) -> TokenStream {
        public_borrow_type_tokens(self.def, self.defs)
    }

    fn public_owned_type_tokens(&self) -> TokenStream {
        public_owned_type_tokens(self.def, self.defs)
    }

    fn concrete_parse_type_tokens(&self, comb: &CombIR, lt: TokenStream) -> TokenStream {
        concrete_parse_type_tokens(self.def, self.defs, comb, lt)
    }

    fn concrete_borrow_type_tokens(&self, comb: &CombIR) -> TokenStream {
        concrete_borrow_type_tokens(self.def, self.defs, comb)
    }

    fn concrete_owned_type_tokens(&self, comb: &CombIR) -> TokenStream {
        concrete_owned_type_tokens(self.def, self.defs, comb)
    }

    fn helper_items(&self) -> TokenStream {
        let helpers = &self.helpers;
        quote! { #(#helpers)* }
    }

    fn needs_runtime_ref(&self) -> bool {
        self.needs_runtime_ref
    }

    fn top_level_generate_alias_body_type_tokens(&self) -> Option<TokenStream> {
        if !self.needs_runtime_ref() {
            return None;
        }

        let env = self.top_level_env();
        let body_type_raw = self.top_level_body_type_tokens_mode_with_options(
            &self.def.body,
            &env,
            Some(quote! { 'x }),
            true,
        );
        let body_type = if let Some(mapper) = self.top_level_mapper_ident() {
            quote! { Mapped<#body_type_raw, #mapper> }
        } else {
            body_type_raw
        };
        Some(body_type)
    }

    fn type_item(&self, body_type: TokenStream, body_type_gen: Option<TokenStream>) -> TokenStream {
        let upper_camel_name = snake_to_upper_camel(&self.def.name);
        let combinator_type_name = format_ident!("{}Combinator", upper_camel_name);
        let alias_name = format_ident!("{}CombinatorAlias", upper_camel_name);
        let type_doc = format!("Type alias for {} combinator", self.def.name);
        let struct_doc = format!("Wrapper struct for {} combinator", self.def.name);

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
        let combinator_type_name =
            format_ident!("{}Combinator", snake_to_upper_camel(&self.def.name));

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

    fn constructor_param_generic_idents(&self) -> Vec<Ident> {
        self.param_specs
            .iter()
            .filter(|param| param.needs_generate_ref)
            .map(ParamSpec::ctor_generic_ident)
            .collect()
    }

    fn constructor_param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .map(|param| {
                let ident = &param.ident;
                if param.needs_generate_ref {
                    let arg_ty = param.ctor_generic_ident();
                    quote! { #ident: #arg_ty }
                } else {
                    let ty = param.ty.to_tokens();
                    quote! { #ident: #ty }
                }
            })
            .collect()
    }

    fn constructor_where_bounds(&self, lt: TokenStream) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .filter(|param| param.needs_generate_ref)
            .map(|param| {
                let arg_ty = param.ctor_generic_ident();
                let raw_ty = param.ty.to_tokens();
                quote! { #arg_ty: CombinatorParam<#lt, #raw_ty> }
            })
            .collect()
    }

    fn constructor_return_type(&self) -> TokenStream {
        let combinator_type = format_ident!("{}Combinator", snake_to_upper_camel(&self.def.name));
        if self.needs_runtime_ref() {
            let alias_name =
                format_ident!("{}CombinatorAlias", snake_to_upper_camel(&self.def.name));
            quote! { #combinator_type<#alias_name<'a>> }
        } else {
            quote! { #combinator_type }
        }
    }

    fn constructor_fn(&self, body_expr: TokenStream) -> TokenStream {
        let fn_name = format_ident!("{}", self.def.name);
        let combinator_type = self.constructor_return_type();
        let ctor_name = format_ident!("{}Combinator", snake_to_upper_camel(&self.def.name));
        let params = self.constructor_param_list_tokens();
        let ctor_doc = format!("Constructor for {} combinator", self.def.name);

        if params.is_empty() {
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name() -> #combinator_type {
                    #ctor_name(#body_expr)
                }
            }
        } else if self.needs_runtime_ref() {
            let generic_args = self.constructor_param_generic_idents();
            let where_bounds = self.constructor_where_bounds(quote! { 'a });
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name<'a, #(#generic_args),*>(#(#params),*) -> #combinator_type
                where
                    #(#where_bounds,)*
                {
                    #ctor_name(#body_expr)
                }
            }
        } else {
            quote! {
                #[doc = #ctor_doc]
                pub fn #fn_name(#(#params),*) -> #combinator_type {
                    #ctor_name(#body_expr)
                }
            }
        }
    }

    fn parse_fn(&self) -> TokenStream {
        let fn_name = format_ident!(
            "{}_{}",
            self.public_fn_prefix(PublicFnKind::Parse),
            self.def.name
        );
        let params = self.param_list_tokens();
        let parse_doc = format!("Parse function for {} combinator", self.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();
        let parse_type = self.public_parse_type_tokens(quote! { 'p });

        if params.is_empty() {
            quote! {
                #[doc = #parse_doc]
                pub fn #fn_name<'p>(input: &'p [u8]) -> Result<(usize, #parse_type), ParseError> {
                    let combinator = #combinator_ctor;
                    combinator.parse(input)
                }
            }
        } else {
            quote! {
                #[doc = #parse_doc]
                pub fn #fn_name<'p>(input: &'p [u8], #(#params),*) -> Result<(usize, #parse_type), ParseError> {
                    let combinator = #combinator_ctor;
                    combinator.parse(input)
                }
            }
        }
    }

    fn serialize_fn(&self) -> TokenStream {
        let fn_name = format_ident!(
            "{}_{}",
            self.public_fn_prefix(PublicFnKind::Serialize),
            self.def.name
        );
        let borrow_type = self.public_borrow_type_tokens();
        let params = self.param_list_tokens();
        let serialize_doc = format!("Serialize function for {} combinator", self.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();

        if params.is_empty() {
            quote! {
                #[doc = #serialize_doc]
                pub fn #fn_name<'s>(v: #borrow_type, data: &mut Vec<u8>, pos: usize) -> Result<usize, SerializeError> {
                    let combinator = #combinator_ctor;
                    combinator.serialize(v, data, pos)
                }
            }
        } else {
            quote! {
                #[doc = #serialize_doc]
                pub fn #fn_name<'s>(v: #borrow_type, data: &mut Vec<u8>, pos: usize, #(#params),*) -> Result<usize, SerializeError> {
                    let combinator = #combinator_ctor;
                    combinator.serialize(v, data, pos)
                }
            }
        }
    }

    fn length_fn(&self) -> TokenStream {
        let fn_name = format_ident!(
            "{}{}",
            self.def.name,
            self.public_fn_suffix(PublicFnKind::Length)
        );
        let borrow_type = self.public_borrow_type_tokens();
        let params = self.param_list_tokens();
        let length_doc = format!("Length function for {} combinator", self.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();

        if params.is_empty() {
            quote! {
                #[doc = #length_doc]
                pub fn #fn_name<'s>(v: #borrow_type) -> usize {
                    let combinator = #combinator_ctor;
                    combinator.length(v)
                }
            }
        } else {
            quote! {
                #[doc = #length_doc]
                pub fn #fn_name<'s>(v: #borrow_type, #(#params),*) -> usize {
                    let combinator = #combinator_ctor;
                    combinator.length(v)
                }
            }
        }
    }

    fn generate_fn(&self) -> TokenStream {
        let fn_name = format_ident!(
            "{}_{}",
            self.public_fn_prefix(PublicFnKind::Generate),
            self.def.name
        );
        let owned_type = self.public_owned_type_tokens();
        let params = self.generate_param_list_tokens();
        let generate_doc = format!("Generate function for {} combinator", self.def.name);
        let combinator_ctor = self.public_ctor_call_tokens();

        if params.is_empty() {
            quote! {
                #[doc = #generate_doc]
                pub fn #fn_name(g: &mut GenSt) -> GResult<#owned_type, GenerateError> {
                    let mut combinator = #combinator_ctor;
                    combinator.generate(g)
                }
            }
        } else if self.needs_runtime_ref() {
            quote! {
                #[doc = #generate_doc]
                pub fn #fn_name<'g>(g: &mut GenSt, #(#params),*) -> GResult<#owned_type, GenerateError> {
                    let mut combinator = #combinator_ctor;
                    combinator.generate(g)
                }
            }
        } else {
            quote! {
                #[doc = #generate_doc]
                pub fn #fn_name(g: &mut GenSt, #(#params),*) -> GResult<#owned_type, GenerateError> {
                    let mut combinator = #combinator_ctor;
                    combinator.generate(g)
                }
            }
        }
    }

    fn param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_list_tokens_with_lifetime(false)
    }

    fn generate_param_list_tokens(&self) -> Vec<TokenStream> {
        self.param_list_tokens_with_lifetime(true)
    }

    fn param_list_tokens_with_lifetime(&self, generate_mode: bool) -> Vec<TokenStream> {
        self.param_specs
            .iter()
            .map(|param| {
                let ident = &param.ident;
                let ty = param.ty.to_tokens();
                if generate_mode && param.needs_generate_ref {
                    quote! { #ident: &'g mut #ty }
                } else {
                    quote! { #ident: #ty }
                }
            })
            .collect()
    }

    fn param_idents(&self) -> Vec<Ident> {
        self.param_specs
            .iter()
            .map(|param| param.ident.clone())
            .collect()
    }

    fn call_ctor_tokens(&self, fn_name: &Ident, args: &[Ident]) -> TokenStream {
        if args.is_empty() {
            quote! { #fn_name() }
        } else {
            quote! { #fn_name(#(#args),*) }
        }
    }

    fn public_ctor_call_tokens(&self) -> TokenStream {
        let combinator_fn = format_ident!("{}", self.def.name);
        let arg_names = self.param_idents();
        self.call_ctor_tokens(&combinator_fn, &arg_names)
    }

    fn public_fn_prefix(&self, kind: PublicFnKind) -> &'static str {
        match kind {
            PublicFnKind::Parse => "parse",
            PublicFnKind::Serialize => "serialize",
            PublicFnKind::Generate => "generate",
            PublicFnKind::Length => "",
        }
    }

    fn public_fn_suffix(&self, kind: PublicFnKind) -> &'static str {
        match kind {
            PublicFnKind::Length => "_len",
            _ => "",
        }
    }

    fn top_level_body_type_tokens(&self, comb: &CombIR, env: &ValueEnv) -> TokenStream {
        self.top_level_body_type_tokens_mode_with_options(comb, env, None, false)
    }

    fn top_level_body_type_tokens_mode_with_options(
        &self,
        comb: &CombIR,
        env: &ValueEnv,
        runtime_lt: Option<TokenStream>,
        use_dispatch_defaults: bool,
    ) -> TokenStream {
        match comb {
            CombIR::Named { name, args } => {
                if runtime_lt.is_some() {
                    if let Some(def) = self.defs.get(name) {
                        let named_env = self.named_arg_env(def, args, env);
                        return self.named_combinator_type_tokens(def, &named_env, runtime_lt);
                    }
                }

                let type_name = format_ident!("{}Combinator", snake_to_upper_camel(name));
                quote! { #type_name }
            }
            _ => self.comb_type_tokens_with_lt_inner(
                comb,
                env,
                &[],
                runtime_lt,
                use_dispatch_defaults,
            ),
        }
    }

    fn top_level_mapper_ident(&self) -> Option<Ident> {
        if self.comb_emits_mapper(&self.def.body) {
            Some(format_ident!(
                "{}Mapper",
                snake_to_upper_camel(&self.def.name)
            ))
        } else {
            None
        }
    }

    fn comb_emits_mapper(&self, comb: &CombIR) -> bool {
        match comb {
            CombIR::Tuple(elems) => !elems.is_empty(),
            CombIR::Pair { .. } | CombIR::Dispatch { .. } => true,
            CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::AndThen { inner, .. } => self.comb_emits_mapper(inner),
            _ => false,
        }
    }

    fn wrap_top_level_mapper_tokens(
        &self,
        body_expr: TokenStream,
        body_type: TokenStream,
    ) -> (TokenStream, TokenStream) {
        if let Some(mapper) = self.top_level_mapper_ident() {
            (
                quote! { Mapped::new(#body_expr, #mapper) },
                quote! { Mapped<#body_type, #mapper> },
            )
        } else {
            (body_expr, body_type)
        }
    }

    fn top_level_body_expr_tokens_mode(
        &mut self,
        comb: &CombIR,
        env: &ValueEnv,
        mode: EmitMode,
    ) -> TokenStream {
        match comb {
            CombIR::Named { name, args } => {
                self.named_or_external_ctor_call_tokens(name, args, env, mode)
            }
            _ => self.comb_expr_tokens_mode(comb, env, &[], mode),
        }
    }

    fn named_combinator_type_tokens(
        &self,
        def: &CombDef,
        env: &ValueEnv,
        runtime_lt: Option<TokenStream>,
    ) -> TokenStream {
        let type_name = format_ident!("{}Combinator", snake_to_upper_camel(&def.name));
        if runtime_lt.is_none() || !env.values().any(|binding| binding.is_mut_ref) {
            return quote! { #type_name };
        }

        let emitter = DefEmitter::new(def, self.defs, self.ctx);
        if emitter.needs_runtime_ref() {
            let alias_name = format_ident!("{}CombinatorAlias", snake_to_upper_camel(&def.name));
            let runtime_lt = runtime_lt.expect("checked above");
            quote! { #type_name<#alias_name<#runtime_lt>> }
        } else {
            quote! { #type_name }
        }
    }

    fn named_ctor_call_tokens_mode(
        &self,
        def: &CombDef,
        args: &[ParamRef],
        env: &ValueEnv,
        mode: EmitMode,
    ) -> TokenStream {
        let fn_name = format_ident!("{}", def.name);
        let arg_tokens: Vec<TokenStream> = def
            .params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| {
                let needs_ref = self.param_needs_generate_ref(&def.body, &param.name);
                match arg {
                    ParamRef::Dependent(name) => {
                        if let Some(binding) = env.get(name) {
                            if needs_ref
                                && (binding.is_mut_ref
                                    || (mode == EmitMode::Unified && binding.is_generic_int_param))
                            {
                                let ident = &binding.ident;
                                quote! { #ident }
                            } else {
                                self.binding_read_tokens(binding)
                            }
                        } else {
                            let ident = format_ident!("{}", name);
                            quote! { #ident }
                        }
                    }
                }
            })
            .collect();
        if arg_tokens.is_empty() {
            quote! { #fn_name() }
        } else {
            quote! { #fn_name(#(#arg_tokens),*) }
        }
    }

    fn named_or_external_ctor_call_tokens(
        &self,
        name: &str,
        args: &[ParamRef],
        env: &ValueEnv,
        mode: EmitMode,
    ) -> TokenStream {
        if let Some(def) = self.defs.get(name) {
            self.named_ctor_call_tokens_mode(def, args, env, mode)
        } else {
            let fn_name = format_ident!("{}", name);
            let arg_tokens: Vec<TokenStream> = args
                .iter()
                .map(|arg| self.param_ref_tokens(arg, env))
                .collect();
            if arg_tokens.is_empty() {
                quote! { #fn_name() }
            } else {
                quote! { #fn_name(#(#arg_tokens),*) }
            }
        }
    }

    fn comb_expr_tokens_mode(
        &mut self,
        comb: &CombIR,
        env: &ValueEnv,
        path: &[usize],
        mode: EmitMode,
    ) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { U8 },
            CombIR::U16(Endian::Little) => quote! { U16Le },
            CombIR::U16(Endian::Big) => quote! { U16Be },
            CombIR::U24(Endian::Little) => quote! { U24Le },
            CombIR::U24(Endian::Big) => quote! { U24Be },
            CombIR::U32(Endian::Little) => quote! { U32Le },
            CombIR::U32(Endian::Big) => quote! { U32Be },
            CombIR::U64(Endian::Little) => quote! { U64Le },
            CombIR::U64(Endian::Big) => quote! { U64Be },

            CombIR::Fixed { len } => {
                let len_lit = Literal::usize_unsuffixed(*len);
                quote! { Fixed::<#len_lit> }
            }
            CombIR::Variable { len } => {
                let len_tokens = self.len_expr_tokens(len, env);
                quote! { Variable(#len_tokens) }
            }
            CombIR::Tail => quote! { Tail },

            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.comb_expr_tokens_mode(&elems[0].1, env, &child_path(path, 0), mode)
                } else {
                    let elem_tokens: Vec<TokenStream> = elems
                        .iter()
                        .enumerate()
                        .map(|(idx, (_, elem))| {
                            self.comb_expr_tokens_mode(elem, env, &child_path(path, idx), mode)
                        })
                        .collect();
                    build_nested_pair_expr(&elem_tokens)
                }
            }
            CombIR::Pair { fst, snd } => {
                let fst_tokens = self.comb_expr_tokens_mode(fst, env, &child_path(path, 0), mode);
                let helper = self.pair_helper_init(path, fst, snd, env);
                quote! { Pair::new(#fst_tokens, #helper) }
            }
            CombIR::Preceded { prefix, inner } => {
                let prefix_tokens =
                    self.comb_expr_tokens_mode(prefix, env, &child_path(path, 0), mode);
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 1), mode);
                quote! { Preceded(#prefix_tokens, #inner_tokens) }
            }
            CombIR::Terminated { inner, suffix } => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                let suffix_tokens =
                    self.comb_expr_tokens_mode(suffix, env, &child_path(path, 1), mode);
                quote! { Terminated(#inner_tokens, #suffix_tokens) }
            }

            CombIR::Choice(choices) => {
                if choices.is_empty() {
                    quote! { Fail("empty choice".into()) }
                } else {
                    let choice_tokens: Vec<TokenStream> = choices
                        .iter()
                        .enumerate()
                        .map(|(idx, choice)| {
                            self.comb_expr_tokens_mode(choice, env, &child_path(path, idx), mode)
                        })
                        .collect();
                    build_nested_choice_expr(&choice_tokens)
                }
            }
            CombIR::Dispatch { tag, branches } => {
                self.ensure_dispatch_case_helper(path, branches, env);
                let tag_tokens = self.tag_ref_tokens(tag, env, mode);
                let branch_tokens: Vec<TokenStream> = branches
                    .iter()
                    .enumerate()
                    .map(|(idx, (tag_val, comb))| {
                        let case_type = self.dispatch_helper_ident(path);
                        let variant = dispatch_variant_ident(idx);
                        let val_tokens = self.tag_value_tokens(tag_val);
                        let comb_tokens =
                            self.comb_expr_tokens_mode(comb, env, &child_path(path, idx), mode);
                        quote! { (#val_tokens, #case_type::#variant(#comb_tokens)) }
                    })
                    .collect();
                quote! { Dispatch::new(#tag_tokens, [#(#branch_tokens),*]) }
            }
            CombIR::Opt(inner) => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                quote! { Opt::new(#inner_tokens) }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_tokens = self.comb_expr_tokens_mode(fst, env, &child_path(path, 0), mode);
                let snd_tokens = self.comb_expr_tokens_mode(snd, env, &child_path(path, 1), mode);
                quote! { OptThen::new(#fst_tokens, #snd_tokens) }
            }

            CombIR::RepeatN { inner, count } => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                let count_tokens = self.len_expr_tokens(count, env);
                quote! { RepeatN::new(#inner_tokens, #count_tokens) }
            }
            CombIR::Repeat(inner) => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                quote! { Repeat::new(#inner_tokens) }
            }

            CombIR::Refined { inner, predicate } => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                let predicate_tokens = predicate_to_tokens(predicate, Some(inner));
                quote! { Refined { inner: #inner_tokens, predicate: #predicate_tokens } }
            }
            CombIR::Mapped { inner, mapper } => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                let mapper_name = format_ident!("{}", mapper.name);
                quote! { Mapped::new(#inner_tokens, #mapper_name) }
            }
            CombIR::AndThen { len_comb, inner } => {
                let len_tokens =
                    self.comb_expr_tokens_mode(len_comb, env, &child_path(path, 0), mode);
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 1), mode);
                quote! { AndThen(#len_tokens, #inner_tokens) }
            }
            CombIR::FixedLen { len, inner } => {
                let len_ctor = self.length_ctor_tokens(len, env, mode);
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                quote! {
                    FixedLen(
                        #len_ctor,
                        #inner_tokens,
                    )
                }
            }
            CombIR::CondEq { lhs, rhs, inner } => {
                let lhs_tokens = self.cond_tag_ref_tokens(lhs, env, mode);
                let rhs_tokens = self.tag_value_tokens(rhs);
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                quote! { CondEq { lhs: #lhs_tokens, rhs: #rhs_tokens, inner: #inner_tokens } }
            }

            CombIR::Tag { inner, value } => {
                let inner_tokens =
                    self.comb_expr_tokens_mode(inner, env, &child_path(path, 0), mode);
                let value_tokens = self.tag_value_tokens(value);
                quote! { Tag::new(#inner_tokens, #value_tokens) }
            }

            CombIR::Named { name, args } => {
                self.named_or_external_ctor_call_tokens(name, args, env, mode)
            }

            CombIR::End => quote! { End },
            CombIR::Success => quote! { Success },
            CombIR::Fail(msg) => {
                let msg_lit = Literal::string(msg);
                quote! { Fail(#msg_lit.into()) }
            }
        }
    }

    fn comb_type_tokens_with_lt(
        &self,
        comb: &CombIR,
        env: &ValueEnv,
        path: &[usize],
        use_runtime_lt: bool,
    ) -> TokenStream {
        self.comb_type_tokens_with_lt_inner(
            comb,
            env,
            path,
            use_runtime_lt.then(|| quote! { 'g }),
            false,
        )
    }

    fn comb_type_tokens_with_lt_inner(
        &self,
        comb: &CombIR,
        env: &ValueEnv,
        path: &[usize],
        runtime_lt: Option<TokenStream>,
        use_dispatch_defaults: bool,
    ) -> TokenStream {
        match comb {
            CombIR::U8 => quote! { U8 },
            CombIR::U16(Endian::Little) => quote! { U16Le },
            CombIR::U16(Endian::Big) => quote! { U16Be },
            CombIR::U24(Endian::Little) => quote! { U24Le },
            CombIR::U24(Endian::Big) => quote! { U24Be },
            CombIR::U32(Endian::Little) => quote! { U32Le },
            CombIR::U32(Endian::Big) => quote! { U32Be },
            CombIR::U64(Endian::Little) => quote! { U64Le },
            CombIR::U64(Endian::Big) => quote! { U64Be },

            CombIR::Fixed { len } => {
                let len_lit = Literal::usize_unsuffixed(*len);
                quote! { Fixed<#len_lit> }
            }
            CombIR::Variable { .. } => quote! { Variable },
            CombIR::Tail => quote! { Tail },

            CombIR::Tuple(elems) => {
                if elems.is_empty() {
                    quote! { () }
                } else if elems.len() == 1 {
                    self.comb_type_tokens_with_lt_inner(
                        &elems[0].1,
                        env,
                        &child_path(path, 0),
                        runtime_lt,
                        use_dispatch_defaults,
                    )
                } else {
                    let elem_types: Vec<TokenStream> = elems
                        .iter()
                        .enumerate()
                        .map(|(idx, (_, elem))| {
                            self.comb_type_tokens_with_lt_inner(
                                elem,
                                env,
                                &child_path(path, idx),
                                runtime_lt.clone(),
                                use_dispatch_defaults,
                            )
                        })
                        .collect();
                    build_nested_pair_type(&elem_types)
                }
            }
            CombIR::Pair { fst, .. } => {
                let fst_type = self.comb_type_tokens_with_lt_inner(
                    fst,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                let helper = self.helper_ident(path);
                quote! { Pair<#fst_type, #helper> }
            }
            CombIR::Preceded { prefix, inner } => {
                let prefix_type = self.comb_type_tokens_with_lt_inner(
                    prefix,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 1),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { Preceded<#prefix_type, #inner_type> }
            }
            CombIR::Terminated { inner, suffix } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let suffix_type = self.comb_type_tokens_with_lt_inner(
                    suffix,
                    env,
                    &child_path(path, 1),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { Terminated<#inner_type, #suffix_type> }
            }

            CombIR::Choice(choices) => {
                if choices.is_empty() {
                    quote! { Fail }
                } else if choices.len() == 1 {
                    self.comb_type_tokens_with_lt_inner(
                        &choices[0],
                        env,
                        &child_path(path, 0),
                        runtime_lt,
                        use_dispatch_defaults,
                    )
                } else {
                    let choice_types: Vec<TokenStream> = choices
                        .iter()
                        .enumerate()
                        .map(|(idx, choice)| {
                            self.comb_type_tokens_with_lt_inner(
                                choice,
                                env,
                                &child_path(path, idx),
                                runtime_lt.clone(),
                                use_dispatch_defaults,
                            )
                        })
                        .collect();
                    build_nested_choice_type(&choice_types)
                }
            }
            CombIR::Dispatch { branches, tag } => {
                if branches.is_empty() {
                    quote! { Fail }
                } else {
                    let branch_type = self.dispatch_helper_ident(path);
                    let n = Literal::usize_unsuffixed(branches.len());
                    let tag_type = dispatch_tag_type_tokens_for_ref(tag, env);
                    let dispatch_lt = runtime_lt.clone().unwrap_or_else(|| quote! { 'static });
                    if runtime_lt.is_some() && !use_dispatch_defaults {
                        let branch_types: Vec<TokenStream> = branches
                            .iter()
                            .enumerate()
                            .map(|(idx, (_, comb))| {
                                self.comb_type_tokens_with_lt_inner(
                                    comb,
                                    env,
                                    &child_path(path, idx),
                                    runtime_lt.clone(),
                                    use_dispatch_defaults,
                                )
                            })
                            .collect();
                        quote! { Dispatch<#dispatch_lt, #tag_type, #branch_type<#(#branch_types),*>, #n> }
                    } else {
                        quote! { Dispatch<#dispatch_lt, #tag_type, #branch_type, #n> }
                    }
                }
            }
            CombIR::Opt(inner) => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { Opt<#inner_type> }
            }
            CombIR::OptThen { fst, snd } => {
                let fst_type = self.comb_type_tokens_with_lt_inner(
                    fst,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let snd_type = self.comb_type_tokens_with_lt_inner(
                    snd,
                    env,
                    &child_path(path, 1),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { OptThen<#fst_type, #snd_type> }
            }

            CombIR::RepeatN { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { RepeatN<#inner_type> }
            }
            CombIR::Repeat(inner) => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { Repeat<#inner_type> }
            }

            CombIR::Refined { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                let pred_type = refined_pred_fn_type_tokens(inner);
                quote! { Refined<#inner_type, #pred_type> }
            }
            CombIR::Mapped { inner, mapper } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                let mapper_name = format_ident!("{}", mapper.name);
                quote! { Mapped<#inner_type, #mapper_name> }
            }
            CombIR::AndThen { len_comb, inner } => {
                let len_type = self.comb_type_tokens_with_lt_inner(
                    len_comb,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 1),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                quote! { AndThen<#len_type, #inner_type> }
            }
            CombIR::FixedLen { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let fixed_len_lt = runtime_lt.unwrap_or_else(|| quote! { 'static });
                quote! { FixedLen<#fixed_len_lt, #inner_type> }
            }
            CombIR::CondEq { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt.clone(),
                    use_dispatch_defaults,
                );
                let cond_lt = runtime_lt.unwrap_or_else(|| quote! { 'static });
                quote! { CondEq<#cond_lt, u8, #inner_type> }
            }

            CombIR::Tag { inner, value } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    runtime_lt,
                    use_dispatch_defaults,
                );
                let tag_type = tag_value_type_tokens(value, inner);
                quote! { Tag<#inner_type, #tag_type> }
            }

            CombIR::Named { name, args } => {
                if runtime_lt.is_some() {
                    if let Some(def) = self.defs.get(name) {
                        let named_env = self.named_arg_env(def, args, env);
                        return self.named_combinator_type_tokens(def, &named_env, runtime_lt);
                    }
                }

                let type_name = format_ident!("{}Combinator", snake_to_upper_camel(name));
                quote! { #type_name }
            }

            CombIR::End => quote! { End },
            CombIR::Success => quote! { Success },
            CombIR::Fail(_) => quote! { Fail },
        }
    }

    fn pair_helper_init(
        &mut self,
        path: &[usize],
        fst: &CombIR,
        snd: &DepCombIR,
        outer_env: &ValueEnv,
    ) -> TokenStream {
        self.ensure_pair_helper(path, fst, snd, outer_env);
        let helper = self.helper_ident(path);
        let used_names = used_names_in_comb(&snd.comb);
        let capture_names = capture_names(&used_names, outer_env, &snd.dep_names);

        let field_inits: Vec<TokenStream> = capture_names
            .iter()
            .map(|name| {
                let binding = &outer_env[name];
                let ident = &binding.ident;
                quote! { #ident: #ident }
            })
            .collect();

        quote! { #helper { #(#field_inits,)* } }
    }

    fn ensure_pair_helper(
        &mut self,
        path: &[usize],
        fst: &CombIR,
        snd: &DepCombIR,
        outer_env: &ValueEnv,
    ) {
        let key = helper_key(path);
        if !self.emitted_helpers.insert(key) {
            return;
        }

        let helper = self.helper_ident(path);
        let fst_type = self.comb_type_tokens_with_lt(fst, outer_env, &child_path(path, 0), false);
        let fst_stype = self.concrete_borrow_type_tokens(fst);
        let fst_gtype = self.concrete_owned_type_tokens(fst);

        let used_names = used_names_in_comb(&snd.comb);
        let capture_names = capture_names(&used_names, outer_env, &snd.dep_names);

        let field_defs: Vec<TokenStream> = capture_names
            .iter()
            .map(|name| {
                let ident = format_ident!("{}", name);
                let ty = outer_env[name].ty.to_tokens();
                quote! { #ident: #ty }
            })
            .collect();

        let capture_lets: Vec<TokenStream> = capture_names
            .iter()
            .map(|name| {
                let ident = format_ident!("{}", name);
                quote! { let #ident = self.#ident; }
            })
            .collect();

        let mut inner_env = ValueEnv::new();
        for name in &capture_names {
            let ident = format_ident!("{}", name);
            inner_env.insert(
                name.clone(),
                Binding {
                    ident,
                    ty: outer_env[name].ty.clone(),
                    is_mut_ref: false,
                    is_generic_int_param: false,
                },
            );
        }

        let mut inner_env_gen = inner_env.clone();
        let dep_parse_lets =
            self.dep_binding_lets(fst, &snd.dep_names, &mut inner_env, EmitMode::Parse);
        let dep_gen_lets =
            self.dep_binding_lets(fst, &snd.dep_names, &mut inner_env_gen, EmitMode::Generate);

        let snd_expr_parse = self.comb_expr_tokens_mode(
            &snd.comb,
            &inner_env,
            &child_path(path, 1),
            EmitMode::Parse,
        );
        let snd_expr_gen = self.comb_expr_tokens_mode(
            &snd.comb,
            &inner_env_gen,
            &child_path(path, 1),
            EmitMode::Generate,
        );
        let snd_type =
            self.comb_type_tokens_with_lt(&snd.comb, &inner_env, &child_path(path, 1), false);
        let snd_gen_type =
            self.comb_type_tokens_with_lt(&snd.comb, &inner_env_gen, &child_path(path, 1), true);
        let helper_item = quote! {
            #[derive(Clone, Copy)]
            pub struct #helper {
                #(#field_defs,)*
            }

            impl DepCombinator<#fst_type, [u8], Vec<u8>> for #helper {
                type Out = #snd_type;
                type OutGen<'g> = #snd_gen_type;

                fn dep_snd<'s>(&self, fst: #fst_stype) -> Self::Out {
                    let fst: #fst_stype = fst;
                    #(#capture_lets)*
                    #(#dep_parse_lets)*
                    #snd_expr_parse
                }

                fn dep_snd_gen<'g>(&self, fst: &'g mut #fst_gtype) -> Self::OutGen<'g> {
                    let fst: &'g mut #fst_gtype = fst;
                    #(#capture_lets)*
                    #(#dep_gen_lets)*
                    #snd_expr_gen
                }
            }
        };

        self.helpers.push(helper_item);
    }

    fn ensure_dispatch_case_helper(
        &mut self,
        path: &[usize],
        branches: &[(TagValue, CombIR)],
        env: &ValueEnv,
    ) {
        let key = dispatch_helper_key(path);
        if !self.emitted_helpers.insert(key) {
            return;
        }

        let helper = self.dispatch_helper_ident(path);
        let default_branch_types: Vec<TokenStream> = branches
            .iter()
            .enumerate()
            .map(|(idx, (_, comb))| {
                self.comb_type_tokens_with_lt(comb, env, &child_path(path, idx), false)
            })
            .collect();
        let branch_params: Vec<Ident> = (0..branches.len())
            .map(|idx| format_ident!("C{}", idx))
            .collect();

        let variant_defs: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, ty)| {
                let variant = dispatch_variant_ident(idx);
                quote! { #variant(#ty) }
            })
            .collect();

        let where_bounds: Vec<TokenStream> = branch_params
            .iter()
            .zip(branches.iter())
            .map(|(ty, (_, comb))| {
                let parse_ty = self.concrete_parse_type_tokens(comb, quote! { 'p });
                let borrow_ty = self.concrete_borrow_type_tokens(comb);
                let owned_ty = self.concrete_owned_type_tokens(comb);
                quote! {
                    for<'p, 's> #ty: Combinator<
                        [u8],
                        Vec<u8>,
                        Type<'p> = #parse_ty,
                        SType<'s> = #borrow_ty,
                        GType = #owned_ty,
                    >
                }
            })
            .collect();

        let parse_type = build_nested_either_type(
            &branches
                .iter()
                .map(|(_, comb)| self.concrete_parse_type_tokens(comb, quote! { 'p }))
                .collect::<Vec<_>>(),
        );
        let serialize_type = build_nested_either_type(
            &branches
                .iter()
                .map(|(_, comb)| self.concrete_borrow_type_tokens(comb))
                .collect::<Vec<_>>(),
        );
        let generate_type = build_nested_either_type(
            &branches
                .iter()
                .map(|(_, comb)| self.concrete_owned_type_tokens(comb))
                .collect::<Vec<_>>(),
        );

        let parse_arms: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let variant = dispatch_variant_ident(idx);
                let wrapped = either_wrap_expr(quote! { v }, idx, branch_params.len());
                quote! {
                    #helper::#variant(inner) => {
                        let (n, v) = inner.parse(s)?;
                        Ok((n, #wrapped))
                    }
                }
            })
            .collect();

        let generate_arms: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let variant = dispatch_variant_ident(idx);
                let wrapped = either_wrap_expr(quote! { v }, idx, branch_params.len());
                quote! {
                    #helper::#variant(inner) => {
                        let (n, v) = inner.generate(g)?;
                        Ok((n, #wrapped))
                    }
                }
            })
            .collect();

        let length_arms: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let variant = dispatch_variant_ident(idx);
                let value = format_ident!("v{}", idx);
                let value_pat = either_value_pattern(&value, idx, branch_params.len());
                quote! {
                    (#helper::#variant(inner), #value_pat) =>
                        inner.length(#value),
                }
            })
            .collect();

        let serialize_arms: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let variant = dispatch_variant_ident(idx);
                let value = format_ident!("v{}", idx);
                let value_pat = either_value_pattern(&value, idx, branch_params.len());
                quote! {
                    (#helper::#variant(inner), #value_pat) =>
                        inner.serialize(#value, data, pos),
                }
            })
            .collect();

        let wf_arms: Vec<TokenStream> = branch_params
            .iter()
            .enumerate()
            .map(|(idx, _)| {
                let variant = dispatch_variant_ident(idx);
                let value = format_ident!("v{}", idx);
                let value_pat = either_value_pattern(&value, idx, branch_params.len());
                quote! {
                    (#helper::#variant(inner), #value_pat) =>
                        inner.well_formed(#value),
                }
            })
            .collect();

        let helper_item = quote! {
            pub enum #helper<#(#branch_params = #default_branch_types),*> {
                #(#variant_defs,)*
            }

            impl<#(#branch_params),*> Combinator<[u8], Vec<u8>> for #helper<#(#branch_params),*>
            where
                #(#where_bounds,)*
            {
                type Type<'p> = #parse_type;
                type SType<'s> = #serialize_type;
                type GType = #generate_type;

                fn length<'s>(&self, v: Self::SType<'s>) -> usize where [u8]: 's {
                    match (self, v) {
                        #(#length_arms)*
                        _ => panic!("dispatch branch combinator does not match value"),
                    }
                }

                fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError> where [u8]: 'p {
                    match self {
                        #(#parse_arms)*
                    }
                }

                fn serialize<'s>(&self, v: Self::SType<'s>, data: &mut Vec<u8>, pos: usize) -> Result<usize, SerializeError> where [u8]: 's {
                    match (self, v) {
                        #(#serialize_arms)*
                        _ => Err(SerializeError::Other("dispatch branch combinator does not match value".into())),
                    }
                }

                fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
                    match self {
                        #(#generate_arms)*
                    }
                }

                fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool where [u8]: 's {
                    match (self, v) {
                        #(#wf_arms)*
                        _ => false,
                    }
                }
            }
        };

        self.helpers.push(helper_item);
    }

    fn dispatch_helper_ident(&self, path: &[usize]) -> Ident {
        let base = format!("{}DispatchCase", snake_to_upper_camel(&self.def.name));
        if path.is_empty() {
            format_ident!("{}", base)
        } else {
            let suffix = path
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("_");
            format_ident!("{}{}", base, suffix)
        }
    }

    fn dep_binding_lets(
        &self,
        fst: &CombIR,
        dep_names: &[String],
        env: &mut ValueEnv,
        mode: EmitMode,
    ) -> Vec<TokenStream> {
        if dep_names.is_empty() {
            return Vec::new();
        }

        let dep_types = match fst {
            CombIR::Tuple(elems) if dep_names.len() > 1 => {
                if elems.len() < dep_names.len() {
                    todo!(
                        "Dependent binding arity mismatch handling is incomplete: have {} tuple elements for {} dependent names",
                        elems.len(),
                        dep_names.len()
                    );
                }
                elems
                    .iter()
                    .map(|(_, elem)| self.value_type_of_comb(elem))
                    .collect::<Vec<_>>()
            }
            _ => vec![self.last_bound_type(fst)],
        };

        // Build identifiers and register them in the environment
        let idents: Vec<_> = dep_names
            .iter()
            .enumerate()
            .map(|(idx, name)| {
                let ident = format_ident!("{}", name);
                let ty = dep_types
                    .get(idx)
                    .cloned()
                    .unwrap_or_else(|| self.last_bound_type(fst));
                env.insert(
                    name.clone(),
                    Binding {
                        ident: ident.clone(),
                        ty,
                        is_mut_ref: mode == EmitMode::Generate,
                        is_generic_int_param: false,
                    },
                );
                ident
            })
            .collect();

        // For single binding, just use the fst directly
        if dep_names.len() == 1 {
            let ident = &idents[0];
            return vec![quote! { let #ident = fst; }];
        }

        // For multiple bindings, use pattern destructuring to avoid field access
        // on generic associated types. Build a right-associative nested pattern.
        let pattern = build_nested_tuple_pattern(&idents);
        vec![quote! { let #pattern = fst; }]
    }

    fn length_ctor_tokens(&self, len: &LenExpr, env: &ValueEnv, mode: EmitMode) -> TokenStream {
        if mode == EmitMode::Unified {
            if let LenExpr::Dependent(name) = len {
                if let Some(binding) = env.get(name) {
                    if binding.is_generic_int_param {
                        let ident = &binding.ident;
                        return quote! { #ident.into_length() };
                    }
                }
            }
        }

        if mode == EmitMode::Generate {
            if let LenExpr::Dependent(name) = len {
                if let Some(binding) = env.get(name) {
                    if binding.is_mut_ref {
                        let ident = &binding.ident;
                        return match binding.ty {
                            ValueType::U8 => quote! { Length::from_u8_mut(#ident) },
                            ValueType::U16 => quote! { Length::from_u16_mut(#ident) },
                            ValueType::U32 => quote! { Length::from_u32_mut(#ident) },
                            ValueType::U64 => quote! { Length::from_u64_mut(#ident) },
                            _ => {
                                let value = self.binding_read_tokens(binding);
                                quote! { Length::from_value(#value as usize) }
                            }
                        };
                    }
                }
            }
        }

        let len_tokens = self.len_expr_tokens(len, env);
        quote! { Length::from_value(#len_tokens) }
    }

    fn len_expr_tokens(&self, len: &LenExpr, env: &ValueEnv) -> TokenStream {
        match len {
            LenExpr::Const(n) => {
                let lit = Literal::usize_unsuffixed(*n);
                quote! { #lit }
            }
            LenExpr::Dependent(name) => {
                if let Some(binding) = env.get(name) {
                    binding
                        .ty
                        .to_usize_tokens(self.binding_read_tokens(binding))
                } else {
                    let ident = format_ident!("{}", name);
                    quote! { #ident as usize }
                }
            }
            LenExpr::SizeOf(name) => {
                if let Some(&size) = self.ctx.ctx.static_sizes.get(name) {
                    let lit = Literal::usize_unsuffixed(size);
                    quote! { #lit }
                } else {
                    let ident = format_ident!("{}_SIZE", name.to_uppercase());
                    quote! { #ident }
                }
            }
            LenExpr::BinOp { op, left, right } => {
                let left = self.len_expr_tokens(left, env);
                let right = self.len_expr_tokens(right, env);
                match op {
                    ArithOp::Add => quote! { (#left + #right) },
                    ArithOp::Sub => quote! { (#left - #right) },
                    ArithOp::Mul => quote! { (#left * #right) },
                    ArithOp::Div => quote! { (#left / #right) },
                }
            }
        }
    }

    fn param_ref_tokens(&self, param: &ParamRef, env: &ValueEnv) -> TokenStream {
        match param {
            ParamRef::Dependent(name) => {
                if let Some(binding) = env.get(name) {
                    self.binding_read_tokens(binding)
                } else {
                    let ident = format_ident!("{}", name);
                    quote! { #ident }
                }
            }
        }
    }

    fn tag_ref_tokens(&self, tag: &TagRef, env: &ValueEnv, mode: EmitMode) -> TokenStream {
        match tag {
            TagRef::Field(name) => {
                if let Some(binding) = env.get(name) {
                    match mode {
                        EmitMode::Unified if binding.is_generic_int_param => {
                            let ident = &binding.ident;
                            quote! { #ident.into_runtime_value() }
                        }
                        EmitMode::Generate if binding.is_mut_ref => {
                            let ident = &binding.ident;
                            quote! { RuntimeValue::from_mut(#ident) }
                        }
                        _ => {
                            let value = self.binding_read_tokens(binding);
                            quote! { RuntimeValue::from_value(#value) }
                        }
                    }
                } else {
                    let ident = format_ident!("{}", name);
                    quote! { RuntimeValue::from_value(#ident) }
                }
            }
            TagRef::Value(value) => {
                let value = self.tag_value_tokens(value);
                quote! { RuntimeValue::from_value(#value) }
            }
        }
    }

    fn cond_tag_ref_tokens(&self, tag: &TagRef, env: &ValueEnv, mode: EmitMode) -> TokenStream {
        if mode != EmitMode::Generate && mode != EmitMode::Unified {
            return self.tag_ref_tokens(tag, env, mode);
        }

        match tag {
            TagRef::Field(name) => {
                if let Some(binding) = env.get(name) {
                    let value = self.binding_read_tokens(binding);
                    quote! { RuntimeValue::from_value(#value) }
                } else {
                    let ident = format_ident!("{}", name);
                    quote! { RuntimeValue::from_value(#ident) }
                }
            }
            TagRef::Value(value) => {
                let value = self.tag_value_tokens(value);
                quote! { RuntimeValue::from_value(#value) }
            }
        }
    }

    fn binding_read_tokens(&self, binding: &Binding) -> TokenStream {
        if binding.is_generic_int_param {
            let ident = &binding.ident;
            quote! { #ident.value() }
        } else {
            binding_value_tokens(binding)
        }
    }

    fn tag_value_tokens(&self, value: &TagValue) -> TokenStream {
        match value {
            TagValue::Int(v) => {
                if let Some(const_ident) = self.const_ident_for_int(*v) {
                    quote! { #const_ident }
                } else {
                    let lit = Literal::i128_unsuffixed(*v);
                    quote! { #lit }
                }
            }
            TagValue::Enum { ty, variant } => {
                let ty_ident = format_ident!("{}", snake_to_upper_camel(ty));
                let variant_ident = format_ident!("{}", variant);
                quote! { #ty_ident::#variant_ident }
            }
            TagValue::Bytes(bytes) => {
                let byte_lits: Vec<Literal> =
                    bytes.iter().map(|&b| Literal::u8_unsuffixed(b)).collect();
                quote! { [#(#byte_lits),*] }
            }
            TagValue::Wildcard => quote! { _ },
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

    fn named_arg_env(&self, def: &CombDef, args: &[ParamRef], env: &ValueEnv) -> ValueEnv {
        def.params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| {
                let binding = match arg {
                    ParamRef::Dependent(name) => env.get(name).cloned().unwrap_or(Binding {
                        ident: format_ident!("{}", name),
                        ty: self.value_type_of_comb(&param.ty),
                        is_mut_ref: false,
                        is_generic_int_param: false,
                    }),
                };
                (param.name.clone(), binding)
            })
            .collect()
    }

    fn param_needs_generate_ref(&self, comb: &CombIR, name: &str) -> bool {
        let mut seen = HashSet::new();
        self.param_needs_generate_ref_inner(comb, name, &mut seen)
    }

    fn param_needs_generate_ref_inner(
        &self,
        comb: &CombIR,
        name: &str,
        seen: &mut HashSet<String>,
    ) -> bool {
        match comb {
            CombIR::Tuple(elems) => elems
                .iter()
                .any(|(_, elem)| self.param_needs_generate_ref_inner(elem, name, seen)),
            CombIR::Pair { fst, snd } => {
                self.param_needs_generate_ref_inner(fst, name, seen)
                    || self.param_needs_generate_ref_inner(&snd.comb, name, seen)
            }
            CombIR::Preceded { prefix, inner } => {
                self.param_needs_generate_ref_inner(prefix, name, seen)
                    || self.param_needs_generate_ref_inner(inner, name, seen)
            }
            CombIR::Terminated { inner, suffix } => {
                self.param_needs_generate_ref_inner(inner, name, seen)
                    || self.param_needs_generate_ref_inner(suffix, name, seen)
            }
            CombIR::Choice(choices) => choices
                .iter()
                .any(|choice| self.param_needs_generate_ref_inner(choice, name, seen)),
            CombIR::Dispatch { tag, branches } => {
                matches!(tag, TagRef::Field(field) if field == name)
                    || branches
                        .iter()
                        .any(|(_, branch)| self.param_needs_generate_ref_inner(branch, name, seen))
            }
            CombIR::Opt(inner)
            | CombIR::Repeat(inner)
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::CondEq { inner, .. }
            | CombIR::Tag { inner, .. } => self.param_needs_generate_ref_inner(inner, name, seen),
            CombIR::OptThen { fst, snd } => {
                self.param_needs_generate_ref_inner(fst, name, seen)
                    || self.param_needs_generate_ref_inner(snd, name, seen)
            }
            CombIR::RepeatN { inner, .. } => self.param_needs_generate_ref_inner(inner, name, seen),
            CombIR::FixedLen { len, inner } => {
                len_uses_dependent_name(len, name)
                    || self.param_needs_generate_ref_inner(inner, name, seen)
            }
            CombIR::Named {
                name: def_name,
                args,
            } => {
                let Some(def) = self.defs.get(def_name) else {
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
                            self.param_needs_generate_ref_inner(&def.body, &param.name, seen)
                        }
                        _ => false,
                    });
                seen.remove(def_name);
                result
            }
            CombIR::Variable { .. }
            | CombIR::Tail
            | CombIR::U8
            | CombIR::U16(_)
            | CombIR::U24(_)
            | CombIR::U32(_)
            | CombIR::U64(_)
            | CombIR::Fixed { .. }
            | CombIR::End
            | CombIR::Success
            | CombIR::Fail(_) => false,
        }
    }

    fn value_type_of_comb(&self, comb: &CombIR) -> ValueType {
        let mut seen = HashSet::new();
        self.value_type_of_comb_inner(comb, &mut seen)
    }

    fn value_type_of_comb_inner(&self, comb: &CombIR, seen: &mut HashSet<String>) -> ValueType {
        match comb {
            CombIR::U8 => ValueType::U8,
            CombIR::U16(_) => ValueType::U16,
            CombIR::U24(_) => ValueType::U24,
            CombIR::U32(_) => ValueType::U32,
            CombIR::U64(_) => ValueType::U64,
            CombIR::Fixed { .. } | CombIR::Variable { .. } | CombIR::Tail => ValueType::ByteSlice,
            CombIR::Tuple(elems) => ValueType::Tuple(
                elems
                    .iter()
                    .map(|(_, elem)| self.value_type_of_comb_inner(elem, seen))
                    .collect(),
            ),
            CombIR::Pair { fst, snd } => ValueType::Tuple(vec![
                self.value_type_of_comb_inner(fst, seen),
                self.value_type_of_comb_inner(&snd.comb, seen),
            ]),
            CombIR::Preceded { inner, .. }
            | CombIR::Terminated { inner, .. }
            | CombIR::Refined { inner, .. }
            | CombIR::Mapped { inner, .. }
            | CombIR::AndThen { inner, .. }
            | CombIR::FixedLen { inner, .. }
            | CombIR::CondEq { inner, .. } => self.value_type_of_comb_inner(inner, seen),
            CombIR::Choice(choices) => value_type_of_choice(self, choices, seen),
            CombIR::Dispatch { branches, .. } => {
                if let Some((_, comb)) = branches.first() {
                    self.value_type_of_comb_inner(comb, seen)
                } else {
                    ValueType::Unit
                }
            }
            CombIR::Opt(inner) => {
                ValueType::Option(Box::new(self.value_type_of_comb_inner(inner, seen)))
            }
            CombIR::OptThen { fst, snd } => ValueType::Tuple(vec![
                ValueType::Option(Box::new(self.value_type_of_comb_inner(fst, seen))),
                self.value_type_of_comb_inner(snd, seen),
            ]),
            CombIR::RepeatN { inner, .. } | CombIR::Repeat(inner) => {
                ValueType::Slice(Box::new(self.value_type_of_comb_inner(inner, seen)))
            }
            CombIR::Tag { .. } | CombIR::End | CombIR::Success | CombIR::Fail(_) => ValueType::Unit,
            CombIR::Named { name, .. } => {
                if !seen.insert(name.clone()) {
                    todo!(
                        "Recursive named combinator value type inference is incomplete for {}",
                        name
                    );
                }
                let value = self
                    .defs
                    .get(name)
                    .map(|def| self.value_type_of_comb_inner(&def.body, seen))
                    .unwrap_or_else(|| {
                        todo!(
                            "Named combinator value type resolution is incomplete for {}",
                            name
                        )
                    });
                seen.remove(name);
                value
            }
        }
    }

    fn helper_ident(&self, path: &[usize]) -> Ident {
        let base = format!("{}Dep", snake_to_upper_camel(&self.def.name));
        if path.is_empty() {
            format_ident!("{}", base)
        } else {
            let suffix = path
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("_");
            format_ident!("{}{}", base, suffix)
        }
    }

    fn last_bound_type(&self, comb: &CombIR) -> ValueType {
        match comb {
            CombIR::Tuple(elems) if !elems.is_empty() => {
                self.last_bound_type(&elems.last().unwrap().1)
            }
            CombIR::Tuple(_) => ValueType::Unit,
            other => self.value_type_of_comb(other),
        }
    }
}

fn value_type_of_choice(
    emitter: &DefEmitter<'_>,
    choices: &[CombIR],
    seen: &mut HashSet<String>,
) -> ValueType {
    if choices.is_empty() {
        ValueType::Unit
    } else if choices.len() == 1 {
        emitter.value_type_of_comb_inner(&choices[0], seen)
    } else {
        let first = emitter.value_type_of_comb_inner(&choices[0], seen);
        let rest = value_type_of_choice(emitter, &choices[1..], seen);
        ValueType::Either(Box::new(first), Box::new(rest))
    }
}

fn used_names_in_comb(comb: &CombIR) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_used_names(comb, &mut names);
    names
}

fn collect_used_names(comb: &CombIR, names: &mut BTreeSet<String>) {
    match comb {
        CombIR::Variable { len }
        | CombIR::FixedLen { len, .. }
        | CombIR::RepeatN { count: len, .. } => {
            collect_len_names(len, names);
        }
        CombIR::Tuple(elems) => {
            for (_, elem) in elems {
                collect_used_names(elem, names);
            }
        }
        CombIR::Choice(elems) => {
            for elem in elems {
                collect_used_names(elem, names);
            }
        }
        CombIR::Pair { fst, snd } => {
            collect_used_names(fst, names);
            collect_used_names(&snd.comb, names);
        }
        CombIR::Preceded { prefix, inner } => {
            collect_used_names(prefix, names);
            collect_used_names(inner, names);
        }
        CombIR::Terminated { inner, suffix } => {
            collect_used_names(inner, names);
            collect_used_names(suffix, names);
        }
        CombIR::Dispatch { tag, branches } => {
            collect_tag_ref_names(tag, names);
            for (_, branch) in branches {
                collect_used_names(branch, names);
            }
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::Tag { inner, .. } => collect_used_names(inner, names),
        CombIR::OptThen { fst, snd } => {
            collect_used_names(fst, names);
            collect_used_names(snd, names);
        }
        CombIR::CondEq { lhs, inner, .. } => {
            collect_tag_ref_names(lhs, names);
            collect_used_names(inner, names);
        }
        CombIR::Named { args, .. } => {
            for arg in args {
                match arg {
                    ParamRef::Dependent(name) => {
                        names.insert(name.clone());
                    }
                }
            }
        }
        CombIR::U8
        | CombIR::U16(_)
        | CombIR::U24(_)
        | CombIR::U32(_)
        | CombIR::U64(_)
        | CombIR::Fixed { .. }
        | CombIR::Tail
        | CombIR::End
        | CombIR::Success
        | CombIR::Fail(_) => {}
    }
}

fn collect_len_names(len: &LenExpr, names: &mut BTreeSet<String>) {
    match len {
        LenExpr::Dependent(name) => {
            names.insert(name.clone());
        }
        LenExpr::BinOp { left, right, .. } => {
            collect_len_names(left, names);
            collect_len_names(right, names);
        }
        LenExpr::Const(_) | LenExpr::SizeOf(_) => {}
    }
}

fn collect_tag_ref_names(tag: &TagRef, names: &mut BTreeSet<String>) {
    if let TagRef::Field(name) = tag {
        names.insert(name.clone());
    }
}

fn capture_names(
    used_names: &BTreeSet<String>,
    env: &ValueEnv,
    current_deps: &[String],
) -> Vec<String> {
    used_names
        .iter()
        .filter(|name| !current_deps.contains(name) && env.contains_key(*name))
        .cloned()
        .collect()
}

/// Builds a right-associative nested tuple pattern from a list of identifiers.
/// For 2 elements: `(a, b)`
/// For 3 elements: `(a, (b, c))`
/// For 4 elements: `(a, (b, (c, d)))`
fn build_nested_tuple_pattern(idents: &[syn::Ident]) -> TokenStream {
    match idents.len() {
        0 => panic!("Cannot build tuple pattern from empty identifiers"),
        1 => {
            let ident = &idents[0];
            quote! { #ident }
        }
        2 => {
            let a = &idents[0];
            let b = &idents[1];
            quote! { (#a, #b) }
        }
        _ => {
            let first = &idents[0];
            let rest = build_nested_tuple_pattern(&idents[1..]);
            quote! { (#first, #rest) }
        }
    }
}

fn binding_value_tokens(binding: &Binding) -> TokenStream {
    let ident = &binding.ident;
    if binding.is_mut_ref {
        quote! { *#ident }
    } else {
        quote! { #ident }
    }
}

fn predicate_to_tokens(pred: &PredicateIR, inner: Option<&CombIR>) -> TokenStream {
    match pred {
        PredicateIR::IntConstraint(constraint) => {
            let arg_ty = refined_pred_arg_type(inner);
            let var_expr = refined_pred_value_as_i128(inner);
            let check = int_constraint_to_check(constraint, var_expr);
            quote! { |v: #arg_ty| #check }
        }
        PredicateIR::Custom(name) => {
            let ident = format_ident!("{}", name);
            quote! { #ident }
        }
    }
}

fn refined_pred_arg_type(inner: Option<&CombIR>) -> TokenStream {
    match inner {
        Some(inner) => comb_uint_or_i128_type_tokens(inner),
        _ => quote! { i128 },
    }
}

fn refined_pred_value_as_i128(inner: Option<&CombIR>) -> TokenStream {
    match inner {
        Some(CombIR::U24(_)) => quote! { v.as_u32() as i128 },
        _ => quote! { v as i128 },
    }
}

fn int_constraint_to_check(constraint: &IntConstraintIR, var: TokenStream) -> TokenStream {
    match constraint {
        IntConstraintIR::Single(elem) => constraint_elem_to_check(elem, var),
        IntConstraintIR::Set(elems) => {
            let checks: Vec<TokenStream> = elems
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

fn constraint_elem_to_check(elem: &ConstraintElem, var: TokenStream) -> TokenStream {
    match elem {
        ConstraintElem::Single(v) => {
            let lit = Literal::i128_unsuffixed(*v);
            quote! { #var == #lit }
        }
        ConstraintElem::Range { start, end } => match (start, end) {
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

fn build_nested_choice_type(types: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(types, None, &|first, rest| quote! { Choice<#first, #rest> })
}

fn build_nested_choice_expr(exprs: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(
        exprs,
        None,
        &|first, rest| quote! { Choice::new(#first, #rest) },
    )
}

fn build_nested_pair_type(types: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(types, None, &|first, rest| quote! { (#first, #rest) })
}

fn build_nested_pair_expr(exprs: &[TokenStream]) -> TokenStream {
    build_right_nested_tokens(exprs, None, &|first, rest| quote! { (#first, #rest) })
}

fn either_wrap_expr(value: TokenStream, index: usize, total: usize) -> TokenStream {
    wrap_right_nested_either(value, index, total)
}

fn either_value_pattern(value: &Ident, index: usize, total: usize) -> TokenStream {
    wrap_right_nested_either(quote! { #value }, index, total)
}

fn dispatch_variant_ident(index: usize) -> Ident {
    format_ident!("V{}", index + 1)
}

fn dispatch_helper_key(path: &[usize]) -> String {
    format!("dispatch_{}", helper_key(path))
}

fn dispatch_tag_type_tokens(tag_value: &TagValue) -> TokenStream {
    tag_literal_type_tokens(tag_value)
}

fn len_uses_dependent_name(len: &LenExpr, name: &str) -> bool {
    match len {
        LenExpr::Const(_) | LenExpr::SizeOf(_) => false,
        LenExpr::Dependent(dep) => dep == name,
        LenExpr::BinOp { left, right, .. } => {
            len_uses_dependent_name(left, name) || len_uses_dependent_name(right, name)
        }
    }
}

fn dispatch_tag_type_tokens_for_ref(tag_ref: &TagRef, env: &ValueEnv) -> TokenStream {
    match tag_ref {
        TagRef::Field(name) => {
            if let Some(binding) = env.get(name) {
                match binding.ty {
                    ValueType::U8 => comb_uint_type_tokens(&CombIR::U8).unwrap(),
                    ValueType::U16 => comb_uint_type_tokens(&CombIR::U16(Endian::Little)).unwrap(),
                    ValueType::U24 => comb_uint_type_tokens(&CombIR::U24(Endian::Little)).unwrap(),
                    ValueType::U32 => comb_uint_type_tokens(&CombIR::U32(Endian::Little)).unwrap(),
                    ValueType::U64 => comb_uint_type_tokens(&CombIR::U64(Endian::Little)).unwrap(),
                    _ => quote! { i128 },
                }
            } else {
                quote! { i128 }
            }
        }
        TagRef::Value(value) => dispatch_tag_type_tokens(value),
    }
}

fn tag_value_type_tokens(tag_value: &TagValue, inner: &CombIR) -> TokenStream {
    match tag_value {
        TagValue::Int(_) => comb_uint_or_i128_type_tokens(inner),
        TagValue::Enum { .. } | TagValue::Bytes(_) | TagValue::Wildcard => {
            tag_literal_type_tokens(tag_value)
        }
    }
}

fn refined_pred_fn_type_tokens(inner: &CombIR) -> TokenStream {
    let arg_ty = comb_uint_or_i128_type_tokens(inner);
    quote! { fn(#arg_ty) -> bool }
}

fn child_path(path: &[usize], index: usize) -> Vec<usize> {
    let mut next = path.to_vec();
    next.push(index);
    next
}

fn helper_key(path: &[usize]) -> String {
    if path.is_empty() {
        "root".to_string()
    } else {
        path.iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join("_")
    }
}
