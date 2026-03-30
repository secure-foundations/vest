use proc_macro2::{Literal, TokenStream};
use quote::{format_ident, quote};

use super::super::analysis::value_kind_for_comb;
use super::super::helper_specs::{child_path, BindingEnv, BindingUse, ValueBinding};
use super::super::{
    const_ident_for_int, CombDef, CombIR, ParamRef, PredicateIR, TagValue, UIntWidth, ValType,
};
use super::module_emit::{
    build_nested_pair_expr, build_nested_pair_type, call_tokens, dispatch_tag_type_tokens_for_ref,
    dispatch_variant_ident, param_needs_generate_ref, predicate_to_tokens,
    refined_pred_fn_type_tokens, tag_value_type_tokens, value_kind_to_usize_tokens,
    DefinitionEmitter,
};

impl<'a> DefinitionEmitter<'a> {
    pub(super) fn top_level_body_expr_tokens(
        &self,
        comb: &CombIR,
        env: &BindingEnv,
    ) -> TokenStream {
        self.comb_expr_tokens(comb, env, &[])
    }

    pub(super) fn comb_expr_tokens(
        &self,
        comb: &CombIR,
        env: &BindingEnv,
        path: &[usize],
    ) -> TokenStream {
        match comb {
            CombIR::UInt(uint) => uint.combinator_type_tokens(),
            CombIR::Fixed { len } => {
                let len_lit = Literal::usize_unsuffixed(*len);
                quote! { Fixed::<#len_lit> }
            }
            CombIR::Variable { len } => {
                let len_tokens = self.length_expr_value_tokens(len, env);
                quote! { Variable(#len_tokens) }
            }
            CombIR::Tail => quote! { Tail },
            CombIR::Struct(fields) => self.seq_like_expr_tokens(
                fields.iter().map(|field| &field.comb).collect(),
                env,
                path,
            ),
            CombIR::Seq(items) => self.seq_like_expr_tokens(items.iter().collect(), env, path),
            CombIR::DepPair {
                fst,
                fst_bindings,
                snd,
            } => {
                let fst_tokens = self.comb_expr_tokens(fst, env, &child_path(path, 0));
                let helper = self.pair_helper_init(path, fst_bindings, snd, env);
                quote! { Pair::new(#fst_tokens, #helper) }
            }
            CombIR::Preceded { prefix, inner } => {
                let prefix_tokens = self.comb_expr_tokens(prefix, env, &child_path(path, 0));
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 1));
                quote! { Preceded(#prefix_tokens, #inner_tokens) }
            }
            CombIR::Terminated { inner, suffix } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let suffix_tokens = self.comb_expr_tokens(suffix, env, &child_path(path, 1));
                quote! { Terminated(#inner_tokens, #suffix_tokens) }
            }
            CombIR::Dispatch { tag, branches } => {
                let tag_tokens = self.tag_ref_tokens(tag, env);
                let helper = self.dispatch_helper_ident(path);
                let branch_tokens: Vec<_> = branches
                    .iter()
                    .enumerate()
                    .map(|(idx, branch)| {
                        let variant = dispatch_variant_ident(idx);
                        let tag_value = self.tag_value_tokens(&branch.tag);
                        let comb_tokens =
                            self.comb_expr_tokens(&branch.comb, env, &child_path(path, idx));
                        quote! { (#tag_value, #helper::#variant(#comb_tokens)) }
                    })
                    .collect();
                quote! { Dispatch::new(#tag_tokens, [#(#branch_tokens),*]) }
            }
            CombIR::Opt(inner) => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                quote! { Opt::new(#inner_tokens) }
            }
            CombIR::RepeatN { inner, count } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let count_tokens = self.length_expr_value_tokens(count, env);
                quote! { RepeatN::new(#inner_tokens, #count_tokens) }
            }
            CombIR::Repeat(inner) => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                quote! { Repeat::new(#inner_tokens) }
            }
            CombIR::Refined { inner, predicate } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let predicate_tokens =
                    predicate_to_tokens(predicate, Some(inner), &self.plan.names);
                quote! { Refined { inner: #inner_tokens, predicate: #predicate_tokens } }
            }
            CombIR::Mapped { inner, mapper } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let mapper_ident = format_ident!("{}", mapper);
                quote! { Mapped::new(#inner_tokens, #mapper_ident) }
            }
            CombIR::Enum {
                inner, predicate, ..
            } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let predicate_tokens = predicate_to_tokens(
                    &PredicateIR::Int(predicate.clone()),
                    Some(inner),
                    &self.plan.names,
                );
                quote! { Refined { inner: #inner_tokens, predicate: #predicate_tokens } }
            }
            CombIR::AndThen { len_comb, inner } => {
                let len_tokens = self.comb_expr_tokens(len_comb, env, &child_path(path, 0));
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 1));
                quote! { AndThen(#len_tokens, #inner_tokens) }
            }
            CombIR::FixedLen { len, inner } => {
                let len_tokens = self.length_ctor_tokens(len, env);
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                quote! {
                    FixedLen(
                        #len_tokens,
                        #inner_tokens,
                    )
                }
            }
            CombIR::Tag { inner, value } => {
                let inner_tokens = self.comb_expr_tokens(inner, env, &child_path(path, 0));
                let value_tokens = self.tag_value_tokens(value);
                quote! { Tag::new(#inner_tokens, #value_tokens) }
            }
            CombIR::Named { name, args } => {
                self.named_or_external_ctor_call_tokens(name, args, env)
            }
            CombIR::End => quote! { End },
            CombIR::Success => quote! { Success },
            CombIR::Fail(msg) => {
                let lit = Literal::string(msg);
                quote! { Fail(#lit.into()) }
            }
        }
    }

    fn seq_like_expr_tokens(
        &self,
        items: Vec<&CombIR>,
        env: &BindingEnv,
        path: &[usize],
    ) -> TokenStream {
        if items.is_empty() {
            quote! { () }
        } else if items.len() == 1 {
            self.comb_expr_tokens(items[0], env, &child_path(path, 0))
        } else {
            let elem_tokens: Vec<_> = items
                .into_iter()
                .enumerate()
                .map(|(idx, item)| self.comb_expr_tokens(item, env, &child_path(path, idx)))
                .collect();
            build_nested_pair_expr(&elem_tokens)
        }
    }

    fn named_ctor_call_tokens(
        &self,
        def: &CombDef,
        args: &[ParamRef],
        env: &BindingEnv,
    ) -> TokenStream {
        let fn_name = &self
            .plan
            .names
            .get(&def.name)
            .expect("names for def")
            .ctor_fn_ident;
        let arg_tokens: Vec<_> = def
            .params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| {
                let needs_ref = param_needs_generate_ref(&def.body, &param.name, &self.defs);
                match arg {
                    ParamRef::Dependent(name) => {
                        if let Some(binding) = env.get(name) {
                            if needs_ref && binding.can_forward_generate_arg() {
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
        call_tokens(fn_name, &arg_tokens)
    }

    fn named_or_external_ctor_call_tokens(
        &self,
        name: &str,
        args: &[ParamRef],
        env: &BindingEnv,
    ) -> TokenStream {
        if let Some(def) = self.defs.get(name) {
            self.named_ctor_call_tokens(def, args, env)
        } else {
            let fn_name = format_ident!("{}", name);
            let arg_tokens: Vec<_> = args
                .iter()
                .map(|arg| self.param_ref_tokens(arg, env))
                .collect();
            call_tokens(&fn_name, &arg_tokens)
        }
    }

    fn param_ref_tokens(&self, param: &ParamRef, env: &BindingEnv) -> TokenStream {
        match param {
            ParamRef::Dependent(name) => env
                .get(name)
                .map(|binding| self.binding_read_tokens(binding))
                .unwrap_or_else(|| {
                    let ident = format_ident!("{}", name);
                    quote! { #ident }
                }),
        }
    }

    fn length_ctor_tokens(&self, len: &crate::vestir::LengthExpr, env: &BindingEnv) -> TokenStream {
        if let crate::vestir::LengthExpr::Dependent(name) = len {
            if let Some(binding) = env.get(name) {
                let ident = &binding.ident;
                match binding.mode {
                    BindingUse::ConstructorParam => {
                        return quote! { #ident.into_length() };
                    }
                    BindingUse::GenerateRef => {
                        return match binding.kind {
                            ValType::UInt(UIntWidth::U8) => {
                                quote! { Length::from_u8_mut(#ident) }
                            }
                            ValType::UInt(UIntWidth::U16) => {
                                quote! { Length::from_u16_mut(#ident) }
                            }
                            ValType::UInt(UIntWidth::U32) => {
                                quote! { Length::from_u32_mut(#ident) }
                            }
                            ValType::UInt(UIntWidth::U64) => {
                                quote! { Length::from_u64_mut(#ident) }
                            }
                            _ => {
                                let value = self.binding_read_tokens(binding);
                                quote! { Length::from_value(#value as usize) }
                            }
                        };
                    }
                    BindingUse::Plain => {}
                }
            }
        }

        let len_tokens = self.length_expr_value_tokens(len, env);
        quote! { Length::from_value(#len_tokens) }
    }

    fn length_expr_value_tokens(
        &self,
        len: &crate::vestir::LengthExpr,
        env: &BindingEnv,
    ) -> TokenStream {
        match len {
            crate::vestir::LengthExpr::Const(n) => {
                let lit = Literal::usize_unsuffixed(*n);
                quote! { #lit }
            }
            crate::vestir::LengthExpr::Dependent(name) => env
                .get(name)
                .map(|binding| {
                    value_kind_to_usize_tokens(&binding.kind, self.binding_read_tokens(binding))
                })
                .unwrap_or_else(|| {
                    let ident = format_ident!("{}", name);
                    quote! { #ident as usize }
                }),
            crate::vestir::LengthExpr::SizeOf(name) => {
                if let Some(&size) = self.plan.ctx.static_sizes.get(name) {
                    let lit = Literal::usize_unsuffixed(size);
                    quote! { #lit }
                } else {
                    let ident = format_ident!("{}_SIZE", name.to_uppercase());
                    quote! { #ident }
                }
            }
            crate::vestir::LengthExpr::BinOp { op, left, right } => {
                let left = self.length_expr_value_tokens(left, env);
                let right = self.length_expr_value_tokens(right, env);
                match op {
                    crate::vestir::ArithOp::Add => quote! { (#left + #right) },
                    crate::vestir::ArithOp::Sub => quote! { (#left - #right) },
                    crate::vestir::ArithOp::Mul => quote! { (#left * #right) },
                    crate::vestir::ArithOp::Div => quote! { (#left / #right) },
                }
            }
        }
    }

    fn tag_ref_tokens(&self, tag: &str, env: &BindingEnv) -> TokenStream {
        if let Some(binding) = env.get(tag) {
            let ident = &binding.ident;
            match binding.mode {
                BindingUse::ConstructorParam => quote! { #ident.into_runtime_value() },
                BindingUse::GenerateRef => quote! { RuntimeValue::from_mut(#ident) },
                BindingUse::Plain => {
                    let value = self.binding_read_tokens(binding);
                    quote! { RuntimeValue::from_value(#value) }
                }
            }
        } else {
            let ident = format_ident!("{}", tag);
            quote! { RuntimeValue::from_value(#ident) }
        }
    }

    fn binding_read_tokens(&self, binding: &ValueBinding) -> TokenStream {
        let ident = &binding.ident;
        match binding.mode {
            BindingUse::GenerateRef => quote! { *#ident },
            BindingUse::ConstructorParam => quote! { #ident.value() },
            BindingUse::Plain => quote! { #ident },
        }
    }

    fn tag_value_tokens(&self, value: &TagValue) -> TokenStream {
        match value {
            TagValue::Int(v) => const_ident_for_int(self.def_ctx.def, *v)
                .map(|ident| quote! { #ident })
                .unwrap_or_else(|| {
                    let lit = Literal::i128_unsuffixed(*v);
                    quote! { #lit }
                }),
            TagValue::Enum { ty, variant } => {
                let ty_ident = &self.plan.names.get(ty).expect("enum tag names").type_ident;
                let variant_ident = format_ident!("{}", variant);
                quote! { #ty_ident::#variant_ident }
            }
            TagValue::Bytes(bytes) => {
                let byte_lits: Vec<_> = bytes.iter().map(|&b| Literal::u8_unsuffixed(b)).collect();
                quote! { [#(#byte_lits),*] }
            }
            TagValue::Wildcard => quote! { _ },
        }
    }

    pub(super) fn top_level_env(&self) -> BindingEnv {
        self.param_specs
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    ValueBinding {
                        ident: param.ident.clone(),
                        kind: param.kind.clone(),
                        mode: BindingUse::Plain,
                    },
                )
            })
            .collect()
    }

    pub(super) fn constructor_env(&self) -> BindingEnv {
        self.param_specs
            .iter()
            .map(|param| {
                (
                    param.name.clone(),
                    ValueBinding {
                        ident: param.ident.clone(),
                        kind: param.kind.clone(),
                        mode: if param.needs_generate_ref {
                            BindingUse::ConstructorParam
                        } else {
                            BindingUse::Plain
                        },
                    },
                )
            })
            .collect()
    }

    pub(super) fn top_level_generate_alias_body_type_tokens(&self) -> Option<TokenStream> {
        if !self.needs_runtime_ref {
            return None;
        }

        let env = self.top_level_env();
        let body_type_raw = self.top_level_body_type_tokens_with_options(
            &self.def_ctx.def.body,
            &env,
            Some(quote! { 'x }),
            true,
        );
        Some(self.wrap_top_level_mapper_type(body_type_raw))
    }

    pub(super) fn wrap_top_level_mapper_type(&self, body_type: TokenStream) -> TokenStream {
        if self.def_ctx.analysis.emits_mapper {
            let mapper = &self.def_ctx.names.mapper_ident;
            quote! { Mapped<#body_type, #mapper> }
        } else {
            body_type
        }
    }

    pub(super) fn top_level_body_type_tokens_with_options(
        &self,
        comb: &CombIR,
        env: &BindingEnv,
        lifetime: Option<TokenStream>,
        use_dispatch_defaults: bool,
    ) -> TokenStream {
        self.comb_type_tokens_with_lt_inner(comb, env, &[], lifetime, use_dispatch_defaults)
    }

    fn named_combinator_type_tokens(
        &self,
        def: &CombDef,
        env: &BindingEnv,
        lifetime: Option<TokenStream>,
    ) -> TokenStream {
        let names = self.plan.names.get(&def.name).expect("names for named def");
        let type_name = &names.combinator_ident;

        if lifetime.is_none() || !env.values().any(ValueBinding::uses_lifetime) {
            return quote! { #type_name };
        }

        let needs_runtime_ref = def
            .params
            .iter()
            .any(|param| param_needs_generate_ref(&def.body, &param.name, &self.defs));
        if needs_runtime_ref {
            let alias_name = &names.alias_ident;
            let lifetime = lifetime.expect("checked above");
            quote! { #type_name<#alias_name<#lifetime>> }
        } else {
            quote! { #type_name }
        }
    }

    fn named_arg_env(&self, def: &CombDef, args: &[ParamRef], env: &BindingEnv) -> BindingEnv {
        def.params
            .iter()
            .zip(args.iter())
            .map(|(param, arg)| {
                let binding = match arg {
                    ParamRef::Dependent(name) => env.get(name).cloned().unwrap_or(ValueBinding {
                        ident: format_ident!("{}", name),
                        kind: value_kind_for_comb(&param.ty, &self.defs, &self.plan.analysis),
                        mode: BindingUse::Plain,
                    }),
                };
                (param.name.clone(), binding)
            })
            .collect()
    }

    pub(super) fn comb_type_tokens_with_lt_inner(
        &self,
        comb: &CombIR,
        env: &BindingEnv,
        path: &[usize],
        lifetime: Option<TokenStream>,
        use_dispatch_defaults: bool,
    ) -> TokenStream {
        match comb {
            CombIR::UInt(uint) => uint.combinator_type_tokens(),
            CombIR::Fixed { len } => {
                let len_lit = Literal::usize_unsuffixed(*len);
                quote! { Fixed<#len_lit> }
            }
            CombIR::Variable { .. } => quote! { Variable },
            CombIR::Tail => quote! { Tail },
            CombIR::Struct(fields) => self.seq_like_type_tokens(
                fields.iter().map(|field| &field.comb).collect(),
                env,
                path,
                lifetime,
                use_dispatch_defaults,
            ),
            CombIR::Seq(items) => self.seq_like_type_tokens(
                items.iter().collect(),
                env,
                path,
                lifetime,
                use_dispatch_defaults,
            ),
            CombIR::DepPair { fst, .. } => {
                let fst_type = self.comb_type_tokens_with_lt_inner(
                    fst,
                    env,
                    &child_path(path, 0),
                    lifetime,
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
                    lifetime.clone(),
                    use_dispatch_defaults,
                );
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 1),
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { Preceded<#prefix_type, #inner_type> }
            }
            CombIR::Terminated { inner, suffix } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime.clone(),
                    use_dispatch_defaults,
                );
                let suffix_type = self.comb_type_tokens_with_lt_inner(
                    suffix,
                    env,
                    &child_path(path, 1),
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { Terminated<#inner_type, #suffix_type> }
            }
            CombIR::Dispatch { branches, tag } => {
                if branches.is_empty() {
                    quote! { Fail }
                } else {
                    let branch_type = self.dispatch_helper_ident(path);
                    let n = Literal::usize_unsuffixed(branches.len());
                    let tag_type = dispatch_tag_type_tokens_for_ref(tag, env, &self.plan.names);
                    let dispatch_lt = lifetime.clone().unwrap_or_else(|| quote! { 'static });
                    if lifetime.is_some() && !use_dispatch_defaults {
                        let branch_types: Vec<_> = branches
                            .iter()
                            .enumerate()
                            .map(|(idx, branch)| {
                                self.comb_type_tokens_with_lt_inner(
                                    &branch.comb,
                                    env,
                                    &child_path(path, idx),
                                    lifetime.clone(),
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
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { Opt<#inner_type> }
            }
            CombIR::RepeatN { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { RepeatN<#inner_type> }
            }
            CombIR::Repeat(inner) => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { Repeat<#inner_type> }
            }
            CombIR::Refined { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime,
                    use_dispatch_defaults,
                );
                let pred_type = refined_pred_fn_type_tokens(inner, &self.plan.names);
                quote! { Refined<#inner_type, #pred_type> }
            }
            CombIR::Mapped { inner, .. } => self.comb_type_tokens_with_lt_inner(
                inner,
                env,
                &child_path(path, 0),
                lifetime,
                use_dispatch_defaults,
            ),
            CombIR::Enum { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime,
                    use_dispatch_defaults,
                );
                let pred_type = refined_pred_fn_type_tokens(inner, &self.plan.names);
                quote! { Refined<#inner_type, #pred_type> }
            }
            CombIR::AndThen { len_comb, inner } => {
                let len_type = self.comb_type_tokens_with_lt_inner(
                    len_comb,
                    env,
                    &child_path(path, 0),
                    lifetime.clone(),
                    use_dispatch_defaults,
                );
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 1),
                    lifetime,
                    use_dispatch_defaults,
                );
                quote! { AndThen<#len_type, #inner_type> }
            }
            CombIR::FixedLen { inner, .. } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime.clone(),
                    use_dispatch_defaults,
                );
                let fixed_lt = lifetime.unwrap_or_else(|| quote! { 'static });
                quote! { FixedLen<#fixed_lt, #inner_type> }
            }
            CombIR::Tag { inner, value } => {
                let inner_type = self.comb_type_tokens_with_lt_inner(
                    inner,
                    env,
                    &child_path(path, 0),
                    lifetime,
                    use_dispatch_defaults,
                );
                let value_type = tag_value_type_tokens(value, inner, &self.plan.names);
                quote! { Tag<#inner_type, #value_type> }
            }
            CombIR::Named { name, args } => {
                let Some(def) = self.defs.get(name) else {
                    let type_name = &self
                        .plan
                        .names
                        .get(name)
                        .expect("names for named def")
                        .combinator_ident;
                    return quote! { #type_name };
                };
                if lifetime.is_some() {
                    let named_env = self.named_arg_env(def, args, env);
                    self.named_combinator_type_tokens(def, &named_env, lifetime)
                } else {
                    let type_name = &self
                        .plan
                        .names
                        .get(name)
                        .expect("names for named def")
                        .combinator_ident;
                    quote! { #type_name }
                }
            }
            CombIR::End => quote! { End },
            CombIR::Success => quote! { Success },
            CombIR::Fail(_) => quote! { Fail },
        }
    }

    fn seq_like_type_tokens(
        &self,
        items: Vec<&CombIR>,
        env: &BindingEnv,
        path: &[usize],
        lifetime: Option<TokenStream>,
        use_dispatch_defaults: bool,
    ) -> TokenStream {
        if items.is_empty() {
            quote! { () }
        } else if items.len() == 1 {
            self.comb_type_tokens_with_lt_inner(
                items[0],
                env,
                &child_path(path, 0),
                lifetime,
                use_dispatch_defaults,
            )
        } else {
            let elem_types: Vec<_> = items
                .into_iter()
                .enumerate()
                .map(|(idx, item)| {
                    self.comb_type_tokens_with_lt_inner(
                        item,
                        env,
                        &child_path(path, idx),
                        lifetime.clone(),
                        use_dispatch_defaults,
                    )
                })
                .collect();
            build_nested_pair_type(&elem_types)
        }
    }
}
