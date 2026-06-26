//! Code generation for mutually-recursive (and self-recursive) format SCCs.

use super::common::{format_names, sum_pattern, tuple_chain, Analysis, SccInfo, TypeMode};
use super::specs::RenderedSpec;
use super::writer::{render_ts, CodeWriter};
use crate::vestir::{
    ChoiceCombinator, ChoicePattern, Combinator, ConstraintElem, ParamDefn, RecursiveScc,
    SccMember, SccMemberBody, StructCombinator, StructField,
};
use heck::ToUpperCamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

#[derive(Clone, Copy, PartialEq, Eq)]
enum RecExecParamAccess {
    SelfFields,
}

// ============================================================
// SCC rewrite context
// ============================================================

/// Context threaded through body emitters to rewrite in-SCC invocations.
pub(crate) struct RecCtx<'a> {
    pub(crate) members: &'a [String],
    pub(crate) scc: &'a SccInfo,
    /// Maps depend_id name to the actual field name in the Param struct.
    pub(crate) dep_to_param_field: std::collections::HashMap<String, String>,
    /// All extra field names in the Param struct (from collect_scc_extra_params).
    pub(crate) all_param_fields: Vec<String>,
}

impl<'a> RecCtx<'a> {
    fn is_in_scc(&self, name: &str) -> bool {
        self.members.contains(&name.to_string())
    }

    fn param_field_for_dep<'b>(&'b self, dep: &'b str) -> &'b str {
        self.dep_to_param_field
            .get(dep)
            .map(|s| s.as_str())
            .unwrap_or(dep)
    }

    /// Always uses the struct form: `rec(XxxParam { which: WhichXxx::MEMBER, <extra_fields> })`.
    /// Fields not supplied in extra_fields are initialized with `arbitrary()`.
    fn rec_call_for_member(
        &self,
        member_name: &str,
        extra_fields: &[(String, TokenStream)],
    ) -> TokenStream {
        let info = format_names(member_name);
        let which_ident = format_ident!("{}", self.scc.which_ident);
        let which_var = format_ident!("{}", info.exec.to_uppercase());
        let param_ident = format_ident!("{}", self.scc.param_ident);
        let supplied: std::collections::HashMap<&str, &TokenStream> =
            extra_fields.iter().map(|(n, v)| (n.as_str(), v)).collect();
        let field_inits: Vec<TokenStream> = self
            .all_param_fields
            .iter()
            .map(|fname| {
                let id = format_ident!("{}", fname);
                if let Some(val) = supplied.get(fname.as_str()) {
                    quote! { #id: #val }
                } else {
                    quote! { #id: arbitrary() }
                }
            })
            .collect();
        quote! { rec(#param_ident { which: #which_ident::#which_var, #(#field_inits),* }) }
    }
}

// ============================================================
// Module-level helpers
// ============================================================

fn is_combinator_in_scc(c: &Combinator, members: &[String]) -> bool {
    matches!(c, Combinator::Invocation(inv) if members.contains(&inv.func))
}

fn get_invocation_name(c: &Combinator) -> &str {
    match c {
        Combinator::Invocation(inv) => &inv.func,
        _ => panic!("expected Invocation"),
    }
}

/// Build `Alt<Cond<ABodyFmt>, Alt<Cond<BBodyFmt>, ...>>` from alias idents.
fn alt_chain_by_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { Empty },
        [only] => quote! { Cond<#only> },
        [first, rest @ ..] => {
            let r = alt_chain_by_idents(rest);
            quote! { Alt<Cond<#first>, #r> }
        }
    }
}

fn alt_expr_chain(exprs: &[TokenStream]) -> TokenStream {
    match exprs {
        [] => quote! { Empty },
        [only] => only.clone(),
        [first, rest @ ..] => {
            let r = alt_expr_chain(rest);
            quote! { Alt(#first, #r) }
        }
    }
}

fn choice_type_chain(tys: &[TokenStream]) -> TokenStream {
    match tys {
        [] => quote! { Empty },
        [only] => only.clone(),
        [first, rest @ ..] => {
            let r = choice_type_chain(rest);
            quote! { Choice<#first, #r> }
        }
    }
}

fn choice_expr_chain(exprs: &[TokenStream]) -> TokenStream {
    match exprs {
        [] => quote! { Empty },
        [only] => only.clone(),
        [first, rest @ ..] => {
            let r = choice_expr_chain(rest);
            quote! { Choice(#first, #r) }
        }
    }
}

fn is_empty_spec(ty: &TokenStream) -> bool {
    ty.to_string() == "Empty"
}

// ============================================================
// Data Types (M3)
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn gen_recursive_data_fragment(&self, scc: &RecursiveScc) -> String {
        let scc_info = match self.scc_info_for(&scc.members[0].name) {
            Some(i) => i,
            None => return String::new(),
        };
        let member_names: Vec<String> = scc.members.iter().map(|m| m.name.clone()).collect();
        let ctx = self.make_ctx(&member_names, scc, scc_info);
        let mut out = CodeWriter::new();
        for member in &scc.members {
            out.push_multiline(self.gen_scc_member_data_type(member, &ctx));
        }
        out.push_multiline(self.gen_scc_value_enum(scc_info, &ctx));
        out.push_multiline(self.gen_scc_which_enum(scc_info));
        // Always emit Param struct (even with no extra fields, it wraps `which`).
        out.push_multiline(self.gen_scc_param_struct(scc, scc_info));
        out.finish()
    }

    fn gen_scc_member_data_type(&self, member: &SccMember, ctx: &RecCtx<'_>) -> String {
        match &member.body {
            SccMemberBody::Struct(s) => self.gen_scc_struct_data_type(&member.name, s, ctx),
            SccMemberBody::Choice(c) => self.gen_scc_choice_data_type(&member.name, c, ctx),
            SccMemberBody::Combinator(comb) => {
                self.gen_scc_combinator_data_type(&member.name, comb, ctx)
            }
        }
    }

    fn gen_scc_struct_data_type(
        &self,
        name: &str,
        s: &StructCombinator,
        ctx: &RecCtx<'_>,
    ) -> String {
        let info = self.info(name);
        let exec_id = format_ident!("{}", info.names.exec);
        let spec_id = format_ident!("{}", info.names.spec);
        let inner_id = format_ident!("{}", info.names.inner);
        let lt = if ctx.scc.needs_lifetime {
            quote! { <'i> }
        } else {
            quote! {}
        };

        let exec_fields: Vec<_> = s
            .0
            .iter()
            .filter_map(|f| match f {
                StructField::Const { .. } => None,
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Exec, ctx.members);
                    Some(quote! { pub #id: #ty })
                }
            })
            .collect();

        let spec_fields: Vec<_> = s
            .0
            .iter()
            .filter_map(|f| match f {
                StructField::Const { .. } => None,
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let id = format_ident!("{}", label);
                    let ty = self.render_value_type_scc(combinator, TypeMode::Spec, ctx.members);
                    Some(quote! { pub #id: #ty })
                }
            })
            .collect();

        let inner_parts: Vec<_> =
            s.0.iter()
                .map(|f| match f {
                    StructField::Const { combinator, .. } => {
                        self.render_const_value_type(combinator, TypeMode::Spec)
                    }
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.render_value_type_scc(combinator, TypeMode::Spec, ctx.members)
                    }
                })
                .collect();
        let inner_ty = super::common::tuple_chain(&inner_parts);

        let view_fields: Vec<_> =
            s.0.iter()
                .filter_map(|f| match f {
                    StructField::Const { .. } => None,
                    StructField::Dependent { label, combinator }
                    | StructField::Ordinary { label, combinator } => {
                        let id = format_ident!("{}", label);
                        let expr = if is_combinator_in_scc(combinator, ctx.members) {
                            let vfn = format_ident!("{}_view", get_invocation_name(combinator));
                            quote! { Box::new(#vfn(&*x.#id)) }
                        } else {
                            quote! { x.#id.deep_view() }
                        };
                        Some(quote! { #id: #expr })
                    }
                })
                .collect();

        let view_fn = format_ident!("{}_view", info.names.dsl);
        let deep_view_impl = if ctx.scc.needs_lifetime {
            quote! {
                pub open spec fn #view_fn(x: &#exec_id) -> #spec_id decreases *x, {
                    #spec_id { #(#view_fields,)* }
                }
                impl<'i> DeepView for #exec_id<'i> {
                    type V = #spec_id;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        } else {
            quote! {
                pub open spec fn #view_fn(x: &#exec_id) -> #spec_id decreases *x, {
                    #spec_id { #(#view_fields,)* }
                }
                impl DeepView for #exec_id {
                    type V = #spec_id;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        };

        let doc = format!("data type for `{}`.", name);
        render_ts(quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq)]
            pub struct #exec_id #lt { #(#exec_fields,)* }
            #[verifier::ext_equal]
            pub struct #spec_id { #(#spec_fields,)* }
            pub type #inner_id = #inner_ty;
            #deep_view_impl
        })
    }

    fn gen_scc_choice_data_type(
        &self,
        name: &str,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
    ) -> String {
        let info = self.info(name);
        let exec_id = format_ident!("{}", info.names.exec);
        let spec_id = format_ident!("{}", info.names.spec);
        let inner_id = format_ident!("{}", info.names.inner);
        let lt = if ctx.scc.needs_lifetime {
            quote! { <'i> }
        } else {
            quote! {}
        };
        let vnames = self.choice_variant_names(c);

        let exec_vars: Vec<_> = vnames
            .iter()
            .zip(&c.choices)
            .map(|(vn, (_, comb))| {
                let id = format_ident!("{}", vn);
                let ty = self.render_value_type_scc(comb, TypeMode::Exec, ctx.members);
                quote! { #id(#ty) }
            })
            .collect();
        let spec_vars: Vec<_> = vnames
            .iter()
            .zip(&c.choices)
            .map(|(vn, (_, comb))| {
                let id = format_ident!("{}", vn);
                let ty = self.render_value_type_scc(comb, TypeMode::Spec, ctx.members);
                quote! { #id(#ty) }
            })
            .collect();
        let spec_tys: Vec<_> = c
            .choices
            .iter()
            .map(|(_, comb)| self.render_value_type_scc(comb, TypeMode::Spec, ctx.members))
            .collect();
        let inner_ty = self.render_choice_sum_type(&spec_tys);

        let view_arms: Vec<_> = vnames
            .iter()
            .zip(&c.choices)
            .map(|(vn, (_, comb))| {
                let id = format_ident!("{}", vn);
                let expr = if is_combinator_in_scc(comb, ctx.members) {
                    let vfn = format_ident!("{}_view", get_invocation_name(comb));
                    quote! { Box::new(#vfn(&**v)) }
                } else {
                    quote! { v.deep_view() }
                };
                quote! { #exec_id::#id(v) => #spec_id::#id(#expr), }
            })
            .collect();

        let view_fn = format_ident!("{}_view", info.names.dsl);
        let deep_view_impl = if ctx.scc.needs_lifetime {
            quote! {
                pub open spec fn #view_fn(x: &#exec_id) -> #spec_id decreases *x, {
                    match x { #(#view_arms)* }
                }
                impl<'i> DeepView for #exec_id<'i> {
                    type V = #spec_id;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        } else {
            quote! {
                pub open spec fn #view_fn(x: &#exec_id) -> #spec_id decreases *x, {
                    match x { #(#view_arms)* }
                }
                impl DeepView for #exec_id {
                    type V = #spec_id;
                    open spec fn deep_view(&self) -> Self::V { #view_fn(self) }
                }
            }
        };

        let doc = format!("data type for `{}`.", name);
        render_ts(quote! {
            #[doc = #doc]
            #[derive(Debug, PartialEq, Eq)]
            pub enum #exec_id #lt { #(#exec_vars,)* }
            #[verifier::ext_equal]
            pub enum #spec_id { #(#spec_vars,)* }
            pub type #inner_id = #inner_ty;
            #deep_view_impl
        })
    }

    fn gen_scc_combinator_data_type(
        &self,
        name: &str,
        comb: &Combinator,
        ctx: &RecCtx<'_>,
    ) -> String {
        let info = self.info(name);
        let exec_id = format_ident!("{}", info.names.exec);
        let spec_id = format_ident!("{}", info.names.spec);
        let exec_ty = self.render_value_type_scc(comb, TypeMode::Exec, ctx.members);
        let spec_ty = self.render_value_type_scc(comb, TypeMode::Spec, ctx.members);
        let doc = format!("data type for `{}`.", name);
        if ctx.scc.needs_lifetime {
            render_ts(
                quote! { #[doc = #doc] pub type #exec_id<'i> = #exec_ty; pub type #spec_id = #spec_ty; },
            )
        } else {
            render_ts(
                quote! { #[doc = #doc] pub type #exec_id = #exec_ty; pub type #spec_id = #spec_ty; },
            )
        }
    }

    fn gen_scc_value_enum(&self, scc_info: &SccInfo, ctx: &RecCtx<'_>) -> String {
        let value_id = format_ident!("{}", scc_info.value_ident);
        let variants: Vec<_> = ctx
            .members
            .iter()
            .map(|name| {
                let n = format_names(name);
                let var_id = format_ident!("{}", n.exec);
                let spec_id = format_ident!("{}", n.spec);
                let field_id = format_ident!("{}", n.dsl);
                quote! { #var_id { #field_id: #spec_id } }
            })
            .collect();
        render_ts(quote! {
            #[verifier::ext_equal]
            pub enum #value_id { #(#variants,)* }
        })
    }

    fn gen_scc_which_enum(&self, scc_info: &SccInfo) -> String {
        let which_id = format_ident!("{}", scc_info.which_ident);
        let variants: Vec<_> = scc_info
            .members
            .iter()
            .map(|name| {
                let id = format_ident!("{}", format_names(name).exec.to_uppercase());
                quote! { #id }
            })
            .collect();
        render_ts(quote! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
            pub enum #which_id { #(#variants,)* }
            impl DeepView for #which_id {
                type V = Self;
                open spec fn deep_view(&self) -> Self::V { *self }
            }
        })
    }

    fn gen_scc_param_struct(&self, scc: &RecursiveScc, scc_info: &SccInfo) -> String {
        let param_id = format_ident!("{}", scc_info.param_ident);
        let which_id = format_ident!("{}", scc_info.which_ident);
        let extra: Vec<(String, TokenStream)> = self.collect_scc_extra_params(scc);
        let fields: Vec<_> = extra
            .iter()
            .map(|(n, ty)| {
                let id = format_ident!("{}", n);
                quote! { pub #id: #ty }
            })
            .collect();
        let views: Vec<_> = extra
            .iter()
            .map(|(n, _)| {
                let id = format_ident!("{}", n);
                quote! { #id: self.#id.deep_view() }
            })
            .collect();
        render_ts(quote! {
            #[verifier::ext_equal]
            pub struct #param_id {
                pub which: #which_id,
                #(#fields,)*
            }
            impl DeepView for #param_id {
                type V = Self;
                open spec fn deep_view(&self) -> Self::V {
                    #param_id {
                        which: self.which.deep_view(),
                        #(#views,)*
                    }
                }
            }
        })
    }

    fn collect_scc_extra_params(&self, scc: &RecursiveScc) -> Vec<(String, TokenStream)> {
        // Collect from all SCC members, using the combinator type name
        // as the field name to avoid collision.
        let mut seen: std::collections::HashMap<String, TokenStream> = Default::default();
        for member in &scc.members {
            for p in &member.param_defns {
                match p {
                    crate::vestir::ParamDefn::Dependent { name, combinator } => {
                        let field_name = match combinator {
                            Combinator::ConstraintInt(_) => name.clone(),
                            Combinator::Invocation(inv) => inv.func.clone(),
                            _ => name.clone(),
                        };
                        seen.entry(field_name)
                            .or_insert_with(|| self.render_value_type(combinator, TypeMode::Spec));
                    }
                }
            }
        }
        let mut v: Vec<_> = seen.into_iter().collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    }

    /// Build a RecCtx for an SCC, including the dep_id → param_field mapping.
    fn make_ctx<'b>(
        &self,
        member_names: &'b [String],
        scc: &RecursiveScc,
        scc_info: &'b SccInfo,
    ) -> RecCtx<'b> {
        // Build dep_name → param_field_name: for each member, for each param_defn,
        // map the dep name (e.g. "t") to the field name in the Param struct (e.g. "expr_kind").
        let mut map: std::collections::HashMap<String, String> = Default::default();
        for member in &scc.members {
            for p in &member.param_defns {
                match p {
                    crate::vestir::ParamDefn::Dependent { name, combinator } => {
                        let field_name = match combinator {
                            Combinator::ConstraintInt(_) => name.clone(),
                            Combinator::Invocation(inv) => inv.func.clone(),
                            _ => name.clone(),
                        };
                        map.insert(name.clone(), field_name);
                    }
                }
            }
        }
        RecCtx {
            members: member_names,
            scc: scc_info,
            dep_to_param_field: map,
            all_param_fields: self
                .collect_scc_extra_params(scc)
                .into_iter()
                .map(|(n, _)| n)
                .collect(),
        }
    }
}

// ============================================================
// Specs (M4) — projections, Fmt structs, SpecRecBody, mappers
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn gen_recursive_specs_fragment(&self, scc: &RecursiveScc) -> String {
        let scc_info = match self.scc_info_for(&scc.members[0].name) {
            Some(i) => i,
            None => return String::new(),
        };
        let member_names: Vec<String> = scc.members.iter().map(|m| m.name.clone()).collect();
        let ctx = self.make_ctx(&member_names, scc, scc_info);
        let mut out = CodeWriter::new();
        // 1. Projections
        for m in &scc.members {
            out.push_multiline(self.gen_scc_projection(m, scc_info));
        }
        // 2. FmtSpec type alias + XxxFmt struct (all members)
        for m in &scc.members {
            out.push_multiline(self.gen_scc_fmt_struct(m, scc, scc_info));
        }
        // 3. Per-member helper spec fns used by direct exec contracts.
        for m in &scc.members {
            out.push_multiline(self.gen_scc_member_exec_spec_helpers(m, scc, scc_info));
        }
        // 4. Mapper structs + SpecMapper impls (all members)
        for m in &scc.members {
            out.push_multiline(self.gen_scc_mapper(m, scc_info, &ctx));
        }
        // 5. Per-member body type aliases + BodyRec impls + combined RecBody
        out.push_multiline(self.gen_scc_rec_bodies(scc, scc_info, &ctx));
        out.finish()
    }

    fn gen_scc_projection(&self, member: &SccMember, scc_info: &SccInfo) -> String {
        let info = self.info(&member.name);
        let exec_id = format_ident!("{}", info.names.exec);
        let spec_id = format_ident!("{}", info.names.spec);
        let proj_ty = format_ident!("{}Proj", info.names.exec);
        let proj_fn = format_ident!("{}_proj", info.names.dsl);
        let value_id = format_ident!("{}", scc_info.value_ident);
        let field_id = format_ident!("{}", info.names.dsl);
        render_ts(quote! {
            pub type #proj_ty<Rec> = Mapped<Refined<Rec, PredFnSpec<#value_id>>, FnSpecMapper<#value_id, #spec_id>>;
            pub open spec fn #proj_fn<Rec>(rec: Rec) -> #proj_ty<Rec>
                where Rec: SpecCombinator<T = #value_id>,
            {
                Mapped {
                    inner: Refined(rec, |v: #value_id| v is #exec_id),
                    mapper: (
                        |v: #value_id| -> #spec_id { v->#field_id },
                        |#field_id: #spec_id| -> #value_id { #value_id::#exec_id { #field_id } },
                    ),
                }
            }
        })
    }

    fn gen_scc_fmt_struct(
        &self,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
    ) -> String {
        let info = self.info(&member.name);
        let fmt_id = format_ident!("{}", info.names.fmt);
        let proj_ty = format_ident!("{}Proj", info.names.exec);
        let proj_fn = format_ident!("{}_proj", info.names.dsl);
        let rb_id = format_ident!("{}", scc_info.rec_body_ident);
        let param_id = format_ident!("{}", scc_info.param_ident);
        let which_id = format_ident!("{}", scc_info.which_ident);
        let which_var = format_ident!("{}", info.names.exec.to_uppercase());
        // FmtSpec type alias
        let fmt_spec_id = format_ident!("{}Spec", info.names.fmt);
        let fmt_spec_ty = quote! { #proj_ty<FixWith<LIMIT, #rb_id, #param_id>> };

        let member_exec_params = self.member_param_fields(member);
        let member_spec_params = self.member_spec_param_fields(member);
        let field_defs: Vec<_> = member_exec_params
            .iter()
            .map(|(_, shared, ty)| {
                let id = format_ident!("{}", shared);
                quote! { pub #id: #ty }
            })
            .collect();
        let accessors: Vec<_> = member
            .param_defns
            .iter()
            .map(|param| match param {
                crate::vestir::ParamDefn::Dependent { name, combinator } => {
                    let field_name = scc_param_field_name(name, combinator);
                    let field_ident = format_ident!("{}", field_name);
                    let accessor_ident = format_ident!("{}_spec", field_name);
                    let spec_ty = self.render_value_type(combinator, TypeMode::Spec);
                    quote! {
                        pub closed spec fn #accessor_ident(&self) -> #spec_ty {
                            self.#field_ident.deep_view()
                        }
                    }
                }
            })
            .collect();
        let own_fields: std::collections::HashSet<String> = member_spec_params
            .iter()
            .map(|(shared, _)| shared.clone())
            .collect();
        let param_inits: Vec<_> = self
            .collect_scc_extra_params(scc)
            .into_iter()
            .map(|(shared, _)| {
                let shared_id = format_ident!("{}", shared);
                if own_fields.contains(&shared) {
                    quote! { #shared_id: #shared_id }
                } else {
                    quote! { #shared_id: arbitrary() }
                }
            })
            .collect();
        let spec_params_sig: Vec<_> = member_spec_params
            .iter()
            .map(|(shared, ty)| {
                let id = format_ident!("{}", shared);
                quote! { #id: #ty }
            })
            .collect();
        let spec_inner_sig = if spec_params_sig.is_empty() {
            quote! { pub open spec fn spec_inner() -> #fmt_spec_ty }
        } else {
            quote! { pub open spec fn spec_inner(#(#spec_params_sig),*) -> #fmt_spec_ty }
        };
        render_ts(quote! {
            pub type #fmt_spec_id<const LIMIT: usize> = #fmt_spec_ty;
            #[derive(Clone, Copy)]
            pub struct #fmt_id<const LIMIT: usize> { #(#field_defs,)* }
            impl<const LIMIT: usize> #fmt_id<LIMIT> {
                #(#accessors)*
                #spec_inner_sig {
                    #proj_fn(
                        FixWith::<LIMIT, #rb_id, #param_id>(
                            #rb_id,
                            #param_id { which: #which_id::#which_var, #(#param_inits,)* },
                        ),
                    )
                }
            }
        })
    }

    fn member_spec_param_fields(&self, member: &SccMember) -> Vec<(String, TokenStream)> {
        member
            .param_defns
            .iter()
            .map(|p| match p {
                crate::vestir::ParamDefn::Dependent { name, combinator } => (
                    scc_param_field_name(name, combinator),
                    self.render_value_type(combinator, TypeMode::Spec),
                ),
            })
            .collect()
    }

    fn gen_scc_member_exec_spec_helpers(
        &self,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
    ) -> String {
        let info = self.info(&member.name);
        let spec_id = format_ident!("{}", info.names.spec);
        let value_id = format_ident!("{}", scc_info.value_ident);
        let param_id = format_ident!("{}", scc_info.param_ident);
        let rec_body_id = format_ident!("{}", scc_info.rec_body_ident);
        let which_id = format_ident!("{}", scc_info.which_ident);
        let which_var = format_ident!("{}", info.names.exec.to_uppercase());
        let value_var = format_ident!("{}", info.names.exec);
        let field_id = format_ident!("{}", info.names.dsl);
        let param_fn = format_ident!("{}_param", info.names.dsl);
        let wrap_fn = format_ident!("{}_into_scc", info.names.dsl);
        let parse_fn = format_ident!("{}_parse_spec_gas", info.names.dsl);
        let consistent_fn = format_ident!("{}_consistent_spec_gas", info.names.dsl);
        let serialize_fn = format_ident!("{}_serialize_spec_gas", info.names.dsl);
        let byte_len_fn = format_ident!("{}_byte_len_spec_gas", info.names.dsl);

        let member_spec_params = self.member_spec_param_fields(member);
        let sig_params: Vec<_> = member_spec_params
            .iter()
            .map(|(shared, ty)| {
                let id = format_ident!("{}", shared);
                quote! { #id: #ty }
            })
            .collect();
        let param_args: Vec<_> = member_spec_params
            .iter()
            .map(|(shared, _)| {
                let id = format_ident!("{}", shared);
                quote! { #id }
            })
            .collect();
        let own_fields: std::collections::HashSet<String> = member_spec_params
            .iter()
            .map(|(shared, _)| shared.clone())
            .collect();
        let param_inits: Vec<_> = self
            .collect_scc_extra_params(scc)
            .into_iter()
            .map(|(shared, _)| {
                let shared_id = format_ident!("{}", shared);
                if own_fields.contains(&shared) {
                    quote! { #shared_id: #shared_id }
                } else {
                    quote! { #shared_id: arbitrary() }
                }
            })
            .collect();
        let param_call = if param_args.is_empty() {
            quote! { #param_fn() }
        } else {
            quote! { #param_fn(#(#param_args),*) }
        };
        let parse_sig = if sig_params.is_empty() {
            quote! { pub open spec fn #parse_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, ibuf: Seq<u8>) -> Option<(int, #spec_id)> }
        } else {
            quote! { pub open spec fn #parse_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, #(#sig_params,)* ibuf: Seq<u8>) -> Option<(int, #spec_id)> }
        };
        let consistent_sig = if sig_params.is_empty() {
            quote! { pub open spec fn #consistent_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, v: #spec_id) -> bool }
        } else {
            quote! { pub open spec fn #consistent_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, #(#sig_params,)* v: #spec_id) -> bool }
        };
        let serialize_sig = if sig_params.is_empty() {
            quote! { pub open spec fn #serialize_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, v: #spec_id) -> Seq<u8> }
        } else {
            quote! { pub open spec fn #serialize_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, #(#sig_params,)* v: #spec_id) -> Seq<u8> }
        };
        let byte_len_sig = if sig_params.is_empty() {
            quote! { pub open spec fn #byte_len_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, v: #spec_id) -> nat }
        } else {
            quote! { pub open spec fn #byte_len_fn<const LIMIT: usize>(body: &#rec_body_id, gas: nat, #(#sig_params,)* v: #spec_id) -> nat }
        };

        render_ts(quote! {
            pub open spec fn #param_fn(#(#sig_params),*) -> #param_id {
                #param_id { which: #which_id::#which_var, #(#param_inits,)* }
            }

            pub open spec fn #wrap_fn(v: #spec_id) -> #value_id {
                #value_id::#value_var { #field_id: v }
            }

            #parse_sig {
                match FixWith::<LIMIT, #rec_body_id, #param_id>::spec_parse_gas(
                    body,
                    gas,
                    #param_call,
                    ibuf,
                ) {
                    Some((n, #value_id::#value_var { #field_id })) => Some((n, #field_id)),
                    _ => None,
                }
            }

            #consistent_sig {
                FixWith::<LIMIT, #rec_body_id, #param_id>::consistent_gas(
                    body,
                    gas,
                    #param_call,
                    #wrap_fn(v),
                )
            }

            #serialize_sig {
                FixWith::<LIMIT, #rec_body_id, #param_id>::spec_serialize_gas(
                    body,
                    gas,
                    #param_call,
                    #wrap_fn(v),
                )
            }

            #byte_len_sig {
                FixWith::<LIMIT, #rec_body_id, #param_id>::byte_len_gas(
                    body,
                    gas,
                    #param_call,
                    #wrap_fn(v),
                )
            }
        })
    }

    fn gen_scc_mapper(&self, member: &SccMember, scc_info: &SccInfo, ctx: &RecCtx<'_>) -> String {
        let info = self.info(&member.name);
        let mapper_id = format_ident!("{}Mapper", info.names.exec);
        let exec_id = format_ident!("{}", info.names.exec);
        let value_id = format_ident!("{}", scc_info.value_ident);
        let body = self.render_scc_body_spec(member, ctx);
        let inner_val = &body.value_ty;
        let (fwd, rev) = self.mapper_fns(member, scc_info, ctx, inner_val);
        render_ts(quote! {
            pub struct #mapper_id;
            impl SpecMapper for #mapper_id {
                type In = #inner_val;
                type Out = #value_id;
                open spec fn spec_map(&self, i: Self::In) -> Self::Out { #fwd }
                open spec fn wf_out(&self, o: Self::Out) -> bool { o is #exec_id }
                open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In { #rev }
            }
        })
    }

    fn gen_scc_rec_bodies(
        &self,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
    ) -> String {
        let mut out = CodeWriter::new();
        let value_id = format_ident!("{}", scc_info.value_ident);
        let rb_id = format_ident!("{}", scc_info.rec_body_ident);
        let param_id = format_ident!("{}", scc_info.param_ident);
        let which_id = format_ident!("{}", scc_info.which_ident);

        // Every SCC member gets its own BodyRec.
        let mut body_alias_ids: Vec<proc_macro2::Ident> = Vec::new();
        for m in &scc.members {
            let (_body_ty, body_alias) = self.scc_member_body_type(m, scc_info, ctx);
            let alias_id = format_ident!("{}BodyFmt", self.info(&m.name).names.exec);
            body_alias_ids.push(alias_id);
            out.push_multiline(body_alias);
            out.push_multiline(self.gen_scc_member_rec_body(m, scc_info, ctx));
        }

        // Combined RecBody: type alias + impl using body aliases.
        let combined_ty = alt_chain_by_idents(&body_alias_ids);
        let rb_idents: Vec<_> = scc
            .members
            .iter()
            .map(|m| format_ident!("{}BodyRec", self.info(&m.name).names.exec))
            .collect();
        let which_vars: Vec<_> = scc
            .members
            .iter()
            .map(|m| format_ident!("{}", self.info(&m.name).names.exec.to_uppercase()))
            .collect();
        let cases: Vec<_> = rb_idents
            .iter()
            .zip(which_vars.iter())
            .map(|(rb, wv)| {
                // Always use param.which for dispatch (since Param is always a struct).
                quote! { Cond(param.which == #which_id::#wv, #rb.spec_body(param, rec)) }
            })
            .collect();
        let body_expr = alt_expr_chain(&cases);

        out.push_multiline(render_ts(quote! {
            pub struct #rb_id;
            impl SpecRecBody for #rb_id {
                type Param = #param_id;
                type T = #value_id;
                type Body = #combined_ty;
                open spec fn spec_body(&self, param: Self::Param, rec: ParamRecSpecs<Self::Param, Self::T>) -> Self::Body {
                    #body_expr
                }
            }
        }));
        out.finish()
    }

    /// Returns (body_type_tokens, body_type_alias_string) for a member.
    fn scc_member_body_type(
        &self,
        member: &SccMember,
        _scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
    ) -> (TokenStream, String) {
        let info = self.info(&member.name);
        let mapper_id = format_ident!("{}Mapper", info.names.exec);
        let alias_id = format_ident!("{}BodyFmt", info.names.exec);
        let body = self.render_scc_body_spec(member, ctx);
        let inner_ty = &body.ty;
        let body_ty = quote! { Mapped<#inner_ty, #mapper_id> };
        // The alias expands to the full type; return the alias ident as the type token.
        let alias = render_ts(quote! { pub type #alias_id = #body_ty; });
        (quote! { #alias_id }, alias)
    }

    fn gen_scc_member_rec_body(
        &self,
        member: &SccMember,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
    ) -> String {
        let info = self.info(&member.name);
        let rb_id = format_ident!("{}BodyRec", info.names.exec);
        let alias_id = format_ident!("{}BodyFmt", info.names.exec);
        let mapper_id = format_ident!("{}Mapper", info.names.exec);
        let value_id = format_ident!("{}", scc_info.value_ident);
        let param_id = format_ident!("{}", scc_info.param_ident);
        // Build per-member dep→(field, enum_type) map from this member's own param_defns.
        let member_dep_map: std::collections::HashMap<String, (String, Option<String>)> = member
            .param_defns
            .iter()
            .filter_map(|p| match p {
                crate::vestir::ParamDefn::Dependent { name, combinator } => {
                    let (field, enum_ty) = match combinator {
                        Combinator::Invocation(inv) => (inv.func.clone(), Some(inv.func.clone())),
                        Combinator::ConstraintInt(_) => (name.clone(), None),
                        _ => (name.clone(), None),
                    };
                    Some((name.clone(), (field, enum_ty)))
                }
            })
            .collect();
        let body = self.render_scc_body_spec_with_member_deps(member, ctx, &member_dep_map);
        let inner_expr = &body.expr;
        // Use `param` in the function signature (it may be used by depend_id dispatch).
        render_ts(quote! {
            pub struct #rb_id;
            impl SpecRecBody for #rb_id {
                type Param = #param_id;
                type T = #value_id;
                type Body = #alias_id;
                open spec fn spec_body(&self, param: Self::Param, rec: ParamRecSpecs<Self::Param, Self::T>) -> Self::Body {
                    Mapped { inner: #inner_expr, mapper: #mapper_id }
                }
            }
        })
    }
}

// ============================================================
// Body spec rendering — builds RenderedSpec for each member
// ============================================================

impl<'a> Analysis<'a> {
    fn render_scc_body_spec(&self, member: &SccMember, ctx: &RecCtx<'_>) -> RenderedSpec {
        self.render_scc_body_spec_with_member_deps(member, ctx, &Default::default())
    }

    fn render_scc_body_spec_with_member_deps(
        &self,
        member: &SccMember,
        ctx: &RecCtx<'_>,
        // dep_name → (param_field_name, Option<enum_type_name>)
        member_deps: &std::collections::HashMap<String, (String, Option<String>)>,
    ) -> RenderedSpec {
        match &member.body {
            SccMemberBody::Struct(s) => self.render_scc_struct_spec(s, ctx),
            SccMemberBody::Choice(c) => {
                // Any choice with a depend_id dispatches on param.<dep> via match/Sum.
                if c.depend_id.is_some() {
                    self.render_scc_param_choice_body(c, ctx, member_deps)
                } else {
                    self.render_scc_choice_body(c, ctx, None)
                }
            }
            SccMemberBody::Combinator(comb) => self.render_scc_comb_spec(comb, ctx),
        }
    }

    /// For choice bodies with depend_id: emit `match param.<field> { pat => Sum::InlX(...), ... }`.
    fn render_scc_param_choice_body(
        &self,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
        member_deps: &std::collections::HashMap<String, (String, Option<String>)>,
    ) -> RenderedSpec {
        let dep = c.depend_id.as_deref().unwrap_or("param");
        // Use per-member dep map first, then fall back to ctx.
        let (param_field, enum_type_opt) = if let Some((field, ety)) = member_deps.get(dep) {
            (field.as_str().to_string(), ety.clone())
        } else {
            (ctx.param_field_for_dep(dep).to_string(), None)
        };
        let param_field_id = format_ident!("{}", param_field);
        let branches: Vec<RenderedSpec> = c
            .choices
            .iter()
            .map(|(_, comb)| self.render_scc_comb_spec(comb, ctx))
            .collect();
        let tys: Vec<_> = branches.iter().map(|b| b.ty.clone()).collect();
        let vtys: Vec<_> = branches.iter().map(|b| b.value_ty.clone()).collect();
        let n = branches.len();
        let match_arms: Vec<_> = c
            .choices
            .iter()
            .zip(branches.iter())
            .enumerate()
            .map(|(idx, ((pat, _), branch))| {
                let pat_tok =
                    self.render_int_choice_pattern_qualified(pat, enum_type_opt.as_deref());
                let sum_expr = sum_pattern(idx, n, branch.expr.clone());
                quote! { #pat_tok => #sum_expr, }
            })
            .collect();
        let sum_ty = self.render_choice_sum_type(&tys);
        let sum_val = self.render_choice_sum_type(&vtys);
        RenderedSpec::new(
            sum_ty,
            quote! { match param.#param_field_id { #(#match_arms)* } },
            sum_val,
            true,
        )
    }

    fn render_int_choice_pattern_qualified(
        &self,
        pat: &ChoicePattern,
        enum_type: Option<&str>,
    ) -> TokenStream {
        match pat {
            ChoicePattern::Int(elem) => self.render_constraint_elem_pat(elem),
            ChoicePattern::Wildcard => quote! { _ },
            ChoicePattern::Enum(name) => {
                let id = format_ident!("{}", name);
                if let Some(et) = enum_type {
                    let et_id = format_ident!("{}", et.to_upper_camel_case());
                    quote! { #et_id::#id }
                } else {
                    quote! { #id }
                }
            }
            ChoicePattern::Array(arr) => self.render_const_array_expr(arr, TypeMode::Exec),
        }
    }

    fn find_scc_member_by_name<'b>(
        &'b self,
        ctx: &RecCtx<'_>,
        name: &str,
    ) -> Option<&'b SccMember> {
        // Walk all RecursiveScc defs to find the member.
        for def in self.defs {
            if let crate::vestir::Definition::RecursiveScc(scc) = def {
                if let Some(m) = scc.members.iter().find(|m| m.name == name) {
                    if ctx.is_in_scc(name) {
                        return Some(m);
                    }
                }
            }
        }
        None
    }

    /// Build extra Param fields from an invocation's args, mapping each arg to the
    /// corresponding field name in the shared Param struct.
    fn build_rec_extra_fields(
        &self,
        inv: &crate::vestir::CombinatorInvocation,
        ctx: &RecCtx<'_>,
    ) -> Vec<(String, TokenStream)> {
        if inv.args.is_empty() {
            return vec![];
        }
        // Find the target member's param_defns to determine field names.
        let target_member = self.find_scc_member_by_name(ctx, &inv.func).or_else(|| {
            // Not found via ctx — search all SCC members.
            for def in self.defs {
                if let crate::vestir::Definition::RecursiveScc(scc) = def {
                    if let Some(m) = scc.members.iter().find(|m| m.name == inv.func) {
                        return Some(m);
                    }
                }
            }
            None
        });
        let target_param_defns: Vec<_> = target_member
            .map(|m| m.param_defns.clone())
            .unwrap_or_default();
        inv.args
            .iter()
            .zip(target_param_defns.iter())
            .map(|(arg, pd)| {
                match (arg, pd) {
                    (
                        crate::vestir::Param::Dependent(arg_name),
                        crate::vestir::ParamDefn::Dependent {
                            name: _,
                            combinator: _,
                        },
                    ) => {
                        // The field name in the shared SCC Param struct is determined by the
                        // callee member's parameter definition, not the caller's local arg name.
                        let field_name = match pd {
                            crate::vestir::ParamDefn::Dependent { name, combinator } => {
                                scc_param_field_name(name, combinator)
                            }
                        };
                        let val_id = format_ident!("{}", arg_name);
                        (field_name, quote! { #val_id })
                    }
                }
            })
            .collect()
    }

    fn find_scc_for_member(&self, name: &str) -> Option<&RecursiveScc> {
        for def in self.defs {
            if let crate::vestir::Definition::RecursiveScc(scc) = def {
                if scc.members.iter().any(|m| m.name == name) {
                    return Some(scc);
                }
            }
        }
        None
    }

    fn find_scc_member_for(&self, name: &str) -> Option<&SccMember> {
        for def in self.defs {
            if let crate::vestir::Definition::RecursiveScc(scc) = def {
                if let Some(m) = scc.members.iter().find(|m| m.name == name) {
                    return Some(m);
                }
            }
        }
        None
    }

    fn render_scc_struct_spec(&self, s: &StructCombinator, ctx: &RecCtx<'_>) -> RenderedSpec {
        self.render_scc_fields_spec(&s.0, ctx)
    }

    fn render_scc_fields_spec(&self, fields: &[StructField], ctx: &RecCtx<'_>) -> RenderedSpec {
        if fields.is_empty() {
            return RenderedSpec::new(quote! { Empty }, quote! { Empty }, quote! { () }, false);
        }
        let cur = match &fields[0] {
            StructField::Const { combinator, .. } => {
                let (ty, expr, vty) = self.render_const_spec_pub(combinator);
                RenderedSpec::new(ty, expr, vty, true)
            }
            StructField::Ordinary { combinator, .. } => self.render_scc_comb_spec(combinator, ctx),
            StructField::Dependent {
                label: _,
                combinator,
            } => self.render_scc_comb_spec(combinator, ctx),
        };
        let rest = self.render_scc_fields_spec(&fields[1..], ctx);
        let dep_label = match &fields[0] {
            StructField::Dependent { label, .. } => Some(label.as_str()),
            _ => None,
        };
        self.seq_spec(cur, &rest, dep_label)
    }

    fn seq_spec(
        &self,
        cur: RenderedSpec,
        rest: &RenderedSpec,
        dep_label: Option<&str>,
    ) -> RenderedSpec {
        if is_empty_spec(&rest.ty) {
            return cur;
        }
        let (ct, ce, cv) = (&cur.ty, &cur.expr, &cur.value_ty);
        let (rt, re, rv) = (&rest.ty, &rest.expr, &rest.value_ty);
        match dep_label {
            None => RenderedSpec::new(
                quote! { Pair<#ct, #rt> },
                quote! { Pair(#ce, #re) },
                quote! { (#cv, #rv) },
                true,
            ),
            Some(lbl) => {
                let lid = format_ident!("{}", lbl);
                RenderedSpec::new(
                    quote! { Bind<#ct, spec_fn(#cv) -> #rt> },
                    quote! { Bind(#ce, |#lid: #cv| #re) },
                    quote! { (#cv, #rv) },
                    true,
                )
            }
        }
    }

    fn render_scc_choice_body(
        &self,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
        _param_tag: Option<&str>,
    ) -> RenderedSpec {
        let branches: Vec<RenderedSpec> = c
            .choices
            .iter()
            .map(|(_, comb)| self.render_scc_comb_spec(comb, ctx))
            .collect();
        let tys: Vec<_> = branches.iter().map(|b| b.ty.clone()).collect();
        let exprs: Vec<_> = branches.iter().map(|b| b.expr.clone()).collect();
        let vtys: Vec<_> = branches.iter().map(|b| b.value_ty.clone()).collect();
        RenderedSpec::new(
            choice_type_chain(&tys),
            choice_expr_chain(&exprs),
            self.render_choice_sum_type(&vtys),
            true,
        )
    }

    fn render_scc_comb_spec(&self, comb: &Combinator, ctx: &RecCtx<'_>) -> RenderedSpec {
        match comb {
            Combinator::Invocation(inv) if ctx.is_in_scc(&inv.func) => {
                let info = self.info(&inv.func);
                let proj_fn = format_ident!("{}_proj", info.names.dsl);
                let proj_ty = format_ident!("{}Proj", info.names.exec);
                let value_id = format_ident!("{}", ctx.scc.value_ident);
                let spec_id = format_ident!("{}", info.names.spec);
                // Build extra fields from the invocation's args: map each arg to the
                // corresponding Param struct field name using the target member's param_defns.
                let extra_fields = self.build_rec_extra_fields(inv, ctx);
                let rec_expr = ctx.rec_call_for_member(&inv.func, &extra_fields);
                RenderedSpec::new(
                    quote! { #proj_ty<BundledSpecs<#value_id>> },
                    quote! { #proj_fn(#rec_expr) },
                    quote! { #spec_id },
                    true,
                )
            }
            Combinator::Invocation(_inv) => {
                // Non-SCC: resolve the alias to get raw spec (avoids Named<> opacity issues).
                let resolved = self.ctx.resolve_alias(comb);
                if !matches!(resolved, Combinator::Invocation(_)) {
                    self.render_spec_combinator_pub(resolved)
                } else {
                    self.render_spec_combinator_pub(comb)
                }
            }
            _ => self.render_spec_combinator_pub(comb),
        }
    }

    fn mapper_fns(
        &self,
        member: &SccMember,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
        _inner_val: &TokenStream,
    ) -> (TokenStream, TokenStream) {
        let info = self.info(&member.name);
        let value_id = format_ident!("{}", scc_info.value_ident);
        let exec_id = format_ident!("{}", info.names.exec);
        let field_id = format_ident!("{}", info.names.dsl);
        let spec_id = format_ident!("{}", info.names.spec);
        match &member.body {
            SccMemberBody::Choice(c) => {
                let vnames = self.choice_variant_names(c);
                let n = vnames.len();
                let fwd_arms: Vec<_> = vnames
                    .iter()
                    .zip(&c.choices)
                    .enumerate()
                    .map(|(i, (vn, (_, comb)))| {
                        let pat = sum_pattern(i, n, quote! { v });
                        let vid = format_ident!("{}", vn);
                        let con = if is_combinator_in_scc(comb, ctx.members) {
                            quote! { #spec_id::#vid(Box::new(v)) }
                        } else {
                            quote! { #spec_id::#vid(v) }
                        };
                        quote! { #pat => #value_id::#exec_id { #field_id: #con }, }
                    })
                    .collect();
                let rev_arms: Vec<_> = vnames
                    .iter()
                    .zip(&c.choices)
                    .enumerate()
                    .map(|(i, (vn, (_, comb)))| {
                        let expr = sum_pattern(
                            i,
                            n,
                            if is_combinator_in_scc(comb, ctx.members) {
                                quote! { *v }
                            } else {
                                quote! { v }
                            },
                        );
                        let vid = format_ident!("{}", vn);
                        quote! { #value_id::#exec_id { #field_id: #spec_id::#vid(v) } => #expr, }
                    })
                    .collect();
                (
                    quote! { match i { #(#fwd_arms)* _ => arbitrary() } },
                    quote! { match o { #(#rev_arms)* _ => arbitrary() } },
                )
            }
            SccMemberBody::Struct(s) => {
                let (labels, combs): (Vec<_>, Vec<_>) =
                    s.0.iter()
                        .filter_map(|f| match f {
                            StructField::Const { .. } => None,
                            StructField::Dependent { label, combinator }
                            | StructField::Ordinary { label, combinator } => {
                                Some((label.clone(), combinator.clone()))
                            }
                        })
                        .unzip();
                let ids: Vec<_> = labels.iter().map(|l| format_ident!("{}", l)).collect();
                let tup_pat = super::common::nested_tuple_pattern_idents(&ids);
                let ctor: Vec<_> = labels
                    .iter()
                    .zip(&combs)
                    .map(|(l, c)| {
                        let id = format_ident!("{}", l);
                        if is_combinator_in_scc(c, ctx.members) {
                            quote! { #id: Box::new(#id) }
                        } else {
                            quote! { #id }
                        }
                    })
                    .collect();
                let rev_elems: Vec<_> = labels
                    .iter()
                    .zip(&combs)
                    .map(|(l, c)| {
                        let id = format_ident!("{}", l);
                        if is_combinator_in_scc(c, ctx.members) {
                            quote! { *#id }
                        } else {
                            quote! { #id }
                        }
                    })
                    .collect();
                let rev_tup = tuple_chain(&rev_elems);
                let fwd = quote! { let #tup_pat = i; #value_id::#exec_id { #field_id: #spec_id { #(#ctor),* } } };
                let rev = quote! { match o { #value_id::#exec_id { #field_id: #spec_id { #(#ids),* } } => #rev_tup, _ => arbitrary() } };
                (fwd, rev)
            }
            SccMemberBody::Combinator(_) => (
                quote! { #value_id::#exec_id { #field_id: i } },
                quote! { match o { #value_id::#exec_id { #field_id: v } => v, _ => arbitrary() } },
            ),
        }
    }
}

fn scc_param_field_name(name: &str, combinator: &Combinator) -> String {
    match combinator {
        Combinator::ConstraintInt(_) => name.to_string(),
        Combinator::Invocation(inv) => inv.func.clone(),
        _ => name.to_string(),
    }
}

fn normalize_verus_signature(s: String) -> String {
    s.replace("== >", "==>").replace("&& &", "&&&")
}

// ============================================================
// Derived Specs (M5a)
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn gen_recursive_derived_specs_fragment(&self, scc: &RecursiveScc) -> String {
        let _scc_info = match self.scc_info_for(&scc.members[0].name) {
            Some(i) => i,
            None => return String::new(),
        };
        scc.members
            .iter()
            .map(|m| self.gen_scc_derived_specs(&m.name))
            .collect()
    }

    fn gen_scc_derived_specs(&self, name: &str) -> String {
        let info = self.info(name);
        let fmt_id = format_ident!("{}", info.names.fmt);
        let spec_id = format_ident!("{}", info.names.spec);
        let spec_call_args = self
            .find_scc_member_for(name)
            .map(|member| {
                member
                    .param_defns
                    .iter()
                    .map(|param| match param {
                        ParamDefn::Dependent { name, combinator } => {
                            let field_name = scc_param_field_name(name, combinator);
                            let accessor_ident = format_ident!("{}_spec", field_name);
                            quote! { self.#accessor_ident() }
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let inner = if spec_call_args.is_empty() {
            quote! { #fmt_id::<LIMIT>::spec_inner() }
        } else {
            quote! { #fmt_id::<LIMIT>::spec_inner(#(#spec_call_args),*) }
        };
        render_ts(quote! {
            impl<const LIMIT: usize> SpecParser for #fmt_id<LIMIT> {
                type PVal = #spec_id;
                open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
                    #inner.spec_parse(ibuf)
                }
            }
            impl<const LIMIT: usize> Consistency for #fmt_id<LIMIT> {
                type Val = #spec_id;
                open spec fn consistent(&self, v: Self::Val) -> bool { #inner.consistent(v) }
            }
            impl<const LIMIT: usize> SpecByteLen for #fmt_id<LIMIT> {
                type T = #spec_id;
                open spec fn byte_len(&self, v: Self::T) -> nat { #inner.byte_len(v) }
            }
            impl<const LIMIT: usize> SpecSerializerDps for #fmt_id<LIMIT> {
                type SValue = #spec_id;
                open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
                    #inner.spec_serialize_dps(v, obuf)
                }
            }
            impl<const LIMIT: usize> SpecSerializer for #fmt_id<LIMIT> {
                type SVal = #spec_id;
                open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> { #inner.spec_serialize(v) }
            }
        })
    }
}

// ============================================================
// Proofs (M5b)
// ============================================================

impl<'a> Analysis<'a> {
    pub(crate) fn gen_recursive_proofs_fragment(&self, scc: &RecursiveScc) -> String {
        let scc_info = match self.scc_info_for(&scc.members[0].name) {
            Some(i) => i,
            None => return String::new(),
        };
        let member_names: Vec<String> = scc.members.iter().map(|m| m.name.clone()).collect();
        let ctx = self.make_ctx(&member_names, scc, scc_info);
        let mut out = String::new();
        // NoLookAhead for enum formats referenced in bodies (non-SCC invocations)
        out.push_str(&self.gen_no_lookahead_for_scc(scc, &ctx));
        // Proof stack for all SCC member fmts.
        for m in &scc.members {
            out.push_str(&self.gen_scc_fmt_proof_stack(&m.name));
        }
        // Mapper proofs (all members)
        for m in &scc.members {
            out.push_str(&self.gen_scc_mapper_proofs(m, scc_info, &ctx));
        }
        // StrictRecBody proofs
        out.push_str(&self.gen_scc_strict_rec_body_proofs(scc, scc_info));
        out
    }

    fn gen_scc_fmt_proof_stack(&self, name: &str) -> String {
        let info = self.info(name);
        let fmt_id = format_ident!("{}", info.names.fmt);
        let spec_call_args = self
            .find_scc_member_for(name)
            .map(|member| {
                member
                    .param_defns
                    .iter()
                    .map(|param| match param {
                        ParamDefn::Dependent { name, combinator } => {
                            let field_name = scc_param_field_name(name, combinator);
                            let accessor_ident = format_ident!("{}_spec", field_name);
                            quote! { self.#accessor_ident() }
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let inner = if spec_call_args.is_empty() {
            quote! { #fmt_id::<LIMIT>::spec_inner() }
        } else {
            quote! { #fmt_id::<LIMIT>::spec_inner(#(#spec_call_args),*) }
        };
        render_ts(quote! {
            impl<const LIMIT: usize> SafeParser for #fmt_id<LIMIT> {
                proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) { #inner.lemma_parse_safe(ibuf); }
            }
            impl<const LIMIT: usize> SoundParser for #fmt_id<LIMIT> {
                proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.sound_inv()); fmt.lemma_parse_sound_consumption(ibuf);
                }
                proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.sound_inv()); fmt.lemma_parse_sound_value(ibuf);
                }
            }
            impl<const LIMIT: usize> NonTailFmt for #fmt_id<LIMIT> {
                proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.serialize_dps_inv()); fmt.lemma_serialize_dps_prepend(v, obuf);
                }
                proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.serialize_dps_inv()); fmt.lemma_serialize_dps_len(v, obuf);
                }
            }
            impl<const LIMIT: usize> GoodSerializer for #fmt_id<LIMIT> {
                proof fn lemma_serialize_len(&self, v: Self::SVal) {
                    let fmt = #inner; assert(fmt.serialize_inv()); fmt.lemma_serialize_len(v);
                }
            }
            impl<const LIMIT: usize> SPRoundTripDps for #fmt_id<LIMIT> {
                proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.unambiguous()); fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
                }
            }
            impl<const LIMIT: usize> NonMalleable for #fmt_id<LIMIT> {
                proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
                    let fmt = #inner; assert(fmt.nonmal_inv()); fmt.lemma_parse_non_malleable(buf1, buf2);
                }
            }
            impl<const LIMIT: usize> EquivSerializersGeneral for #fmt_id<LIMIT> {
                proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
                    let fmt = #inner; assert(fmt.equiv_general_inv()); fmt.lemma_serialize_equiv(v, obuf);
                }
            }
            impl<const LIMIT: usize> EquivSerializers for #fmt_id<LIMIT> {
                proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
                    let fmt = #inner; assert(fmt.equiv_inv()); fmt.lemma_serialize_equiv_on_empty(v);
                }
            }
        })
    }

    fn gen_scc_mapper_proofs(
        &self,
        member: &SccMember,
        _scc_info: &SccInfo,
        _ctx: &RecCtx<'_>,
    ) -> String {
        let mapper_id = format_ident!("{}Mapper", self.info(&member.name).names.exec);
        render_ts(quote! {
            impl LossyMapper for #mapper_id {
                proof fn lemma_sound_mapper(&self, o: Self::Out) {}
                proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {}
            }
            impl LosslessMapper for #mapper_id {
                proof fn lemma_lossless_mapper(&self, i: Self::In) {
                    assert(self.spec_map_rev(self.spec_map(i)) == i);
                }
                proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {}
            }
        })
    }

    fn gen_no_lookahead_for_scc(&self, scc: &RecursiveScc, ctx: &RecCtx<'_>) -> String {
        let mut seen: std::collections::HashSet<String> = Default::default();
        for m in &scc.members {
            self.collect_non_scc_invocations(m, ctx, &mut seen);
        }
        seen.iter()
            .filter(|n| {
                matches!(
                    self.def_by_name(n),
                    Some(crate::vestir::Definition::EnumDef { .. })
                )
            })
            .map(|n| self.gen_no_lookahead_impl(n))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    fn collect_non_scc_invocations(
        &self,
        member: &SccMember,
        ctx: &RecCtx<'_>,
        out: &mut std::collections::HashSet<String>,
    ) {
        match &member.body {
            SccMemberBody::Struct(s) => s.0.iter().for_each(|f| match f {
                StructField::Const { .. } => {}
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    self.collect_comb_invocations(combinator, ctx, out)
                }
            }),
            SccMemberBody::Choice(c) => c
                .choices
                .iter()
                .for_each(|(_, comb)| self.collect_comb_invocations(comb, ctx, out)),
            SccMemberBody::Combinator(c) => self.collect_comb_invocations(c, ctx, out),
        }
    }

    fn collect_comb_invocations(
        &self,
        c: &Combinator,
        ctx: &RecCtx<'_>,
        out: &mut std::collections::HashSet<String>,
    ) {
        match c {
            Combinator::Invocation(inv) if !ctx.is_in_scc(&inv.func) => {
                out.insert(inv.func.clone());
            }
            Combinator::AndThen(l, r) => {
                self.collect_comb_invocations(l, ctx, out);
                self.collect_comb_invocations(r, ctx, out);
            }
            _ => {}
        }
    }

    fn gen_no_lookahead_impl(&self, name: &str) -> String {
        let fmt_id = format_ident!("{}", self.info(name).names.fmt);
        render_ts(quote! {
            impl NoLookAhead for #fmt_id {
                proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
                    reveal(<#fmt_id as SpecParser>::spec_parse);
                    let fmt = #fmt_id::spec_inner();
                    fmt.lemma_no_lookahead(i1, i2);
                }
            }
        })
    }

    fn gen_scc_strict_rec_body_proofs(&self, scc: &RecursiveScc, scc_info: &SccInfo) -> String {
        let rb_id = format_ident!("{}", scc_info.rec_body_ident);
        // Every SCC member gets a StrictRecBody proof shell.
        let rb_idents: Vec<_> = scc
            .members
            .iter()
            .map(|m| format_ident!("{}BodyRec", self.info(&m.name).names.exec))
            .collect();

        let per_member: Vec<_> = rb_idents
            .iter()
            .map(|rb| {
                quote! {
                    impl StrictRecBody for #rb {
                        proof fn lemma_body_all_inv_preservation(
                            &self,
                            _param: Self::Param,
                            rec: ParamRecSpecs<Self::Param, Self::T>,
                        ) {
                            broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;
                        }
                    }
                }
            })
            .collect();

        let hides: Vec<_> = rb_idents
            .iter()
            .map(|rb| quote! { hide(<#rb as SpecRecBody>::spec_body); })
            .collect();
        let calls: Vec<_> = rb_idents
            .iter()
            .map(|rb| quote! { #rb.lemma_body_all_inv_preservation(param, rec); })
            .collect();
        render_ts(quote! {
            #(#per_member)*
            impl StrictRecBody for #rb_id {
                proof fn lemma_body_all_inv_preservation(
                    &self,
                    param: Self::Param,
                    rec: ParamRecSpecs<Self::Param, Self::T>,
                ) {
                    #(#hides)*
                    broadcast use vest_lib2::combinators::disjoint::disjointness_lemmas;
                    #(#calls)*
                }
            }
        })
    }

    fn member_param_fields(&self, member: &SccMember) -> Vec<(String, String, TokenStream)> {
        member
            .param_defns
            .iter()
            .map(|p| match p {
                crate::vestir::ParamDefn::Dependent { name, combinator } => (
                    name.clone(),
                    scc_param_field_name(name, combinator),
                    self.render_value_type(combinator, TypeMode::Exec),
                ),
            })
            .collect()
    }

    fn render_member_spec_param_args(&self, member: &SccMember) -> Vec<TokenStream> {
        member
            .param_defns
            .iter()
            .map(|param| match param {
                crate::vestir::ParamDefn::Dependent { name, combinator } => {
                    let field_name = scc_param_field_name(name, combinator);
                    let accessor_ident = format_ident!("{}_spec", field_name);
                    quote! { self.#accessor_ident() }
                }
            })
            .collect()
    }

    fn render_member_parse_spec_match(
        &self,
        member: &SccMember,
        _scc: &RecursiveScc,
        scc_info: &SccInfo,
        _access: RecExecParamAccess,
    ) -> TokenStream {
        let rec_body_ident = format_ident!("{}", scc_info.rec_body_ident);
        let helper_fn = format_ident!("{}_parse_spec_gas", self.info(&member.name).names.dsl);
        let param_args = self.render_member_spec_param_args(member);
        quote! {
            #helper_fn::<LIMIT>(&#rec_body_ident, gas as nat, #(#param_args,)* ibuf@)
        }
    }

    fn render_member_consistent_expr(
        &self,
        member: &SccMember,
        _scc: &RecursiveScc,
        scc_info: &SccInfo,
        _access: RecExecParamAccess,
        value_expr: TokenStream,
    ) -> TokenStream {
        let rec_body_ident = format_ident!("{}", scc_info.rec_body_ident);
        let helper_fn = format_ident!("{}_consistent_spec_gas", self.info(&member.name).names.dsl);
        let param_args = self.render_member_spec_param_args(member);
        quote! {
            #helper_fn::<LIMIT>(&#rec_body_ident, gas as nat, #(#param_args,)* #value_expr)
        }
    }

    fn render_member_serialize_spec_expr(
        &self,
        member: &SccMember,
        _scc: &RecursiveScc,
        scc_info: &SccInfo,
        _access: RecExecParamAccess,
        value_expr: TokenStream,
    ) -> TokenStream {
        let rec_body_ident = format_ident!("{}", scc_info.rec_body_ident);
        let helper_fn = format_ident!("{}_serialize_spec_gas", self.info(&member.name).names.dsl);
        let param_args = self.render_member_spec_param_args(member);
        quote! {
            #helper_fn::<LIMIT>(&#rec_body_ident, gas as nat, #(#param_args,)* #value_expr)
        }
    }

    fn render_member_byte_len_expr(
        &self,
        member: &SccMember,
        _scc: &RecursiveScc,
        scc_info: &SccInfo,
        _access: RecExecParamAccess,
        value_expr: TokenStream,
    ) -> TokenStream {
        let rec_body_ident = format_ident!("{}", scc_info.rec_body_ident);
        let helper_fn = format_ident!("{}_byte_len_spec_gas", self.info(&member.name).names.dsl);
        let param_args = self.render_member_spec_param_args(member);
        quote! {
            #helper_fn::<LIMIT>(&#rec_body_ident, gas as nat, #(#param_args,)* #value_expr)
        }
    }

    fn fmt_expr_for_recursive_invocation(
        &self,
        invocation: &crate::vestir::CombinatorInvocation,
        current_member: &SccMember,
        access: RecExecParamAccess,
        value_base: Option<&str>,
    ) -> TokenStream {
        let fmt_ident = format_ident!("{}", self.info(&invocation.func).names.fmt);
        let target_member = self
            .find_scc_for_member(&invocation.func)
            .and_then(|scc| scc.members.iter().find(|m| m.name == invocation.func))
            .expect("recursive invocation target missing from SCC");
        if target_member.param_defns.is_empty() {
            return quote! { #fmt_ident::<LIMIT> {} };
        }
        let field_inits: Vec<_> = target_member
            .param_defns
            .iter()
            .zip(invocation.args.iter())
            .map(|(param, arg)| match (param, arg) {
                (
                    crate::vestir::ParamDefn::Dependent { name, combinator },
                    crate::vestir::Param::Dependent(arg_name),
                ) => {
                    // Use the shared param field name (e.g., "expr_kind"), not the dep name (e.g., "t").
                    let shared_name = scc_param_field_name(name, combinator);
                    let field_ident = format_ident!("{}", shared_name);
                    let value = self.render_recursive_runtime_dep_expr(
                        arg_name,
                        &current_member.param_defns,
                        access,
                        value_base,
                    );
                    quote! { #field_ident: #value }
                }
            })
            .collect();
        quote! { #fmt_ident::<LIMIT> { #(#field_inits),* } }
    }

    fn render_recursive_runtime_dep_expr(
        &self,
        dep: &str,
        current_param_defns: &[crate::vestir::ParamDefn],
        access: RecExecParamAccess,
        value_base: Option<&str>,
    ) -> TokenStream {
        let base = dep.split('.').next().unwrap();
        let suffix = &dep[base.len()..];
        let is_outer_param = current_param_defns.iter().any(|p| match p {
            crate::vestir::ParamDefn::Dependent { name, .. } => name == base,
        });
        if is_outer_param {
            // Find the shared param field name (e.g. "expr_kind") for this dep (e.g. "t").
            let shared_name = current_param_defns
                .iter()
                .find_map(|p| match p {
                    crate::vestir::ParamDefn::Dependent { name, combinator } if name == base => {
                        Some(scc_param_field_name(name, combinator))
                    }
                    _ => None,
                })
                .unwrap_or_else(|| base.to_string());
            let shared_ident = format_ident!("{}", shared_name);
            match access {
                RecExecParamAccess::SelfFields => {
                    if suffix.is_empty() {
                        quote! { self.#shared_ident }
                    } else {
                        let suffix_ts: TokenStream =
                            format!("self.{}{}", shared_name, suffix).parse().unwrap();
                        suffix_ts
                    }
                }
            }
        } else if let Some(value_base) = value_base {
            let path: TokenStream = format!("{}.{}", value_base, dep).parse().unwrap();
            path
        } else {
            let ts: TokenStream = dep.parse().unwrap();
            ts
        }
    }

    fn render_recursive_parse_call(
        &self,
        invocation: &crate::vestir::CombinatorInvocation,
        current_member: &SccMember,
        access: RecExecParamAccess,
        input_expr: TokenStream,
    ) -> TokenStream {
        let fmt_expr =
            self.fmt_expr_for_recursive_invocation(invocation, current_member, access, None);
        quote! { (#fmt_expr).parse_gas(gas - 1, #input_expr) }
    }

    fn render_recursive_serialize_call(
        &self,
        invocation: &crate::vestir::CombinatorInvocation,
        current_member: &SccMember,
        access: RecExecParamAccess,
        value_expr: TokenStream,
        value_base: Option<&str>,
    ) -> TokenStream {
        let fmt_expr =
            self.fmt_expr_for_recursive_invocation(invocation, current_member, access, value_base);
        quote! { (#fmt_expr).serialize_gas(gas - 1, #value_expr, obuf) }
    }

    fn render_recursive_prepare_call(
        &self,
        invocation: &crate::vestir::CombinatorInvocation,
        current_member: &SccMember,
        access: RecExecParamAccess,
        value_expr: TokenStream,
        value_base: Option<&str>,
    ) -> TokenStream {
        let fmt_expr =
            self.fmt_expr_for_recursive_invocation(invocation, current_member, access, value_base);
        quote! { (#fmt_expr).prepare_gas(gas - 1, #value_expr) }
    }

    fn render_struct_exec_local_binding(
        &self,
        combinator: &Combinator,
        label_ident: &proc_macro2::Ident,
    ) -> TokenStream {
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_)
            | Combinator::ConstraintEnum(_)
            | Combinator::Tail(_)
            | Combinator::Bytes(_) => quote! { src.#label_ident },
            Combinator::Invocation(inv) => match self.def_by_name(&inv.func) {
                Some(crate::vestir::Definition::EnumDef { .. }) => quote! { src.#label_ident },
                _ => quote! { &src.#label_ident },
            },
            _ => quote! { &src.#label_ident },
        }
    }

    pub(crate) fn gen_recursive_execs_fragment(&self, scc: &RecursiveScc) -> String {
        let scc_info = match self.scc_info_for(&scc.members[0].name) {
            Some(i) => i,
            None => return String::new(),
        };
        let member_names: Vec<String> = scc.members.iter().map(|m| m.name.clone()).collect();
        let ctx = self.make_ctx(&member_names, scc, scc_info);
        let mut out = CodeWriter::new();
        // Every SCC member gets Parser/Serializer/Prepare wrappers and a direct exec impl block.
        for member in &scc.members {
            out.push_multiline(self.gen_recursive_exec_wrappers(member));
            out.blank_line();
        }
        for member in &scc.members {
            out.push_multiline(self.gen_recursive_exec_impl(member, scc, scc_info, &ctx));
            out.blank_line();
        }
        out.finish()
    }
}

impl<'a> Analysis<'a> {
    fn gen_recursive_exec_wrappers(&self, member: &SccMember) -> String {
        let fmt_ident = format_ident!("{}", self.info(&member.name).names.fmt);
        let exec_ty = self.render_nominal_type(&member.name, TypeMode::Exec);
        render_ts(quote! {
            impl<'i, const LIMIT: usize> Parser<&'i [u8]> for #fmt_ident<LIMIT> {
                type PT = #exec_ty;

                fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
                    self.parse_gas(LIMIT, ibuf)
                }
            }

            impl<'i, const LIMIT: usize> Serializer<#exec_ty> for #fmt_ident<LIMIT> {
                fn serialize(&self, v: &#exec_ty, obuf: &mut Vec<u8>) {
                    self.serialize_gas(LIMIT, v, obuf);
                }
            }

            impl<'i, const LIMIT: usize> Prepare<#exec_ty> for #fmt_ident<LIMIT> {
                fn prepare(&self, v: &#exec_ty) -> Result<usize, PreSerializeError> {
                    self.prepare_gas(LIMIT, v)
                }
            }
        })
    }

    fn gen_recursive_exec_impl(
        &self,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
    ) -> String {
        let fmt_ident = format_ident!("{}", self.info(&member.name).names.fmt);
        let mut out = CodeWriter::new();
        out.block(
            format!("impl<const LIMIT: usize> {}<LIMIT>", fmt_ident),
            |w| {
                self.emit_recursive_parse_gas_method(
                    w,
                    member,
                    scc,
                    scc_info,
                    ctx,
                    RecExecParamAccess::SelfFields,
                );
                w.blank_line();
                self.emit_recursive_serialize_gas_method(
                    w,
                    member,
                    scc,
                    scc_info,
                    ctx,
                    RecExecParamAccess::SelfFields,
                );
                w.blank_line();
                self.emit_recursive_prepare_gas_method(
                    w,
                    member,
                    scc,
                    scc_info,
                    ctx,
                    RecExecParamAccess::SelfFields,
                );
            },
        );
        out.finish()
    }

    fn emit_recursive_parse_gas_method(
        &self,
        out: &mut CodeWriter,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ty = self.render_nominal_type(&member.name, TypeMode::Exec);
        let spec_match = self.render_member_parse_spec_match(member, scc, scc_info, access);
        let header = normalize_verus_signature(render_ts(quote! {
            fn parse_gas<'i>(&self, gas: usize, ibuf: &&'i [u8]) -> (r: PResult<#exec_ty>)
                ensures
                    parse_matches_spec(r, #spec_match),
                    r matches Ok((n, _)) ==> n <= ibuf@.len(),
                decreases gas,
        }));
        out.block(header, |w| {
            w.line("broadcast use vest_lib2::core::spec::SafeParser::lemma_parse_safe;");
            w.blank_line();
            w.line("let _ = ibuf.len();");
            w.line(render_ts(quote! { let ghost parse_spec = #spec_match; }));
            w.line("let rest = *ibuf;");
            w.blank_line();
            self.emit_recursive_member_parse_body(w, member, ctx, access);
        });
    }

    fn emit_recursive_serialize_gas_method(
        &self,
        out: &mut CodeWriter,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ty = self.render_nominal_type(&member.name, TypeMode::Exec);
        let consistent = self.render_member_consistent_expr(
            member,
            scc,
            scc_info,
            access,
            quote! { v.deep_view() },
        );
        let serialize_spec = self.render_member_serialize_spec_expr(
            member,
            scc,
            scc_info,
            access,
            quote! { v.deep_view() },
        );
        let header = normalize_verus_signature(render_ts(quote! {
            fn serialize_gas<'i>(&self, gas: usize, v: &#exec_ty, obuf: &mut Vec<u8>)
                requires
                    #consistent,
                ensures
                    final(obuf)@ == old(obuf)@ + #serialize_spec,
                decreases gas,
        }));
        out.block(header, |w| {
            self.emit_recursive_member_serialize_body(w, member, ctx, access);
        });
    }

    fn emit_recursive_prepare_gas_method(
        &self,
        out: &mut CodeWriter,
        member: &SccMember,
        scc: &RecursiveScc,
        scc_info: &SccInfo,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ty = self.render_nominal_type(&member.name, TypeMode::Exec);
        let consistent = self.render_member_consistent_expr(
            member,
            scc,
            scc_info,
            access,
            quote! { v.deep_view() },
        );
        let byte_len = self.render_member_byte_len_expr(
            member,
            scc,
            scc_info,
            access,
            quote! { v.deep_view() },
        );
        let header = normalize_verus_signature(render_ts(quote! {
            fn prepare_gas<'i>(&self, gas: usize, v: &#exec_ty) -> (checked: Result<usize, PreSerializeError>)
                ensures
                    checked matches Ok(len) ==> {
                        &&& #consistent
                        &&& len == #byte_len
                    },
                decreases gas,
        }));
        out.block(header, |w| {
            self.emit_recursive_member_prepare_body(w, member, ctx, access);
        });
    }

    fn emit_recursive_member_parse_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        match &member.body {
            SccMemberBody::Struct(s) => {
                self.emit_recursive_struct_parse_body(w, member, s, ctx, access)
            }
            SccMemberBody::Choice(c) => {
                self.emit_recursive_choice_parse_body(w, member, c, ctx, access)
            }
            SccMemberBody::Combinator(c) => {
                self.emit_recursive_combinator_parse_body(w, member, c, ctx, access)
            }
        }
    }

    fn emit_recursive_member_serialize_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        match &member.body {
            SccMemberBody::Struct(s) => {
                self.emit_recursive_struct_serialize_body(w, member, s, ctx, access)
            }
            SccMemberBody::Choice(c) => {
                self.emit_recursive_choice_serialize_body(w, member, c, ctx, access)
            }
            SccMemberBody::Combinator(c) => {
                self.emit_recursive_combinator_serialize_body(w, member, c, ctx, access)
            }
        }
    }

    fn emit_recursive_member_prepare_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        match &member.body {
            SccMemberBody::Struct(s) => {
                self.emit_recursive_struct_prepare_body(w, member, s, ctx, access)
            }
            SccMemberBody::Choice(c) => {
                self.emit_recursive_choice_prepare_body(w, member, c, ctx, access)
            }
            SccMemberBody::Combinator(c) => {
                self.emit_recursive_combinator_prepare_body(w, member, c, ctx, access)
            }
        }
    }
}

impl<'a> Analysis<'a> {
    fn emit_recursive_struct_parse_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        s: &StructCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let mut n_vars = Vec::new();
        let mut seen_recursive = false;
        for (idx, field) in s.0.iter().enumerate() {
            let n_var = format!("n{}", idx + 1);
            match field {
                StructField::Const { label, combinator } => {
                    let fmt_expr = self.render_exec_const_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Parse,
                    );
                    let fmt_str = render_ts(quote! { #fmt_expr });
                    w.call_chain_stmt(
                        Some(&format!("({}, {})", n_var, label)),
                        &fmt_str,
                        "parse",
                        &["&rest"],
                        Some("?;"),
                    );
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let n_ident = format_ident!("{}", n_var);
                    let label_ident = format_ident!("{}", label);
                    if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            if !seen_recursive {
                                w.if_block("gas == 0", |w| {
                                    w.line("return Err(ParseError::recursion_limit_exceeded());");
                                });
                                seen_recursive = true;
                            }
                            let call = self.render_recursive_parse_call(
                                inv,
                                member,
                                access,
                                quote! { &rest },
                            );
                            w.push_multiline(render_ts(quote! {
                                let (#n_ident, #label_ident) = #call?;
                            }));
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Parse,
                            );
                            let fmt_str = render_ts(quote! { #fmt_expr });
                            w.call_chain_stmt(
                                Some(&format!("({}, {})", n_var, label)),
                                &fmt_str,
                                "parse",
                                &["&rest"],
                                Some("?;"),
                            );
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Parse,
                        );
                        let fmt_str = render_ts(quote! { #fmt_expr });
                        w.call_chain_stmt(
                            Some(&format!("({}, {})", n_var, label)),
                            &fmt_str,
                            "parse",
                            &["&rest"],
                            Some("?;"),
                        );
                    }

                    let label_ident = format_ident!("{}", label);
                    if let Some(pred) =
                        self.gen_constraint_pred(combinator, quote! { #label_ident })
                    {
                        w.if_block(format!("!({})", render_ts(pred)), |w| {
                            w.line("return Err(ParseError::predicate_failed());");
                        });
                    }
                }
            }
            w.line(format!("let rest = rest.skip({});", n_var));
            n_vars.push(n_var);
        }

        let total_n_expr = if n_vars.is_empty() {
            "0usize".to_string()
        } else {
            n_vars.join(" + ")
        };
        let exec_ident = format_ident!("{}", self.info(&member.name).names.exec);
        let ctor_fields: Vec<String> =
            s.0.iter()
                .filter_map(|f| match f {
                    StructField::Const { .. } => None,
                    StructField::Dependent { label, combinator }
                    | StructField::Ordinary { label, combinator } => {
                        let expr = if is_combinator_in_scc(combinator, ctx.members) {
                            format!("{}: Box::new({})", label, label)
                        } else {
                            format!("{}: {}", label, label)
                        };
                        Some(expr)
                    }
                })
                .collect();
        w.line(format!("let total_n = {};", total_n_expr));
        w.record_constructor_stmt("final_v", &exec_ident.to_string(), &ctor_fields);
        w.line("assert(parse_spec == Some((total_n as int, final_v.deep_view())));");
        w.line("Ok((total_n, final_v))");
    }

    fn emit_recursive_struct_serialize_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        s: &StructCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        w.line("let src = v;");
        for field in &s.0 {
            if let StructField::Dependent { label, combinator }
            | StructField::Ordinary { label, combinator } = field
            {
                let label_ident = format_ident!("{}", label);
                let bind_expr = self.render_struct_exec_local_binding(combinator, &label_ident);
                w.line(render_ts(quote! { let #label_ident = #bind_expr; }));
            }
        }
        let mut seen_recursive = false;
        for field in &s.0 {
            match field {
                StructField::Const { label, combinator } => {
                    let fmt_expr = self.render_exec_const_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Serialize,
                    );
                    let fmt_str = render_ts(quote! { #fmt_expr });
                    w.call_chain_stmt(
                        None,
                        &fmt_str,
                        "serialize",
                        &[label, "obuf"].as_slice(),
                        Some(";"),
                    );
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let value_expr = quote! { #label_ident };
                    if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            if !seen_recursive {
                                seen_recursive = true;
                            }
                            let call = self.render_recursive_serialize_call(
                                inv, member, access, value_expr, None,
                            );
                            w.line(render_ts(quote! { #call; }));
                            continue;
                        }
                    }
                    let fmt_expr = self.render_exec_combinator_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Serialize,
                    );
                    w.line(render_ts(
                        quote! { (#fmt_expr).serialize(&src.#label_ident, obuf); },
                    ));
                }
            }
        }
    }

    fn emit_recursive_struct_prepare_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        s: &StructCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        w.line("let src = v;");
        for field in &s.0 {
            if let StructField::Dependent { label, combinator }
            | StructField::Ordinary { label, combinator } = field
            {
                let label_ident = format_ident!("{}", label);
                let bind_expr = self.render_struct_exec_local_binding(combinator, &label_ident);
                w.line(render_ts(quote! { let #label_ident = #bind_expr; }));
            }
        }
        let mut lens = Vec::new();
        let mut seen_recursive = false;
        for (idx, field) in s.0.iter().enumerate() {
            let l_var = format!("l{}", idx + 1);
            let l_ident = format_ident!("{}", l_var);
            match field {
                StructField::Const { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    let fmt_expr = self.render_exec_const_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Serialize,
                    );
                    w.push_multiline(render_ts(quote! {
                        let #l_ident = (#fmt_expr).prepare(#label_ident)?;
                    }));
                }
                StructField::Dependent { label, combinator }
                | StructField::Ordinary { label, combinator } => {
                    let label_ident = format_ident!("{}", label);
                    if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            if !seen_recursive {
                                w.if_block("gas == 0", |w| {
                                    w.line(
                                        "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded));",
                                    );
                                });
                                seen_recursive = true;
                            }
                            let call = self.render_recursive_prepare_call(
                                inv,
                                member,
                                access,
                                quote! { #label_ident },
                                None,
                            );
                            w.push_multiline(render_ts(quote! {
                                let #l_ident = #call?;
                            }));
                            lens.push(l_var);
                            continue;
                        }
                    }
                    let fmt_expr = self.render_exec_combinator_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Serialize,
                    );
                    let prep = self.render_prepare_value(
                        quote! { &src.#label_ident },
                        fmt_expr,
                        combinator,
                    );
                    w.push_multiline(render_ts(quote! {
                        let #l_ident = #prep?;
                    }));
                }
            }
            lens.push(l_var);
        }
        self.emit_checked_add_return(w, "total", &lens);
    }

    fn emit_recursive_choice_parse_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ident = format_ident!("{}", self.info(&member.name).names.exec);
        let variants = self.choice_variant_names(c);
        if let Some(dep) = &c.depend_id {
            let dep_expr =
                self.render_recursive_runtime_dep_expr(dep, &member.param_defns, access, None);
            w.match_block_stmt(Some("(n, v)"), &render_ts(dep_expr), |w| {
                for ((pat, combinator), variant_name) in c.choices.iter().zip(variants.iter()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let pat_ts = match pat {
                        ChoicePattern::Enum(name) => {
                            let enum_ty = self
                                .resolve_dep_enum_type(dep, &member.param_defns)
                                .unwrap_or_else(|| quote! { _ });
                            let pat_ident = format_ident!("{}", name);
                            quote! { #enum_ty::#pat_ident }
                        }
                        ChoicePattern::Int(elem) => self.render_constraint_elem_pat(elem),
                        ChoicePattern::Array(arr) => {
                            let pat_expr = self.render_const_array_expr(arr, TypeMode::Exec);
                            quote! { x if x.deep_eq(&#pat_expr) }
                        }
                        ChoicePattern::Wildcard => quote! { _ },
                    };

                    let parse_stmt = if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            let call = self.render_recursive_parse_call(
                                inv,
                                member,
                                access,
                                quote! { ibuf },
                            );
                            quote! {
                                if gas == 0 {
                                    return Err(ParseError::recursion_limit_exceeded());
                                }
                                let (n, inner) = #call?;
                            }
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Parse,
                            );
                            quote! { let (n, inner) = (#fmt_expr).parse(ibuf)?; }
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Parse,
                        );
                        quote! { let (n, inner) = (#fmt_expr).parse(ibuf)?; }
                    };

                    let ctor = if is_combinator_in_scc(combinator, ctx.members) {
                        quote! { #exec_ident::#variant_ident(Box::new(inner)) }
                    } else {
                        quote! { #exec_ident::#variant_ident(inner) }
                    };
                    w.push_multiline(render_ts(quote! {
                        #pat_ts => {
                            #parse_stmt
                            (n, #ctor)
                        },
                    }));
                }
            });
        } else {
            let mut chain = quote! { Err(ParseError::invalid_choice()) };
            for ((_, combinator), variant_name) in c.choices.iter().zip(variants.iter()).rev() {
                let variant_ident = format_ident!("{}", variant_name);
                let ctor = if is_combinator_in_scc(combinator, ctx.members) {
                    quote! { #exec_ident::#variant_ident(Box::new(va)) }
                } else {
                    quote! { #exec_ident::#variant_ident(va) }
                };
                chain = if let Combinator::Invocation(inv) = combinator {
                    if ctx.is_in_scc(&inv.func) {
                        let call =
                            self.render_recursive_parse_call(inv, member, access, quote! { ibuf });
                        quote! {
                            if gas == 0 {
                                Err(ParseError::recursion_limit_exceeded())
                            } else {
                                match #call {
                                    Ok((n, va)) => Ok((n, #ctor)),
                                    _ => #chain,
                                }
                            }
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Parse,
                        );
                        quote! {
                            match (#fmt_expr).parse(ibuf) {
                                Ok((n, va)) => Ok((n, #ctor)),
                                _ => #chain,
                            }
                        }
                    }
                } else {
                    let fmt_expr = self.render_exec_combinator_expr(
                        combinator,
                        &member.param_defns,
                        super::execs::CodegenMode::Parse,
                    );
                    quote! {
                        match (#fmt_expr).parse(ibuf) {
                            Ok((n, va)) => Ok((n, #ctor)),
                            _ => #chain,
                        }
                    }
                };
            }
            w.line(render_ts(quote! {
                let (n, v) = match #chain {
                    Ok(parsed) => parsed,
                    Err(err) => return Err(err),
                };
            }));
        }
        w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
        w.line("Ok((n, v))");
    }

    fn emit_recursive_choice_serialize_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ident = format_ident!("{}", self.info(&member.name).names.exec);
        let variants = self.choice_variant_names(c);
        if let Some(dep) = &c.depend_id {
            let dep_expr =
                self.render_recursive_runtime_dep_expr(dep, &member.param_defns, access, None);
            w.match_block_stmt(None, &format!("({}, v)", render_ts(dep_expr)), |w| {
                for ((pat, combinator), variant_name) in c.choices.iter().zip(variants.iter()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let pat_ts = match pat {
                        ChoicePattern::Enum(name) => {
                            let enum_ty = self
                                .resolve_dep_enum_type(dep, &member.param_defns)
                                .unwrap_or_else(|| quote! { _ });
                            let pat_ident = format_ident!("{}", name);
                            quote! { (#enum_ty::#pat_ident, #exec_ident::#variant_ident(v)) }
                        }
                        ChoicePattern::Int(elem) => match elem {
                            ConstraintElem::Single(v) => {
                                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                quote! { (#lit, #exec_ident::#variant_ident(v)) }
                            }
                            _ => {
                                let cond = self.render_constraint_elem_pred(elem, quote! { x });
                                quote! { (x, #exec_ident::#variant_ident(v)) if #cond }
                            }
                        },
                        ChoicePattern::Array(arr) => {
                            let pat_expr = self.render_const_array_expr(arr, TypeMode::Exec);
                            quote! { (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) }
                        }
                        ChoicePattern::Wildcard => quote! { (_, #exec_ident::#variant_ident(v)) },
                    };
                    let ser = if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            self.render_recursive_serialize_call(
                                inv,
                                member,
                                access,
                                quote! { v },
                                Some("v"),
                            )
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Serialize,
                            );
                            quote! { (#fmt_expr).serialize(v, obuf) }
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Serialize,
                        );
                        quote! { (#fmt_expr).serialize(v, obuf) }
                    };
                    w.push_multiline(render_ts(quote! {
                        #pat_ts => { #ser; },
                    }));
                }
                w.line("_ => {},");
            });
        } else {
            w.match_block_stmt(None, "v", |w| {
                for ((_, combinator), variant_name) in c.choices.iter().zip(variants.iter()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let ser = if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            self.render_recursive_serialize_call(
                                inv,
                                member,
                                access,
                                quote! { v },
                                Some("v"),
                            )
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Serialize,
                            );
                            quote! { (#fmt_expr).serialize(v, obuf) }
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Serialize,
                        );
                        quote! { (#fmt_expr).serialize(v, obuf) }
                    };
                    w.push_multiline(render_ts(quote! {
                        #exec_ident::#variant_ident(v) => { #ser; },
                    }));
                }
            });
        }
    }

    fn emit_recursive_choice_prepare_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        c: &ChoiceCombinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        let exec_ident = format_ident!("{}", self.info(&member.name).names.exec);
        let variants = self.choice_variant_names(c);
        if let Some(dep) = &c.depend_id {
            let dep_expr =
                self.render_recursive_runtime_dep_expr(dep, &member.param_defns, access, None);
            w.match_block_stmt(None, &format!("({}, v)", render_ts(dep_expr)), |w| {
                for ((pat, combinator), variant_name) in c.choices.iter().zip(variants.iter()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let pat_ts = match pat {
                        ChoicePattern::Enum(name) => {
                            let enum_ty = self
                                .resolve_dep_enum_type(dep, &member.param_defns)
                                .unwrap_or_else(|| quote! { _ });
                            let pat_ident = format_ident!("{}", name);
                            quote! { (#enum_ty::#pat_ident, #exec_ident::#variant_ident(v)) }
                        }
                        ChoicePattern::Int(elem) => match elem {
                            ConstraintElem::Single(v) => {
                                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                                quote! { (#lit, #exec_ident::#variant_ident(v)) }
                            }
                            _ => {
                                let cond = self.render_constraint_elem_pred(elem, quote! { x });
                                quote! { (x, #exec_ident::#variant_ident(v)) if #cond }
                            }
                        },
                        ChoicePattern::Array(arr) => {
                            let pat_expr = self.render_const_array_expr(arr, TypeMode::Exec);
                            quote! { (x, #exec_ident::#variant_ident(v)) if x.deep_eq(&#pat_expr) }
                        }
                        ChoicePattern::Wildcard => quote! { (_, #exec_ident::#variant_ident(v)) },
                    };
                    let prep = if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            let call =
                                self.render_recursive_prepare_call(inv, member, access, quote! { v }, Some("v"));
                            quote! {{
                                if gas == 0 {
                                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded))
                                } else {
                                    #call
                                }
                            }}
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Serialize,
                            );
                            self.render_prepare_value(quote! { v }, fmt_expr, combinator)
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Serialize,
                        );
                        self.render_prepare_value(quote! { v }, fmt_expr, combinator)
                    };
                    w.push_multiline(render_ts(quote! {
                        #pat_ts => #prep,
                    }));
                }
                w.line("_ => Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag)),");
            });
        } else {
            w.match_block_stmt(None, "v", |w| {
                for ((_, combinator), variant_name) in c.choices.iter().zip(variants.iter()) {
                    let variant_ident = format_ident!("{}", variant_name);
                    let prep = if let Combinator::Invocation(inv) = combinator {
                        if ctx.is_in_scc(&inv.func) {
                            let call =
                                self.render_recursive_prepare_call(inv, member, access, quote! { v }, Some("v"));
                            quote! {{
                                if gas == 0 {
                                    Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded))
                                } else {
                                    #call
                                }
                            }}
                        } else {
                            let fmt_expr = self.render_exec_combinator_expr(
                                combinator,
                                &member.param_defns,
                                super::execs::CodegenMode::Serialize,
                            );
                            self.render_prepare_value(quote! { v }, fmt_expr, combinator)
                        }
                    } else {
                        let fmt_expr = self.render_exec_combinator_expr(
                            combinator,
                            &member.param_defns,
                            super::execs::CodegenMode::Serialize,
                        );
                        self.render_prepare_value(quote! { v }, fmt_expr, combinator)
                    };
                    w.push_multiline(render_ts(quote! {
                        #exec_ident::#variant_ident(v) => #prep,
                    }));
                }
            });
        }
    }

    fn emit_recursive_combinator_parse_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        combinator: &Combinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        if let Combinator::Invocation(inv) = combinator {
            if ctx.is_in_scc(&inv.func) {
                w.if_block("gas == 0", |w| {
                    w.line("return Err(ParseError::recursion_limit_exceeded());");
                });
                let call = self.render_recursive_parse_call(inv, member, access, quote! { ibuf });
                w.push_multiline(render_ts(quote! {
                    let (n, v) = #call?;
                }));
                w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
                w.line("Ok((n, v))");
                return;
            }
        }
        let fmt_expr = self.render_exec_combinator_expr(
            combinator,
            &member.param_defns,
            super::execs::CodegenMode::Parse,
        );
        w.push_multiline(render_ts(quote! {
            let (n, v) = (#fmt_expr).parse(ibuf)?;
        }));
        if let Some(pred) = self.gen_constraint_pred(combinator, quote! { v }) {
            w.if_block(format!("!({})", render_ts(pred)), |w| {
                w.line("return Err(ParseError::predicate_failed());");
            });
        }
        w.line("assert(parse_spec == Some((n as int, v.deep_view())));");
        w.line("Ok((n, v))");
    }

    fn emit_recursive_combinator_serialize_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        combinator: &Combinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        if let Combinator::Invocation(inv) = combinator {
            if ctx.is_in_scc(&inv.func) {
                let call = self.render_recursive_serialize_call(
                    inv,
                    member,
                    access,
                    quote! { v },
                    Some("v"),
                );
                w.line(render_ts(quote! { #call; }));
                return;
            }
        }
        let fmt_expr = self.render_exec_combinator_expr(
            combinator,
            &member.param_defns,
            super::execs::CodegenMode::Serialize,
        );
        w.line(render_ts(quote! { (#fmt_expr).serialize(v, obuf); }));
    }

    fn emit_recursive_combinator_prepare_body(
        &self,
        w: &mut CodeWriter,
        member: &SccMember,
        combinator: &Combinator,
        ctx: &RecCtx<'_>,
        access: RecExecParamAccess,
    ) {
        if let Combinator::Invocation(inv) = combinator {
            if ctx.is_in_scc(&inv.func) {
                w.if_block("gas == 0", |w| {
                    w.line(
                        "return Err(PreSerializeError::not_compliant(ComplianceErrorKind::RecursionLimitExceeded));",
                    );
                });
                let call = self.render_recursive_prepare_call(
                    inv,
                    member,
                    access,
                    quote! { v },
                    Some("v"),
                );
                w.line(render_ts(call));
                return;
            }
        }
        let fmt_expr = self.render_exec_combinator_expr(
            combinator,
            &member.param_defns,
            super::execs::CodegenMode::Serialize,
        );
        let prep = self.render_prepare_value(quote! { v }, fmt_expr, combinator);
        w.line(render_ts(prep));
    }
}
