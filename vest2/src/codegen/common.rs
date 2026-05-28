use crate::vestir::{
    self, ArrayCombinator, ChoiceCombinator, Choices, Combinator, CombinatorInvocation,
    ConstCombinator, ConstraintEnumCombinator, ConstraintIntCombinator, Definition, Endianess,
    GlobalCtx, LengthExpr, OptionCombinator, ParamDefn, StructCombinator, StructField,
    TailCombinator, VecCombinator, WrapCombinator,
};
use heck::ToUpperCamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct FormatNames {
    #[allow(dead_code)]
    pub(crate) dsl: String,
    pub(crate) exec: String,
    pub(crate) spec: String,
    pub(crate) inner: String,
    pub(crate) fmt: String,
    pub(crate) fmt_fn: String,
}

#[derive(Debug, Clone)]
pub(crate) struct FormatInfo {
    pub(crate) names: FormatNames,
    pub(crate) needs_lifetime: bool,
    pub(crate) non_tail: bool,
    pub(crate) non_malleable: bool,
}

pub(crate) struct Analysis<'a> {
    pub(crate) defs: &'a [Definition],
    pub(crate) ctx: &'a GlobalCtx,
    #[allow(dead_code)]
    pub(crate) endianness: Endianess,
    pub(crate) infos: HashMap<String, FormatInfo>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeMode {
    Exec,
    Spec,
}

pub(crate) struct CodeWriter {
    buf: String,
    indent: usize,
    needs_indent: bool,
}

impl CodeWriter {
    pub(crate) fn new() -> Self {
        Self {
            buf: String::new(),
            indent: 0,
            needs_indent: true,
        }
    }

    pub(crate) fn line(&mut self, line: impl AsRef<str>) {
        self.write_line_inner(line.as_ref());
        self.buf.push('\n');
        self.needs_indent = true;
    }

    pub(crate) fn blank_line(&mut self) {
        if !self.buf.ends_with("\n") {
            self.buf.push('\n');
        }
        if !self.buf.ends_with("\n\n") {
            self.buf.push('\n');
        }
        self.needs_indent = true;
    }

    pub(crate) fn push_multiline(&mut self, text: impl AsRef<str>) {
        let text = text.as_ref();
        for line in text.lines() {
            self.write_line_inner(line);
            self.buf.push('\n');
            self.needs_indent = true;
        }
    }

    pub(crate) fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indent += 1;
        f(self);
        self.indent -= 1;
    }

    pub(crate) fn block(&mut self, header: impl AsRef<str>, f: impl FnOnce(&mut Self)) {
        self.line(format!("{} {{", header.as_ref()));
        self.indented(f);
        self.line("}");
    }

    pub(crate) fn finish(mut self) -> String {
        while self.buf.ends_with("\n\n\n") {
            self.buf.pop();
        }
        self.buf
    }

    fn write_line_inner(&mut self, line: &str) {
        if line.is_empty() {
            return;
        }
        if self.needs_indent {
            self.buf.push_str(&"    ".repeat(self.indent));
            self.needs_indent = false;
        }
        self.buf.push_str(line);
    }
}

pub(crate) fn render_ts(ts: TokenStream) -> String {
    format_verus_snippet(&ts.to_string())
}

pub(crate) fn format_verus_snippet(input: &str) -> String {
    let chars = input.chars().collect::<Vec<_>>();
    let mut out = String::new();
    let mut i = 0usize;
    let mut indent = 0usize;
    let mut line_start = true;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    let mut in_string = false;
    let mut escape = false;

    fn next_non_space(chars: &[char], mut i: usize) -> Option<char> {
        while i < chars.len() {
            if !chars[i].is_whitespace() {
                return Some(chars[i]);
            }
            i += 1;
        }
        None
    }

    fn write_indent(out: &mut String, indent: usize, line_start: &mut bool) {
        if *line_start {
            out.push_str(&"    ".repeat(indent));
            *line_start = false;
        }
    }

    fn trim_trailing_space(out: &mut String) {
        while out.ends_with(' ') || out.ends_with('\t') {
            out.pop();
        }
    }

    fn newline(out: &mut String, line_start: &mut bool) {
        trim_trailing_space(out);
        if !out.ends_with('\n') {
            out.push('\n');
        }
        *line_start = true;
    }

    while i < chars.len() {
        let ch = chars[i];
        let next = next_non_space(&chars, i + 1);

        if in_string {
            write_indent(&mut out, indent, &mut line_start);
            out.push(ch);
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }

        match ch {
            '"' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(ch);
                in_string = true;
            }
            '{' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('{');
                brace_depth += 1;
                newline(&mut out, &mut line_start);
                indent += 1;
            }
            '}' => {
                indent = indent.saturating_sub(1);
                brace_depth = brace_depth.saturating_sub(1);
                newline(&mut out, &mut line_start);
                write_indent(&mut out, indent, &mut line_start);
                out.push('}');
                if matches!(next, Some(',') | Some(';')) {
                    i += 1;
                    out.push(chars[i]);
                }
                newline(&mut out, &mut line_start);
            }
            '(' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('(');
                paren_depth += 1;
            }
            ')' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(')');
                paren_depth = paren_depth.saturating_sub(1);
            }
            '[' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('[');
                bracket_depth += 1;
            }
            ']' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(']');
                bracket_depth = bracket_depth.saturating_sub(1);
                if bracket_depth == 0
                    && brace_depth == 0
                    && matches!(next, Some('#' | 'p' | 'i' | 'm'))
                {
                    newline(&mut out, &mut line_start);
                }
            }
            ';' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(';');
                newline(&mut out, &mut line_start);
            }
            ',' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(',');
                if brace_depth > 0 && bracket_depth == 0 {
                    newline(&mut out, &mut line_start);
                } else if !matches!(next, Some(')' | ']' | '}' | ',' | ';')) {
                    out.push(' ');
                }
            }
            '\n' | '\r' | '\t' | ' ' => {
                if !line_start && !out.ends_with(' ') && !out.ends_with('\n') {
                    out.push(' ');
                }
            }
            _ => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(ch);
            }
        }

        i += 1;
    }

    let mut formatted = out
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    while formatted.ends_with("\n\n") {
        formatted.pop();
    }
    formatted
}

pub(crate) fn prelude() -> String {
    render_ts(quote! {
        #![allow(warnings)]
        use vest_lib2::combinators::mapped::spec::*;
        use vest_lib2::combinators::*;
        use vest_lib2::core::exec::input::{InputBuf, InputSlice};
        use vest_lib2::core::exec::parser::*;
        use vest_lib2::core::exec::serializer::*;
        use vest_lib2::core::exec::ParseError;
        use vest_lib2::core::{proof::*, spec::*};
        use vest_lib2::primitives::btcvarint::VarInt;
        use vest_lib2::primitives::leb128::ULeb128;
        use vstd::prelude::*;
    })
}

impl<'a> Analysis<'a> {
    pub(crate) fn direct_alias<'b>(
        &self,
        combinator: &'b Combinator,
    ) -> Option<&'b CombinatorInvocation> {
        match combinator {
            Combinator::Invocation(invocation) => Some(invocation),
            _ => None,
        }
    }

    pub(crate) fn new(defs: &'a [Definition], ctx: &'a GlobalCtx) -> Self {
        let endianness = defs
            .iter()
            .find_map(|def| match def {
                Definition::Endianess(endianness) => Some(*endianness),
                _ => None,
            })
            .unwrap_or(Endianess::Little);

        let mut this = Self {
            defs,
            ctx,
            endianness,
            infos: HashMap::new(),
        };
        for def in defs {
            if let Some(name) = definition_name(def) {
                let names = format_names(name);
                let needs_lifetime = this.definition_needs_lifetime(def);
                let non_tail = this.definition_non_tail(def);
                let non_malleable = this.definition_non_malleable(def);
                this.infos.insert(
                    name.to_string(),
                    FormatInfo {
                        names,
                        needs_lifetime,
                        non_tail,
                        non_malleable,
                    },
                );
            }
        }
        this
    }

    pub(crate) fn info(&self, name: &str) -> &FormatInfo {
        self.infos
            .get(name)
            .unwrap_or_else(|| panic!("missing format info for `{name}`"))
    }

    pub(crate) fn eval_const_length_expr(&self, len: &LengthExpr) -> Option<usize> {
        match len {
            LengthExpr::Const(n) => Some(*n),
            LengthExpr::Dependent(_) => None,
            LengthExpr::SizeOf(name) => self.ctx.static_sizes.get(name).copied(),
            LengthExpr::BinOp { op, left, right } => {
                let left = self.eval_const_length_expr(left)?;
                let right = self.eval_const_length_expr(right)?;
                match op {
                    vestir::ArithOp::Add => left.checked_add(right),
                    vestir::ArithOp::Sub => left.checked_sub(right),
                    vestir::ArithOp::Mul => left.checked_mul(right),
                    vestir::ArithOp::Div => left.checked_div(right),
                }
            }
        }
    }

    pub(crate) fn render_value_type(
        &self,
        combinator: &Combinator,
        mode: TypeMode,
        top_level: bool,
    ) -> TokenStream {
        match combinator {
            Combinator::AndThen(_, rhs) => self.render_value_type(rhs, mode, top_level),
            _ => self.render_inner_type(combinator, mode, top_level),
        }
    }

    pub(crate) fn render_inner_type(
        &self,
        inner: &Combinator,
        mode: TypeMode,
        top_level: bool,
    ) -> TokenStream {
        if let Combinator::Invocation(invocation) = inner {
            return self.invocation_value_type(invocation, mode);
        }

        match self.ctx.resolve_alias(inner) {
            Combinator::ConstraintInt(ConstraintIntCombinator { combinator, .. }) => {
                self.int_type(combinator, mode)
            }
            Combinator::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
                self.invocation_value_type(combinator, mode)
            }
            Combinator::Wrap(WrapCombinator { combinator, .. }) => {
                self.render_value_type(combinator, mode, top_level)
            }
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                let inner_ty = self.render_value_type(combinator, mode, false);
                match mode {
                    TypeMode::Exec => quote! { Vec<#inner_ty> },
                    TypeMode::Spec => quote! { Seq<#inner_ty> },
                }
            }
            Combinator::Array(ArrayCombinator { combinator, len }) => {
                let inner_ty = self.render_value_type(combinator, mode, false);
                match (mode, self.eval_const_length_expr(len)) {
                    (TypeMode::Exec, Some(n)) => {
                        let n = syn_usize(n);
                        quote! { [#inner_ty; #n] }
                    }
                    (TypeMode::Exec, None) => quote! { Vec<#inner_ty> },
                    (TypeMode::Spec, _) => quote! { Seq<#inner_ty> },
                }
            }
            Combinator::Bytes(_) | Combinator::Tail(TailCombinator) => match mode {
                TypeMode::Exec => quote! { &'i [u8] },
                TypeMode::Spec => quote! { Seq<u8> },
            },
            Combinator::Option(OptionCombinator(combinator)) => {
                let inner_ty = self.render_value_type(combinator, mode, false);
                quote! { Option<#inner_ty> }
            }
            Combinator::Invocation(invocation) => self.invocation_value_type(invocation, mode),
            Combinator::AndThen(_, rhs) => self.render_value_type(rhs, mode, top_level),
        }
    }

    pub(crate) fn invocation_value_type(
        &self,
        invocation: &vestir::CombinatorInvocation,
        mode: TypeMode,
    ) -> TokenStream {
        self.nominal_type(&invocation.func, mode)
    }

    pub(crate) fn nominal_type(&self, dsl_name: &str, mode: TypeMode) -> TokenStream {
        let info = self.info(dsl_name);
        let ident = match mode {
            TypeMode::Exec => format_ident!("{}", info.names.exec),
            TypeMode::Spec => format_ident!("{}", info.names.spec),
        };
        if matches!(mode, TypeMode::Exec) && info.needs_lifetime {
            quote! { #ident <'i> }
        } else {
            quote! { #ident }
        }
    }

    pub(crate) fn render_struct_inner_type(
        &self,
        struct_comb: &StructCombinator,
        mode: TypeMode,
    ) -> TokenStream {
        let mut retained = Vec::new();
        for field in &struct_comb.0 {
            match field {
                StructField::Const { combinator, .. } => {
                    retained.push(self.render_const_value_type(combinator, mode));
                }
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    retained.push(self.render_value_type(combinator, mode, true));
                }
            }
        }
        tuple_chain(&retained)
    }

    pub(crate) fn choice_variant_names(&self, choice_comb: &ChoiceCombinator) -> Vec<String> {
        match &choice_comb.choices {
            Choices::Enums(branches) => branches
                .iter()
                .map(|(name, _)| {
                    if name == "_" {
                        "Default".to_string()
                    } else {
                        name.clone()
                    }
                })
                .collect(),
            Choices::Ints(branches) => branches
                .iter()
                .enumerate()
                .map(|(idx, (constraint, _))| {
                    if constraint.is_none() {
                        "Default".to_string()
                    } else {
                        format!("Variant{}", idx + 1)
                    }
                })
                .collect(),
            Choices::Arrays(branches) => branches
                .iter()
                .enumerate()
                .map(|(idx, (array, _))| {
                    if matches!(array, vestir::ConstArray::Wildcard) {
                        "Default".to_string()
                    } else {
                        format!("Variant{}", idx + 1)
                    }
                })
                .collect(),
        }
    }

    pub(crate) fn choice_branch_types(
        &self,
        choice_comb: &ChoiceCombinator,
        mode: TypeMode,
    ) -> Vec<TokenStream> {
        match &choice_comb.choices {
            Choices::Enums(branches) => branches
                .iter()
                .map(|(_, combinator)| self.render_value_type(combinator, mode, true))
                .collect(),
            Choices::Ints(branches) => branches
                .iter()
                .map(|(_, combinator)| self.render_value_type(combinator, mode, true))
                .collect(),
            Choices::Arrays(branches) => branches
                .iter()
                .map(|(_, combinator)| self.render_value_type(combinator, mode, true))
                .collect(),
        }
    }

    pub(crate) fn choice_sum_type(&self, branch_types: &[TokenStream]) -> TokenStream {
        match branch_types {
            [] => quote! { () },
            [only] => only.clone(),
            [first, rest @ ..] => {
                let rest = self.choice_sum_type(rest);
                quote! { Sum<#first, #rest> }
            }
        }
    }

    pub(crate) fn int_type(
        &self,
        combinator: &vestir::IntCombinator,
        mode: TypeMode,
    ) -> TokenStream {
        match mode {
            TypeMode::Exec => self.int_exec_type(combinator),
            TypeMode::Spec => self.int_spec_type(combinator),
        }
    }

    pub(crate) fn int_exec_type(&self, combinator: &vestir::IntCombinator) -> TokenStream {
        match combinator {
            vestir::IntCombinator::Signed(bits) => {
                let ident = format_ident!("i{}", bits);
                quote! { #ident }
            }
            vestir::IntCombinator::Unsigned(24) => quote! { u32 },
            vestir::IntCombinator::Unsigned(bits) => {
                let ident = format_ident!("u{}", bits);
                quote! { #ident }
            }
            vestir::IntCombinator::BtcVarint => quote! { u64 },
            vestir::IntCombinator::ULEB128 => quote! { u64 },
        }
    }

    pub(crate) fn int_spec_type(&self, combinator: &vestir::IntCombinator) -> TokenStream {
        self.int_exec_type(combinator)
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
            ConstCombinator::ConstInt(int_comb) => self.int_type(&int_comb.combinator, mode),
            ConstCombinator::ConstEnum(enum_comb) => {
                self.nominal_type(&enum_comb.combinator.func, mode)
            }
            ConstCombinator::ConstCombinatorInvocation(name) => self.nominal_type(name, mode),
        }
    }

    pub(crate) fn wrapper_generics(&self, param_defns: &[ParamDefn]) -> TokenStream {
        if param_defns.iter().any(|p| self.param_needs_lifetime(p)) {
            quote! { <'i> }
        } else {
            quote! {}
        }
    }

    pub(crate) fn wrapper_spec_call_args(&self, param_defns: &[ParamDefn]) -> Vec<TokenStream> {
        param_defns
            .iter()
            .map(|param| match param {
                ParamDefn::Dependent { name, .. } => {
                    let ident = format_ident!("{}", name);
                    quote! { self.#ident.deep_view() }
                }
            })
            .collect()
    }

    pub(crate) fn param_needs_lifetime(&self, param: &ParamDefn) -> bool {
        match param {
            ParamDefn::Dependent { combinator, .. } => self.combinator_needs_lifetime(combinator),
        }
    }

    pub(crate) fn param_defns_for(&self, name: &str) -> &[ParamDefn] {
        match self.definition_for(name) {
            Some(def) => def.param_defns(),
            _ => &[],
        }
    }

    fn definition_for(&self, name: &str) -> Option<&Definition> {
        self.defs
            .iter()
            .find(|def| definition_name(def).is_some_and(|def_name| def_name == name))
    }

    fn choice_branches<'b>(&self, choice: &'b ChoiceCombinator) -> Vec<&'b Combinator> {
        match &choice.choices {
            Choices::Enums(branches) => branches.iter().map(|(_, combinator)| combinator).collect(),
            Choices::Ints(branches) => branches.iter().map(|(_, combinator)| combinator).collect(),
            Choices::Arrays(branches) => {
                branches.iter().map(|(_, combinator)| combinator).collect()
            }
        }
    }

    fn definition_needs_lifetime(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_needs_lifetime(combinator),
            Definition::ChoiceDef { combinator, .. } => self.choice_needs_lifetime(combinator),
            Definition::EnumDef { .. } => false,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_needs_lifetime(combinator)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_needs_lifetime(const_combinator),
            Definition::Endianess(_) => false,
        }
    }

    fn combinator_needs_lifetime(&self, combinator: &Combinator) -> bool {
        match combinator {
            Combinator::AndThen(_, rhs) => self.combinator_needs_lifetime(rhs),
            _ => self.inner_needs_lifetime(combinator),
        }
    }

    fn inner_needs_lifetime(&self, inner: &Combinator) -> bool {
        match self.ctx.resolve_alias(inner) {
            Combinator::ConstraintInt(_) | Combinator::ConstraintEnum(_) => false,
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().any(|c| self.const_needs_lifetime(c))
                    || self.combinator_needs_lifetime(combinator)
                    || post.iter().any(|c| self.const_needs_lifetime(c))
            }
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => true,
            Combinator::Option(OptionCombinator(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).needs_lifetime,
            Combinator::AndThen(_, rhs) => self.combinator_needs_lifetime(rhs),
        }
    }

    fn struct_needs_lifetime(&self, struct_comb: &StructCombinator) -> bool {
        struct_comb.0.iter().any(|field| match field {
            StructField::Const { combinator, .. } => self.const_needs_lifetime(combinator),
            StructField::Dependent { combinator, .. }
            | StructField::Ordinary { combinator, .. } => {
                self.combinator_needs_lifetime(combinator)
            }
        })
    }

    fn choice_needs_lifetime(&self, choice: &ChoiceCombinator) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .any(|branch| self.combinator_needs_lifetime(branch))
    }

    fn const_needs_lifetime(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_) => false,
            ConstCombinator::ConstInt(_) | ConstCombinator::ConstEnum(_) => false,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).needs_lifetime,
        }
    }

    fn definition_non_tail(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_non_tail_at(combinator, true),
            Definition::ChoiceDef { combinator, .. } => self.choice_non_tail_at(combinator, true),
            Definition::EnumDef { .. } => true,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_non_tail_at(combinator, true)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_non_tail(const_combinator),
            Definition::Endianess(_) => true,
        }
    }

    fn combinator_non_tail(&self, combinator: &Combinator) -> bool {
        self.combinator_non_tail_at(combinator, false)
    }

    fn combinator_non_tail_at(&self, combinator: &Combinator, tail_position: bool) -> bool {
        match combinator {
            Combinator::AndThen(lhs, rhs) => {
                return match self.ctx.resolve_alias(lhs) {
                    Combinator::Bytes(_) => true,
                    _ => self.combinator_non_tail_at(rhs, tail_position),
                };
            }
            _ => {}
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::Tail(_) => false,
            Combinator::ConstraintInt(_) | Combinator::ConstraintEnum(_) | Combinator::Bytes(_) => {
                true
            }
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_tail(c))
                    && self.combinator_non_tail_at(combinator, tail_position)
                    && post.iter().all(|c| self.const_non_tail(c))
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_tail(combinator)
            }
            Combinator::Option(OptionCombinator(combinator))
            | Combinator::Vec(VecCombinator::Vec(combinator)) => {
                !tail_position && self.combinator_non_tail(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).non_tail,
            Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn struct_non_tail_at(&self, struct_comb: &StructCombinator, tail_position: bool) -> bool {
        let mut at_tail = tail_position;
        for field in struct_comb.0.iter().rev() {
            let ok = match field {
                StructField::Const { combinator, .. } => self.const_non_tail(combinator),
                StructField::Dependent { combinator, .. }
                | StructField::Ordinary { combinator, .. } => {
                    self.combinator_non_tail_at(combinator, at_tail)
                }
            };
            if !ok {
                return false;
            }
            at_tail = false;
        }
        true
    }

    fn choice_non_tail_at(&self, choice: &ChoiceCombinator, tail_position: bool) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .all(|branch| self.combinator_non_tail_at(branch, tail_position))
    }

    fn const_non_tail(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_)
            | ConstCombinator::ConstInt(_)
            | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).non_tail,
        }
    }

    fn definition_non_malleable(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_non_malleable(combinator),
            Definition::ChoiceDef { combinator, .. } => self.choice_non_malleable(combinator),
            Definition::EnumDef { .. } => true,
            Definition::CombinatorDef { combinator, .. } => {
                self.combinator_non_malleable(combinator)
            }
            Definition::ConstCombinatorDef {
                const_combinator, ..
            } => self.const_non_malleable(const_combinator),
            Definition::Endianess(_) => true,
        }
    }

    fn combinator_non_malleable(&self, combinator: &Combinator) -> bool {
        match combinator {
            Combinator::AndThen(_, rhs) => return self.combinator_non_malleable(rhs),
            _ => {}
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) | Combinator::ConstraintEnum(_) | Combinator::Bytes(_) => {
                true
            }
            Combinator::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_malleable(c))
                    && self.combinator_non_malleable(combinator)
                    && post.iter().all(|c| self.const_non_malleable(c))
            }
            Combinator::Tail(_) => true,
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Option(OptionCombinator(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            Combinator::Invocation(invocation) => self.info(&invocation.func).non_malleable,
            Combinator::AndThen(_, _) => unreachable!(),
        }
    }

    fn struct_non_malleable(&self, struct_comb: &StructCombinator) -> bool {
        struct_comb.0.iter().all(|field| match field {
            StructField::Const { combinator, .. } => self.const_non_malleable(combinator),
            StructField::Dependent { combinator, .. }
            | StructField::Ordinary { combinator, .. } => self.combinator_non_malleable(combinator),
        })
    }

    fn choice_non_malleable(&self, choice: &ChoiceCombinator) -> bool {
        self.choice_branches(choice)
            .into_iter()
            .all(|branch| self.combinator_non_malleable(branch))
    }

    fn const_non_malleable(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_)
            | ConstCombinator::ConstInt(_)
            | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.info(name).non_malleable,
        }
    }
}

pub(crate) fn definition_name(def: &Definition) -> Option<&str> {
    match def {
        Definition::StructDef { name, .. }
        | Definition::ChoiceDef { name, .. }
        | Definition::EnumDef { name, .. }
        | Definition::CombinatorDef { name, .. }
        | Definition::ConstCombinatorDef { name, .. } => Some(name),
        Definition::Endianess(_) => None,
    }
}

pub(crate) fn format_names(name: &str) -> FormatNames {
    let camel = name.to_upper_camel_case();
    FormatNames {
        dsl: name.to_string(),
        exec: camel.clone(),
        spec: format!("{camel}Spec"),
        inner: format!("{camel}Inner"),
        fmt: format!("{camel}Fmt"),
        fmt_fn: format!("{name}_fmt"),
    }
}

pub(crate) fn tuple_chain(types: &[TokenStream]) -> TokenStream {
    match types {
        [] => quote! { () },
        [only] => only.clone(),
        [first, rest @ ..] => {
            let rest = tuple_chain(rest);
            quote! { (#first, #rest) }
        }
    }
}

pub(crate) fn type_needs_exec_lifetime(ty: &TokenStream) -> bool {
    ty.to_string().contains("'i")
}

pub(crate) fn syn_usize(n: usize) -> TokenStream {
    let lit = proc_macro2::Literal::usize_unsuffixed(n);
    quote! { #lit }
}

pub(crate) fn int_literal(value: i128, combinator: &vestir::IntCombinator) -> TokenStream {
    match combinator {
        vestir::IntCombinator::Unsigned(8) => {
            let lit = proc_macro2::Literal::u8_unsuffixed(value as u8);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(16) => {
            let lit = proc_macro2::Literal::u16_unsuffixed(value as u16);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(24) | vestir::IntCombinator::Unsigned(32) => {
            let lit = proc_macro2::Literal::u32_unsuffixed(value as u32);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(64)
        | vestir::IntCombinator::BtcVarint
        | vestir::IntCombinator::ULEB128 => {
            let lit = proc_macro2::Literal::u64_unsuffixed(value as u64);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(8) => {
            let lit = proc_macro2::Literal::i8_unsuffixed(value as i8);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(16) => {
            let lit = proc_macro2::Literal::i16_unsuffixed(value as i16);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(32) => {
            let lit = proc_macro2::Literal::i32_unsuffixed(value as i32);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(64) => {
            let lit = proc_macro2::Literal::i64_unsuffixed(value as i64);
            quote! { #lit }
        }
        other => panic!("unsupported integer literal combinator: {:?}", other),
    }
}
