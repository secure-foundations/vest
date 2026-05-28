use crate::vestir::{
    self, ArrayCombinator, ChoiceCombinator, Choices, Combinator, CombinatorInner,
    CombinatorInvocation, ConstArray, ConstCombinator, ConstraintEnumCombinator,
    ConstraintIntCombinator, Definition, Endianess, EnumCombinator, GlobalCtx, LengthExpr,
    OptionCombinator, ParamDefn, StructCombinator, StructField, TailCombinator, VecCombinator,
    WrapCombinator,
};
use heck::ToUpperCamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};

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
                if bracket_depth == 0 && brace_depth == 0 && matches!(next, Some('#' | 'p' | 'i' | 'm')) {
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
        if combinator.and_then.is_none() {
            if let CombinatorInner::Invocation(invocation) = &combinator.inner {
                return Some(invocation);
            }
        }
        None
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
        if let Some(and_then) = &combinator.and_then {
            return self.render_value_type(and_then, mode, top_level);
        }
        self.render_inner_type(&combinator.inner, mode, top_level)
    }

    pub(crate) fn render_inner_type(
        &self,
        inner: &CombinatorInner,
        mode: TypeMode,
        top_level: bool,
    ) -> TokenStream {
        if let CombinatorInner::Invocation(invocation) = inner {
            return self.invocation_value_type(invocation, mode);
        }

        match self.ctx.resolve_alias(inner) {
            CombinatorInner::ConstraintInt(ConstraintIntCombinator { combinator, .. }) => {
                self.int_type(combinator, mode)
            }
            CombinatorInner::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
                self.invocation_value_type(combinator, mode)
            }
            CombinatorInner::Struct(struct_comb) => {
                if top_level {
                    if let Some(name) = self.definition_name_for_inner_opt(inner) {
                        self.nominal_type(&name, mode)
                    } else {
                        self.render_struct_inner_type(struct_comb, mode)
                    }
                } else {
                    self.render_struct_inner_type(struct_comb, mode)
                }
            }
            CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
                self.render_value_type(combinator, mode, top_level)
            }
            CombinatorInner::Enum(enum_comb) => {
                if top_level {
                    if let Some(name) = self.definition_name_for_inner_opt(inner) {
                        self.nominal_type(&name, mode)
                    } else {
                        let branch_types = match enum_comb {
                            EnumCombinator::Exhaustive { enums, inferred }
                            | EnumCombinator::NonExhaustive { enums, inferred } => {
                                let mut tys = enums
                                    .iter()
                                    .map(|_| self.int_type(inferred, mode))
                                    .collect::<Vec<_>>();
                                if matches!(enum_comb, EnumCombinator::NonExhaustive { .. }) {
                                    tys.push(self.int_type(inferred, mode));
                                }
                                tys
                            }
                        };
                        self.choice_sum_type(&branch_types)
                    }
                } else {
                    let branch_types = match enum_comb {
                        EnumCombinator::Exhaustive { enums, inferred }
                        | EnumCombinator::NonExhaustive { enums, inferred } => {
                            let mut tys = enums
                                .iter()
                                .map(|_| self.int_type(inferred, mode))
                                .collect::<Vec<_>>();
                            if matches!(enum_comb, EnumCombinator::NonExhaustive { .. }) {
                                tys.push(self.int_type(inferred, mode));
                            }
                            tys
                        }
                    };
                    self.choice_sum_type(&branch_types)
                }
            }
            CombinatorInner::Choice(choice_comb) => {
                if top_level {
                    if let Some(name) = self.definition_name_for_inner_opt(inner) {
                        self.nominal_type(&name, mode)
                    } else {
                        self.choice_sum_type(&self.choice_branch_types(choice_comb, mode))
                    }
                } else {
                    self.choice_sum_type(&self.choice_branch_types(choice_comb, mode))
                }
            }
            CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
                let inner_ty = self.render_value_type(combinator, mode, false);
                match mode {
                    TypeMode::Exec => quote! { Vec<#inner_ty> },
                    TypeMode::Spec => quote! { Seq<#inner_ty> },
                }
            }
            CombinatorInner::Array(ArrayCombinator { combinator, len }) => {
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
            CombinatorInner::Bytes(_) | CombinatorInner::Tail(TailCombinator) => match mode {
                TypeMode::Exec => quote! { &'i [u8] },
                TypeMode::Spec => quote! { Seq<u8> },
            },
            CombinatorInner::Option(OptionCombinator(combinator)) => {
                let inner_ty = self.render_value_type(combinator, mode, false);
                quote! { Option<#inner_ty> }
            }
            CombinatorInner::Invocation(invocation) => self.invocation_value_type(invocation, mode),
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

    pub(crate) fn definition_name_for_inner_opt(&self, inner: &CombinatorInner) -> Option<String> {
        match inner {
            CombinatorInner::Invocation(invocation) => Some(invocation.func.clone()),
            _ => self.defs.iter().find_map(|def| match def {
                Definition::Combinator {
                    name, combinator, ..
                } if std::ptr::eq(&combinator.inner, inner) => Some(name.clone()),
                _ => None,
            }),
        }
    }

    pub(crate) fn definition_name_for_inner(&self, inner: &CombinatorInner) -> String {
        self.definition_name_for_inner_opt(inner)
            .unwrap_or_else(|| "Anonymous".to_string())
    }

    pub(crate) fn param_needs_lifetime(&self, param: &ParamDefn) -> bool {
        match param {
            ParamDefn::Dependent { combinator, .. } => self.inner_needs_lifetime(combinator),
        }
    }

    pub(crate) fn param_defns_for(&self, name: &str) -> &[ParamDefn] {
        match self.definition_for(name) {
            Some(Definition::Combinator { param_defns, .. }) => param_defns.as_slice(),
            _ => &[],
        }
    }

    fn definition_for(&self, name: &str) -> Option<&Definition> {
        self.defs.iter().find(|def| matches!(
            def,
            Definition::Combinator { name: def_name, .. } | Definition::ConstCombinator { name: def_name, .. }
                if def_name == name
        ))
    }

    pub(crate) fn repeated_u8_array_ineq_facts(
        &self,
        combinator: &Combinator,
    ) -> Vec<(u8, u8, usize)> {
        let mut facts = HashSet::new();
        let mut visited = HashSet::new();
        self.collect_repeated_u8_array_ineq_facts(combinator, &mut facts, &mut visited);
        let mut facts = facts.into_iter().collect::<Vec<_>>();
        facts.sort_unstable();
        facts
    }

    fn collect_repeated_u8_array_ineq_facts(
        &self,
        combinator: &Combinator,
        facts: &mut HashSet<(u8, u8, usize)>,
        visited: &mut HashSet<String>,
    ) {
        self.collect_repeated_u8_array_ineq_facts_inner(&combinator.inner, facts, visited);
        if let Some(and_then) = &combinator.and_then {
            self.collect_repeated_u8_array_ineq_facts(and_then, facts, visited);
        }
    }

    fn collect_repeated_u8_array_ineq_facts_inner(
        &self,
        inner: &CombinatorInner,
        facts: &mut HashSet<(u8, u8, usize)>,
        visited: &mut HashSet<String>,
    ) {
        match inner {
            CombinatorInner::Choice(choice) => {
                self.collect_choice_repeated_u8_array_ineq_facts(choice, facts);
                for branch in self.choice_branches(choice) {
                    self.collect_repeated_u8_array_ineq_facts(branch, facts, visited);
                }
            }
            CombinatorInner::Struct(StructCombinator(fields)) => {
                for field in fields {
                    match field {
                        StructField::Dependent { combinator, .. }
                        | StructField::Ordinary { combinator, .. } => {
                            self.collect_repeated_u8_array_ineq_facts(combinator, facts, visited);
                        }
                        StructField::Const { .. } => {}
                    }
                }
            }
            CombinatorInner::Wrap(WrapCombinator { combinator, .. }) => {
                self.collect_repeated_u8_array_ineq_facts(combinator, facts, visited);
            }
            CombinatorInner::Vec(VecCombinator::Vec(combinator))
            | CombinatorInner::Option(OptionCombinator(combinator)) => {
                self.collect_repeated_u8_array_ineq_facts(combinator, facts, visited);
            }
            CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
                self.collect_repeated_u8_array_ineq_facts(combinator, facts, visited);
            }
            CombinatorInner::Invocation(invocation) => {
                if visited.insert(invocation.func.clone()) {
                    if let Some(Definition::Combinator { combinator, .. }) =
                        self.definition_for(&invocation.func)
                    {
                        self.collect_repeated_u8_array_ineq_facts(combinator, facts, visited);
                    }
                }
            }
            CombinatorInner::ConstraintInt(_)
            | CombinatorInner::ConstraintEnum(_)
            | CombinatorInner::Enum(_)
            | CombinatorInner::Bytes(_)
            | CombinatorInner::Tail(_) => {}
        }
    }

    fn collect_choice_repeated_u8_array_ineq_facts(
        &self,
        choice: &ChoiceCombinator,
        facts: &mut HashSet<(u8, u8, usize)>,
    ) {
        let Choices::Arrays(branches) = &choice.choices else {
            return;
        };
        let repeats = branches
            .iter()
            .filter_map(|(array, _)| match array {
                ConstArray::Repeat(value, len)
                    if (0..=u8::MAX as i128).contains(value) && *len > 0 =>
                {
                    Some((*value as u8, *len))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        for i in 0..repeats.len() {
            for j in i + 1..repeats.len() {
                let (lhs, len_lhs) = repeats[i];
                let (rhs, len_rhs) = repeats[j];
                if len_lhs == len_rhs && lhs != rhs {
                    let fact = if lhs < rhs {
                        (lhs, rhs, len_lhs)
                    } else {
                        (rhs, lhs, len_lhs)
                    };
                    facts.insert(fact);
                }
            }
        }
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
            Definition::Combinator { combinator, .. } => self.combinator_needs_lifetime(combinator),
            Definition::ConstCombinator {
                const_combinator, ..
            } => self.const_needs_lifetime(const_combinator),
            Definition::Endianess(_) => false,
        }
    }

    fn combinator_needs_lifetime(&self, combinator: &Combinator) -> bool {
        if let Some(and_then) = &combinator.and_then {
            return self.combinator_needs_lifetime(and_then);
        }
        self.inner_needs_lifetime(&combinator.inner)
    }

    fn inner_needs_lifetime(&self, inner: &CombinatorInner) -> bool {
        match self.ctx.resolve_alias(inner) {
            CombinatorInner::ConstraintInt(_)
            | CombinatorInner::ConstraintEnum(_)
            | CombinatorInner::Enum(_) => false,
            CombinatorInner::Struct(StructCombinator(fields)) => {
                fields.iter().any(|field| match field {
                    StructField::Const { combinator, .. } => self.const_needs_lifetime(combinator),
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.combinator_needs_lifetime(combinator)
                    }
                })
            }
            CombinatorInner::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().any(|c| self.const_needs_lifetime(c))
                    || self.combinator_needs_lifetime(combinator)
                    || post.iter().any(|c| self.const_needs_lifetime(c))
            }
            CombinatorInner::Choice(choice) => match &choice.choices {
                Choices::Enums(branches) => branches
                    .iter()
                    .any(|(_, combinator)| self.combinator_needs_lifetime(combinator)),
                Choices::Ints(branches) => branches
                    .iter()
                    .any(|(_, combinator)| self.combinator_needs_lifetime(combinator)),
                Choices::Arrays(branches) => branches
                    .iter()
                    .any(|(_, combinator)| self.combinator_needs_lifetime(combinator)),
            },
            CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_needs_lifetime(combinator)
            }
            CombinatorInner::Bytes(_) | CombinatorInner::Tail(_) => true,
            CombinatorInner::Option(OptionCombinator(combinator)) => {
                self.combinator_needs_lifetime(combinator)
            }
            CombinatorInner::Invocation(invocation) => self.info(&invocation.func).needs_lifetime,
        }
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
            Definition::Combinator { combinator, .. } => {
                self.combinator_non_tail_at(combinator, true)
            }
            Definition::ConstCombinator {
                const_combinator, ..
            } => self.const_non_tail(const_combinator),
            Definition::Endianess(_) => true,
        }
    }

    fn combinator_non_tail(&self, combinator: &Combinator) -> bool {
        self.combinator_non_tail_at(combinator, false)
    }

    fn combinator_non_tail_at(&self, combinator: &Combinator, tail_position: bool) -> bool {
        if let Some(and_then) = &combinator.and_then {
            return match self.ctx.resolve_alias(&combinator.inner) {
                // `bytes >>= fmt` lowers to `ExactLen(len, fmt)`, which is non-tail even when
                // the inner format itself is tail-like because the exact-length wrapper "boxes"
                // the inner parser/serializer from the outside context.
                CombinatorInner::Bytes(_) => true,
                _ => self.combinator_non_tail_at(and_then, tail_position),
            };
        }
        match self.ctx.resolve_alias(&combinator.inner) {
            CombinatorInner::Tail(_) => false,
            CombinatorInner::ConstraintInt(_)
            | CombinatorInner::ConstraintEnum(_)
            | CombinatorInner::Enum(_)
            | CombinatorInner::Bytes(_) => true,
            CombinatorInner::Struct(StructCombinator(fields)) => {
                let mut at_tail = tail_position;
                for field in fields.iter().rev() {
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
            CombinatorInner::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_tail(c))
                    && self.combinator_non_tail_at(combinator, tail_position)
                    && post.iter().all(|c| self.const_non_tail(c))
            }
            CombinatorInner::Choice(choice) => match &choice.choices {
                Choices::Enums(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_tail_at(combinator, tail_position)),
                Choices::Ints(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_tail_at(combinator, tail_position)),
                Choices::Arrays(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_tail_at(combinator, tail_position)),
            },
            CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_tail(combinator)
            }
            CombinatorInner::Option(OptionCombinator(combinator))
            | CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
                !tail_position && self.combinator_non_tail(combinator)
            }
            CombinatorInner::Invocation(invocation) => self.info(&invocation.func).non_tail,
        }
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
            Definition::Combinator { combinator, .. } => self.combinator_non_malleable(combinator),
            Definition::ConstCombinator {
                const_combinator, ..
            } => self.const_non_malleable(const_combinator),
            Definition::Endianess(_) => true,
        }
    }

    fn combinator_non_malleable(&self, combinator: &Combinator) -> bool {
        if let Some(and_then) = &combinator.and_then {
            return self.combinator_non_malleable(and_then);
        }
        match self.ctx.resolve_alias(&combinator.inner) {
            CombinatorInner::ConstraintInt(_)
            | CombinatorInner::ConstraintEnum(_)
            | CombinatorInner::Enum(_)
            | CombinatorInner::Bytes(_) => true,
            CombinatorInner::Struct(StructCombinator(fields)) => {
                fields.iter().all(|field| match field {
                    StructField::Const { combinator, .. } => self.const_non_malleable(combinator),
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.combinator_non_malleable(combinator)
                    }
                })
            }
            CombinatorInner::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            }) => {
                prior.iter().all(|c| self.const_non_malleable(c))
                    && self.combinator_non_malleable(combinator)
                    && post.iter().all(|c| self.const_non_malleable(c))
            }
            CombinatorInner::Choice(choice) => match &choice.choices {
                Choices::Enums(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_malleable(combinator)),
                Choices::Ints(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_malleable(combinator)),
                Choices::Arrays(branches) => branches
                    .iter()
                    .all(|(_, combinator)| self.combinator_non_malleable(combinator)),
            },
            CombinatorInner::Tail(_) => true,
            CombinatorInner::Vec(VecCombinator::Vec(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            CombinatorInner::Array(ArrayCombinator { combinator, .. }) => {
                self.combinator_non_malleable(combinator)
            }
            CombinatorInner::Option(OptionCombinator(combinator)) => {
                self.combinator_non_malleable(combinator)
            }
            CombinatorInner::Invocation(invocation) => self.info(&invocation.func).non_malleable,
        }
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
        Definition::Combinator { name, .. } => Some(name),
        Definition::ConstCombinator { name, .. } => Some(name),
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
