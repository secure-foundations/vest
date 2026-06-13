use crate::vestir::{
    self, ArrayCombinator, ChoiceCombinator, ChoicePattern, Combinator, CombinatorInvocation,
    ConstArray, ConstCombinator, ConstraintElem, ConstraintEnumCombinator, ConstraintIntCombinator,
    Definition, Endianess, EnumCombinator, GlobalCtx, IntCombinator, LengthExpr, OptionCombinator,
    ParamDefn, StructCombinator, StructField, TailCombinator, VecCombinator, WrapCombinator,
};
use heck::ToUpperCamelCase;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct FormatNames {
    pub(crate) dsl: String,
    pub(crate) exec: String,
    pub(crate) spec: String,
    pub(crate) inner: String,
    pub(crate) fmt: String,
}

impl FormatNames {
    pub(crate) fn spec_ctor_ident(&self) -> proc_macro2::Ident {
        format_ident!("spec_inner")
    }

    pub(crate) fn wrapper_ctor_ident(&self) -> proc_macro2::Ident {
        format_ident!("spec")
    }

    pub(crate) fn wrapper_field_ident(name: &str) -> proc_macro2::Ident {
        format_ident!("{}", name)
    }

    pub(crate) fn wrapper_accessor_ident(name: &str) -> proc_macro2::Ident {
        format_ident!("{}_spec", name)
    }
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
    pub(crate) endianness: Endianess,
    pub(crate) infos: HashMap<String, FormatInfo>,
}

#[derive(Debug, Clone)]
pub(crate) struct BitsFieldLayout {
    pub(crate) label: String,
    pub(crate) logical_width: u8,
    pub(crate) carrier_ty: vestir::IntCombinator,
    pub(crate) mask: u64,
    pub(crate) shift: u8,
    pub(crate) is_enum: bool,
    pub(crate) is_closed_enum: bool,
    pub(crate) enum_name: Option<String>,
}

#[derive(Debug, Clone)]
pub(crate) struct BitsLayout {
    pub(crate) repr_int: vestir::IntCombinator,
    pub(crate) fields: Vec<BitsFieldLayout>,
}

pub(crate) fn bits_tuple_type_tokens(tys: &[TokenStream]) -> TokenStream {
    match tys {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#tys),*) },
    }
}

pub(crate) fn bits_tuple_pattern_tokens(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#idents),*) },
    }
}

pub(crate) fn bits_tuple_expr_tokens(exprs: &[TokenStream]) -> TokenStream {
    match exprs {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#exprs),*) },
    }
}

pub(crate) fn bits_tuple_expr_from_idents(idents: &[proc_macro2::Ident]) -> TokenStream {
    match idents {
        [] => quote! { () },
        [only] => quote! { #only },
        _ => quote! { (#(#idents),*) },
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeMode {
    Exec,
    Spec,
}

impl<'a> Analysis<'a> {
    pub(crate) fn int_is_byte_aligned(&self, int: &IntCombinator) -> bool {
        match int {
            IntCombinator::Signed(bits) | IntCombinator::Unsigned(bits) => bits % 8 == 0,
            IntCombinator::BtcVarint | IntCombinator::ULEB128 => true,
        }
    }

    pub(crate) fn enum_is_bit_sized(&self, enum_comb: &vestir::EnumCombinator) -> bool {
        let inferred = match enum_comb {
            vestir::EnumCombinator::Exhaustive { inferred, .. }
            | vestir::EnumCombinator::NonExhaustive { inferred, .. } => inferred,
        };
        !self.int_is_byte_aligned(inferred)
    }

    pub(crate) fn direct_alias<'b>(
        &self,
        combinator: &'b Combinator,
    ) -> Option<&'b CombinatorInvocation> {
        match combinator {
            Combinator::Invocation(invocation) => Some(invocation),
            _ => None,
        }
    }

    pub(crate) fn enum_value_literals(&self, enum_name: &str) -> Vec<TokenStream> {
        let def = self
            .defs
            .iter()
            .find(|d| d.name() == Some(enum_name))
            .unwrap_or_else(|| panic!("unknown enum {}", enum_name));
        match def {
            Definition::EnumDef { combinator, .. } => {
                let (enums, inferred) = match combinator {
                    EnumCombinator::Exhaustive { enums, inferred }
                    | EnumCombinator::NonExhaustive { enums, inferred } => {
                        (enums.as_slice(), inferred)
                    }
                };
                enums
                    .iter()
                    .map(|variant| int_literal(variant.value, inferred))
                    .collect()
            }
            _ => panic!("{} is not an enum", enum_name),
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
        match &len.kind {
            vestir::LengthExprKind::Const(n) => Some(*n),
            vestir::LengthExprKind::Dependent(_) => None,
            vestir::LengthExprKind::SizeOf(name) => self.ctx.static_sizes.get(name).copied(),
            vestir::LengthExprKind::BinOp { op, left, right } => {
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

    pub(crate) fn bits_layout(&self, bits_comb: &vestir::BitsCombinator) -> BitsLayout {
        let mut fields = Vec::new();
        let mut total_width = 0u16;
        let mut field_widths = Vec::new();
        for field in &bits_comb.0 {
            let w = self.bits_field_width(field);
            field_widths.push(w);
            total_width += w as u16;
        }
        let repr_width = match total_width {
            8 => 8,
            16 => 16,
            24 => 24,
            32 => 32,
            64 => 64,
            _ => panic!("unsupported bitfield total width {}", total_width),
        };
        let repr_int = vestir::IntCombinator::Unsigned(repr_width);
        let mut current_shift = repr_width;
        for (idx, field) in bits_comb.0.iter().enumerate() {
            let label = match field {
                vestir::BitField::Dependent { label, .. }
                | vestir::BitField::Ordinary { label, .. } => label.clone(),
            };
            let logical_width = field_widths[idx];
            current_shift -= logical_width;
            let shift = current_shift;
            let mask = if logical_width == 64 {
                u64::MAX
            } else {
                (1u64 << logical_width) - 1
            };
            let (is_enum, is_closed_enum, enum_name) = match field.combinator() {
                vestir::BitFieldCombinator::Enum(inv) => {
                    let is_closed = matches!(
                        self.defs
                            .iter()
                            .find(|d| d.name() == Some(inv.func.as_str())),
                        Some(vestir::Definition::EnumDef {
                            combinator: EnumCombinator::Exhaustive { .. },
                            ..
                        })
                    );
                    (true, is_closed, Some(inv.func.clone()))
                }
                _ => (false, false, None),
            };
            let carrier_ty = match field.combinator() {
                vestir::BitFieldCombinator::UInt(_) => {
                    vestir::IntCombinator::Unsigned(logical_width)
                }
                vestir::BitFieldCombinator::Enum(inv) => {
                    let def = self
                        .defs
                        .iter()
                        .find(|d| d.name() == Some(inv.func.as_str()))
                        .unwrap();
                    match def {
                        vestir::Definition::EnumDef { combinator, .. } => match combinator {
                            EnumCombinator::Exhaustive { inferred, .. }
                            | EnumCombinator::NonExhaustive { inferred, .. } => inferred.clone(),
                        },
                        _ => panic!("expected enum def"),
                    }
                }
            };
            fields.push(BitsFieldLayout {
                label,
                logical_width,
                carrier_ty,
                mask,
                shift,
                is_enum,
                is_closed_enum,
                enum_name,
            });
        }
        BitsLayout { repr_int, fields }
    }

    pub(crate) fn bits_field_width(&self, field: &vestir::BitField) -> u8 {
        match field.combinator() {
            vestir::BitFieldCombinator::UInt(c) => match c.combinator {
                vestir::IntCombinator::Unsigned(bits) => bits,
                _ => panic!("invalid bitfield integer {:?}", c.combinator),
            },
            vestir::BitFieldCombinator::Enum(inv) => {
                let def = self
                    .defs
                    .iter()
                    .find(|d| d.name() == Some(inv.func.as_str()))
                    .unwrap_or_else(|| panic!("unknown bitfield enum {}", inv.func));
                match def {
                    vestir::Definition::EnumDef { combinator, .. } => match combinator {
                        EnumCombinator::Exhaustive { inferred, .. }
                        | EnumCombinator::NonExhaustive { inferred, .. } => match inferred {
                            vestir::IntCombinator::Unsigned(bits) => *bits,
                            _ => panic!("bitfield enum must be unsigned"),
                        },
                    },
                    _ => panic!("bitfield member {} is not an enum", inv.func),
                }
            }
        }
    }

    pub(crate) fn render_value_type(&self, combinator: &Combinator, mode: TypeMode) -> TokenStream {
        if let Combinator::Invocation(invocation) = combinator {
            return self.render_nominal_type(&invocation.func, mode);
        }

        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(ConstraintIntCombinator { combinator, .. }) => {
                self.render_int_type(combinator)
            }
            Combinator::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
                self.render_nominal_type(&combinator.func, mode)
            }
            Combinator::Wrap(WrapCombinator { combinator, .. }) => {
                self.render_value_type(combinator, mode)
            }
            Combinator::Vec(VecCombinator::Vec(combinator)) => {
                let inner_ty = self.render_value_type(combinator, mode);
                match mode {
                    TypeMode::Exec => quote! { Vec<#inner_ty> },
                    TypeMode::Spec => quote! { Seq<#inner_ty> },
                }
            }
            Combinator::Array(ArrayCombinator { combinator, len }) => {
                let inner_ty = self.render_value_type(combinator, mode);
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
                let inner_ty = self.render_value_type(combinator, mode);
                quote! { Option<#inner_ty> }
            }
            Combinator::Invocation(invocation) => self.render_nominal_type(&invocation.func, mode),
            Combinator::AndThen(_, rhs) => self.render_value_type(rhs, mode),
        }
    }

    pub(crate) fn render_nominal_type(&self, dsl_name: &str, mode: TypeMode) -> TokenStream {
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
    pub(crate) fn render_choice_sum_type(&self, branch_types: &[TokenStream]) -> TokenStream {
        match branch_types {
            [] => quote! { () },
            [only] => only.clone(),
            [first, rest @ ..] => {
                let rest = self.render_choice_sum_type(rest);
                quote! { Sum<#first, #rest> }
            }
        }
    }

    pub(crate) fn render_int_type(&self, combinator: &vestir::IntCombinator) -> TokenStream {
        match combinator {
            vestir::IntCombinator::Signed(bits) => {
                let carrier: u32 = match bits {
                    1..=8 => 8,
                    9..=16 => 16,
                    17..=32 => 32,
                    33..=64 => 64,
                    _ => panic!("unsupported signed integer width {}", bits),
                };
                let ident = format_ident!("i{}", carrier);
                quote! { #ident }
            }
            vestir::IntCombinator::Unsigned(bits) => {
                let carrier: u32 = match bits {
                    1..=8 => 8,
                    9..=16 => 16,
                    17..=32 => 32,
                    33..=64 => 64,
                    _ => panic!("unsupported unsigned integer width {}", bits),
                };
                let ident = format_ident!("u{}", carrier);
                quote! { #ident }
            }
            vestir::IntCombinator::BtcVarint => quote! { u64 },
            vestir::IntCombinator::ULEB128 => quote! { u64 },
        }
    }

    pub(crate) fn render_int_combinator_ty(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt<true> },
            IntCombinator::ULEB128 => quote! { ULeb128<true, 10> },
            other => panic!(
                "unsupported integer combinator in spec emitter: {:?}",
                other
            ),
        }
    }

    pub(crate) fn render_int_combinator_expr(&self, combinator: &IntCombinator) -> TokenStream {
        match combinator {
            IntCombinator::Unsigned(8) => quote! { U8 },
            IntCombinator::Unsigned(16) => match self.endianness {
                vestir::Endianess::Little => quote! { U16Le },
                vestir::Endianess::Big => quote! { U16Be },
            },
            IntCombinator::Unsigned(24) => match self.endianness {
                vestir::Endianess::Little => quote! { U24Le },
                vestir::Endianess::Big => quote! { U24Be },
            },
            IntCombinator::Unsigned(32) => match self.endianness {
                vestir::Endianess::Little => quote! { U32Le },
                vestir::Endianess::Big => quote! { U32Be },
            },
            IntCombinator::Unsigned(64) => match self.endianness {
                vestir::Endianess::Little => quote! { U64Le },
                vestir::Endianess::Big => quote! { U64Be },
            },
            IntCombinator::BtcVarint => quote! { VarInt::<true> },
            IntCombinator::ULEB128 => quote! { ULeb128::<true, 10> },
            other => panic!(
                "unsupported integer combinator in spec emitter: {:?}",
                other
            ),
        }
    }

    pub(crate) fn render_length_expr_with<F>(
        &self,
        len: &LengthExpr,
        render_dep: &F,
        cast_ty: Option<&TokenStream>,
    ) -> TokenStream
    where
        F: Fn(&str) -> TokenStream,
    {
        match &len.kind {
            vestir::LengthExprKind::Const(n) => {
                let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                quote! { #lit }
            }
            vestir::LengthExprKind::Dependent(name) => render_dep(name),
            vestir::LengthExprKind::SizeOf(name) => {
                if let Some(n) = self.ctx.static_sizes.get(name) {
                    let lit = proc_macro2::Literal::usize_unsuffixed(*n);
                    quote! { #lit }
                } else {
                    let fmt_ident = format_ident!("{}Spec", self.info(name).names.fmt);
                    quote! { <#fmt_ident as StaticByteLen>::static_byte_len() }
                }
            }
            vestir::LengthExprKind::BinOp { op, left, right } => {
                let left = self.render_length_expr_with(left, render_dep, cast_ty);
                let right = self.render_length_expr_with(right, render_dep, cast_ty);
                let expr = match op {
                    vestir::ArithOp::Add => quote! { (#left + #right) },
                    vestir::ArithOp::Sub => quote! { (#left - #right) },
                    vestir::ArithOp::Mul => quote! { (#left * #right) },
                    vestir::ArithOp::Div => quote! { (#left / #right) },
                };
                match cast_ty {
                    Some(ty) => quote! { (#expr as #ty) },
                    None => expr,
                }
            }
        }
    }

    pub(crate) fn render_const_array_expr(
        &self,
        array: &ConstArray,
        mode: TypeMode,
    ) -> TokenStream {
        match array {
            ConstArray::Char(bytes) => {
                let elems = bytes
                    .iter()
                    .map(|b| {
                        let hex_str = match mode {
                            TypeMode::Exec => format!("0x{:02x}", *b),
                            TypeMode::Spec => format!("0x{:02x}u8", *b),
                        };
                        hex_str.parse::<TokenStream>().unwrap()
                    })
                    .collect::<Vec<_>>();
                quote! { [#(#elems),*] }
            }
            ConstArray::Int(values) => {
                let elems = values
                    .iter()
                    .map(|v| {
                        if (0..=u8::MAX as i128).contains(v) {
                            let hex_str = match mode {
                                TypeMode::Exec => format!("0x{:02x}", *v as u8),
                                TypeMode::Spec => format!("0x{:02x}u8", *v as u8),
                            };
                            hex_str.parse::<TokenStream>().unwrap()
                        } else {
                            panic!("integer literal {} is too large to fit in a byte", v);
                        }
                    })
                    .collect::<Vec<_>>();
                quote! { [#(#elems),*] }
            }
            ConstArray::Repeat(value, len) => {
                let value_stream = if (0..=u8::MAX as i128).contains(value) {
                    let hex_str = match mode {
                        TypeMode::Exec => format!("0x{:02x}", *value as u8),
                        TypeMode::Spec => format!("0x{:02x}u8", *value as u8),
                    };
                    hex_str.parse::<TokenStream>().unwrap()
                } else {
                    let hex_str = if *value < 0 {
                        format!("-0x{:x}", value.abs())
                    } else {
                        format!("0x{:x}", *value)
                    };
                    hex_str.parse::<TokenStream>().unwrap()
                };
                let len_stream = syn_usize(*len);
                quote! { [#value_stream; #len_stream] }
            }
        }
    }

    pub(crate) fn render_constraint_elem_pred(
        &self,
        elem: &ConstraintElem,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    pub(crate) fn render_int_constraint(
        &self,
        constraint: &vestir::IntConstraint,
        int_ty: &IntCombinator,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match constraint {
            vestir::IntConstraint::Single(elem) => {
                self.render_constraint_elem_with_ty(elem, int_ty, value)
            }
            vestir::IntConstraint::Set(elems) => {
                let parts = elems
                    .iter()
                    .map(|elem| self.render_constraint_elem_with_ty(elem, int_ty, value.clone()))
                    .collect::<Vec<_>>();
                quote! { #(#parts)||* }
            }
            vestir::IntConstraint::Neg(inner) => {
                let inner = self.render_int_constraint(inner, int_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    fn render_constraint_elem_with_ty(
        &self,
        elem: &ConstraintElem,
        int_ty: &IntCombinator,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = int_literal(*v, int_ty);
                quote! { #value == #lit }
            }
            ConstraintElem::Range { start, end } => {
                let lower = start.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value >= #lit }
                });
                let upper = end.as_ref().map(|v| {
                    let lit = int_literal(*v, int_ty);
                    quote! { #value <= #lit }
                });
                match (lower, upper) {
                    (Some(l), Some(u)) => quote! { #l && #u },
                    (Some(l), None) => l,
                    (None, Some(u)) => u,
                    (None, None) => quote! { true },
                }
            }
        }
    }

    pub(crate) fn render_enum_constraint(
        &self,
        constraint: &vestir::EnumConstraint,
        enum_ty: &proc_macro2::TokenStream,
        value: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        match constraint {
            vestir::EnumConstraint::Single(name) => {
                let variant = format_ident!("{}", name);
                quote! { #value == #enum_ty::#variant }
            }
            vestir::EnumConstraint::Set(names) => {
                let parts = names.iter().map(|name| {
                    let variant = format_ident!("{}", name);
                    quote! { #value == #enum_ty::#variant }
                });
                quote! { #(#parts)||* }
            }
            vestir::EnumConstraint::Neg(inner) => {
                let inner = self.render_enum_constraint(inner, enum_ty, value);
                quote! { !(#inner) }
            }
        }
    }

    pub(crate) fn render_constraint_elem_pat(
        &self,
        elem: &ConstraintElem,
    ) -> proc_macro2::TokenStream {
        match elem {
            ConstraintElem::Single(v) => {
                let lit = proc_macro2::Literal::i128_unsuffixed(*v);
                quote! { #lit }
            }
            ConstraintElem::Range {
                start: Some(start),
                end: Some(end),
            } => {
                let start = proc_macro2::Literal::i128_unsuffixed(*start);
                let end = proc_macro2::Literal::i128_unsuffixed(*end);
                quote! { #start ..= #end }
            }
            _ => {
                let cond = self.render_constraint_elem_pred(elem, quote! { x });
                quote! { x if #cond }
            }
        }
    }

    pub(crate) fn choice_variant_names(&self, choice_comb: &ChoiceCombinator) -> Vec<String> {
        choice_comb
            .choices
            .iter()
            .enumerate()
            .map(|(idx, (pat, _))| match pat {
                ChoicePattern::Enum(name) => name.clone(),
                ChoicePattern::Int(_) => format!("Variant{}", idx + 1),
                ChoicePattern::Array(_) => format!("Variant{}", idx + 1),
                ChoicePattern::Wildcard => "Default".to_string(),
            })
            .collect()
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
                    let accessor = FormatNames::wrapper_accessor_ident(name);
                    quote! { self.#accessor() }
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
        choice
            .choices
            .iter()
            .map(|(_, combinator)| combinator)
            .collect()
    }

    fn definition_needs_lifetime(&self, def: &Definition) -> bool {
        match def {
            Definition::StructDef { combinator, .. } => self.struct_needs_lifetime(combinator),
            Definition::BitsDef { .. } => false,
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
            Definition::BitsDef { .. } => true,
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
            Definition::BitsDef { .. } => true,
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

    pub(crate) fn is_copyable(&self, name: &str) -> bool {
        let def = self.defs.iter().find(|d| d.name() == Some(name));
        match def {
            Some(Definition::StructDef { combinator, .. }) => {
                combinator.0.iter().all(|field| match field {
                    StructField::Const { .. } => true,
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.combinator_is_copyable(combinator)
                    }
                })
            }
            Some(Definition::BitsDef { .. }) => true,
            Some(Definition::ChoiceDef { combinator, .. }) => combinator
                .choices
                .iter()
                .all(|(_, comb)| self.combinator_is_copyable(comb)),
            Some(Definition::EnumDef { .. }) => true,
            Some(Definition::CombinatorDef { combinator, .. }) => {
                self.combinator_is_copyable(combinator)
            }
            Some(Definition::ConstCombinatorDef { .. }) => true,
            _ => true,
        }
    }

    pub(crate) fn combinator_is_copyable(&self, combinator: &Combinator) -> bool {
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) => true,
            Combinator::ConstraintEnum(_) => true,
            Combinator::Wrap(wrap) => self.combinator_is_copyable(&wrap.combinator),
            Combinator::Vec(_) => false,
            Combinator::Array(arr) => {
                self.eval_const_length_expr(&arr.len).is_some()
                    && self.combinator_is_copyable(&arr.combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => true,
            Combinator::Option(OptionCombinator(inner)) => self.combinator_is_copyable(inner),
            Combinator::Invocation(invocation) => self.is_copyable(&invocation.func),
            Combinator::AndThen(_, rhs) => self.combinator_is_copyable(rhs),
        }
    }

    pub(crate) fn is_selfview(&self, name: &str) -> bool {
        let def = self.defs.iter().find(|d| d.name() == Some(name));
        match def {
            Some(Definition::StructDef { combinator, .. }) => {
                combinator.0.iter().all(|field| match field {
                    StructField::Const { combinator, .. } => {
                        self.const_combinator_is_selfview(combinator)
                    }
                    StructField::Dependent { combinator, .. }
                    | StructField::Ordinary { combinator, .. } => {
                        self.combinator_is_selfview(combinator)
                    }
                })
            }
            Some(Definition::BitsDef { .. }) => true,
            Some(Definition::ChoiceDef { combinator, .. }) => combinator
                .choices
                .iter()
                .all(|(_, comb)| self.combinator_is_selfview(comb)),
            Some(Definition::EnumDef { .. }) => true,
            Some(Definition::CombinatorDef { combinator, .. }) => {
                self.combinator_is_selfview(combinator)
            }
            Some(Definition::ConstCombinatorDef {
                const_combinator, ..
            }) => self.const_combinator_is_selfview(const_combinator),
            _ => true,
        }
    }

    pub(crate) fn combinator_is_selfview(&self, combinator: &Combinator) -> bool {
        if !self.combinator_is_copyable(combinator) {
            return false;
        }
        match self.ctx.resolve_alias(combinator) {
            Combinator::ConstraintInt(_) => true,
            Combinator::ConstraintEnum(_) => true,
            Combinator::Wrap(wrap) => self.combinator_is_selfview(&wrap.combinator),
            Combinator::Vec(_) => false,
            Combinator::Array(arr) => {
                self.eval_const_length_expr(&arr.len).is_some()
                    && self.combinator_is_selfview(&arr.combinator)
            }
            Combinator::Bytes(_) | Combinator::Tail(_) => false,
            Combinator::Option(OptionCombinator(inner)) => self.combinator_is_selfview(inner),
            Combinator::Invocation(invocation) => self.is_selfview(&invocation.func),
            Combinator::AndThen(_, rhs) => self.combinator_is_selfview(rhs),
        }
    }

    pub(crate) fn const_combinator_is_selfview(&self, combinator: &ConstCombinator) -> bool {
        match self.ctx.resolve_const(combinator) {
            ConstCombinator::ConstBytes(_) => false,
            ConstCombinator::ConstInt(_) | ConstCombinator::ConstEnum(_) => true,
            ConstCombinator::ConstCombinatorInvocation(name) => self.is_selfview(name),
        }
    }
}

pub(crate) fn definition_name(def: &Definition) -> Option<&str> {
    match def {
        Definition::StructDef { name, .. }
        | Definition::BitsDef { name, .. }
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
        vestir::IntCombinator::Unsigned(bits) if (1..=8).contains(bits) => {
            let lit = proc_macro2::Literal::u8_unsuffixed(value as u8);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (9..=16).contains(bits) => {
            let lit = proc_macro2::Literal::u16_unsuffixed(value as u16);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (17..=32).contains(bits) => {
            let lit = proc_macro2::Literal::u32_unsuffixed(value as u32);
            quote! { #lit }
        }
        vestir::IntCombinator::Unsigned(bits) if (33..=64).contains(bits) => {
            let lit = proc_macro2::Literal::u64_unsuffixed(value as u64);
            quote! { #lit }
        }
        vestir::IntCombinator::BtcVarint | vestir::IntCombinator::ULEB128 => {
            let lit = proc_macro2::Literal::u64_unsuffixed(value as u64);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (1..=8).contains(bits) => {
            let lit = proc_macro2::Literal::i8_unsuffixed(value as i8);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (9..=16).contains(bits) => {
            let lit = proc_macro2::Literal::i16_unsuffixed(value as i16);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (17..=32).contains(bits) => {
            let lit = proc_macro2::Literal::i32_unsuffixed(value as i32);
            quote! { #lit }
        }
        vestir::IntCombinator::Signed(bits) if (33..=64).contains(bits) => {
            let lit = proc_macro2::Literal::i64_unsuffixed(value as i64);
            quote! { #lit }
        }
        other => panic!("unsupported integer literal combinator: {:?}", other),
    }
}
