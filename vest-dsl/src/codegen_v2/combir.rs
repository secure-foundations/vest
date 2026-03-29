//! Combinator Intermediate Representation (CombIR)
//!
//! This IR maps directly to the `vest::regular::*` combinator types in the backend library.

use std::collections::{BTreeSet, HashMap, HashSet};

use proc_macro2::{Literal, TokenStream};
use quote::{format_ident, quote};

pub use crate::vestir::ArithOp;
pub use crate::vestir::Endianess as Endian;
pub use crate::vestir::IntConstraint as IntConstraintIR;
pub use crate::vestir::LengthExpr as LenExpr;
pub use crate::vestir::Param as ParamRef;

/// A reference to a tag field in the current struct.
pub type TagRef = String;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UIntWidth {
    U8,
    U16,
    U24,
    U32,
    U64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UIntIR {
    pub width: UIntWidth,
    pub endian: Endian,
}

impl UIntIR {
    pub fn new(width: UIntWidth, endian: Endian) -> Self {
        Self { width, endian }
    }

    pub fn rust_type_tokens(self) -> TokenStream {
        match self.width {
            UIntWidth::U8 => quote! { u8 },
            UIntWidth::U16 => quote! { u16 },
            UIntWidth::U24 => quote! { u24 },
            UIntWidth::U32 => quote! { u32 },
            UIntWidth::U64 => quote! { u64 },
        }
    }

    pub fn combinator_type_tokens(self) -> TokenStream {
        match (self.width, self.endian) {
            (UIntWidth::U8, _) => quote! { U8 },
            (UIntWidth::U16, Endian::Little) => quote! { U16Le },
            (UIntWidth::U16, Endian::Big) => quote! { U16Be },
            (UIntWidth::U24, Endian::Little) => quote! { U24Le },
            (UIntWidth::U24, Endian::Big) => quote! { U24Be },
            (UIntWidth::U32, Endian::Little) => quote! { U32Le },
            (UIntWidth::U32, Endian::Big) => quote! { U32Be },
            (UIntWidth::U64, Endian::Little) => quote! { U64Le },
            (UIntWidth::U64, Endian::Big) => quote! { U64Be },
        }
    }

    pub fn is_u24(self) -> bool {
        matches!(self.width, UIntWidth::U24)
    }
}

/// Tag values for dispatch branches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TagValue {
    /// Integer tag value.
    Int(i128),
    /// Enum variant name.
    Enum { ty: String, variant: String },
    /// Byte array tag.
    Bytes(Vec<u8>),
    /// Wildcard/default case.
    Wildcard,
}

/// Predicate IR for refined combinators.
pub type PredicateIR = IntConstraintIR;

/// Mapper IR for mapped combinators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapperIR {
    /// The name of the mapper struct.
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TupleField {
    pub name: String,
    pub comb: CombIR,
}

impl TupleField {
    pub fn named(name: impl Into<String>, comb: CombIR) -> Self {
        Self {
            name: name.into(),
            comb,
        }
    }

    pub fn anonymous(comb: CombIR) -> Self {
        Self::named("", comb)
    }

    pub fn is_anonymous(&self) -> bool {
        self.name.is_empty()
    }
}

/// Combinator Intermediate Representation.
///
/// Each variant maps to a combinator type in `vest::regular::*`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombIR {
    // ===== Primitive integers =====
    /// `uints::U8`, `uints::U16*`, `uints::U24*`, `uints::U32*`, or `uints::U64*`.
    UInt(UIntIR),

    // ===== Bytes =====
    /// `bytes::Fixed<N>` - fixed-length bytes known at compile time.
    Fixed { len: usize },
    /// `bytes::Variable` - variable-length bytes.
    Variable { len: LenExpr },
    /// `bytes::Tail` - consume remaining input.
    Tail,

    // ===== Sequencing =====
    /// Tuple combinator `(A, B)` or `(A, (B, C))` for independent fields.
    /// An empty field name denotes an internal anonymous tuple element.
    Tuple(Vec<TupleField>),
    /// `sequence::Pair` - dependent pair where second depends on first.
    Pair {
        fst: Box<CombIR>,
        snd: Box<DepCombIR>,
    },
    /// `sequence::Preceded` - parse prefix then inner, return only inner.
    Preceded {
        prefix: Box<CombIR>,
        inner: Box<CombIR>,
    },
    /// `sequence::Terminated` - parse inner then suffix, return only inner.
    Terminated {
        inner: Box<CombIR>,
        suffix: Box<CombIR>,
    },

    // ===== Variants/Choice =====
    /// `variant::Dispatch` - select branch based on tag.
    Dispatch {
        tag: TagRef,
        branches: Vec<(TagValue, CombIR)>,
    },
    /// `variant::Opt` - optional combinator.
    Opt(Box<CombIR>),

    // ===== Repetition =====
    /// `repetition::RepeatN` - repeat N times.
    RepeatN { inner: Box<CombIR>, count: LenExpr },
    /// `repetition::Repeat` - repeat until end of input.
    Repeat(Box<CombIR>),

    // ===== Modifiers =====
    /// `modifier::Refined` - add predicate constraint.
    Refined {
        inner: Box<CombIR>,
        predicate: PredicateIR,
    },
    /// `modifier::Mapped` - transform parsed value.
    Mapped {
        inner: Box<CombIR>,
        mapper: MapperIR,
    },
    /// `modifier::AndThen` - chain variable-length with inner parser.
    AndThen {
        len_comb: Box<CombIR>,
        inner: Box<CombIR>,
    },
    /// `modifier::FixedLen` - enforce exact byte count.
    FixedLen { len: LenExpr, inner: Box<CombIR> },
    /// Exhaustive enum lowered to a validated integer plus a nominal mapper.
    Enum {
        inner: Box<CombIR>,
        variants: Vec<(String, i128)>,
    },

    // ===== Tag =====
    /// `tag::Tag` - match a constant value.
    Tag { inner: Box<CombIR>, value: TagValue },

    // ===== Named references =====
    /// Reference to another named combinator definition.
    Named { name: String, args: Vec<ParamRef> },

    // ===== Special =====
    /// `end::End` - succeed only at end of input.
    End,
    /// `success::Success` - always succeed, consume nothing.
    Success,
    /// `fail::Fail` - always fail with message.
    Fail(String),
}

/// Dependent combinator for `Pair` second component.
///
/// The second component of a `Pair` can depend on the result of the first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DepCombIR {
    /// The combinator IR (may reference the first component's value).
    pub comb: CombIR,
    /// The bound dependency names introduced by the first component.
    pub dep_names: Vec<String>,
}

impl DepCombIR {
    /// Create a non-dependent second combinator.
    pub fn independent(comb: CombIR) -> Self {
        Self {
            comb,
            dep_names: Vec::new(),
        }
    }

    /// Create a dependent second combinator.
    pub fn dependent(comb: CombIR, dep_names: Vec<String>) -> Self {
        Self { comb, dep_names }
    }
}

/// A const definition for a constant field in a struct.
#[derive(Debug, Clone)]
pub struct ConstDef {
    /// The name of the constant (e.g., "HEADER_MAGIC_CONST").
    pub name: String,
    /// The Rust type of the constant (e.g., "u16").
    pub ty: String,
    /// The value of the constant (e.g., 51966).
    pub value: i128,
}

/// A top-level combinator definition.
#[derive(Debug, Clone)]
pub struct CombDef {
    /// The name of the combinator.
    pub name: String,
    /// Parameters for parameterized combinators.
    pub params: Vec<ParamDef>,
    /// The combinator body.
    pub body: CombIR,
    /// Whether this is a const combinator (unit type).
    pub is_const: bool,
    /// Const definitions for const fields in this struct.
    pub const_defs: Vec<ConstDef>,
}

/// Parameter definition for parameterized combinators.
#[derive(Debug, Clone)]
pub struct ParamDef {
    /// Parameter name.
    pub name: String,
    /// Parameter type (as CombIR for the type it parses).
    pub ty: CombIR,
}

pub type EnumBindings = HashMap<String, String>;

/// Context for code generation.
#[derive(Debug, Clone)]
pub struct CodegenCtx {
    /// Current endianness setting.
    pub endian: Endian,
    /// Map of format names to their static sizes (if known).
    pub static_sizes: HashMap<String, usize>,
    /// Top-level exhaustive enum definitions.
    pub enum_types: HashSet<String>,
}

impl Default for CodegenCtx {
    fn default() -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: HashMap::new(),
            enum_types: HashSet::new(),
        }
    }
}

impl From<&crate::type_check::GlobalCtx<'_>> for CodegenCtx {
    fn from(ctx: &crate::type_check::GlobalCtx<'_>) -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: ctx.static_sizes.clone(),
            enum_types: ctx.enums.keys().map(|name| (*name).to_string()).collect(),
        }
    }
}

impl CodegenCtx {
    pub fn is_enum_type(&self, name: &str) -> bool {
        self.enum_types.contains(name)
    }
}

pub fn nominal_wrapper_inner(comb: &CombIR) -> Option<&CombIR> {
    match comb {
        CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::AndThen { inner, .. } => Some(inner),
        _ => None,
    }
}

pub fn transparent_inner(comb: &CombIR) -> Option<&CombIR> {
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

pub fn comb_needs_lifetime(comb: &CombIR, def_map: &HashMap<String, &CombDef>) -> bool {
    match comb {
        CombIR::Variable { .. } | CombIR::Tail | CombIR::Fixed { .. } => true,
        CombIR::Tuple(elems) => elems
            .iter()
            .any(|field| comb_needs_lifetime(&field.comb, def_map)),
        CombIR::Pair { fst, snd } => {
            comb_needs_lifetime(fst, def_map) || comb_needs_lifetime(&snd.comb, def_map)
        }
        CombIR::Preceded { inner, .. } | CombIR::Terminated { inner, .. } => {
            comb_needs_lifetime(inner, def_map)
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::Tag { inner, .. } => comb_needs_lifetime(inner, def_map),
        CombIR::RepeatN { inner, .. } => comb_needs_lifetime(inner, def_map),
        CombIR::Dispatch { branches, .. } => branches
            .iter()
            .any(|(_, branch)| comb_needs_lifetime(branch, def_map)),
        CombIR::Named { name, .. } => def_map
            .get(name)
            .map(|def| comb_needs_lifetime(&def.body, def_map))
            .unwrap_or(false),
        CombIR::UInt(_) | CombIR::End | CombIR::Success | CombIR::Fail(_) => false,
    }
}

pub fn comb_uint_type_tokens(comb: &CombIR) -> Option<TokenStream> {
    match comb {
        CombIR::UInt(uint) => Some(uint.rust_type_tokens()),
        CombIR::Enum { inner, .. } => comb_uint_type_tokens(inner),
        _ => None,
    }
}

pub fn comb_uint_or_i128_type_tokens(comb: &CombIR) -> TokenStream {
    comb_uint_type_tokens(comb).unwrap_or_else(|| quote! { i128 })
}

pub fn tag_literal_type_tokens(tag_value: &TagValue) -> TokenStream {
    match tag_value {
        TagValue::Int(_) => quote! { i128 },
        TagValue::Enum { ty, .. } => {
            let ty_ident =
                format_ident!("{}", crate::codegen_v2::nominal::snake_to_upper_camel(ty));
            quote! { #ty_ident }
        }
        TagValue::Bytes(bytes) => {
            let n = Literal::usize_unsuffixed(bytes.len());
            quote! { [u8; #n] }
        }
        TagValue::Wildcard => quote! { i128 },
    }
}

pub fn len_uses_dependent_name(len: &LenExpr, name: &str) -> bool {
    match len {
        LenExpr::Const(_) | LenExpr::SizeOf(_) => false,
        LenExpr::Dependent(dep) => dep == name,
        LenExpr::BinOp { left, right, .. } => {
            len_uses_dependent_name(left, name) || len_uses_dependent_name(right, name)
        }
    }
}

pub fn used_names_in_comb(comb: &CombIR) -> BTreeSet<String> {
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
            for field in elems {
                collect_used_names(&field.comb, names);
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
            names.insert(tag.clone());
            for (_, branch) in branches {
                collect_used_names(branch, names);
            }
        }
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::Tag { inner, .. } => collect_used_names(inner, names),
        CombIR::Named { args, .. } => {
            for arg in args {
                match arg {
                    ParamRef::Dependent(name) => {
                        names.insert(name.clone());
                    }
                }
            }
        }
        CombIR::UInt(_)
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
