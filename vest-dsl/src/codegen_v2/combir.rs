//! Combinator Intermediate Representation (CombIR)
//!
//! This IR maps directly to the `vest::regular::*` combinator types in the backend library.

use std::collections::{HashMap, HashSet};

use proc_macro2::{Literal, TokenStream};
use quote::{format_ident, quote};

pub use crate::vestir::ArithOp;
pub use crate::vestir::Endianess as Endian;
pub use crate::vestir::IntConstraint as IntConstraintIR;
pub use crate::vestir::LengthExpr as LenExpr;
pub use crate::vestir::Param as ParamRef;

/// A reference to a tag value (for dispatch/choice).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TagRef {
    /// Reference to a field in the current struct.
    Field(String),
    /// A direct value (for static dispatch).
    Value(TagValue),
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PredicateIR {
    /// Integer constraint expression.
    IntConstraint(IntConstraintIR),
    /// Custom predicate function name.
    Custom(String),
}

/// Mapper IR for mapped combinators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MapperIR {
    /// The name of the mapper struct.
    pub name: String,
}

/// Combinator Intermediate Representation.
///
/// Each variant maps to a combinator type in `vest::regular::*`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombIR {
    // ===== Primitive integers =====
    /// `uints::U8`
    U8,
    /// `uints::U16Le` or `uints::U16Be`
    U16(Endian),
    /// `uints::U24Le` or `uints::U24Be`
    U24(Endian),
    /// `uints::U32Le` or `uints::U32Be`
    U32(Endian),
    /// `uints::U64Le` or `uints::U64Be`
    U64(Endian),

    // ===== Bytes =====
    /// `bytes::Fixed<N>` - fixed-length bytes known at compile time.
    Fixed { len: usize },
    /// `bytes::Variable` - variable-length bytes.
    Variable { len: LenExpr },
    /// `bytes::Tail` - consume remaining input.
    Tail,

    // ===== Sequencing =====
    /// Tuple combinator `(A, B)` or `(A, (B, C))` for independent fields.
    /// Each element has an optional field name for nominal type generation.
    Tuple(Vec<(Option<String>, CombIR)>),
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
    /// `variant::Choice` for unsupported non-dispatch sum types.
    Choice(Vec<CombIR>),
    /// `variant::Dispatch` - select branch based on tag.
    Dispatch {
        tag: TagRef,
        branches: Vec<(TagValue, CombIR)>,
    },
    /// `variant::Opt` - optional combinator.
    Opt(Box<CombIR>),
    /// `variant::OptThen` - optional prefix with required tail.
    OptThen { fst: Box<CombIR>, snd: Box<CombIR> },

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
    /// `modifier::CondEq` - conditional on equality.
    CondEq {
        lhs: TagRef,
        rhs: TagValue,
        inner: Box<CombIR>,
    },
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

/// Context for code generation.
#[derive(Debug, Clone)]
pub struct CodegenCtx {
    /// Current endianness setting.
    pub endian: Endian,
    /// Map of format names to their static sizes (if known).
    pub static_sizes: HashMap<String, usize>,
    /// Top-level exhaustive enum definitions.
    pub enum_names: HashSet<String>,
}

impl Default for CodegenCtx {
    fn default() -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: HashMap::new(),
            enum_names: HashSet::new(),
        }
    }
}

impl From<&crate::type_check::GlobalCtx<'_>> for CodegenCtx {
    fn from(ctx: &crate::type_check::GlobalCtx<'_>) -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: ctx.static_sizes.clone(),
            enum_names: ctx.enums.keys().map(|name| (*name).to_string()).collect(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifetimeCheckMode {
    Full,
    LegacyDispatch,
}

pub fn comb_needs_lifetime(
    comb: &CombIR,
    def_map: &HashMap<String, &CombDef>,
    mode: LifetimeCheckMode,
) -> bool {
    match comb {
        CombIR::Variable { .. } | CombIR::Tail | CombIR::Fixed { .. } => true,
        CombIR::Tuple(elems) => elems
            .iter()
            .any(|(_, elem)| comb_needs_lifetime(elem, def_map, mode)),
        CombIR::Choice(elems) => elems
            .iter()
            .any(|elem| comb_needs_lifetime(elem, def_map, mode)),
        CombIR::Pair { fst, snd } => {
            comb_needs_lifetime(fst, def_map, mode) || comb_needs_lifetime(&snd.comb, def_map, mode)
        }
        CombIR::Preceded { inner, .. } | CombIR::Terminated { inner, .. } => match mode {
            LifetimeCheckMode::Full => comb_needs_lifetime(inner, def_map, mode),
            LifetimeCheckMode::LegacyDispatch => false,
        },
        CombIR::Opt(inner)
        | CombIR::Repeat(inner)
        | CombIR::Refined { inner, .. }
        | CombIR::Mapped { inner, .. }
        | CombIR::AndThen { inner, .. }
        | CombIR::FixedLen { inner, .. }
        | CombIR::Enum { inner, .. }
        | CombIR::Tag { inner, .. } => comb_needs_lifetime(inner, def_map, mode),
        CombIR::CondEq { inner, .. } => match mode {
            LifetimeCheckMode::Full => comb_needs_lifetime(inner, def_map, mode),
            LifetimeCheckMode::LegacyDispatch => false,
        },
        CombIR::OptThen { fst, snd } => match mode {
            LifetimeCheckMode::Full => {
                comb_needs_lifetime(fst, def_map, mode) || comb_needs_lifetime(snd, def_map, mode)
            }
            LifetimeCheckMode::LegacyDispatch => false,
        },
        CombIR::RepeatN { inner, .. } => comb_needs_lifetime(inner, def_map, mode),
        CombIR::Dispatch { branches, .. } => branches
            .iter()
            .any(|(_, branch)| comb_needs_lifetime(branch, def_map, mode)),
        CombIR::Named { name, .. } => def_map
            .get(name)
            .map(|def| comb_needs_lifetime(&def.body, def_map, mode))
            .unwrap_or(false),
        CombIR::U8
        | CombIR::U16(_)
        | CombIR::U24(_)
        | CombIR::U32(_)
        | CombIR::U64(_)
        | CombIR::End
        | CombIR::Success
        | CombIR::Fail(_) => false,
    }
}

pub fn comb_uint_type_tokens(comb: &CombIR) -> Option<TokenStream> {
    match comb {
        CombIR::U8 => Some(quote! { u8 }),
        CombIR::U16(_) => Some(quote! { u16 }),
        CombIR::U24(_) => Some(quote! { u24 }),
        CombIR::U32(_) => Some(quote! { u32 }),
        CombIR::U64(_) => Some(quote! { u64 }),
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
