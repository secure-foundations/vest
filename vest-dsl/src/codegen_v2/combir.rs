//! Combinator Intermediate Representation (CombIR)
//!
//! This IR maps directly to the `vest::regular::*` combinator types in the backend library.

use std::collections::HashMap;

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
    Tuple(Vec<CombIR>),
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
    /// Nested `variant::Choice` / `variant::Either` for sum types.
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
}

impl Default for CodegenCtx {
    fn default() -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: HashMap::new(),
        }
    }
}

impl From<&crate::type_check::GlobalCtx<'_>> for CodegenCtx {
    fn from(ctx: &crate::type_check::GlobalCtx<'_>) -> Self {
        Self {
            endian: Endian::Little,
            static_sizes: ctx.static_sizes.clone(),
        }
    }
}
