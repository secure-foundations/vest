use itertools::Itertools;
use std::fmt::Display;
use std::hash::Hash;

use pest::error::Error;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "vest.pest"]
pub struct VestCombinator;

pub type Span<'i> = pest::Span<'i>;

#[derive(Debug, Clone, Eq)]
pub struct Identifier<'i> {
    pub name: String,
    pub span: Span<'i>,
}

impl PartialEq for Identifier<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Hash for Identifier<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

#[derive(Debug, Clone)]
pub enum Definition<'i> {
    Combinator {
        name: Identifier<'i>,
        param_defns: Vec<ParamDefn<'i>>,
        combinator: Combinator<'i>,
        span: Span<'i>,
    },
    ConstCombinator {
        name: Identifier<'i>,
        const_combinator: ConstCombinator<'i>,
        span: Span<'i>,
    },
    Endianess(Endianess),
    MacroDefn {
        name: Identifier<'i>,
        params: Vec<String>,
        body: Combinator<'i>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Endianess {
    Little,
    Big,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParamDefn<'i> {
    Dependent {
        name: Identifier<'i>,
        combinator: CombinatorInner<'i>,
        span: Span<'i>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Combinator<'i> {
    pub inner: CombinatorInner<'i>,
    pub and_then: Option<Box<Combinator<'i>>>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CombinatorInner<'i> {
    ConstraintInt(ConstraintIntCombinator<'i>),
    ConstraintEnum(ConstraintEnumCombinator<'i>),
    Struct(StructCombinator<'i>),
    Wrap(WrapCombinator<'i>),
    Enum(EnumCombinator<'i>),
    Choice(ChoiceCombinator<'i>),
    Vec(VecCombinator<'i>),
    Array(ArrayCombinator<'i>),
    Bytes(BytesCombinator<'i>),
    Tail(TailCombinator<'i>),
    Option(OptionCombinator<'i>),
    Invocation(CombinatorInvocation<'i>),
    MacroInvocation {
        name: String,
        args: Vec<CombinatorInner<'i>>,
    },
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ConstraintIntCombinator<'i> {
    pub combinator: IntCombinator,
    pub constraint: Option<IntConstraint<'i>>,
    pub span: Span<'i>,
}

impl PartialEq for ConstraintIntCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.combinator == other.combinator && self.constraint == other.constraint
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ConstraintEnumCombinator<'i> {
    pub combinator: CombinatorInvocation<'i>,
    pub constraint: EnumConstraint<'i>,
    pub span: Span<'i>,
}

impl PartialEq for ConstraintEnumCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.combinator == other.combinator && self.constraint == other.constraint
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub enum EnumConstraint<'i> {
    Single {
        elem: Identifier<'i>,
        span: Span<'i>,
    },
    Set(Vec<Identifier<'i>>),
    Neg(Box<EnumConstraint<'i>>),
}

impl PartialEq for EnumConstraint<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (EnumConstraint::Single { elem: e1, .. }, EnumConstraint::Single { elem: e2, .. }) => {
                e1 == e2
            }
            (EnumConstraint::Set(set1), EnumConstraint::Set(set2)) => set1 == set2,
            (EnumConstraint::Neg(c1), EnumConstraint::Neg(c2)) => c1 == c2,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntCombinator {
    Signed(u8),
    Unsigned(u8),
    BtcVarint,
    ULEB128,
}

#[derive(Debug, Clone, Eq, Hash)]
pub enum IntConstraint<'i> {
    Single {
        elem: ConstraintElem<'i>,
        span: Span<'i>,
    },
    Set(Vec<ConstraintElem<'i>>),
    Neg(Box<IntConstraint<'i>>),
}

impl PartialEq for IntConstraint<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (IntConstraint::Single { elem: e1, .. }, IntConstraint::Single { elem: e2, .. }) => {
                e1 == e2
            }
            (IntConstraint::Set(set1), IntConstraint::Set(set2)) => set1 == set2,
            (IntConstraint::Neg(c1), IntConstraint::Neg(c2)) => c1 == c2,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub enum ConstraintElem<'i> {
    Range {
        start: Option<i128>,
        end: Option<i128>,
        span: Span<'i>,
    },
    Single {
        elem: i128,
        span: Span<'i>,
    },
}

impl PartialEq for ConstraintElem<'_> {
    // Disregard the span for equality checks
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ConstraintElem::Range {
                    start: s1, end: e1, ..
                },
                ConstraintElem::Range {
                    start: s2, end: e2, ..
                },
            ) => s1 == s2 && e1 == e2,
            (ConstraintElem::Single { elem: e1, .. }, ConstraintElem::Single { elem: e2, .. }) => {
                e1 == e2
            }
            _ => false,
        }
    }
}

impl<'i> ConstraintElem<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            ConstraintElem::Range { span, .. } => *span,
            ConstraintElem::Single { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct StructCombinator<'i> {
    pub fields: Vec<StructField<'i>>,
    pub span: Span<'i>,
}

impl PartialEq for StructCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.fields == other.fields
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub enum StructField<'i> {
    Dependent {
        label: Identifier<'i>,
        combinator: Combinator<'i>,
        span: Span<'i>,
    },
    Const {
        label: Identifier<'i>,
        combinator: ConstCombinator<'i>,
        span: Span<'i>,
    },
    Ordinary {
        label: Identifier<'i>,
        combinator: Combinator<'i>,
        span: Span<'i>,
    },
}

impl PartialEq for StructField<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                StructField::Dependent {
                    label: l1,
                    combinator: c1,
                    ..
                },
                StructField::Dependent {
                    label: l2,
                    combinator: c2,
                    ..
                },
            ) => l1 == l2 && c1 == c2,
            (
                StructField::Const {
                    label: l1,
                    combinator: c1,
                    ..
                },
                StructField::Const {
                    label: l2,
                    combinator: c2,
                    ..
                },
            ) => l1 == l2 && c1 == c2,
            (
                StructField::Ordinary {
                    label: l1,
                    combinator: c1,
                    ..
                },
                StructField::Ordinary {
                    label: l2,
                    combinator: c2,
                    ..
                },
            ) => l1 == l2 && c1 == c2,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Param<'i> {
    Dependent(Identifier<'i>),
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct WrapCombinator<'i> {
    pub prior: Vec<ConstCombinator<'i>>,
    pub combinator: Box<Combinator<'i>>,
    pub post: Vec<ConstCombinator<'i>>,
    pub span: Span<'i>,
}

impl PartialEq for WrapCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.prior == other.prior && self.combinator == other.combinator && self.post == other.post
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub enum EnumCombinator<'i> {
    Exhaustive {
        enums: Vec<Enum<'i>>,
        span: Span<'i>,
    },
    NonExhaustive {
        enums: Vec<Enum<'i>>,
        span: Span<'i>,
    },
}

impl PartialEq for EnumCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                EnumCombinator::Exhaustive { enums: e1, .. },
                EnumCombinator::Exhaustive { enums: e2, .. },
            ) => e1 == e2,
            (
                EnumCombinator::NonExhaustive { enums: e1, .. },
                EnumCombinator::NonExhaustive { enums: e2, .. },
            ) => e1 == e2,
            _ => false,
        }
    }
}

impl<'i> EnumCombinator<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            EnumCombinator::Exhaustive { span, .. }
            | EnumCombinator::NonExhaustive { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Enum<'i> {
    pub name: Identifier<'i>,
    pub value: i128,
    pub type_annotation: Option<IntCombinator>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ChoiceCombinator<'i> {
    pub depend_id: Option<Identifier<'i>>,
    // pub choices: Vec<Choice>,
    pub choices: Choices<'i>,
    pub span: Span<'i>,
}

impl PartialEq for ChoiceCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.depend_id == other.depend_id && self.choices == other.choices
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Choices<'i> {
    Enums(Vec<(Identifier<'i>, Combinator<'i>)>),
    Ints(Vec<(Option<ConstraintElem<'i>>, Combinator<'i>)>),
    Arrays(Vec<(ConstArray<'i>, Combinator<'i>)>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VecCombinator<'i> {
    Vec(Box<Combinator<'i>>),
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ArrayCombinator<'i> {
    pub combinator: Box<Combinator<'i>>,
    pub len: LengthExpr<'i>,
    pub span: Span<'i>,
}

impl PartialEq for ArrayCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.combinator == other.combinator && self.len == other.len
    }
}

/// Arithmetic operators for length expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// A dependent field identifier, potentially with nested field access (e.g., @hdr.payload_length)
#[derive(Debug, Clone, Eq)]
pub struct DependentId<'i> {
    /// The root field name (without @)
    pub root: String,
    /// Optional path of nested field accesses
    pub path: Vec<String>,
    pub span: Span<'i>,
}

impl PartialEq for DependentId<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root && self.path == other.path
    }
}

impl Hash for DependentId<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.root.hash(state);
        self.path.hash(state);
    }
}

impl<'i> DependentId<'i> {
    pub fn simple(name: String, span: Span<'i>) -> Self {
        Self {
            root: name,
            path: Vec::new(),
            span,
        }
    }

    pub fn is_simple(&self) -> bool {
        self.path.is_empty()
    }

    /// Returns the full path as a dotted string (e.g., "hdr.payload_length")
    pub fn full_path(&self) -> String {
        if self.path.is_empty() {
            self.root.clone()
        } else {
            format!("{}.{}", self.root, self.path.join("."))
        }
    }
}

impl Display for DependentId<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.full_path())
    }
}

/// Length expression for array sizes - supports constants, dependent fields,
/// static size expressions, and arithmetic
#[derive(Debug, Clone, Eq, Hash)]
pub enum LengthExpr<'i> {
    Const {
        value: usize,
        span: Span<'i>,
    },
    Dependent(DependentId<'i>),
    SizeOf {
        format_name: Identifier<'i>,
        span: Span<'i>,
    },
    BinOp {
        op: ArithOp,
        left: Box<LengthExpr<'i>>,
        right: Box<LengthExpr<'i>>,
        span: Span<'i>,
    },
}

impl PartialEq for LengthExpr<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (LengthExpr::Const { value: v1, .. }, LengthExpr::Const { value: v2, .. }) => v1 == v2,
            (LengthExpr::Dependent(d1), LengthExpr::Dependent(d2)) => d1 == d2,
            (
                LengthExpr::SizeOf {
                    format_name: n1, ..
                },
                LengthExpr::SizeOf {
                    format_name: n2, ..
                },
            ) => n1 == n2,
            (
                LengthExpr::BinOp {
                    op: o1,
                    left: l1,
                    right: r1,
                    ..
                },
                LengthExpr::BinOp {
                    op: o2,
                    left: l2,
                    right: r2,
                    ..
                },
            ) => o1 == o2 && l1 == l2 && r1 == r2,
            _ => false,
        }
    }
}

impl<'i> LengthExpr<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            LengthExpr::Const { span, .. } => *span,
            LengthExpr::Dependent(d) => d.span,
            LengthExpr::SizeOf { span, .. } => *span,
            LengthExpr::BinOp { span, .. } => *span,
        }
    }

    /// Collects all dependent identifiers referenced in this length expression
    pub fn collect_dependent_ids(&self) -> Vec<&DependentId<'i>> {
        match self {
            LengthExpr::Const { .. } | LengthExpr::SizeOf { .. } => Vec::new(),
            LengthExpr::Dependent(d) => vec![d],
            LengthExpr::BinOp { left, right, .. } => {
                let mut ids = left.collect_dependent_ids();
                ids.extend(right.collect_dependent_ids());
                ids
            }
        }
    }

    /// Returns true if this is a simple constant value
    pub fn is_const(&self) -> bool {
        matches!(self, LengthExpr::Const { .. })
    }

    /// Returns the constant value if this is a simple constant
    pub fn as_const(&self) -> Option<usize> {
        match self {
            LengthExpr::Const { value, .. } => Some(*value),
            _ => None,
        }
    }
}

impl<'i> DependentId<'i> {
    /// Convert to an Identifier (only works for simple ids without nested access)
    pub fn to_identifier(&self) -> Identifier<'i> {
        Identifier {
            name: self.root.clone(),
            span: self.span,
        }
    }
}

impl Display for LengthExpr<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LengthExpr::Const { value, .. } => write!(f, "{}", value),
            LengthExpr::Dependent(d) => write!(f, "{}", d),
            LengthExpr::SizeOf { format_name, .. } => write!(f, "|{}|", format_name),
            LengthExpr::BinOp {
                op, left, right, ..
            } => {
                let op_str = match op {
                    ArithOp::Add => "+",
                    ArithOp::Sub => "-",
                    ArithOp::Mul => "*",
                    ArithOp::Div => "/",
                };
                write!(f, "({} {} {})", left, op_str, right)
            }
        }
    }
}

pub type LengthSpecifier<'i> = LengthExpr<'i>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OptionCombinator<'i>(pub Box<Combinator<'i>>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BytesCombinator<'i> {
    pub len: LengthSpecifier<'i>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct TailCombinator<'i> {
    pub span: Span<'i>,
}

impl PartialEq for TailCombinator<'_> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct CombinatorInvocation<'i> {
    pub func: Identifier<'i>,
    pub args: Vec<Param<'i>>,
    pub span: Span<'i>,
}

impl PartialEq for CombinatorInvocation<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.func == other.func && self.args == other.args
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstCombinator<'i> {
    ConstBytes(ConstBytesCombinator<'i>),
    ConstInt(ConstIntCombinator<'i>),
    ConstEnum(ConstEnumCombinator<'i>),
    ConstCombinatorInvocation {
        name: Identifier<'i>,
        span: Span<'i>,
    },
}

impl<'i> ConstCombinator<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            ConstCombinator::ConstBytes(c) => c.span,
            ConstCombinator::ConstInt(c) => c.span,
            ConstCombinator::ConstEnum(c) => c.span,
            ConstCombinator::ConstCombinatorInvocation { span, .. } => *span,
        }
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ConstBytesCombinator<'i> {
    pub len: usize,
    pub values: ConstArray<'i>,
    pub span: Span<'i>,
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ConstEnumCombinator<'i> {
    pub combinator: CombinatorInvocation<'i>,
    pub variant: Identifier<'i>,
    pub span: Span<'i>,
}

impl PartialEq for ConstEnumCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.combinator == other.combinator && self.variant == other.variant
    }
}

impl PartialEq for ConstBytesCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.values == other.values
    }
}

#[derive(Debug, Clone, Eq)]
pub enum ConstArray<'i> {
    Char {
        chars: Vec<u8>,
        span: Span<'i>,
    },
    Int {
        ints: Vec<i128>,
        span: Span<'i>,
    },
    Repeat {
        repeat: i128,
        count: usize,
        span: Span<'i>,
    },
    Wildcard,
}

impl PartialEq for ConstArray<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ConstArray::Char { chars: c1, .. }, ConstArray::Char { chars: c2, .. }) => c1 == c2,
            (ConstArray::Int { ints: i1, .. }, ConstArray::Int { ints: i2, .. }) => i1 == i2,
            (
                ConstArray::Repeat {
                    repeat: r1,
                    count: c1,
                    ..
                },
                ConstArray::Repeat {
                    repeat: r2,
                    count: c2,
                    ..
                },
            ) => r1 == r2 && c1 == c2,
            (ConstArray::Wildcard, ConstArray::Wildcard) => true,
            _ => false,
        }
    }
}

impl Hash for ConstArray<'_> {
    // Ignore the span for hashing
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            ConstArray::Char { chars, .. } => chars.hash(state),
            ConstArray::Int { ints, .. } => ints.hash(state),
            ConstArray::Repeat { repeat, count, .. } => {
                repeat.hash(state);
                count.hash(state);
            }
            ConstArray::Wildcard => ().hash(state),
        }
    }
}

impl<'i> ConstArray<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            ConstArray::Char { span, .. } => *span,
            ConstArray::Int { span, .. } => *span,
            ConstArray::Repeat { span, .. } => *span,
            ConstArray::Wildcard => Span::new("", 0, 0).unwrap(),
        }
    }
}

#[derive(Debug, Clone, Eq, Hash)]
pub struct ConstIntCombinator<'i> {
    pub combinator: IntCombinator,
    pub value: i128,
    pub span: Span<'i>,
}

impl PartialEq for ConstIntCombinator<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.combinator == other.combinator && self.value == other.value
    }
}

impl Display for Identifier<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Display for Definition<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Definition::Combinator {
                name,
                param_defns,
                combinator,
                ..
            } => {
                write!(f, "{}", name)?;
                if !param_defns.is_empty() {
                    write!(f, "({})", param_defns.iter().join(","))?;
                }
                write!(f, " = {}", combinator)
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
                ..
            } => {
                write!(f, "const {}: {}", name, const_combinator)
            }
            Definition::Endianess(endianess) => match endianess {
                Endianess::Little => write!(f, "!LITTLE_ENDIAN"),
                Endianess::Big => write!(f, "!BIG_ENDIAN"),
            },
            Definition::MacroDefn {
                name,
                params,
                body: combinator,
            } => {
                write!(
                    f,
                    "macro {}!({}) = {}",
                    name,
                    params.iter().join(","),
                    combinator
                )
            }
        }
    }
}

impl Display for ParamDefn<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamDefn::Dependent {
                name, combinator, ..
            } => write!(f, "{}:{}", name, combinator),
        }
    }
}

impl Display for Combinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)?;
        if let Some(next) = &self.and_then {
            write!(f, " >>= {}", next)?;
        }
        Ok(())
    }
}

impl Display for CombinatorInner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CombinatorInner::ConstraintInt(c) => write!(f, "{}", c),
            CombinatorInner::ConstraintEnum(c) => write!(f, "{}", c),
            CombinatorInner::Struct(s) => write!(f, "{}", s),
            CombinatorInner::Wrap(w) => write!(f, "{}", w),
            CombinatorInner::Enum(e) => write!(f, "{}", e),
            CombinatorInner::Choice(c) => write!(f, "{}", c),
            CombinatorInner::Vec(v) => write!(f, "{}", v),
            CombinatorInner::Array(a) => write!(f, "{}", a),
            CombinatorInner::Bytes(a) => write!(f, "{}", a),
            CombinatorInner::Tail(t) => write!(f, "{}", t),
            CombinatorInner::Option(o) => write!(f, "{}", o),
            CombinatorInner::Invocation(i) => write!(f, "{}", i),
            CombinatorInner::MacroInvocation { name, args } => {
                write!(f, "{}!({})", name, args.iter().join(","))
            }
        }
    }
}

impl Display for ConstraintIntCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.constraint {
            Some(c) => write!(f, "{}_in_{}", self.combinator, c),
            None => write!(f, "{}", self.combinator),
        }
    }
}

impl Display for IntCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntCombinator::Signed(n) => write!(f, "i{}", n),
            IntCombinator::Unsigned(n) => write!(f, "u{}", n),
            IntCombinator::BtcVarint => write!(f, "VarInt"),
            IntCombinator::ULEB128 => write!(f, "u64"),
        }
    }
}

impl Display for IntConstraint<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntConstraint::Single { elem, .. } => write!(f, "{}", elem),
            IntConstraint::Set(set) => {
                write!(f, "{}", set.iter().join("_and_"))
            }
            IntConstraint::Neg(c) => write!(f, "not_{}", c),
        }
    }
}

impl Display for ConstraintElem<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintElem::Range { start, end, .. } => match (start, end) {
                (Some(start), Some(end)) => write!(f, "{}..{}", start, end),
                (Some(start), None) => write!(f, "{}..max", start),
                (None, Some(end)) => write!(f, "min..{}", end),
                (None, None) => write!(f, "min..max"),
            },
            ConstraintElem::Single { elem, .. } => write!(f, "{}", elem),
        }
    }
}

impl Display for StructCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for field in &self.fields {
            write!(f, "{}", field)?;
            writeln!(f, ",")?;
        }
        write!(f, "}}")
    }
}

impl Display for StructField<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StructField::Dependent {
                label, combinator, ..
            } => {
                write!(f, "{}:{}", label, combinator)
            }
            StructField::Const {
                label, combinator, ..
            } => {
                write!(f, "{}:{}", label, combinator)
            }
            StructField::Ordinary {
                label, combinator, ..
            } => {
                write!(f, "{}:{}", label, combinator)
            }
        }
    }
}

impl Display for ConstCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstCombinator::ConstBytes(b) => write!(f, "{}", b),
            ConstCombinator::ConstInt(i) => write!(f, "{}", i),
            ConstCombinator::ConstEnum(e) => write!(f, "{}", e),
            ConstCombinator::ConstCombinatorInvocation { name, .. } => write!(f, "{}", name),
        }
    }
}

impl Display for ConstBytesCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.values)
    }
}

impl Display for ConstraintEnumCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}|{}", self.combinator, self.constraint)
    }
}

impl Display for EnumConstraint<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnumConstraint::Single { elem, .. } => write!(f, "{}", elem),
            EnumConstraint::Set(set) => {
                write!(f, "{{")?;
                for (i, elem) in set.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "}}")
            }
            EnumConstraint::Neg(c) => write!(f, "!{}", c),
        }
    }
}

impl Display for ConstEnumCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}={}", self.combinator, self.variant)
    }
}

impl Display for ConstArray<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstArray::Char { chars, .. } => {
                write!(f, "\"")?;
                for byte in chars {
                    write!(f, "\\x{:02x}", byte)?;
                }
                write!(f, "\"")
            }
            ConstArray::Int { ints, .. } => {
                write!(f, "[")?;
                for (i, int) in ints.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", int)?;
                }
                write!(f, "]")
            }
            ConstArray::Repeat { repeat, count, .. } => write!(f, "[{}; {}]", repeat, count),
            ConstArray::Wildcard => write!(f, "_"),
        }
    }
}

impl Display for ConstIntCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_{}", self.combinator, self.value)
    }
}

impl Display for Param<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Param::Dependent(s) => write!(f, "{}", s),
        }
    }
}

impl Display for WrapCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "wrap(")?;
        for combinator in &self.prior {
            write!(f, "{}, ", combinator)?;
        }
        write!(f, "{}", self.combinator)?;
        for combinator in &self.post {
            write!(f, ", {}", combinator)?;
        }
        write!(f, ")")
    }
}

impl Display for EnumCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "enum {{")?;
        match self {
            EnumCombinator::Exhaustive { enums, .. }
            | EnumCombinator::NonExhaustive { enums, .. } => {
                for enum_ in enums {
                    writeln!(f, "{},", enum_)?;
                }
            }
        }
        if let EnumCombinator::NonExhaustive { .. } = self {
            writeln!(f, "...")?;
        }
        write!(f, "}}")
    }
}

impl Display for Enum<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.type_annotation {
            Some(ty) => write!(f, "{} = {}{}", self.name, self.value, ty),
            None => write!(f, "{} = {}", self.name, self.value),
        }
    }
}

impl Display for ChoiceCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "choose ")?;
        if let Some(depend_id) = &self.depend_id {
            write!(f, "({})", depend_id)?;
        }
        writeln!(f, "{{")?;
        write!(f, "{}", self.choices)?;
        write!(f, "}}")
    }
}

impl Display for Choices<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Choices::Enums(enums) => {
                for (name, combinator) in enums {
                    writeln!(f, "{} => {},", name, combinator)?;
                }
                Ok(())
            }
            Choices::Ints(ints) => {
                for (pattern, combinator) in ints {
                    let value = pattern
                        .as_ref()
                        .map_or("_".to_string(), |elem| elem.to_string());
                    writeln!(f, "{} => {},", value, combinator)?;
                }
                Ok(())
            }
            Choices::Arrays(arrays) => {
                for (array, combinator) in arrays {
                    writeln!(f, "{} => {},", array, combinator)?;
                }
                Ok(())
            }
        }
    }
}

impl Display for VecCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VecCombinator::Vec(v) => write!(f, "Vec<{}>", v),
        }
    }
}

impl Display for ArrayCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}; {}]", self.combinator, self.len)
    }
}

impl Display for BytesCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[u8; {}]", self.len)
    }
}

impl Display for TailCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tail")
    }
}

impl Display for OptionCombinator<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Option<{}>", self.0)
    }
}

impl Display for CombinatorInvocation<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.func)
        } else {
            write!(f, "{}({})", self.func, self.args.iter().join(","))
        }
    }
}

impl<'i> CombinatorInner<'i> {
    pub fn as_span(&self) -> Span<'i> {
        match self {
            CombinatorInner::ConstraintInt(c) => c.span,
            CombinatorInner::ConstraintEnum(c) => c.span,
            CombinatorInner::Struct(s) => s.span,
            CombinatorInner::Wrap(w) => w.span,
            CombinatorInner::Enum(
                EnumCombinator::Exhaustive { span, .. }
                | EnumCombinator::NonExhaustive { span, .. },
            ) => *span,
            CombinatorInner::Choice(c) => c.span,
            CombinatorInner::Vec(VecCombinator::Vec(v)) => v.span,
            CombinatorInner::Array(a) => a.span,
            CombinatorInner::Bytes(b) => b.span,
            CombinatorInner::Tail(t) => t.span,
            CombinatorInner::Option(o) => o.0.span,
            CombinatorInner::Invocation(i) => i.span,
            CombinatorInner::MacroInvocation { .. } => Span::new("", 0, 0).unwrap(),
        }
    }
}

pub fn from_str(source: &str) -> Result<Vec<Definition<'_>>, Box<Error<Rule>>> {
    let mut definitions = vec![];

    let pairs = VestCombinator::parse(Rule::grammar, source)?;
    // let pairs = VestCombinator::parse(Rule::grammar, source).unwrap_or_else(|e| panic!("{}", e));
    for pair in pairs {
        if let Rule::definition = pair.as_rule() {
            definitions.push(build_definition(pair));
        }
    }

    Ok(definitions)
}

fn build_id(pair: pest::iterators::Pair<Rule>) -> Identifier {
    let span = pair.as_span();
    let name = pair.as_str().to_string();
    Identifier { name, span }
}

fn build_definition(pair: pest::iterators::Pair<Rule>) -> Definition {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::combinator_defn => {
            let mut inner_rules = rule.into_inner();
            let name = build_id(inner_rules.next().unwrap());
            let next_rule = inner_rules.next().unwrap();
            match next_rule.as_rule() {
                Rule::param_defn_list => {
                    let param_defns = build_param_defns(next_rule);
                    let combinator = build_combinator(inner_rules.next().unwrap());
                    Definition::Combinator {
                        name,
                        param_defns,
                        combinator,
                        span,
                    }
                }
                Rule::combinator => {
                    let combinator = build_combinator(next_rule);
                    Definition::Combinator {
                        name,
                        param_defns: vec![],
                        combinator,
                        span,
                    }
                }
                _ => unreachable!(),
            }
        }
        Rule::const_combinator_defn => {
            let mut inner_rules = rule.into_inner();
            let _ = inner_rules.next().unwrap(); // skip the "const" keyword
            let next_rule = inner_rules.next().unwrap();
            let name = next_rule.as_str().to_string();
            let name_span = next_rule.as_span();
            let const_combinator = build_const_combinator(inner_rules.next().unwrap());
            Definition::ConstCombinator {
                name: Identifier {
                    name,
                    span: name_span,
                },
                const_combinator,
                span,
            }
        }
        Rule::endianess_defn => {
            let endianess = rule.as_str();
            match endianess {
                "!LITTLE_ENDIAN" => Definition::Endianess(Endianess::Little),
                "!BIG_ENDIAN" => Definition::Endianess(Endianess::Big),
                _ => unreachable!(),
            }
        }
        Rule::macro_defn => {
            let mut inner_rules = rule.into_inner();
            let name = build_id(inner_rules.next().unwrap());
            let params = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(|r| r.as_str().to_string())
                .collect();
            let combinator = build_combinator(inner_rules.next().unwrap());
            Definition::MacroDefn {
                name,
                params,
                body: combinator,
            }
        }
        _ => unreachable!(),
    }
}

fn build_param_defns(pair: pest::iterators::Pair<Rule>) -> Vec<ParamDefn> {
    let mut param_defns = vec![];
    for pair in pair.into_inner() {
        let span = pair.as_span();
        match pair.as_rule() {
            Rule::param_defn => {
                let mut inner_rules = pair.into_inner();
                let mut name = build_id(inner_rules.next().unwrap());
                match name.name.strip_prefix('@') {
                    Some(stripped) => name.name = stripped.to_string(),
                    None => unreachable!(),
                }
                let combinator = build_combinator_inner(inner_rules.next().unwrap());
                param_defns.push(ParamDefn::Dependent {
                    name,
                    combinator,
                    span,
                });
            }
            _ => unreachable!(),
        }
    }
    param_defns
}

fn build_combinator(pair: pest::iterators::Pair<Rule>) -> Combinator {
    let mut inner_rules = pair.into_inner();
    let next_rule = inner_rules.next().unwrap();
    let inner_span = next_rule.as_span();
    let inner = build_combinator_inner(next_rule);
    let next_rule = inner_rules.next();
    let (and_then, and_then_span) = match next_rule {
        Some(rule) => {
            let and_then = build_combinator(rule);
            (Some(Box::new(and_then.clone())), and_then.span)
        }
        None => (None, inner_span),
    };
    let span = Span::new(
        inner_span.get_input(),
        inner_span.start(),
        and_then_span.end(),
    )
    .expect("Failed to create span for combinator: {:inner_span:?}, {and_then_span:?}");
    Combinator {
        inner,
        and_then,
        span,
    }
}

fn build_combinator_inner(pair: pest::iterators::Pair<Rule>) -> CombinatorInner {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::constraint_int_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = build_int_combinator(inner_rules.next().unwrap());
            let constraint = inner_rules.next().map(build_int_constraint);
            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                combinator,
                constraint,
                span,
            })
        }
        Rule::constraint_enum_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = build_combinator_invocation(inner_rules.next().unwrap());
            let constraint = build_enum_constraint(inner_rules.next().unwrap());
            CombinatorInner::ConstraintEnum(ConstraintEnumCombinator {
                combinator,
                constraint,
                span,
            })
        }
        Rule::struct_combinator => {
            let inner_rules = rule.into_inner();
            let fields = inner_rules.map(build_field).collect();
            CombinatorInner::Struct(StructCombinator { fields, span })
        }
        Rule::wrap_combinator => {
            let mut inner_rules = rule.into_inner();
            let prior = inner_rules.next().unwrap();
            let prior_span = prior.as_span();
            let prior = prior.into_inner().map(build_const_combinator).collect();
            let combinator = Box::new(build_combinator(inner_rules.next().unwrap()));
            let post = inner_rules.next().unwrap();
            let post_span = post.as_span();
            let post = post.into_inner().map(build_const_combinator).collect();
            let span = Span::new(prior_span.get_input(), prior_span.start(), post_span.end())
                .expect("Failed to create span for wrap combinator");
            CombinatorInner::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
                span,
            })
        }
        Rule::enum_combinator => {
            let rule = rule.into_inner().next().unwrap();
            let span = rule.as_span();
            match rule.as_rule() {
                Rule::exhaustive_enum => {
                    let enums = rule.into_inner().map(build_enum).collect();
                    CombinatorInner::Enum(EnumCombinator::Exhaustive { enums, span })
                }
                Rule::non_exhaustive_enum => {
                    let enums = rule
                        .into_inner()
                        .filter(|pair| pair.as_rule() == Rule::enum_field)
                        .map(build_enum)
                        .collect();
                    CombinatorInner::Enum(EnumCombinator::NonExhaustive { enums, span })
                }
                _ => unreachable!(),
            }
        }
        Rule::choice_combinator => {
            let mut inner_rules = rule.into_inner();
            match inner_rules.peek().unwrap().as_rule() {
                Rule::depend_id => {
                    let mut depend_id = build_id(inner_rules.next().unwrap());
                    depend_id.name = depend_id.name.strip_prefix('@').unwrap().to_string();
                    let choices = build_choices(inner_rules);
                    CombinatorInner::Choice(ChoiceCombinator {
                        depend_id: Some(depend_id),
                        choices,
                        span,
                    })
                }
                Rule::choice => {
                    let choices = build_choices(inner_rules);
                    CombinatorInner::Choice(ChoiceCombinator {
                        depend_id: None,
                        choices,
                        span,
                    })
                }
                _ => unreachable!(),
            }
        }
        Rule::vec_combinator => CombinatorInner::Vec(build_vec_combinator(rule)),
        Rule::array_combinator => {
            let mut inner_rules = rule.into_inner();
            let comb = build_combinator(inner_rules.next().unwrap());
            let len_rule = inner_rules.next().unwrap();
            let len = build_length_expr(len_rule);
            match comb.inner {
                // [u8; ...] would generate bytes combinator
                CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                    combinator: IntCombinator::Unsigned(8),
                    constraint,
                    ..
                }) if constraint.is_none() => CombinatorInner::Bytes(BytesCombinator { len, span }),
                _ => {
                    let combinator = Box::new(comb);
                    CombinatorInner::Array(ArrayCombinator {
                        combinator,
                        len,
                        span,
                    })
                }
            }
        }
        Rule::option_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = build_combinator(inner_rules.next().unwrap());
            CombinatorInner::Option(OptionCombinator(Box::new(combinator)))
        }
        Rule::tail_combinator => CombinatorInner::Tail(TailCombinator { span }),
        Rule::combinator_invocation => {
            CombinatorInner::Invocation(build_combinator_invocation(rule))
        }
        Rule::macro_invocation => {
            let mut inner_rules = rule.into_inner();
            let name = inner_rules.next().unwrap().as_str().to_string();
            let args = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(build_combinator_inner)
                .collect();
            CombinatorInner::MacroInvocation { name, args }
        }
        _ => unreachable!(),
    }
}

fn build_int_combinator(pair: pest::iterators::Pair<Rule>) -> IntCombinator {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let mut parse_width = || inner_rules.next().unwrap().as_str().parse::<u8>().unwrap();
    match rule.as_rule() {
        Rule::unsigned => IntCombinator::Unsigned(parse_width()),
        Rule::signed => IntCombinator::Signed(parse_width()),
        Rule::btc_varint => IntCombinator::BtcVarint,
        Rule::uleb128 => IntCombinator::ULEB128,
        _ => unreachable!(),
    }
}

fn build_int_constraint(pair: pest::iterators::Pair<Rule>) -> IntConstraint {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::constraint_elem => IntConstraint::Single {
            elem: build_constraint_elem(rule),
            span,
        },
        Rule::constraint_elem_set => {
            let inner_rules = rule.into_inner();
            let elems = inner_rules.map(build_constraint_elem).collect::<Vec<_>>();
            IntConstraint::Set(elems)
        }
        Rule::int_constraint => IntConstraint::Neg(Box::new(build_int_constraint(rule))),
        _ => unreachable!(),
    }
}

fn build_constraint_elem(pair: pest::iterators::Pair<Rule>) -> ConstraintElem {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::const_int_range => {
            let mut inner_rules = rule.into_inner();
            let start = inner_rules.next().map(build_const_int);
            let end = inner_rules.next().map(build_const_int);
            // TODO: check that start <= end (?)
            ConstraintElem::Range { start, end, span }
        }
        Rule::const_int => ConstraintElem::Single {
            elem: build_const_int(rule),
            span,
        },
        _ => unreachable!(),
    }
}

fn build_const_int(pair: pest::iterators::Pair<Rule>) -> i128 {
    let mut inner_rules = pair.into_inner();
    let pair = inner_rules.next().unwrap();
    match pair.as_rule() {
        Rule::decimal => pair.as_str().parse::<i128>().unwrap(),
        Rule::hex => i128::from_str_radix(&pair.as_str()[2..], 16).unwrap(),
        Rule::ascii => {
            // strip leading and trailing quotes
            let str = &pair.as_str();
            let str = &str[1..str.len() - 1];
            if let Some(rem) = str.strip_prefix("\\x") {
                i128::from_str_radix(rem, 16).unwrap()
            } else {
                str.as_bytes()[0] as i128
            }
        }
        _ => unreachable!(),
    }
}

fn build_length_expr(pair: pest::iterators::Pair<Rule>) -> LengthExpr {
    let span = pair.as_span();
    match pair.as_rule() {
        Rule::length_expr => {
            let mut inner_rules = pair.into_inner();
            let first_term = build_length_expr(inner_rules.next().unwrap());

            let mut result = first_term;
            while let Some(op_rule) = inner_rules.next() {
                let op = match op_rule.as_rule() {
                    Rule::add_op => ArithOp::Add,
                    Rule::sub_op => ArithOp::Sub,
                    _ => unreachable!("Expected add_op or sub_op"),
                };
                let right_term = build_length_expr(inner_rules.next().unwrap());
                let new_span = Span::new(
                    result.as_span().get_input(),
                    result.as_span().start(),
                    right_term.as_span().end(),
                )
                .unwrap();
                result = LengthExpr::BinOp {
                    op,
                    left: Box::new(result),
                    right: Box::new(right_term),
                    span: new_span,
                };
            }
            result
        }
        Rule::length_term => {
            let mut inner_rules = pair.into_inner();
            let first_atom = build_length_expr(inner_rules.next().unwrap());

            let mut result = first_atom;
            while let Some(op_rule) = inner_rules.next() {
                let op = match op_rule.as_rule() {
                    Rule::mul_op => ArithOp::Mul,
                    Rule::div_op => ArithOp::Div,
                    _ => unreachable!("Expected mul_op or div_op"),
                };
                let right_atom = build_length_expr(inner_rules.next().unwrap());
                let new_span = Span::new(
                    result.as_span().get_input(),
                    result.as_span().start(),
                    right_atom.as_span().end(),
                )
                .unwrap();
                result = LengthExpr::BinOp {
                    op,
                    left: Box::new(result),
                    right: Box::new(right_atom),
                    span: new_span,
                };
            }
            result
        }
        Rule::length_atom => {
            let inner_rule = pair.into_inner().next().unwrap();
            build_length_expr(inner_rule)
        }
        Rule::size_expr => {
            let mut inner_rules = pair.into_inner();
            let format_name = build_id(inner_rules.next().unwrap());
            LengthExpr::SizeOf { format_name, span }
        }
        Rule::const_int => {
            let value = build_const_int(pair);
            let value: usize = value
                .try_into()
                .unwrap_or_else(|_| panic!("Array length {} does not fit into usize", value));
            LengthExpr::Const { value, span }
        }
        Rule::depend_id => {
            let dep_id = build_dependent_id(pair);
            LengthExpr::Dependent(dep_id)
        }
        _ => unreachable!("Unexpected rule in length_expr: {:?}", pair.as_rule()),
    }
}

fn build_dependent_id(pair: pest::iterators::Pair<Rule>) -> DependentId {
    let span = pair.as_span();
    let full_str = pair.as_str();

    // Parse @root.field1.field2 format
    let without_at = full_str.strip_prefix('@').unwrap();
    let parts: Vec<&str> = without_at.split('.').collect();

    let root = parts[0].to_string();
    let path = parts[1..].iter().map(|s| s.to_string()).collect();

    DependentId { root, path, span }
}

fn build_field(pair: pest::iterators::Pair<Rule>) -> StructField {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::constant => {
            let next_rule = inner_rules.next().unwrap();
            let label = build_id(next_rule);
            let next_rule = inner_rules.next().unwrap();
            let combinator_span = next_rule.as_span();
            let combinator = build_const_combinator(next_rule);
            StructField::Const {
                label,
                combinator,
                span: Span::new(span.get_input(), span.start(), combinator_span.end())
                    .expect("Failed to create span for constant field"),
            }
        }
        Rule::depend_id | Rule::var_id => {
            let mut label = build_id(rule);
            let next_rule = inner_rules.next().unwrap();
            let combinator_span = next_rule.as_span();
            let combinator = build_combinator(next_rule);
            let span = Span::new(span.get_input(), span.start(), combinator_span.end())
                .expect("Failed to create span for struct field");
            if let Some(label_str) = label.name.strip_prefix('@') {
                label.name = label_str.to_string();
                StructField::Dependent {
                    label,
                    combinator,
                    span,
                }
            } else {
                StructField::Ordinary {
                    label,
                    combinator,
                    span,
                }
            }
        }
        _ => unreachable!(),
    }
}

fn build_params(pair: pest::iterators::Pair<'_, Rule>) -> Vec<Param<'_>> {
    pair.into_inner().map(build_param).collect()
}

fn build_param(pair: pest::iterators::Pair<Rule>) -> Param {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let rule_kind = rule.as_rule();
    let mut name = build_id(rule);
    match rule_kind {
        Rule::depend_id => {
            name.name = name.name.strip_prefix('@').unwrap().to_string();
            Param::Dependent(name)
        }
        _ => unreachable!(),
    }
}

fn build_combinator_invocation(pair: pest::iterators::Pair<Rule>) -> CombinatorInvocation {
    let span = pair.as_span();
    let mut inner_rules = pair.into_inner();
    let func = build_id(inner_rules.next().unwrap());
    let args = inner_rules.next().map(build_params).unwrap_or_default();
    CombinatorInvocation { func, args, span }
}

fn build_enum(pair: pest::iterators::Pair<Rule>) -> Enum {
    let mut inner_rules = pair.into_inner();
    let next_rule = inner_rules.next().unwrap();
    let name = build_id(next_rule);
    let next_rule = inner_rules.next().unwrap();
    let value_span = next_rule.as_span();
    let (value, type_annotation) = build_typed_const_int(next_rule);
    // Create a span that covers the entire enum
    let span = Span::new(name.span.get_input(), name.span.start(), value_span.end())
        .expect("Failed to create span for enum");
    Enum {
        name,
        value,
        type_annotation,
        span,
    }
}

fn build_typed_const_int(pair: pest::iterators::Pair<Rule>) -> (i128, Option<IntCombinator>) {
    let mut inner_rules = pair.into_inner();
    let const_int_pair = inner_rules.next().unwrap();
    let value = build_const_int(const_int_pair);
    let type_annotation = inner_rules.next().map(build_int_type_suffix);
    (value, type_annotation)
}

fn build_int_type_suffix(pair: pest::iterators::Pair<Rule>) -> IntCombinator {
    let s = pair.as_str();
    let (sign, width_str) = s.split_at(1);
    let width: u8 = width_str.parse().unwrap();
    match sign {
        "u" => IntCombinator::Unsigned(width),
        "i" => IntCombinator::Signed(width),
        _ => unreachable!(),
    }
}

fn build_choices<'i>(inner_rules: pest::iterators::Pairs<'i, Rule>) -> Choices<'i> {
    // peak the first variant
    let choice_variant = inner_rules
        .peek()
        .unwrap()
        .into_inner()
        .peek()
        .unwrap()
        .as_rule();
    match choice_variant {
        Rule::variant_id => {
            let parse_enum_choice = |pair: pest::iterators::Pair<'i, Rule>| {
                let mut inner_rules = pair.into_inner();
                let name = build_id(inner_rules.next().unwrap());
                let combinator = build_combinator(inner_rules.next().unwrap());
                (name, combinator)
            };
            let choices = inner_rules.map(parse_enum_choice).collect();
            Choices::Enums(choices)
        }
        Rule::constraint_elem => {
            let parse_int_choice = |pair: pest::iterators::Pair<'i, Rule>| {
                let mut inner_rules = pair.into_inner();
                match inner_rules.peek().unwrap().as_rule() {
                    Rule::constraint_elem => {
                        let pattern = build_constraint_elem(inner_rules.next().unwrap());
                        let combinator = build_combinator(inner_rules.next().unwrap());
                        (Some(pattern), combinator)
                    }
                    Rule::variant_id => {
                        let name = inner_rules.next().unwrap().as_str();
                        let combinator = build_combinator(inner_rules.next().unwrap());
                        if name == "_" {
                            (None, combinator)
                        } else {
                            panic!("Invalid pattern for int choice: {}", name)
                        }
                    }
                    _ => unreachable!(),
                }
            };
            let choices = inner_rules.map(parse_int_choice).collect();
            Choices::Ints(choices)
        }
        Rule::const_array => {
            let parse_array_choice = |pair: pest::iterators::Pair<'i, Rule>| {
                let mut inner_rules = pair.into_inner();
                match inner_rules.peek().unwrap().as_rule() {
                    Rule::const_array => {
                        let array = build_const_array(inner_rules.next().unwrap());
                        let combinator = build_combinator(inner_rules.next().unwrap());
                        (array, combinator)
                    }
                    Rule::variant_id => {
                        let name = inner_rules.next().unwrap().as_str();
                        let combinator = build_combinator(inner_rules.next().unwrap());
                        if name == "_" {
                            (ConstArray::Wildcard, combinator)
                        } else {
                            panic!("Invalid pattern for array choice: {}", name)
                        }
                    }
                    _ => unreachable!(),
                }
            };
            let choices = inner_rules.map(parse_array_choice).collect();
            Choices::Arrays(choices)
        }
        _ => unreachable!(),
    }
}

fn build_vec_combinator(pair: pest::iterators::Pair<'_, Rule>) -> VecCombinator<'_> {
    let mut inner_rules = pair.into_inner();
    let _ = inner_rules.next().unwrap();
    let combinator = build_combinator(inner_rules.next().unwrap());
    VecCombinator::Vec(Box::new(combinator))
}

fn build_const_combinator(rule: pest::iterators::Pair<'_, Rule>) -> ConstCombinator<'_> {
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::const_combinator | Rule::inline_const_combinator => {
            build_const_combinator(rule.into_inner().next().unwrap())
        }
        Rule::const_bytes_combinator => {
            let mut inner_rules = rule.into_inner();
            let len = build_const_int(inner_rules.next().unwrap());
            let len: usize = len
                .try_into()
                .unwrap_or_else(|_| panic!("length {} does not fit into usize", len));
            let values = build_const_array(inner_rules.next().unwrap());
            ConstCombinator::ConstBytes(ConstBytesCombinator { len, values, span })
        }
        Rule::const_enum_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = build_combinator_invocation(inner_rules.next().unwrap());
            let variant = build_id(inner_rules.next().unwrap());
            ConstCombinator::ConstEnum(ConstEnumCombinator {
                combinator,
                variant,
                span,
            })
        }
        Rule::const_int_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = build_int_combinator(inner_rules.next().unwrap());
            let value = build_const_int(inner_rules.next().unwrap());
            ConstCombinator::ConstInt(ConstIntCombinator {
                combinator,
                value,
                span,
            })
        }
        Rule::const_id => ConstCombinator::ConstCombinatorInvocation {
            name: build_id(rule),
            span: span.clone(),
        },
        _ => unreachable!(),
    }
}

fn build_enum_constraint(pair: pest::iterators::Pair<'_, Rule>) -> EnumConstraint<'_> {
    let span = pair.as_span();
    match pair.as_rule() {
        Rule::enum_constraint_elem => {
            let mut inner = pair.into_inner();
            let ident = build_id(inner.next().unwrap());
            EnumConstraint::Single { elem: ident, span }
        }
        Rule::enum_constraint_set => {
            let elems = pair
                .into_inner()
                .map(|p| build_id(p.into_inner().next().unwrap()))
                .collect();
            EnumConstraint::Set(elems)
        }
        Rule::enum_constraint => {
            let mut inner = pair.into_inner();
            let first = inner.next().unwrap();
            match first.as_rule() {
                Rule::enum_constraint_elem | Rule::enum_constraint_set => {
                    build_enum_constraint(first)
                }
                Rule::enum_constraint => {
                    EnumConstraint::Neg(Box::new(build_enum_constraint(first)))
                }
                Rule::variant_id => {
                    let ident = build_id(first);
                    EnumConstraint::Single { elem: ident, span }
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

fn build_const_array(pair: pest::iterators::Pair<'_, Rule>) -> ConstArray<'_> {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let span = rule.as_span();
    match rule.as_rule() {
        Rule::const_char_array => {
            // strip leading and trailing quotes
            let str = &rule.as_str();
            let str = &str[1..str.len() - 1];
            ConstArray::Char {
                chars: str.as_bytes().to_vec(),
                span,
            }
        }
        Rule::const_int_array => {
            let mut inner_rules = rule.into_inner();
            let next_rule = inner_rules.next().unwrap();
            match next_rule.as_rule() {
                Rule::int_array_expr => ConstArray::Int {
                    ints: next_rule.into_inner().map(build_const_int).collect(),
                    span,
                },
                Rule::repeat_int_array_expr => {
                    let mut inner_rules = next_rule.into_inner();
                    let value = build_const_int(inner_rules.next().unwrap());
                    let count = build_const_int(inner_rules.next().unwrap());
                    let count: usize = count
                        .try_into()
                        .unwrap_or_else(|_| panic!("length {} does not fit into usize", count));
                    ConstArray::Repeat {
                        repeat: value,
                        count,
                        span,
                    }
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}
