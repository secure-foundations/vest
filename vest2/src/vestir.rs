use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

// ============================================================
// Top-level definitions
// ============================================================

#[derive(Debug, Clone)]
pub enum Definition {
    StructDef {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: StructCombinator,
    },
    ChoiceDef {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: ChoiceCombinator,
    },
    EnumDef {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: EnumCombinator,
    },
    CombinatorDef {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: Combinator,
    },
    ConstCombinatorDef {
        name: String,
        const_combinator: ConstCombinator,
    },
    Endianess(Endianess),
}

impl Definition {
    pub fn name(&self) -> Option<&str> {
        match self {
            Definition::StructDef { name, .. }
            | Definition::ChoiceDef { name, .. }
            | Definition::EnumDef { name, .. }
            | Definition::CombinatorDef { name, .. }
            | Definition::ConstCombinatorDef { name, .. } => Some(name.as_str()),
            Definition::Endianess(_) => None,
        }
    }

    pub fn param_defns(&self) -> &[ParamDefn] {
        match self {
            Definition::StructDef { param_defns, .. }
            | Definition::ChoiceDef { param_defns, .. }
            | Definition::EnumDef { param_defns, .. }
            | Definition::CombinatorDef { param_defns, .. } => param_defns.as_slice(),
            _ => &[],
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Endianess {
    Little,
    Big,
}

// ============================================================
// Parameters
// ============================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParamDefn {
    Dependent {
        name: String,
        combinator: Combinator,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Param {
    Dependent(String),
}

// ============================================================
// Format Combinators
// (Struct, Choice, and Enum only appear at Definition level)
// ============================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Combinator {
    ConstraintInt(ConstraintIntCombinator),
    ConstraintEnum(ConstraintEnumCombinator),
    Wrap(WrapCombinator),
    Vec(VecCombinator),
    Array(ArrayCombinator),
    Bytes(BytesCombinator),
    Tail(TailCombinator),
    Option(OptionCombinator),
    Invocation(CombinatorInvocation),
    /// `lhs >>= rhs`
    AndThen(Box<Combinator>, Box<Combinator>),
}

// ============================================================
// Sub-combinator types
// ============================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstraintIntCombinator {
    pub combinator: IntCombinator,
    pub constraint: Option<IntConstraint>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntCombinator {
    Signed(u8),
    Unsigned(u8),
    BtcVarint,
    ULEB128,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IntConstraint {
    Single(ConstraintElem),
    Set(Vec<ConstraintElem>),
    Neg(Box<IntConstraint>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstraintEnumCombinator {
    pub combinator: CombinatorInvocation,
    pub constraint: EnumConstraint,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EnumConstraint {
    Single(String),
    Set(Vec<String>),
    Neg(Box<EnumConstraint>),
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum ConstraintElem {
    Range {
        start: Option<i128>,
        end: Option<i128>,
    },
    Single(i128),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructCombinator(pub Vec<StructField>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StructField {
    Dependent {
        label: String,
        combinator: Combinator,
    },
    Const {
        label: String,
        combinator: ConstCombinator,
    },
    Ordinary {
        label: String,
        combinator: Combinator,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WrapCombinator {
    pub prior: Vec<ConstCombinator>,
    pub combinator: Box<Combinator>,
    pub post: Vec<ConstCombinator>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EnumCombinator {
    Exhaustive {
        enums: Vec<Enum>,
        inferred: IntCombinator,
    },
    NonExhaustive {
        enums: Vec<Enum>,
        inferred: IntCombinator,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Enum {
    pub name: String,
    pub value: i128,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ChoiceCombinator {
    pub depend_id: Option<String>,
    pub choices: Vec<(ChoicePattern, Combinator)>,
}

/// The discriminant pattern of a single choice branch.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChoicePattern {
    Enum(String),
    Int(ConstraintElem),
    Array(ConstArray),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VecCombinator {
    Vec(Box<Combinator>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayCombinator {
    pub combinator: Box<Combinator>,
    pub len: LengthExpr,
}

/// Arithmetic operators for length expressions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
}

/// Length expression for array sizes
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LengthExpr {
    pub ty: IntCombinator,
    pub kind: LengthExprKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LengthExprKind {
    Const(usize),
    Dependent(String),
    SizeOf(String),
    BinOp {
        op: ArithOp,
        left: Box<LengthExpr>,
        right: Box<LengthExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OptionCombinator(pub Box<Combinator>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BytesCombinator {
    pub len: LengthExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TailCombinator;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CombinatorInvocation {
    pub func: String,
    pub args: Vec<Param>,
}

// ============================================================
// Const format combinators
// ============================================================

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstCombinator {
    ConstBytes(ConstBytesCombinator),
    ConstInt(ConstIntCombinator),
    ConstEnum(ConstEnumCombinator),
    ConstCombinatorInvocation(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstBytesCombinator {
    pub len: usize,
    pub values: ConstArray,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstEnumCombinator {
    pub combinator: CombinatorInvocation,
    pub variant: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstArray {
    Char(Vec<u8>),
    Int(Vec<i128>),
    Repeat(i128, usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstIntCombinator {
    pub combinator: IntCombinator,
    pub value: i128,
}

// ============================================================
// Display impls
// ============================================================

impl Display for Definition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Definition::StructDef {
                name,
                param_defns,
                combinator,
            } => {
                write!(f, "{}", name)?;
                if !param_defns.is_empty() {
                    write!(f, "({})", param_defns.iter().join(","))?;
                }
                write!(f, " = {}", combinator)
            }
            Definition::ChoiceDef {
                name,
                param_defns,
                combinator,
            } => {
                write!(f, "{}", name)?;
                if !param_defns.is_empty() {
                    write!(f, "({})", param_defns.iter().join(","))?;
                }
                write!(f, " = {}", combinator)
            }
            Definition::EnumDef {
                name,
                param_defns,
                combinator,
            } => {
                write!(f, "{}", name)?;
                if !param_defns.is_empty() {
                    write!(f, "({})", param_defns.iter().join(","))?;
                }
                write!(f, " = {}", combinator)
            }
            Definition::CombinatorDef {
                name,
                param_defns,
                combinator,
            } => {
                write!(f, "{}", name)?;
                if !param_defns.is_empty() {
                    write!(f, "({})", param_defns.iter().join(","))?;
                }
                write!(f, " = {}", combinator)
            }
            Definition::ConstCombinatorDef {
                name,
                const_combinator,
            } => {
                write!(f, "const {} = {}", name, const_combinator)
            }
            Definition::Endianess(endianess) => match endianess {
                Endianess::Little => write!(f, "!LITTLE_ENDIAN"),
                Endianess::Big => write!(f, "!BIG_ENDIAN"),
            },
        }
    }
}

impl Display for ParamDefn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamDefn::Dependent { name, combinator } => write!(f, "{}:{}", name, combinator),
        }
    }
}

impl Display for Combinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Combinator::ConstraintInt(c) => write!(f, "{}", c),
            Combinator::ConstraintEnum(c) => write!(f, "{}", c),
            Combinator::Wrap(w) => write!(f, "{}", w),
            Combinator::Vec(v) => write!(f, "{}", v),
            Combinator::Array(a) => write!(f, "{}", a),
            Combinator::Bytes(b) => write!(f, "{}", b),
            Combinator::Tail(t) => write!(f, "{}", t),
            Combinator::Option(o) => write!(f, "{}", o),
            Combinator::Invocation(i) => write!(f, "{}", i),
            Combinator::AndThen(lhs, rhs) => write!(f, "{} >>= {}", lhs, rhs),
        }
    }
}

impl Display for ConstraintIntCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.constraint {
            Some(c) => write!(f, "{}_in_{}", self.combinator, c),
            None => write!(f, "{}", self.combinator),
        }
    }
}

impl Display for ConstraintEnumCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}|{}", self.combinator, self.constraint)
    }
}

impl Display for EnumConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnumConstraint::Single(elem) => write!(f, "{}", elem),
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

impl Display for IntConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntConstraint::Single(elem) => write!(f, "{}", elem),
            IntConstraint::Set(set) => {
                write!(f, "{}", set.iter().join("_and_"))
            }
            IntConstraint::Neg(c) => write!(f, "not_{}", c),
        }
    }
}

impl Display for ConstraintElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstraintElem::Range { start, end } => match (start, end) {
                (Some(start), Some(end)) => write!(f, "{}_to_{}", start, end),
                (Some(start), None) => write!(f, "{}_to_max", start),
                (None, Some(end)) => write!(f, "min_to{}", end),
                (None, None) => write!(f, "min_to_max"),
            },
            ConstraintElem::Single(elem) => write!(f, "{}", elem),
        }
    }
}

impl Display for StructCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for field in &self.0 {
            write!(f, "{}", field)?;
            writeln!(f, ",")?;
        }
        write!(f, "}}")
    }
}

impl Display for StructField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StructField::Dependent { label, combinator } => {
                write!(f, "{}:{}", label, combinator)
            }
            StructField::Const { label, combinator } => {
                write!(f, "{}:{}", label, combinator)
            }
            StructField::Ordinary { label, combinator } => {
                write!(f, "{}:{}", label, combinator)
            }
        }
    }
}

impl Display for ConstCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstCombinator::ConstBytes(b) => write!(f, "{}", b),
            ConstCombinator::ConstInt(i) => write!(f, "{}", i),
            ConstCombinator::ConstEnum(e) => write!(f, "{}", e),
            ConstCombinator::ConstCombinatorInvocation(i) => write!(f, "{}", i),
        }
    }
}

impl Display for ConstBytesCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.values)
    }
}

impl Display for ConstEnumCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}={}", self.combinator, self.variant)
    }
}

impl Display for ConstArray {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstArray::Char(bytes) => {
                write!(f, "\"")?;
                for byte in bytes {
                    write!(f, "\\x{:02x}", byte)?;
                }
                write!(f, "\"")
            }
            ConstArray::Int(ints) => {
                write!(f, "[")?;
                for (i, int) in ints.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", int)?;
                }
                write!(f, "]")
            }
            ConstArray::Repeat(value, count) => write!(f, "[{}; {}]", value, count),
        }
    }
}

impl Display for ConstIntCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_{}", self.combinator, self.value)
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Param::Dependent(s) => write!(f, "{}", s),
        }
    }
}

impl Display for WrapCombinator {
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

impl Display for EnumCombinator {
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

impl Display for Enum {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.name, self.value)
    }
}

impl Display for ChoiceCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "choice ")?;
        if let Some(depend_id) = &self.depend_id {
            write!(f, "({})", depend_id)?;
        }
        writeln!(f, "{{")?;
        for (pat, combinator) in &self.choices {
            writeln!(f, "{} => {},", pat, combinator)?;
        }
        write!(f, "}}")
    }
}

impl Display for ChoicePattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChoicePattern::Enum(name) => write!(f, "{}", name),
            ChoicePattern::Int(elem) => write!(f, "{}", elem),
            ChoicePattern::Array(arr) => write!(f, "{}", arr),
            ChoicePattern::Wildcard => write!(f, "_"),
        }
    }
}

impl Display for VecCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VecCombinator::Vec(v) => write!(f, "{}*", v),
        }
    }
}

impl Display for ArrayCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}; {}]", self.combinator, self.len)
    }
}

impl Display for LengthExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            LengthExprKind::Const(n) => write!(f, "{}", n),
            LengthExprKind::Dependent(s) => write!(f, "@{}", s),
            LengthExprKind::SizeOf(name) => write!(f, "|{}|", name),
            LengthExprKind::BinOp { op, left, right } => {
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

impl Display for BytesCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[u8; {}]", self.len)
    }
}

impl Display for TailCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tail")
    }
}

impl Display for OptionCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}?", self.0)
    }
}

impl Display for CombinatorInvocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.func)
        } else {
            write!(f, "{}({})", self.func, self.args.iter().join(","))
        }
    }
}

// ============================================================
// Global context
// ============================================================

#[derive(Debug, Clone)]
pub struct GlobalCtx {
    pub combinators: HashSet<CombinatorSig>,
    pub const_combinators: HashSet<ConstCombinatorSig>,
    pub enums: HashMap<String, EnumCombinator>,
    pub static_sizes: HashMap<String, usize>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CombinatorSig {
    pub name: String,
    pub param_defns: Vec<ParamDefn>,
    /// The resolved "final" type of this combinator (after following any AndThen chain
    /// and resolving Invocation aliases). Stored as a Combinator for uniformity;
    /// it will never be `AndThen` or `Invocation` after resolution.
    pub resolved_combinator: Combinator,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ConstCombinatorSig {
    pub name: String,
    pub resolved_combinator: ConstCombinator,
}

impl GlobalCtx {
    /// Follow `AndThen` to its final RHS and then resolve `Invocation` aliases.
    pub fn resolve<'a>(&'a self, c: &'a Combinator) -> &'a Combinator {
        match c {
            Combinator::AndThen(_, rhs) => self.resolve(rhs),
            Combinator::Invocation(CombinatorInvocation { func, .. }) => {
                let sig = self
                    .combinators
                    .iter()
                    .find(|s| s.name == *func)
                    .unwrap_or_else(|| panic!("Format `{}` is not defined", func));
                &sig.resolved_combinator
            }
            other => other,
        }
    }

    /// Resolve an `Invocation` alias one level (does not follow AndThen).
    pub fn resolve_alias<'a>(&'a self, c: &'a Combinator) -> &'a Combinator {
        match c {
            Combinator::Invocation(CombinatorInvocation { func, .. }) => {
                let sig = self
                    .combinators
                    .iter()
                    .find(|s| s.name == *func)
                    .unwrap_or_else(|| panic!("Format `{}` is not defined", func));
                &sig.resolved_combinator
            }
            other => other,
        }
    }

    pub fn resolve_const<'a>(&'a self, combinator: &'a ConstCombinator) -> &'a ConstCombinator {
        match combinator {
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let const_combinator_sig = self
                    .const_combinators
                    .iter()
                    .find(|sig| sig.name == *name)
                    .unwrap_or_else(|| {
                        panic!("Const format `{}` is not defined", name);
                    });
                &const_combinator_sig.resolved_combinator
            }
            combinator => combinator,
        }
    }
}

// ============================================================
// AST Lowering
// ============================================================

pub mod lowering {
    use crate::ast;
    use crate::type_check::resolve_enum_type;
    use crate::vestir as ir;

    pub fn lower_checked_definitions<'i>(
        ast: &'i [ast::Definition<'i>],
        global_ctx: &'i crate::type_check::GlobalCtx<'i>,
    ) -> Vec<ir::Definition> {
        let lowerer = CheckedLowerer { global_ctx };
        ast.iter()
            .map(|defn| lowerer.lower_definition(defn))
            .collect()
    }

    struct CheckedLowerer<'a, 'i> {
        global_ctx: &'a crate::type_check::GlobalCtx<'i>,
    }

    impl<'a, 'i> CheckedLowerer<'a, 'i> {
        fn lower_definition(&self, d: &ast::Definition<'i>) -> ir::Definition {
            match d {
                ast::Definition::Combinator {
                    name,
                    param_defns,
                    combinator,
                    ..
                } => {
                    let name_str = name.name.clone();
                    let params: Vec<ir::ParamDefn> = param_defns
                        .iter()
                        .map(|param| self.lower_param_defn(param, param_defns, &[]))
                        .collect();
                    match &combinator.inner {
                        ast::CombinatorInner::Struct(s) if combinator.and_then.is_none() => {
                            ir::Definition::StructDef {
                                name: name_str,
                                param_defns: params,
                                combinator: self.lower_struct_combinator(s, param_defns, &[]),
                            }
                        }
                        ast::CombinatorInner::Choice(c) if combinator.and_then.is_none() => {
                            ir::Definition::ChoiceDef {
                                name: name_str,
                                param_defns: params,
                                combinator: self.lower_choice_combinator(c, param_defns, &[]),
                            }
                        }
                        ast::CombinatorInner::Enum(e) if combinator.and_then.is_none() => {
                            ir::Definition::EnumDef {
                                name: name_str,
                                param_defns: params,
                                combinator: self.lower_enum_combinator(e),
                            }
                        }
                        _ => ir::Definition::CombinatorDef {
                            name: name_str,
                            param_defns: params,
                            combinator: self.lower_combinator(combinator, param_defns, &[]),
                        },
                    }
                }
                ast::Definition::ConstCombinator {
                    name,
                    const_combinator,
                    ..
                } => ir::Definition::ConstCombinatorDef {
                    name: name.name.clone(),
                    const_combinator: self.lower_const_combinator(const_combinator),
                },
                ast::Definition::Endianess(e) => {
                    ir::Definition::Endianess(self.lower_endianess(*e))
                }
                ast::Definition::MacroDefn { .. } => unreachable!(
                    "Macro definitions should have been expanded before lowering to IR"
                ),
            }
        }

        fn lower_param_defn(
            &self,
            p: &ast::ParamDefn<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::ParamDefn {
            match p {
                ast::ParamDefn::Dependent {
                    name, combinator, ..
                } => ir::ParamDefn::Dependent {
                    name: name.name.clone(),
                    combinator: self.lower_combinator_inner(combinator, param_defns, local_deps),
                },
            }
        }

        fn lower_combinator(
            &self,
            c: &ast::Combinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::Combinator {
            let lhs = self.lower_combinator_inner(&c.inner, param_defns, local_deps);
            match &c.and_then {
                None => lhs,
                Some(rhs) => ir::Combinator::AndThen(
                    Box::new(lhs),
                    Box::new(self.lower_combinator(rhs, param_defns, local_deps)),
                ),
            }
        }

        fn lower_combinator_inner(
            &self,
            ci: &ast::CombinatorInner<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::Combinator {
            use ast::CombinatorInner as A;
            match ci {
                A::ConstraintInt(x) => {
                    ir::Combinator::ConstraintInt(self.lower_constraint_int_combinator(x))
                }
                A::ConstraintEnum(x) => {
                    ir::Combinator::ConstraintEnum(self.lower_constraint_enum_combinator(x))
                }
                A::Struct(x) => panic!(
                    "Inline Struct in lowering — input must be elaborated first: {:?}",
                    x
                ),
                A::Choice(x) => panic!(
                    "Inline Choice in lowering — input must be elaborated first: {:?}",
                    x
                ),
                A::Enum(x) => panic!(
                    "Inline Enum in lowering — input must be elaborated first: {:?}",
                    x
                ),
                A::Wrap(x) => {
                    ir::Combinator::Wrap(self.lower_wrap_combinator(x, param_defns, local_deps))
                }
                A::Vec(x) => {
                    ir::Combinator::Vec(self.lower_vec_combinator(x, param_defns, local_deps))
                }
                A::Array(x) => {
                    ir::Combinator::Array(self.lower_array_combinator(x, param_defns, local_deps))
                }
                A::Bytes(x) => {
                    ir::Combinator::Bytes(self.lower_bytes_combinator(x, param_defns, local_deps))
                }
                A::Tail(_) => ir::Combinator::Tail(ir::TailCombinator),
                A::Option(x) => ir::Combinator::Option(ir::OptionCombinator(Box::new(
                    self.lower_combinator(&x.0, param_defns, local_deps),
                ))),
                A::Invocation(x) => ir::Combinator::Invocation(self.lower_invocation(x)),
                A::MacroInvocation { .. } => unreachable!(
                    "Macro invocations should have been expanded before lowering to IR"
                ),
            }
        }

        fn lower_struct_combinator(
            &self,
            s: &ast::StructCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::StructCombinator {
            let mut visible = local_deps.to_vec();
            let mut fields = Vec::with_capacity(s.fields.len());
            for field in &s.fields {
                match field {
                    ast::StructField::Dependent {
                        label, combinator, ..
                    } => {
                        fields.push(ir::StructField::Dependent {
                            label: label.name.clone(),
                            combinator: self.lower_combinator(combinator, param_defns, &visible),
                        });
                        visible.push((label.name.clone(), combinator.clone()));
                    }
                    ast::StructField::Const {
                        label, combinator, ..
                    } => {
                        fields.push(ir::StructField::Const {
                            label: label.name.clone(),
                            combinator: self.lower_const_combinator(combinator),
                        });
                    }
                    ast::StructField::Ordinary {
                        label, combinator, ..
                    } => {
                        fields.push(ir::StructField::Ordinary {
                            label: label.name.clone(),
                            combinator: self.lower_combinator(combinator, param_defns, &visible),
                        });
                    }
                }
            }
            ir::StructCombinator(fields)
        }

        fn lower_wrap_combinator(
            &self,
            w: &ast::WrapCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::WrapCombinator {
            ir::WrapCombinator {
                prior: w
                    .prior
                    .iter()
                    .map(|c| self.lower_const_combinator(c))
                    .collect(),
                combinator: Box::new(self.lower_combinator(&w.combinator, param_defns, local_deps)),
                post: w
                    .post
                    .iter()
                    .map(|c| self.lower_const_combinator(c))
                    .collect(),
            }
        }

        fn lower_enum_combinator(&self, e: &ast::EnumCombinator<'i>) -> ir::EnumCombinator {
            match e {
                ast::EnumCombinator::Exhaustive { enums, .. } => ir::EnumCombinator::Exhaustive {
                    enums: enums.iter().map(|e| self.lower_enum(e)).collect(),
                    inferred: self.lower_int_combinator(&resolve_enum_type(enums)),
                },
                ast::EnumCombinator::NonExhaustive { enums, .. } => {
                    ir::EnumCombinator::NonExhaustive {
                        enums: enums.iter().map(|e| self.lower_enum(e)).collect(),
                        inferred: self.lower_int_combinator(&resolve_enum_type(enums)),
                    }
                }
            }
        }

        fn lower_choice_combinator(
            &self,
            c: &ast::ChoiceCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::ChoiceCombinator {
            ir::ChoiceCombinator {
                depend_id: c.depend_id.as_ref().map(|dep| dep.name.clone()),
                choices: match &c.choices {
                    ast::Choices::Enums(v) => v
                        .iter()
                        .map(|(i, c)| {
                            let pat = if i.name == "_" {
                                ir::ChoicePattern::Wildcard
                            } else {
                                ir::ChoicePattern::Enum(i.name.clone())
                            };
                            (pat, self.lower_combinator(c, param_defns, local_deps))
                        })
                        .collect(),
                    ast::Choices::Ints(v) => v
                        .iter()
                        .map(|(ce, c)| {
                            let pat = match ce {
                                Some(elem) => {
                                    ir::ChoicePattern::Int(self.lower_constraint_elem(elem))
                                }
                                None => ir::ChoicePattern::Wildcard,
                            };
                            (pat, self.lower_combinator(c, param_defns, local_deps))
                        })
                        .collect(),
                    ast::Choices::Arrays(v) => v
                        .iter()
                        .map(|(a, c)| {
                            let pat = match a {
                                ast::ConstArray::Wildcard => ir::ChoicePattern::Wildcard,
                                _ => ir::ChoicePattern::Array(self.lower_const_array(a)),
                            };
                            (pat, self.lower_combinator(c, param_defns, local_deps))
                        })
                        .collect(),
                },
            }
        }

        fn lower_vec_combinator(
            &self,
            v: &ast::VecCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::VecCombinator {
            match v {
                ast::VecCombinator::Vec(b) => ir::VecCombinator::Vec(Box::new(
                    self.lower_combinator(b, param_defns, local_deps),
                )),
            }
        }

        fn lower_array_combinator(
            &self,
            a: &ast::ArrayCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::ArrayCombinator {
            ir::ArrayCombinator {
                combinator: Box::new(self.lower_combinator(&a.combinator, param_defns, local_deps)),
                len: self.lower_length_expr(&a.len, param_defns, local_deps),
            }
        }

        fn lower_bytes_combinator(
            &self,
            b: &ast::BytesCombinator<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::BytesCombinator {
            ir::BytesCombinator {
                len: self.lower_length_expr(&b.len, param_defns, local_deps),
            }
        }

        fn lower_length_expr(
            &self,
            len: &ast::LengthExpr<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::LengthExpr {
            let ty = self.infer_length_expr_ty(len, param_defns, local_deps);
            let kind = match len {
                ast::LengthExpr::Const { value, .. } => ir::LengthExprKind::Const(*value),
                ast::LengthExpr::Dependent(dep) => ir::LengthExprKind::Dependent(dep.full_path()),
                ast::LengthExpr::SizeOf { format_name, .. } => {
                    ir::LengthExprKind::SizeOf(format_name.name.clone())
                }
                ast::LengthExpr::BinOp {
                    op, left, right, ..
                } => ir::LengthExprKind::BinOp {
                    op: self.lower_arith_op(*op),
                    left: Box::new(self.lower_length_expr(left, param_defns, local_deps)),
                    right: Box::new(self.lower_length_expr(right, param_defns, local_deps)),
                },
            };
            ir::LengthExpr { ty, kind }
        }

        fn infer_length_expr_ty(
            &self,
            len: &ast::LengthExpr<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::IntCombinator {
            match len {
                ast::LengthExpr::Const { value, .. } => self.const_length_ty(*value),
                ast::LengthExpr::Dependent(dep) => {
                    self.dependent_length_ty(dep, param_defns, local_deps)
                }
                ast::LengthExpr::SizeOf { format_name, .. } => {
                    let size = self
                        .global_ctx
                        .static_sizes
                        .get(&format_name.name)
                        .copied()
                        .unwrap_or_else(|| {
                            panic!(
                                "size-of target `{}` should have a static size after type checking",
                                format_name.name
                            )
                        });
                    self.const_length_ty(size)
                }
                ast::LengthExpr::BinOp { left, right, .. } => self.promote_length_ty(
                    self.infer_length_expr_ty(left, param_defns, local_deps),
                    self.infer_length_expr_ty(right, param_defns, local_deps),
                ),
            }
        }

        fn dependent_length_ty(
            &self,
            dep: &ast::DependentId<'i>,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> ir::IntCombinator {
            let combinator = self
                .resolve_length_dep_combinator(&dep.full_path(), param_defns, local_deps)
                .unwrap_or_else(|| {
                    panic!(
                        "unresolved length dependency `@{}` after type checking",
                        dep.full_path()
                    )
                });
            match self.global_ctx.resolve(&combinator) {
                ast::CombinatorInner::ConstraintInt(ast::ConstraintIntCombinator {
                    combinator,
                    ..
                }) => Self::length_carrier_ty(combinator),
                other => panic!(
                    "length dependency `@{}` should resolve to an unsigned int, got {:?}",
                    dep.full_path(),
                    other
                ),
            }
        }

        fn resolve_length_dep_combinator(
            &self,
            name: &str,
            param_defns: &'i [ast::ParamDefn<'i>],
            local_deps: &[(String, ast::Combinator<'i>)],
        ) -> Option<ast::Combinator<'i>> {
            let parts: Vec<&str> = name.split('.').collect();
            let root = *parts.first()?;
            let mut current =
                if let Some((_, combinator)) = local_deps.iter().rev().find(|(n, _)| n == root) {
                    combinator.clone()
                } else {
                    param_defns.iter().find_map(|param| match param {
                        ast::ParamDefn::Dependent {
                            name,
                            combinator,
                            span,
                        } if name.name == root => Some(ast::Combinator {
                            inner: combinator.clone(),
                            and_then: None,
                            span: *span,
                        }),
                        _ => None,
                    })?
                };

            for field_name in parts.iter().skip(1) {
                let ast::CombinatorInner::Struct(struct_comb) = self.global_ctx.resolve(&current)
                else {
                    return None;
                };
                current = struct_comb.fields.iter().find_map(|field| match field {
                    ast::StructField::Dependent {
                        label, combinator, ..
                    } if label.name == *field_name => Some(combinator.clone()),
                    _ => None,
                })?;
            }

            Some(current)
        }

        fn const_length_ty(&self, value: usize) -> ir::IntCombinator {
            if value <= u8::MAX as usize {
                ir::IntCombinator::Unsigned(8)
            } else if value <= u16::MAX as usize {
                ir::IntCombinator::Unsigned(16)
            } else if value <= u32::MAX as usize {
                ir::IntCombinator::Unsigned(32)
            } else {
                ir::IntCombinator::Unsigned(64)
            }
        }

        fn promote_length_ty(
            &self,
            left: ir::IntCombinator,
            right: ir::IntCombinator,
        ) -> ir::IntCombinator {
            match Self::length_rank(&left).max(Self::length_rank(&right)) {
                0 => ir::IntCombinator::Unsigned(8),
                1 => ir::IntCombinator::Unsigned(16),
                2 => ir::IntCombinator::Unsigned(32),
                3 => ir::IntCombinator::Unsigned(64),
                rank => panic!("invalid length rank {rank}"),
            }
        }

        fn length_rank(ty: &ir::IntCombinator) -> u8 {
            match ty {
                ir::IntCombinator::Unsigned(8) => 0,
                ir::IntCombinator::Unsigned(16) => 1,
                ir::IntCombinator::Unsigned(24) | ir::IntCombinator::Unsigned(32) => 2,
                ir::IntCombinator::Unsigned(64)
                | ir::IntCombinator::BtcVarint
                | ir::IntCombinator::ULEB128 => 3,
                other => panic!("invalid length-carrier type {:?}", other),
            }
        }

        fn length_carrier_ty(combinator: &ast::IntCombinator) -> ir::IntCombinator {
            match combinator {
                ast::IntCombinator::Unsigned(8) => ir::IntCombinator::Unsigned(8),
                ast::IntCombinator::Unsigned(16) => ir::IntCombinator::Unsigned(16),
                ast::IntCombinator::Unsigned(24) | ast::IntCombinator::Unsigned(32) => {
                    ir::IntCombinator::Unsigned(32)
                }
                ast::IntCombinator::Unsigned(64)
                | ast::IntCombinator::BtcVarint
                | ast::IntCombinator::ULEB128 => ir::IntCombinator::Unsigned(64),
                other => panic!("invalid integer type for length expression: {:?}", other),
            }
        }

        fn lower_endianess(&self, e: ast::Endianess) -> ir::Endianess {
            match e {
                ast::Endianess::Little => ir::Endianess::Little,
                ast::Endianess::Big => ir::Endianess::Big,
            }
        }

        fn lower_arith_op(&self, op: ast::ArithOp) -> ir::ArithOp {
            match op {
                ast::ArithOp::Add => ir::ArithOp::Add,
                ast::ArithOp::Sub => ir::ArithOp::Sub,
                ast::ArithOp::Mul => ir::ArithOp::Mul,
                ast::ArithOp::Div => ir::ArithOp::Div,
            }
        }

        fn lower_int_combinator(&self, i: &ast::IntCombinator) -> ir::IntCombinator {
            match i {
                ast::IntCombinator::Signed(n) => ir::IntCombinator::Signed(*n),
                ast::IntCombinator::Unsigned(n) => ir::IntCombinator::Unsigned(*n),
                ast::IntCombinator::BtcVarint => ir::IntCombinator::BtcVarint,
                ast::IntCombinator::ULEB128 => ir::IntCombinator::ULEB128,
            }
        }

        fn lower_constraint_elem(&self, e: &ast::ConstraintElem<'i>) -> ir::ConstraintElem {
            match e {
                ast::ConstraintElem::Range { start, end, .. } => ir::ConstraintElem::Range {
                    start: *start,
                    end: *end,
                },
                ast::ConstraintElem::Single { elem, .. } => ir::ConstraintElem::Single(*elem),
            }
        }

        fn lower_int_constraint(&self, c: &ast::IntConstraint<'i>) -> ir::IntConstraint {
            match c {
                ast::IntConstraint::Single { elem, .. } => {
                    ir::IntConstraint::Single(self.lower_constraint_elem(elem))
                }
                ast::IntConstraint::Set(v) => ir::IntConstraint::Set(
                    v.iter()
                        .map(|elem| self.lower_constraint_elem(elem))
                        .collect(),
                ),
                ast::IntConstraint::Neg(b) => {
                    ir::IntConstraint::Neg(Box::new(self.lower_int_constraint(b)))
                }
            }
        }

        fn lower_enum_constraint(&self, c: &ast::EnumConstraint<'i>) -> ir::EnumConstraint {
            match c {
                ast::EnumConstraint::Single { elem, .. } => {
                    ir::EnumConstraint::Single(elem.name.clone())
                }
                ast::EnumConstraint::Set(v) => {
                    ir::EnumConstraint::Set(v.iter().map(|elem| elem.name.clone()).collect())
                }
                ast::EnumConstraint::Neg(b) => {
                    ir::EnumConstraint::Neg(Box::new(self.lower_enum_constraint(b)))
                }
            }
        }

        fn lower_constraint_int_combinator(
            &self,
            x: &ast::ConstraintIntCombinator<'i>,
        ) -> ir::ConstraintIntCombinator {
            ir::ConstraintIntCombinator {
                combinator: self.lower_int_combinator(&x.combinator),
                constraint: x.constraint.as_ref().map(|c| self.lower_int_constraint(c)),
            }
        }

        fn lower_constraint_enum_combinator(
            &self,
            x: &ast::ConstraintEnumCombinator<'i>,
        ) -> ir::ConstraintEnumCombinator {
            ir::ConstraintEnumCombinator {
                combinator: self.lower_invocation(&x.combinator),
                constraint: self.lower_enum_constraint(&x.constraint),
            }
        }

        fn lower_param(&self, p: &ast::Param<'i>) -> ir::Param {
            match p {
                ast::Param::Dependent(i) => ir::Param::Dependent(i.name.clone()),
            }
        }

        fn lower_invocation(&self, ci: &ast::CombinatorInvocation<'i>) -> ir::CombinatorInvocation {
            ir::CombinatorInvocation {
                func: ci.func.name.clone(),
                args: ci.args.iter().map(|p| self.lower_param(p)).collect(),
            }
        }

        fn lower_enum(&self, e: &ast::Enum<'i>) -> ir::Enum {
            ir::Enum {
                name: e.name.name.clone(),
                value: e.value,
            }
        }

        fn lower_const_array(&self, a: &ast::ConstArray<'i>) -> ir::ConstArray {
            match a {
                ast::ConstArray::Char { chars, .. } => ir::ConstArray::Char(chars.clone()),
                ast::ConstArray::Int { ints, .. } => ir::ConstArray::Int(ints.clone()),
                ast::ConstArray::Repeat { repeat, count, .. } => {
                    ir::ConstArray::Repeat(*repeat, *count)
                }
                ast::ConstArray::Wildcard => unreachable!("Wildcard in const array lowering"),
            }
        }

        fn lower_const_bytes_combinator(
            &self,
            c: &ast::ConstBytesCombinator<'i>,
        ) -> ir::ConstBytesCombinator {
            ir::ConstBytesCombinator {
                len: c.len,
                values: self.lower_const_array(&c.values),
            }
        }

        fn lower_const_enum_combinator(
            &self,
            c: &ast::ConstEnumCombinator<'i>,
        ) -> ir::ConstEnumCombinator {
            ir::ConstEnumCombinator {
                combinator: self.lower_invocation(&c.combinator),
                variant: c.variant.name.clone(),
            }
        }

        fn lower_const_int_combinator(
            &self,
            c: &ast::ConstIntCombinator<'i>,
        ) -> ir::ConstIntCombinator {
            ir::ConstIntCombinator {
                combinator: self.lower_int_combinator(&c.combinator),
                value: c.value,
            }
        }

        fn lower_const_combinator(&self, c: &ast::ConstCombinator<'i>) -> ir::ConstCombinator {
            match c {
                ast::ConstCombinator::ConstBytes(x) => {
                    ir::ConstCombinator::ConstBytes(self.lower_const_bytes_combinator(x))
                }
                ast::ConstCombinator::ConstInt(x) => {
                    ir::ConstCombinator::ConstInt(self.lower_const_int_combinator(x))
                }
                ast::ConstCombinator::ConstEnum(x) => {
                    ir::ConstCombinator::ConstEnum(self.lower_const_enum_combinator(x))
                }
                ast::ConstCombinator::ConstCombinatorInvocation { name, .. } => {
                    ir::ConstCombinator::ConstCombinatorInvocation(name.name.clone())
                }
            }
        }
    }

    impl<'i> From<&crate::type_check::GlobalCtx<'i>> for ir::GlobalCtx {
        fn from(src: &crate::type_check::GlobalCtx<'i>) -> Self {
            use std::collections::{HashMap, HashSet};

            let lowerer = CheckedLowerer { global_ctx: src };
            let combinators: HashSet<ir::CombinatorSig> = src
                .combinators
                .iter()
                .map(|sig| {
                    let name = sig.name.name.clone();
                    let resolved_combinator = match &sig.resolved_combinator {
                        ast::CombinatorInner::Struct(_)
                        | ast::CombinatorInner::Choice(_)
                        | ast::CombinatorInner::Enum(_) => {
                            ir::Combinator::Invocation(ir::CombinatorInvocation {
                                func: name.clone(),
                                args: vec![],
                            })
                        }
                        _ => lowerer.lower_combinator_inner(
                            &sig.resolved_combinator,
                            sig.param_defns,
                            &[],
                        ),
                    };
                    ir::CombinatorSig {
                        name,
                        param_defns: sig
                            .param_defns
                            .iter()
                            .map(|param| lowerer.lower_param_defn(param, sig.param_defns, &[]))
                            .collect(),
                        resolved_combinator,
                    }
                })
                .collect();

            let const_combinators: HashSet<ir::ConstCombinatorSig> = src
                .const_combinators
                .iter()
                .map(|sig| ir::ConstCombinatorSig {
                    name: sig.name.name.clone(),
                    resolved_combinator: lowerer.lower_const_combinator(&sig.resolved_combinator),
                })
                .collect();

            let enums: HashMap<String, ir::EnumCombinator> = src
                .enums
                .iter()
                .map(|(k, v)| (k.to_string(), lowerer.lower_enum_combinator(v)))
                .collect();

            ir::GlobalCtx {
                combinators,
                const_combinators,
                enums,
                static_sizes: src.static_sizes.clone(),
            }
        }
    }
}
