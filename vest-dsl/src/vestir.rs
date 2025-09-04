use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

#[derive(Debug, Clone)]
pub enum Definition {
    Combinator {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: Combinator,
    },
    ConstCombinator {
        name: String,
        const_combinator: ConstCombinator,
    },
    Endianess(Endianess),
}

#[derive(Debug, Clone, Copy)]
pub enum Endianess {
    Little,
    Big,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParamDefn {
    Dependent {
        name: String,
        combinator: CombinatorInner,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Combinator {
    pub inner: CombinatorInner,
    pub and_then: Option<Box<Combinator>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CombinatorInner {
    ConstraintInt(ConstraintIntCombinator),
    Struct(StructCombinator),
    Wrap(WrapCombinator),
    Enum(EnumCombinator),
    Choice(ChoiceCombinator),
    SepBy(SepByCombinator),
    Vec(VecCombinator),
    Array(ArrayCombinator),
    Bytes(BytesCombinator),
    Tail(TailCombinator),
    Apply(ApplyCombinator),
    Option(OptionCombinator),
    Invocation(CombinatorInvocation),
}

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
pub enum Param {
    Stream(String),
    Dependent(String),
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
    // pub choices: Vec<Choice>,
    pub choices: Choices,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Choices {
    Enums(Vec<(String, Combinator)>),
    Ints(Vec<(Option<ConstraintElem>, Combinator)>),
    Arrays(Vec<(ConstArray, Combinator)>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VecCombinator {
    Vec(Box<Combinator>),
    Vec1(Box<Combinator>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SepByCombinator {
    pub combinator: VecCombinator,
    pub sep: ConstCombinator,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayCombinator {
    pub combinator: Box<Combinator>,
    pub len: LengthSpecifier,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LengthSpecifier {
    Const(usize),
    Dependent(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OptionCombinator(pub Box<Combinator>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BytesCombinator {
    pub len: LengthSpecifier,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TailCombinator;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ApplyCombinator {
    pub stream: String,
    pub combinator: Box<Combinator>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CombinatorInvocation {
    pub func: String,
    pub args: Vec<Param>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstCombinator {
    Vec(Box<ConstCombinator>),
    ConstArray(ConstArrayCombinator),
    ConstBytes(ConstBytesCombinator),
    ConstInt(ConstIntCombinator),
    ConstStruct(ConstStructCombinator),
    ConstChoice(ConstChoiceCombinator),
    ConstCombinatorInvocation(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstArrayCombinator {
    pub combinator: IntCombinator,
    pub len: usize,
    pub values: ConstArray,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstBytesCombinator {
    pub len: usize,
    pub values: ConstArray,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstArray {
    Char(Vec<u8>),
    Int(Vec<i128>),
    Repeat(i128, usize),
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstIntCombinator {
    pub combinator: IntCombinator,
    pub value: i128,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstStructCombinator(pub Vec<ConstCombinator>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstChoiceCombinator(pub Vec<ConstChoice>);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstChoice {
    pub tag: String,
    pub combinator: ConstCombinator,
}

impl Display for Definition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Definition::Combinator {
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
            Definition::ConstCombinator {
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
        write!(f, "{}", self.inner)?;
        if let Some(next) = &self.and_then {
            write!(f, " >>= {}", next)?;
        }
        Ok(())
    }
}

impl Display for CombinatorInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CombinatorInner::ConstraintInt(c) => write!(f, "{}", c),
            CombinatorInner::Struct(s) => write!(f, "{}", s),
            CombinatorInner::Wrap(w) => write!(f, "{}", w),
            CombinatorInner::Enum(e) => write!(f, "{}", e),
            CombinatorInner::Choice(c) => write!(f, "{}", c),
            CombinatorInner::SepBy(s) => write!(f, "{}", s),
            CombinatorInner::Vec(v) => write!(f, "{}", v),
            CombinatorInner::Array(a) => write!(f, "{}", a),
            CombinatorInner::Bytes(a) => write!(f, "{}", a),
            CombinatorInner::Tail(t) => write!(f, "{}", t),
            CombinatorInner::Apply(a) => write!(f, "{}", a),
            CombinatorInner::Option(o) => write!(f, "{}", o),
            CombinatorInner::Invocation(i) => write!(f, "{}", i),
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
            ConstCombinator::Vec(v) => write!(f, "{}", v),
            ConstCombinator::ConstArray(a) => write!(f, "{}", a),
            ConstCombinator::ConstBytes(b) => write!(f, "{}", b),
            ConstCombinator::ConstInt(i) => write!(f, "{}", i),
            ConstCombinator::ConstStruct(s) => write!(f, "{}", s),
            ConstCombinator::ConstChoice(c) => write!(f, "{}", c),
            ConstCombinator::ConstCombinatorInvocation(i) => write!(f, "{}", i),
        }
    }
}

impl Display for ConstArrayCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.values)
    }
}

impl Display for ConstBytesCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.values)
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
            ConstArray::Wildcard => write!(f, "_"),
        }
    }
}

impl Display for ConstIntCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_{}", self.combinator, self.value)
    }
}

impl Display for ConstStructCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for combinator in &self.0 {
            write!(f, "{}", combinator)?;
        }
        write!(f, "}}")
    }
}

impl Display for ConstChoiceCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for choice in &self.0 {
            write!(f, "{}", choice)?;
        }
        write!(f, "}}")
    }
}

impl Display for ConstChoice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.tag, self.combinator)
    }
}

impl Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Param::Stream(s) => write!(f, "${}", s),
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
        write!(f, "{}", self.choices)?;
        write!(f, "}}")
    }
}

impl Display for Choices {
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

impl Display for SepByCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_sepby_{}", self.combinator, self.sep)
    }
}

impl Display for VecCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VecCombinator::Vec(v) => write!(f, "{}*", v),
            VecCombinator::Vec1(v) => write!(f, "{}+", v),
        }
    }
}

impl Display for ArrayCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}; {}]", self.combinator, self.len)
    }
}

impl Display for LengthSpecifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LengthSpecifier::Const(n) => write!(f, "{}", n),
            LengthSpecifier::Dependent(s) => write!(f, "{}", s),
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

impl Display for ApplyCombinator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.stream, self.combinator)
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

#[derive(Debug, Clone)]
pub struct GlobalCtx {
    pub combinators: HashSet<CombinatorSig>,
    pub const_combinators: HashSet<ConstCombinatorSig>,
    pub enums: HashMap<String, EnumCombinator>,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CombinatorSig {
    pub name: String,
    pub param_defns: Vec<ParamDefn>,
    pub resolved_combinator: CombinatorInner,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ConstCombinatorSig {
    pub name: String,
    pub resolved_combinator: ConstCombinator,
}

impl GlobalCtx {
    pub fn resolve<'a>(&'a self, c: &'a Combinator) -> &'a CombinatorInner {
        if let Some(next) = &c.and_then {
            self.resolve(next)
        } else {
            self.resolve_alias(&c.inner)
        }
    }

    pub fn resolve_alias<'a>(&'a self, inner: &'a CombinatorInner) -> &'a CombinatorInner {
        use CombinatorInner::*;
        match inner {
            Invocation(CombinatorInvocation { func, .. }) => {
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

pub mod lowering {
    use crate::ast;
    use crate::type_check::infer_enum_type;
    use crate::vestir as ir;

    #[inline]
    fn id<'i>(x: ast::Identifier<'i>) -> String {
        x.name
    }

    // ---------- Top-level ----------
    impl<'i> From<ast::Definition<'i>> for ir::Definition {
        fn from(d: ast::Definition<'i>) -> Self {
            match d {
                ast::Definition::Combinator {
                    name,
                    param_defns,
                    combinator,
                    ..
                } => ir::Definition::Combinator {
                    name: id(name),
                    param_defns: param_defns.into_iter().map(Into::into).collect(),
                    combinator: combinator.into(),
                },
                ast::Definition::ConstCombinator {
                    name,
                    const_combinator,
                    ..
                } => ir::Definition::ConstCombinator {
                    name: id(name),
                    const_combinator: const_combinator.into(),
                },
                ast::Definition::Endianess(e) => ir::Definition::Endianess(e.into()),
                ast::Definition::SecCombinator { .. } => {
                    unimplemented!("Secret format is not supported by VestDSL yet")
                }
                ast::Definition::MacroDefn { .. } => unreachable!(
                    "Macro definitions should have been expanded before lowering to IR"
                ),
            }
        }
    }

    impl From<ast::Endianess> for ir::Endianess {
        fn from(e: ast::Endianess) -> Self {
            match e {
                ast::Endianess::Little => ir::Endianess::Little,
                ast::Endianess::Big => ir::Endianess::Big,
            }
        }
    }

    // ---------- Params / ParamDefns ----------
    impl<'i> From<ast::ParamDefn<'i>> for ir::ParamDefn {
        fn from(p: ast::ParamDefn<'i>) -> Self {
            match p {
                ast::ParamDefn::Stream { .. } => {
                    unimplemented!("Stream transformations are not supported by VestDSL yet")
                }
                ast::ParamDefn::Dependent {
                    name, combinator, ..
                } => ir::ParamDefn::Dependent {
                    name: id(name),
                    combinator: combinator.into(),
                },
            }
        }
    }

    impl<'i> From<ast::Param<'i>> for ir::Param {
        fn from(p: ast::Param<'i>) -> Self {
            match p {
                ast::Param::Stream(i) => ir::Param::Stream(id(i)),
                ast::Param::Dependent(i) => ir::Param::Dependent(id(i)),
            }
        }
    }

    // ---------- Combinators ----------
    impl<'i> From<ast::Combinator<'i>> for ir::Combinator {
        fn from(c: ast::Combinator<'i>) -> Self {
            ir::Combinator {
                inner: c.inner.into(),
                and_then: c.and_then.map(|b| Box::new((*b).into())),
            }
        }
    }

    impl<'i> From<ast::CombinatorInner<'i>> for ir::CombinatorInner {
        fn from(ci: ast::CombinatorInner<'i>) -> Self {
            use ast::CombinatorInner as A;
            use ir::CombinatorInner as B;
            match ci {
                A::ConstraintInt(x) => B::ConstraintInt(x.into()),
                A::Struct(x) => B::Struct(x.into()),
                A::Wrap(x) => B::Wrap(x.into()),
                A::Enum(x) => B::Enum(x.into()),
                A::Choice(x) => B::Choice(x.into()),
                A::SepBy(x) => B::SepBy(x.into()),
                A::Vec(x) => B::Vec(x.into()),
                A::Array(x) => B::Array(x.into()),
                A::Bytes(x) => B::Bytes(x.into()),
                A::Tail(_x) => B::Tail(ir::TailCombinator),
                A::Apply(x) => B::Apply(x.into()),
                A::Option(x) => B::Option(ir::OptionCombinator(Box::new((*x.0).clone().into()))),
                A::Invocation(x) => B::Invocation(x.into()),
                A::MacroInvocation { .. } => unreachable!(
                    "Macro invocations should have been expanded before lowering to IR"
                ),
            }
        }
    }

    // ---------- Ints / Constraints ----------
    impl<'i> From<ast::ConstraintIntCombinator<'i>> for ir::ConstraintIntCombinator {
        fn from(x: ast::ConstraintIntCombinator<'i>) -> Self {
            ir::ConstraintIntCombinator {
                combinator: x.combinator.into(),
                constraint: x.constraint.map(Into::into),
            }
        }
    }

    impl From<ast::IntCombinator> for ir::IntCombinator {
        fn from(i: ast::IntCombinator) -> Self {
            match i {
                ast::IntCombinator::Signed(n) => ir::IntCombinator::Signed(n),
                ast::IntCombinator::Unsigned(n) => ir::IntCombinator::Unsigned(n),
                ast::IntCombinator::BtcVarint => ir::IntCombinator::BtcVarint,
                ast::IntCombinator::ULEB128 => ir::IntCombinator::ULEB128,
            }
        }
    }

    impl<'i> From<ast::IntConstraint<'i>> for ir::IntConstraint {
        fn from(c: ast::IntConstraint<'i>) -> Self {
            match c {
                ast::IntConstraint::Single { elem, .. } => ir::IntConstraint::Single(elem.into()),
                ast::IntConstraint::Set(v) => {
                    ir::IntConstraint::Set(v.into_iter().map(Into::into).collect())
                }
                ast::IntConstraint::Neg(b) => ir::IntConstraint::Neg(Box::new((*b).into())),
            }
        }
    }

    impl<'i> From<ast::ConstraintElem<'i>> for ir::ConstraintElem {
        fn from(e: ast::ConstraintElem<'i>) -> Self {
            match e {
                ast::ConstraintElem::Range { start, end, .. } => {
                    ir::ConstraintElem::Range { start, end }
                }
                ast::ConstraintElem::Single { elem, .. } => ir::ConstraintElem::Single(elem),
            }
        }
    }

    // ---------- Struct ----------
    impl<'i> From<ast::StructCombinator<'i>> for ir::StructCombinator {
        fn from(s: ast::StructCombinator<'i>) -> Self {
            ir::StructCombinator(s.fields.into_iter().map(Into::into).collect())
        }
    }

    impl<'i> From<ast::StructField<'i>> for ir::StructField {
        fn from(f: ast::StructField<'i>) -> Self {
            match f {
                ast::StructField::Stream(..) => {
                    unimplemented!("Stream transformations are not supported by VestDSL yet")
                }
                ast::StructField::Dependent {
                    label, combinator, ..
                } => ir::StructField::Dependent {
                    label: id(label),
                    combinator: combinator.into(),
                },
                ast::StructField::Const {
                    label, combinator, ..
                } => ir::StructField::Const {
                    label: id(label),
                    combinator: combinator.into(),
                },
                ast::StructField::Ordinary {
                    label, combinator, ..
                } => ir::StructField::Ordinary {
                    label: id(label),
                    combinator: combinator.into(),
                },
            }
        }
    }

    // ---------- Wrap ----------
    impl<'i> From<ast::WrapCombinator<'i>> for ir::WrapCombinator {
        fn from(w: ast::WrapCombinator<'i>) -> Self {
            ir::WrapCombinator {
                prior: w.prior.into_iter().map(Into::into).collect(),
                combinator: Box::new((*w.combinator).into()),
                post: w.post.into_iter().map(Into::into).collect(),
            }
        }
    }

    // ---------- Enum ----------
    impl<'i> From<ast::EnumCombinator<'i>> for ir::EnumCombinator {
        fn from(e: ast::EnumCombinator<'i>) -> Self {
            match e {
                ast::EnumCombinator::Exhaustive { enums, .. } => ir::EnumCombinator::Exhaustive {
                    enums: enums.clone().into_iter().map(Into::into).collect(),
                    inferred: infer_enum_type(&enums).into(),
                },
                ast::EnumCombinator::NonExhaustive { enums, .. } => {
                    ir::EnumCombinator::NonExhaustive {
                        enums: enums.clone().into_iter().map(Into::into).collect(),
                        inferred: infer_enum_type(&enums).into(),
                    }
                }
            }
        }
    }

    impl<'i> From<ast::Enum<'i>> for ir::Enum {
        fn from(e: ast::Enum<'i>) -> Self {
            ir::Enum {
                name: id(e.name),
                value: e.value,
            }
        }
    }

    // ---------- Choice ----------
    impl<'i> From<ast::ChoiceCombinator<'i>> for ir::ChoiceCombinator {
        fn from(c: ast::ChoiceCombinator<'i>) -> Self {
            ir::ChoiceCombinator {
                depend_id: c.depend_id.map(id),
                choices: c.choices.into(),
            }
        }
    }

    impl<'i> From<ast::Choices<'i>> for ir::Choices {
        fn from(ch: ast::Choices<'i>) -> Self {
            match ch {
                ast::Choices::Enums(v) => {
                    ir::Choices::Enums(v.into_iter().map(|(i, c)| (id(i), c.into())).collect())
                }
                ast::Choices::Ints(v) => ir::Choices::Ints(
                    v.into_iter()
                        .map(|(ce, c)| (ce.map(Into::into), c.into()))
                        .collect(),
                ),
                ast::Choices::Arrays(v) => {
                    ir::Choices::Arrays(v.into_iter().map(|(a, c)| (a.into(), c.into())).collect())
                }
            }
        }
    }

    // ---------- Vec / SepBy ----------
    impl<'i> From<ast::VecCombinator<'i>> for ir::VecCombinator {
        fn from(v: ast::VecCombinator<'i>) -> Self {
            match v {
                ast::VecCombinator::Vec(b) => ir::VecCombinator::Vec(Box::new((*b).into())),
                ast::VecCombinator::Vec1(b) => ir::VecCombinator::Vec1(Box::new((*b).into())),
            }
        }
    }

    impl<'i> From<ast::SepByCombinator<'i>> for ir::SepByCombinator {
        fn from(s: ast::SepByCombinator<'i>) -> Self {
            ir::SepByCombinator {
                combinator: s.combinator.into(),
                sep: s.sep.into(),
            }
        }
    }

    // ---------- Array / Bytes / Tail / Apply / Option ----------
    impl<'i> From<ast::ArrayCombinator<'i>> for ir::ArrayCombinator {
        fn from(a: ast::ArrayCombinator<'i>) -> Self {
            ir::ArrayCombinator {
                combinator: Box::new((*a.combinator).into()),
                len: a.len.into(),
            }
        }
    }

    impl<'i> From<ast::LengthSpecifier<'i>> for ir::LengthSpecifier {
        fn from(l: ast::LengthSpecifier<'i>) -> Self {
            match l {
                ast::LengthSpecifier::Const(n) => ir::LengthSpecifier::Const(n),
                ast::LengthSpecifier::Dependent(i) => ir::LengthSpecifier::Dependent(id(i)),
            }
        }
    }

    impl<'i> From<ast::BytesCombinator<'i>> for ir::BytesCombinator {
        fn from(b: ast::BytesCombinator<'i>) -> Self {
            ir::BytesCombinator { len: b.len.into() }
        }
    }

    impl<'i> From<ast::TailCombinator<'i>> for ir::TailCombinator {
        fn from(_: ast::TailCombinator<'i>) -> Self {
            ir::TailCombinator
        }
    }

    impl<'i> From<ast::ApplyCombinator<'i>> for ir::ApplyCombinator {
        fn from(a: ast::ApplyCombinator<'i>) -> Self {
            ir::ApplyCombinator {
                stream: id(a.stream),
                combinator: Box::new((*a.combinator).into()),
            }
        }
    }

    impl<'i> From<ast::OptionCombinator<'i>> for ir::OptionCombinator {
        fn from(o: ast::OptionCombinator<'i>) -> Self {
            ir::OptionCombinator(Box::new((*o.0).into()))
        }
    }

    impl<'i> From<ast::CombinatorInvocation<'i>> for ir::CombinatorInvocation {
        fn from(ci: ast::CombinatorInvocation<'i>) -> Self {
            ir::CombinatorInvocation {
                func: id(ci.func),
                args: ci.args.into_iter().map(Into::into).collect(),
            }
        }
    }

    // ---------- Consts ----------
    impl<'i> From<ast::ConstCombinator<'i>> for ir::ConstCombinator {
        fn from(c: ast::ConstCombinator<'i>) -> Self {
            match c {
                ast::ConstCombinator::Vec(b) => ir::ConstCombinator::Vec(Box::new((*b).into())),
                ast::ConstCombinator::ConstArray(x) => ir::ConstCombinator::ConstArray(x.into()),
                ast::ConstCombinator::ConstBytes(x) => ir::ConstCombinator::ConstBytes(x.into()),
                ast::ConstCombinator::ConstInt(x) => ir::ConstCombinator::ConstInt(x.into()),
                ast::ConstCombinator::ConstStruct(x) => ir::ConstCombinator::ConstStruct(x.into()),
                ast::ConstCombinator::ConstChoice(x) => ir::ConstCombinator::ConstChoice(x.into()),
                ast::ConstCombinator::ConstCombinatorInvocation { name, .. } => {
                    ir::ConstCombinator::ConstCombinatorInvocation(id(name))
                }
            }
        }
    }

    impl<'i> From<ast::ConstArrayCombinator<'i>> for ir::ConstArrayCombinator {
        fn from(c: ast::ConstArrayCombinator<'i>) -> Self {
            ir::ConstArrayCombinator {
                combinator: c.combinator.into(),
                len: c.len,
                values: c.values.into(),
            }
        }
    }

    impl<'i> From<ast::ConstBytesCombinator<'i>> for ir::ConstBytesCombinator {
        fn from(c: ast::ConstBytesCombinator<'i>) -> Self {
            ir::ConstBytesCombinator {
                len: c.len,
                values: c.values.into(),
            }
        }
    }

    impl<'i> From<ast::ConstArray<'i>> for ir::ConstArray {
        fn from(a: ast::ConstArray<'i>) -> Self {
            match a {
                ast::ConstArray::Char { chars, .. } => ir::ConstArray::Char(chars),
                ast::ConstArray::Int { ints, .. } => ir::ConstArray::Int(ints),
                ast::ConstArray::Repeat { repeat, count, .. } => {
                    ir::ConstArray::Repeat(repeat, count)
                }
                ast::ConstArray::Wildcard => ir::ConstArray::Wildcard,
            }
        }
    }

    impl<'i> From<ast::ConstIntCombinator<'i>> for ir::ConstIntCombinator {
        fn from(c: ast::ConstIntCombinator<'i>) -> Self {
            ir::ConstIntCombinator {
                combinator: c.combinator.into(),
                value: c.value,
            }
        }
    }

    impl<'i> From<ast::ConstStructCombinator<'i>> for ir::ConstStructCombinator {
        fn from(c: ast::ConstStructCombinator<'i>) -> Self {
            ir::ConstStructCombinator(c.0.into_iter().map(Into::into).collect())
        }
    }

    impl<'i> From<ast::ConstChoiceCombinator<'i>> for ir::ConstChoiceCombinator {
        fn from(c: ast::ConstChoiceCombinator<'i>) -> Self {
            ir::ConstChoiceCombinator(c.0.into_iter().map(Into::into).collect())
        }
    }

    impl<'i> From<ast::ConstChoice<'i>> for ir::ConstChoice {
        fn from(c: ast::ConstChoice<'i>) -> Self {
            ir::ConstChoice {
                tag: c.tag,
                combinator: c.combinator.into(),
            }
        }
    }

    impl<'i> From<crate::type_check::ConstCombinatorSig<'i>> for ir::ConstCombinatorSig {
        fn from(src: crate::type_check::ConstCombinatorSig<'i>) -> Self {
            ir::ConstCombinatorSig {
                name: src.name.name,
                resolved_combinator: src.resolved_combinator.into(),
            }
        }
    }

    impl<'i> From<&crate::type_check::GlobalCtx<'i>> for ir::GlobalCtx {
        fn from(src: &crate::type_check::GlobalCtx<'i>) -> Self {
            use std::collections::{HashMap, HashSet};

            let combinators: HashSet<ir::CombinatorSig> =
                src.combinators.iter().cloned().map(Into::into).collect();

            let const_combinators: HashSet<ir::ConstCombinatorSig> = src
                .const_combinators
                .iter()
                .cloned()
                .map(Into::into)
                .collect();

            let enums: HashMap<String, ir::EnumCombinator> = src
                .enums
                .iter()
                .map(|(k, v)| (k.to_string(), v.clone().into()))
                .collect();

            ir::GlobalCtx {
                combinators,
                const_combinators,
                enums,
            }
        }
    }

    impl<'i> From<crate::type_check::CombinatorSig<'i>> for ir::CombinatorSig {
        fn from(src: crate::type_check::CombinatorSig<'i>) -> Self {
            ir::CombinatorSig {
                name: src.name.name,
                param_defns: src.param_defns.iter().cloned().map(Into::into).collect(),
                resolved_combinator: src.resolved_combinator.into(),
            }
        }
    }
}
