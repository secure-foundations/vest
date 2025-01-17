use itertools::Itertools;
use std::fmt::Display;

use pest::error::Error;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "vest.pest"]
pub struct VestCombinator;

#[derive(Debug, Clone)]
pub enum Definition {
    Combinator {
        name: String,
        param_defns: Vec<ParamDefn>,
        combinator: Combinator,
    },
    SecCombinator {
        name: String,
        combinator: Combinator,
    },
    ConstCombinator {
        name: String,
        const_combinator: ConstCombinator,
    },
    Endianess(Endianess),
    MacroDefn {
        name: String,
        params: Vec<String>,
        body: Combinator,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum Endianess {
    Little,
    Big,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParamDefn {
    Stream {
        name: String,
    },
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
    MacroInvocation {
        name: String,
        args: Vec<CombinatorInner>,
    },
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
    Stream(StreamTransform),
    Dependent {
        label: String,
        combinator: Combinator,
    },
    Const {
        label: String,
        combinator: ConstCombinator,
    },
    Preser {
        label: String,
        length: usize,
    },
    Ordinary {
        label: String,
        combinator: Combinator,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StreamTransform {
    pub streams: Vec<String>,
    pub func: String,
    pub args: Vec<Param>,
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
    Exhaustive { enums: Vec<Enum> },
    NonExhaustive { enums: Vec<Enum> },
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
            Definition::SecCombinator { name, combinator } => {
                write!(f, "secret {} = {}", name, combinator)
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

impl Display for ParamDefn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParamDefn::Stream { name } => write!(f, "${}", name),
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
            CombinatorInner::MacroInvocation { name, args } => {
                write!(f, "{}({})", name, args.iter().join(","))
            }
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
            StructField::Preser { label, length } => {
                write!(f, "preser {}:{}", label, length)
            }
            StructField::Stream(s) => write!(f, "{}", s),
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

impl Display for StreamTransform {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}({})", self.func, self.args.iter().join(","))
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
            EnumCombinator::Exhaustive { enums } | EnumCombinator::NonExhaustive { enums } => {
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

pub fn from_str(source: &str) -> Result<Vec<Definition>, Box<Error<Rule>>> {
    let mut definitions = vec![];

    // let pairs = VestCombinator::parse(Rule::grammar, source)?;
    let pairs = VestCombinator::parse(Rule::grammar, source).unwrap_or_else(|e| panic!("{}", e));
    for pair in pairs {
        if let Rule::definition = pair.as_rule() {
            definitions.push(parse_definition(pair));
        }
    }

    Ok(definitions)
}

fn parse_definition(pair: pest::iterators::Pair<Rule>) -> Definition {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::combinator_defn => {
            // combinator_defn     = { secret? ~ var_id ~ param_defn_list? ~ "=" ~ combinator }
            let mut inner_rules = rule.into_inner();
            // check if secret
            let next_rule = inner_rules.next().unwrap();
            match next_rule.as_rule() {
                Rule::secret => {
                    let name = inner_rules.next().unwrap().as_str().to_string();
                    let next_rule = inner_rules.next().unwrap();
                    match next_rule.as_rule() {
                        Rule::param_defn_list => {
                            // ignore the param_defn_list for now
                            // let param_defns = parse_param_defns(next_rule);
                            let combinator = parse_combinator(inner_rules.next().unwrap());
                            Definition::SecCombinator { name, combinator }
                        }
                        Rule::combinator => {
                            let combinator = parse_combinator(next_rule);
                            Definition::SecCombinator { name, combinator }
                        }
                        _ => unreachable!(),
                    }
                }
                _ =>
                // must be var_id
                {
                    let name = next_rule.as_str().to_string();
                    let next_rule = inner_rules.next().unwrap();
                    match next_rule.as_rule() {
                        Rule::param_defn_list => {
                            let param_defns = parse_param_defns(next_rule);
                            let combinator = parse_combinator(inner_rules.next().unwrap());
                            Definition::Combinator {
                                name,
                                param_defns,
                                combinator,
                            }
                        }
                        Rule::combinator => {
                            let combinator = parse_combinator(next_rule);
                            Definition::Combinator {
                                name,
                                param_defns: vec![],
                                combinator,
                            }
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
        Rule::const_combinator_defn => {
            let mut inner_rules = rule.into_inner();
            let _ = inner_rules.next().unwrap(); // skip the "const" keyword
            let name = inner_rules.next().unwrap().as_str().to_string();
            let const_combinator = parse_const_combinator(inner_rules.next().unwrap());
            Definition::ConstCombinator {
                name,
                const_combinator,
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
            let name = inner_rules.next().unwrap().as_str().to_string();
            let params = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(|r| r.as_str().to_string())
                .collect();
            let combinator = parse_combinator(inner_rules.next().unwrap());
            Definition::MacroDefn {
                name,
                params,
                body: combinator,
            }
        }
        _ => unreachable!(),
    }
}

fn parse_param_defns(pair: pest::iterators::Pair<Rule>) -> Vec<ParamDefn> {
    let mut param_defns = vec![];
    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::param_defn => {
                let mut inner_rules = pair.into_inner();
                let next_rule = inner_rules.next().unwrap();
                let name = next_rule.as_str();
                match next_rule.as_rule() {
                    Rule::stream_id => {
                        let name = name.strip_prefix('$').unwrap().to_string();
                        param_defns.push(ParamDefn::Stream { name });
                    }
                    Rule::depend_id => {
                        let name = name.strip_prefix('@').unwrap().to_string();
                        let combinator = parse_combinator_inner(inner_rules.next().unwrap());
                        param_defns.push(ParamDefn::Dependent { name, combinator });
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
    param_defns
}

fn parse_combinator(pair: pest::iterators::Pair<Rule>) -> Combinator {
    let mut inner_rules = pair.into_inner();
    let inner = parse_combinator_inner(inner_rules.next().unwrap());
    let and_then = inner_rules.next().map(|r| Box::new(parse_combinator(r)));
    Combinator { inner, and_then }
}

fn parse_combinator_inner(pair: pest::iterators::Pair<Rule>) -> CombinatorInner {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::constraint_int_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = parse_int_combinator(inner_rules.next().unwrap());
            let constraint = inner_rules.next().map(parse_int_constraint);
            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                combinator,
                constraint,
            })
        }
        Rule::struct_combinator => {
            let inner_rules = rule.into_inner();
            let fields = inner_rules.map(parse_field).collect();
            CombinatorInner::Struct(StructCombinator(fields))
        }
        Rule::wrap_combinator => {
            let mut inner_rules = rule.into_inner();
            let prior = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(parse_const_combinator)
                .collect();
            let combinator = Box::new(parse_combinator(inner_rules.next().unwrap()));
            let post = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(parse_const_combinator)
                .collect();
            CombinatorInner::Wrap(WrapCombinator {
                prior,
                combinator,
                post,
            })
        }
        Rule::enum_combinator => {
            let rule = rule.into_inner().next().unwrap();
            match rule.as_rule() {
                Rule::exhaustive_enum => {
                    let enums = rule.into_inner().map(parse_enum).collect();
                    CombinatorInner::Enum(EnumCombinator::Exhaustive { enums })
                }
                Rule::non_exhaustive_enum => {
                    let enums = rule.into_inner().map(parse_enum).collect();
                    CombinatorInner::Enum(EnumCombinator::NonExhaustive { enums })
                }
                _ => unreachable!(),
            }
            // let enums = rule.into_inner().map(parse_enum).collect();
            // CombinatorInner::Enum(EnumCombinator { enums })
        }
        Rule::choice_combinator => {
            let mut inner_rules = rule.into_inner();
            match inner_rules.peek().unwrap().as_rule() {
                Rule::depend_id => {
                    let depend_id = Some(
                        inner_rules
                            .next()
                            .unwrap()
                            .as_str()
                            .strip_prefix('@')
                            .unwrap()
                            .to_string(),
                    );
                    let choices = parse_choices(inner_rules);
                    CombinatorInner::Choice(ChoiceCombinator { depend_id, choices })
                }
                Rule::choice => {
                    let choices = parse_choices(inner_rules);
                    CombinatorInner::Choice(ChoiceCombinator {
                        depend_id: None,
                        choices,
                    })
                }
                _ => unreachable!(),
            }
        }
        Rule::sepby_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = parse_vec_combinator(inner_rules.next().unwrap());
            let sep = parse_const_combinator(inner_rules.next().unwrap());
            CombinatorInner::SepBy(SepByCombinator { combinator, sep })
        }
        Rule::vec_combinator => CombinatorInner::Vec(parse_vec_combinator(rule)),
        Rule::array_combinator => {
            let mut inner_rules = rule.into_inner();
            let comb = parse_combinator(inner_rules.next().unwrap());
            let next_rule = inner_rules.next().unwrap();
            let len = match next_rule.as_rule() {
                Rule::const_int => {
                    let len = parse_const_int(next_rule);
                    let len: usize = len
                        .try_into()
                        .unwrap_or_else(|_| panic!("Array length {} does not fit into usize", len));
                    LengthSpecifier::Const(len)
                }
                Rule::depend_id => LengthSpecifier::Dependent(
                    next_rule.as_str().strip_prefix('@').unwrap().to_string(),
                ),
                _ => unreachable!(),
            };
            match comb.inner {
                // [u8; ...] would generate bytes combinator
                CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                    combinator: IntCombinator::Unsigned(8),
                    constraint,
                }) if constraint.is_none() => CombinatorInner::Bytes(BytesCombinator { len }),
                _ => {
                    let combinator = Box::new(comb);
                    CombinatorInner::Array(ArrayCombinator { combinator, len })
                }
            }
        }
        Rule::option_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = parse_combinator(inner_rules.next().unwrap());
            CombinatorInner::Option(OptionCombinator(Box::new(combinator)))
        }
        Rule::tail_combinator => CombinatorInner::Tail(TailCombinator),
        Rule::apply_combinator => {
            let mut inner_rules = rule.into_inner();
            let stream = inner_rules.next().unwrap().as_str().to_string();
            let combinator = Box::new(parse_combinator(inner_rules.next().unwrap()));
            CombinatorInner::Apply(ApplyCombinator { stream, combinator })
        }
        Rule::combinator_invocation => {
            let mut inner_rules = rule.into_inner();
            let func = inner_rules.next().unwrap().as_str().to_string();
            let args = inner_rules.next().map(parse_params).unwrap_or_default();
            CombinatorInner::Invocation(CombinatorInvocation { func, args })
        }
        Rule::macro_invocation => {
            let mut inner_rules = rule.into_inner();
            let name = inner_rules.next().unwrap().as_str().to_string();
            let args = inner_rules
                .next()
                .unwrap()
                .into_inner()
                .map(parse_combinator_inner)
                .collect();
            CombinatorInner::MacroInvocation { name, args }
        }
        _ => unreachable!(),
    }
}

fn parse_int_combinator(pair: pest::iterators::Pair<Rule>) -> IntCombinator {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let mut parse_width = || inner_rules.next().unwrap().as_str().parse::<u8>().unwrap();
    match rule.as_rule() {
        Rule::unsigned => IntCombinator::Unsigned(parse_width()),
        Rule::signed => IntCombinator::Signed(parse_width()),
        Rule::btc_varint => IntCombinator::BtcVarint,
        _ => unreachable!(),
    }
}

fn parse_int_constraint(pair: pest::iterators::Pair<Rule>) -> IntConstraint {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::constraint_elem => IntConstraint::Single(parse_constraint_elem(rule)),
        Rule::constraint_elem_set => {
            let inner_rules = rule.into_inner();
            let elems = inner_rules.map(parse_constraint_elem).collect::<Vec<_>>();
            IntConstraint::Set(elems)
        }
        Rule::int_constraint => IntConstraint::Neg(Box::new(parse_int_constraint(rule))),
        _ => unreachable!(),
    }
}

fn parse_constraint_elem(pair: pest::iterators::Pair<Rule>) -> ConstraintElem {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::const_int_range => {
            let mut inner_rules = rule.into_inner();
            let start = inner_rules.next().map(parse_const_int);
            let end = inner_rules.next().map(parse_const_int);
            // TODO: check that start <= end (?)
            ConstraintElem::Range { start, end }
        }
        Rule::const_int => ConstraintElem::Single(parse_const_int(rule)),
        _ => unreachable!(),
    }
}

fn parse_const_int(pair: pest::iterators::Pair<Rule>) -> i128 {
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

fn parse_field(pair: pest::iterators::Pair<Rule>) -> StructField {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::stream_transform => parse_stream_transform(rule),
        Rule::constant => {
            let next_rule = inner_rules.next().unwrap();
            let label = next_rule.as_str().to_string();
            let combinator = parse_const_combinator(inner_rules.next().unwrap());
            StructField::Const { label, combinator }
        }
        Rule::preser_combinator => parse_preser(rule),
        Rule::depend_id | Rule::var_id => {
            let label = rule.as_str().to_string();
            let next_rule = inner_rules.next().unwrap();
            let combinator = parse_combinator(next_rule);
            if let Some(label) = label.strip_prefix('@') {
                StructField::Dependent {
                    label: label.to_owned(),
                    combinator,
                }
            } else {
                StructField::Ordinary { label, combinator }
            }
            // if label.starts_with('@') {
            //     StructField::Dependent { label, combinator }
            // } else {
            //     StructField::Ordinary { label, combinator }
            // }
        }
        _ => unreachable!(),
    }
}

fn parse_preser(pair: pest::iterators::Pair<Rule>) -> StructField {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::var_id => {
            let label = rule.as_str().to_string();
            let rule2 = inner_rules.next().unwrap();
            match rule2.as_rule() {
                Rule::decimal => {
                    let length = rule2.as_str().parse::<usize>().unwrap();
                    StructField::Preser { label, length }
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

fn parse_stream_transform(pair: pest::iterators::Pair<Rule>) -> StructField {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::stream_ids => {
            let streams = rule.into_inner().map(|r| r.as_str().to_string()).collect();
            let func = inner_rules.next().unwrap().as_str().to_string();
            let args = parse_params(inner_rules.next().unwrap());
            StructField::Stream(StreamTransform {
                streams,
                func,
                args,
            })
        }
        Rule::var_id => {
            let func = rule.as_str().to_string();
            let args = parse_params(inner_rules.next().unwrap());
            StructField::Stream(StreamTransform {
                streams: vec![],
                func,
                args,
            })
        }
        _ => unreachable!(),
    }
}

fn parse_params(pair: pest::iterators::Pair<'_, Rule>) -> Vec<Param> {
    pair.into_inner().map(parse_param).collect()
}

fn parse_param(pair: pest::iterators::Pair<Rule>) -> Param {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let name = rule.as_str().to_string();
    match rule.as_rule() {
        Rule::stream_id => Param::Stream(name.strip_prefix('$').unwrap().to_string()),
        Rule::depend_id => Param::Dependent(name.strip_prefix('@').unwrap().to_string()),
        _ => unreachable!(),
    }
}

fn parse_enum(pair: pest::iterators::Pair<Rule>) -> Enum {
    let mut inner_rules = pair.into_inner();
    let name = inner_rules.next().unwrap().as_str().to_string();
    let value = parse_const_int(inner_rules.next().unwrap());
    Enum { name, value }
}

fn parse_choices(inner_rules: pest::iterators::Pairs<Rule>) -> Choices {
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
            let parse_enum_choice = |pair: pest::iterators::Pair<Rule>| {
                let mut inner_rules = pair.into_inner();
                let name = inner_rules.next().unwrap().as_str().to_string();
                let combinator = parse_combinator(inner_rules.next().unwrap());
                (name, combinator)
            };
            let choices = inner_rules.map(parse_enum_choice).collect();
            Choices::Enums(choices)
        }
        Rule::constraint_elem => {
            let parse_int_choice = |pair: pest::iterators::Pair<Rule>| {
                let mut inner_rules = pair.into_inner();
                match inner_rules.peek().unwrap().as_rule() {
                    Rule::constraint_elem => {
                        let pattern = parse_constraint_elem(inner_rules.next().unwrap());
                        let combinator = parse_combinator(inner_rules.next().unwrap());
                        (Some(pattern), combinator)
                    }
                    Rule::variant_id => {
                        let name = inner_rules.next().unwrap().as_str();
                        let combinator = parse_combinator(inner_rules.next().unwrap());
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
            let parse_array_choice = |pair: pest::iterators::Pair<Rule>| {
                let mut inner_rules = pair.into_inner();
                match inner_rules.peek().unwrap().as_rule() {
                    Rule::const_array => {
                        let array = parse_const_array(inner_rules.next().unwrap());
                        let combinator = parse_combinator(inner_rules.next().unwrap());
                        (array, combinator)
                    }
                    Rule::variant_id => {
                        let name = inner_rules.next().unwrap().as_str();
                        let combinator = parse_combinator(inner_rules.next().unwrap());
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

fn parse_vec_combinator(pair: pest::iterators::Pair<'_, Rule>) -> VecCombinator {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    let combinator = parse_combinator(inner_rules.next().unwrap());
    match rule.as_rule() {
        Rule::vec1 => VecCombinator::Vec1(Box::new(combinator)),
        Rule::vec => VecCombinator::Vec(Box::new(combinator)),
        _ => unreachable!(),
    }
}

fn parse_const_combinator(rule: pest::iterators::Pair<'_, Rule>) -> ConstCombinator {
    let mut inner_rules = rule.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::vec => ConstCombinator::Vec(Box::new(parse_const_combinator(
            inner_rules.next().unwrap(),
        ))),
        Rule::const_array_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = parse_int_combinator(inner_rules.next().unwrap());
            let len = parse_const_int(inner_rules.next().unwrap());
            let len: usize = len
                .try_into()
                .unwrap_or_else(|_| panic!("length {} does not fit into usize", len));
            let values = parse_const_array(inner_rules.next().unwrap());
            // check for special case of `[u8; ...] = [...]` ==> ConstBytes
            match combinator {
                IntCombinator::Unsigned(8) => {
                    ConstCombinator::ConstBytes(ConstBytesCombinator { len, values })
                }
                _ => ConstCombinator::ConstArray(ConstArrayCombinator {
                    combinator,
                    len,
                    values,
                }),
            }
        }
        Rule::const_int_combinator => {
            let mut inner_rules = rule.into_inner();
            let combinator = parse_int_combinator(inner_rules.next().unwrap());
            let value = parse_const_int(inner_rules.next().unwrap());
            ConstCombinator::ConstInt(ConstIntCombinator { combinator, value })
        }
        Rule::const_struct_combinator => ConstCombinator::ConstStruct(ConstStructCombinator(
            rule.into_inner().map(parse_const_combinator).collect(),
        )),
        Rule::const_choice_combinator => ConstCombinator::ConstChoice(ConstChoiceCombinator(
            rule.into_inner().map(parse_const_choice).collect(),
        )),
        Rule::const_id => ConstCombinator::ConstCombinatorInvocation(rule.as_str().to_string()),
        _ => unreachable!(),
    }
}

fn parse_const_choice(pair: pest::iterators::Pair<'_, Rule>) -> ConstChoice {
    let mut inner_rules = pair.into_inner();
    let tag = inner_rules.next().unwrap().as_str().to_string();
    let combinator = parse_const_combinator(inner_rules.next().unwrap());
    ConstChoice { tag, combinator }
}

fn parse_const_array(pair: pest::iterators::Pair<'_, Rule>) -> ConstArray {
    let mut inner_rules = pair.into_inner();
    let rule = inner_rules.next().unwrap();
    match rule.as_rule() {
        Rule::const_char_array => {
            // strip leading and trailing quotes
            let str = &rule.as_str();
            let str = &str[1..str.len() - 1];
            ConstArray::Char(str.as_bytes().to_vec())
        }
        Rule::const_int_array => {
            let mut inner_rules = rule.into_inner();
            let next_rule = inner_rules.next().unwrap();
            match next_rule.as_rule() {
                Rule::int_array_expr => {
                    ConstArray::Int(next_rule.into_inner().map(parse_const_int).collect())
                }
                Rule::repeat_int_array_expr => {
                    let mut inner_rules = next_rule.into_inner();
                    let value = parse_const_int(inner_rules.next().unwrap());
                    let count = parse_const_int(inner_rules.next().unwrap());
                    let count: usize = count
                        .try_into()
                        .unwrap_or_else(|_| panic!("length {} does not fit into usize", count));
                    ConstArray::Repeat(value, count)
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}
