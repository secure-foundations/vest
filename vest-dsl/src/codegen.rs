// tempararily disable dead code warning
#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::hash_map::DefaultHasher;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::{collections::HashMap, fmt::Display};

use crate::vestir::*;

/// convert snake case to upper camel case
/// e.g. `foo_bar` -> `FooBar`
fn snake_to_upper_caml(s: &str) -> String {
    let mut result = String::new();
    let mut first = true;
    for c in s.chars() {
        if c == '_' {
            first = true;
        } else if first {
            result.push(c.to_ascii_uppercase());
            first = false;
        } else {
            result.push(c);
        }
    }
    result
}

/// convert camel case to snake case
/// e.g. `FooBar` -> `foo_bar`
fn upper_camel_to_snake(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        if c.is_ascii_uppercase() {
            if !result.is_empty() {
                result.push('_');
            }
            result.push(c.to_ascii_lowercase());
        } else {
            result.push(c);
        }
    }
    result
}

/// convert lower snake case to upper snake case
/// e.g. `foo_bar` -> `FOO_BAR`
fn lower_snake_to_upper_snake(s: &str) -> String {
    s.to_ascii_uppercase()
}

fn compute_hash<T: Hash>(data: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, Clone, Copy)]
enum Bracket {
    Parentheses,
    Angle,
    Square,
    DoubleParentheses, // only used for struct combinator wrappers
    ChoiceParentheses, // only used for choice combinator wrappers
}

impl Bracket {
    fn to_str_pair(self) -> (&'static str, &'static str) {
        match self {
            Bracket::Parentheses => ("(", ")"),
            Bracket::Angle => ("<", ">"),
            Bracket::Square => ("[", "]"),
            Bracket::DoubleParentheses => ("((", "))"),
            Bracket::ChoiceParentheses => ("(Choice::new(", "))"),
        }
    }
}

/// format a vector into pairs of tuples, optionally prepended by `prepend`
/// e.g. `["R1", "R2", "R3", "R4"] ==> "prepend(R1, prepend(R2, prepend(R3, R4)))"`
fn fmt_in_pairs<T: Display>(tuples: &[T], prepend: &str, bracket: Bracket) -> String {
    // let (left, right) = bracket.to_str_pair();
    // match tuples.split_last() {
    //     None => String::new(),
    //     Some((last, rest)) => rest.iter().rfold(last.to_string(), |acc, t| {
    //         format!("{prepend}{left}{t}, {acc}{right}")
    //     }),
    // }
    fmt_in_pairs_statefull(tuples, &|_| prepend.to_string(), bracket, 0)
}

fn fmt_in_pairs_statefull<T: Display>(
    tuples: &[T],
    prepend: &impl Fn(usize) -> String,
    bracket: Bracket,
    mut state: usize,
) -> String {
    let (left, right) = bracket.to_str_pair();
    match tuples.split_last() {
        None => String::new(),
        Some((last, rest)) => rest.iter().rfold(last.to_string(), |acc, t| {
            let prepend = prepend(state);
            state += 1;
            format!("{prepend}{left}{t}, {acc}{right}")
        }),
    }
}

/// generate nested `Either`s based on the number of variants and a variable name
/// (right-associative)
/// - The [`num_of_variants`] should be at least 2
///
/// ## Examples
/// ==== `gen_nested_eithers(2, "m")` ====
/// Either::Left(m)
/// Either::Right(m)
/// ==== `gen_nested_eithers(3, "m")` ====
/// Either::Left(m)
/// Either::Right(Either::Left(m))
/// Either::Right(Either::Right(m))
/// ==== `gen_nested_eithers(4, "m")` ====
/// Either::Left(m)
/// Either::Right(Either::Left(m))
/// Either::Right(Either::Right(Either::Left(m)))
/// Either::Right(Either::Right(Either::Right(m)))
fn gen_nested_eithers(num_of_variants: usize, var_name: &str) -> Vec<String> {
    if num_of_variants == 2 {
        vec![
            format!("Either::Left({})", var_name),
            format!("Either::Right({})", var_name),
        ]
    } else {
        std::iter::once(format!("Either::Left({})", var_name))
            .chain(
                gen_nested_eithers(num_of_variants - 1, var_name)
                    .iter()
                    .map(|nested| format!("Either::Right({})", nested)),
            )
            .collect()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Mode {
    Spec,
    Exec(LifetimeAnn),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LifetimeAnn {
    Some,
    None,
}

impl Display for LifetimeAnn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LifetimeAnn::Some => write!(f, "<'a>"),
            LifetimeAnn::None => Ok(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct CodegenCtx {
    pub msg_lifetimes: HashMap<String, LifetimeAnn>,
    pub global_ctx: GlobalCtx,
    pub constraint_int_combs: HashSet<u64>,
    pub param_defns: Vec<ParamDefn>,
    pub endianess: Endianess,
    pub wrap: bool,
    pub top_level: bool,
    pub flags: CodegenOpts,
}

/// Helper function to determine if a message type needs lifetime annotations
///
/// A message type needs lifetime annotations if the combinator, after resolving,
/// - is a `bytes::Variable` or `bytes::Tail` combinator
/// - is any combinator that recursively contains a message type that needs lifetime
///   annotations
fn msg_need_lifetime(combinator: &Combinator, ctx: &GlobalCtx) -> bool {
    use CombinatorInner::*;
    let resolved = ctx.resolve(combinator);
    // after resolving, we don't need to consider `and_then` or `invocation` anymore
    match resolved {
        Bytes(_) => true,
        Tail(_) => true,
        Struct(StructCombinator(fields)) => fields.iter().any(|field| match field {
            StructField::Ordinary { combinator, .. } => msg_need_lifetime(combinator, ctx),
            StructField::Dependent { combinator, .. } => msg_need_lifetime(combinator, ctx),
            StructField::Const { combinator, .. } => const_msg_need_lifetime(combinator, ctx),
        }),
        Wrap(WrapCombinator {
            prior,
            combinator,
            post,
        }) => {
            prior
                .iter()
                .any(|combinator| const_msg_need_lifetime(combinator, ctx))
                || msg_need_lifetime(combinator, ctx)
                || post
                    .iter()
                    .any(|combinator| const_msg_need_lifetime(combinator, ctx))
        }
        Choice(ChoiceCombinator { choices, .. }) => match choices {
            Choices::Enums(enums) => enums
                .iter()
                .any(|(_, combinator)| msg_need_lifetime(combinator, ctx)),
            Choices::Ints(ints) => ints
                .iter()
                .any(|(_, combinator)| msg_need_lifetime(combinator, ctx)),
            Choices::Arrays(arrays) => arrays
                .iter()
                .any(|(_, combinator)| msg_need_lifetime(combinator, ctx)),
        },
        SepBy(SepByCombinator { combinator, sep }) => {
            let combinator = Combinator {
                inner: Vec(combinator.clone()),
                and_then: None,
            };
            msg_need_lifetime(&combinator, ctx) || const_msg_need_lifetime(sep, ctx)
        }
        Vec(VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator)) => {
            msg_need_lifetime(combinator, ctx)
        }
        Array(ArrayCombinator { combinator, .. }) => msg_need_lifetime(combinator, ctx),
        Option(OptionCombinator(combinator)) => msg_need_lifetime(combinator, ctx),
        ConstraintInt(_) | Enum(_) | Apply(_) => false,
        Invocation(_) => unreachable!("invocation should be resolved by now"),
    }
}

/// Helper function to determine if a const format needs lifetime annotations
fn const_msg_need_lifetime(const_combinator: &ConstCombinator, ctx: &GlobalCtx) -> bool {
    let const_combinator = ctx.resolve_const(const_combinator);
    match const_combinator {
        ConstCombinator::ConstArray(_) => true, // TODO: can be more fine-grained
        ConstCombinator::ConstBytes(_) => true, // TODO: can be more fine-grained
        ConstCombinator::ConstStruct(ConstStructCombinator(fields)) => fields
            .iter()
            .any(|field| const_msg_need_lifetime(field, ctx)),
        ConstCombinator::ConstChoice(ConstChoiceCombinator(choices)) => choices
            .iter()
            .any(|ConstChoice { combinator, .. }| const_msg_need_lifetime(combinator, ctx)),
        ConstCombinator::Vec(combinator) => const_msg_need_lifetime(combinator, ctx),
        ConstCombinator::ConstInt(_) | ConstCombinator::ConstCombinatorInvocation(_) => false,
    }
}

impl CodegenCtx {
    pub fn new(
        msg_lifetimes: HashMap<String, LifetimeAnn>,
        global_ctx: GlobalCtx,
        endianness: Endianess,
        flags: CodegenOpts,
    ) -> Self {
        Self {
            msg_lifetimes,
            global_ctx,
            constraint_int_combs: HashSet::new(),
            param_defns: Vec::new(),
            endianess: endianness,
            wrap: false,
            top_level: true,
            flags,
        }
    }

    pub fn disable_top_level(&self) -> Self {
        Self {
            top_level: false,
            ..self.clone()
        }
    }

    pub fn with_ast(ast: &[Definition], ctx: &GlobalCtx, flags: CodegenOpts) -> Self {
        // first we need to determine which formats' types need lifetime annotations

        // init the format lifetimes with None
        let mut msg_lifetimes: HashMap<String, LifetimeAnn> = HashMap::new();
        for defn in ast {
            match defn {
                Definition::Combinator { name, .. } => {
                    msg_lifetimes.insert(name.to_string(), LifetimeAnn::None);
                }
                Definition::ConstCombinator { name, .. } => {
                    msg_lifetimes.insert(name.to_string(), LifetimeAnn::None);
                }
                _ => {}
            }
        }

        // default endianness is little
        let mut endianness = Endianess::Little;
        // NOTE: by now ast should already be topologically sorted
        ast.iter().for_each(|defn| match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                let msg_lifetime = if msg_need_lifetime(combinator, ctx) {
                    LifetimeAnn::Some
                } else {
                    LifetimeAnn::None
                };
                msg_lifetimes.insert(name.to_string(), msg_lifetime);
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
            } => {
                let lifetime = if const_msg_need_lifetime(const_combinator, ctx) {
                    LifetimeAnn::Some
                } else {
                    LifetimeAnn::None
                };
                msg_lifetimes.insert(name.to_string(), lifetime);
            }
            Definition::Endianess(end) => {
                endianness = *end;
            }
        });

        Self::new(msg_lifetimes, ctx.clone(), endianness, flags)
    }
}

trait Codegen {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String;
    /// will generate a pair of (combinator type, additional code), where additional code can be
    /// - refined predicates for `ConstraintInt`
    /// - constant int and array declarations
    /// - type declaration for continuations of dependent structs
    /// - additional code recursively generated from the inner combinators for `Struct` and `Choice`
    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &mut CodegenCtx)
        -> (String, String);
    /// will generate a pair of (combinator expr, additional code), where additional code can be
    /// - the continuation of the second half of a dependent struct
    /// - additional code recursively generated from the inner combinators
    ///
    /// The `name` parameter is used to
    /// - generate the wrapper type for the combinator definition
    /// - refer to the XXXMapper
    /// - refer to the `UPPER_CAML` const int for `ConstIntCombinator`
    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String);
}

impl Codegen for Combinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let name = &snake_to_upper_caml(name);
        if let Some(and_then) = &self.and_then {
            and_then.gen_msg_type(name, mode, ctx)
        } else {
            self.inner.gen_msg_type(name, mode, ctx)
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let wrapper_code = if !ctx.top_level {
            "".to_string()
        } else {
            let msg_has_lifetime = ctx
                .msg_lifetimes
                .get(name)
                .unwrap_or_else(|| panic!("format lifetime not found for combinator: {}", name));

            // Check if this is a non-exhaustive enum, and if so, use primitive type
            let (spec_type, exec_type) = if let CombinatorInner::Enum(enum_comb) =
                ctx.global_ctx.resolve_alias(&self.inner)
            {
                if let EnumCombinator::NonExhaustive { inferred, .. } = enum_comb {
                    // Use primitive type for non-exhaustive enums
                    let int_type_str = format!("{}", inferred);
                    (int_type_str.clone(), int_type_str)
                } else {
                    // Regular exhaustive enum
                    let name_camel = snake_to_upper_caml(name);
                    (format!("Spec{name_camel}"), format!("{name_camel}"))
                }
            } else {
                // Not an enum
                let name_camel = snake_to_upper_caml(name);
                (
                    format!("Spec{name_camel}"),
                    format!("{name_camel}{msg_has_lifetime}"),
                )
            };

            let name = &snake_to_upper_caml(name);
            match mode {
                Mode::Spec => format!(
                    r#"
pub struct Spec{name}Combinator(Spec{name}CombinatorAlias);

impl SpecCombinator for Spec{name}Combinator {{
    type Type = {spec_type};
    closed spec fn requires(&self) -> bool
    {{ self.0.requires() }}
    closed spec fn wf(&self, v: Self::Type) -> bool
    {{ self.0.wf(v) }}
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    {{ self.0.spec_parse(s) }}
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    {{ self.0.spec_serialize(v) }}
}}
impl SecureSpecCombinator for Spec{name}Combinator {{
    open spec fn is_prefix_secure() -> bool 
    {{ Spec{name}CombinatorAlias::is_prefix_secure() }}
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    {{ self.0.theorem_serialize_parse_roundtrip(v) }}
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {{ self.0.theorem_parse_serialize_roundtrip(buf) }}
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {{ self.0.lemma_prefix_secure(s1, s2) }}
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    {{ self.0.lemma_parse_length(s) }}
    closed spec fn is_productive(&self) -> bool 
    {{ self.0.is_productive() }}
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    {{ self.0.lemma_parse_productive(s) }}
}}
"#
                ),
                Mode::Exec(_) => {
                    format!(
                        r#"
pub struct {name}Combinator({name}CombinatorAlias);

impl View for {name}Combinator {{
    type V = Spec{name}Combinator;
    closed spec fn view(&self) -> Self::V {{ Spec{name}Combinator(self.0@) }}
}}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for {name}Combinator {{
    type Type = {exec_type};
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    {{ <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }}
    closed spec fn ex_requires(&self) -> bool 
    {{ <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }}
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    {{ <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }}
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {{ <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }}
}} 
"#
                    )
                }
            }
        };
        if let Some(and_then) = &self.and_then {
            let (comb_type, additional_code) = self.inner.gen_combinator_type(name, mode, ctx); // must be `bytes::Variable` or `bytes::Tail`
            let (and_then_comb_type, and_then_additional_code) =
                and_then.inner.gen_combinator_type(name, mode, ctx);
            if !ctx.top_level {
                (
                    format!("AndThen<{comb_type}, {and_then_comb_type}>"),
                    additional_code + &and_then_additional_code,
                )
            } else {
                let name = &snake_to_upper_caml(name);
                (
                    match mode {
                        Mode::Spec => format!(
                            "pub type Spec{name}CombinatorAlias = AndThen<{comb_type}, {and_then_comb_type}>;\n"
                        ),
                        _ => format!(
                            "pub type {name}CombinatorAlias = AndThen<{comb_type}, {and_then_comb_type}>;\n"),
                },
                    additional_code + &and_then_additional_code + &wrapper_code,
                )
            }
        } else if !ctx.top_level {
            self.inner.gen_combinator_type(name, mode, ctx)
        } else {
            let (combinator_type, additional_code) =
                self.inner.gen_combinator_type(name, mode, ctx);
            let name = &snake_to_upper_caml(name);
            (
                match mode {
                    Mode::Spec => {
                        format!("pub type Spec{name}CombinatorAlias = {combinator_type};\n")
                    }
                    _ => format!("pub type {name}CombinatorAlias = {combinator_type};\n"),
                },
                additional_code + &wrapper_code,
            )
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        if let Some(and_then) = &self.and_then {
            let (comb_expr, additional_code) = self.inner.gen_combinator_expr(name, mode, ctx);
            let (and_then_comb_expr, and_then_additional_code) =
                and_then.inner.gen_combinator_expr(name, mode, ctx);
            let combinator_expr = format!("AndThen({}, {})", comb_expr, and_then_comb_expr);
            (combinator_expr, additional_code + &and_then_additional_code)
        } else {
            self.inner.gen_combinator_expr(name, mode, ctx)
        }
    }
}

impl Codegen for CombinatorInner {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Bytes(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Tail(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Invocation(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Struct(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Enum(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Choice(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Array(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Vec(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::SepBy(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Wrap(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Apply(p) => p.gen_msg_type(name, mode, ctx),
            CombinatorInner::Option(p) => p.gen_msg_type(name, mode, ctx),
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let upper_caml_name = &snake_to_upper_caml(name);
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Bytes(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Tail(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Invocation(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Struct(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Enum(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Choice(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Array(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Vec(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::SepBy(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Wrap(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Apply(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
            CombinatorInner::Option(p) => p.gen_combinator_type(upper_caml_name, mode, ctx),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Bytes(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Tail(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Invocation(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Struct(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Enum(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Choice(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Array(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Vec(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::SepBy(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Wrap(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Apply(p) => p.gen_combinator_expr(name, mode, ctx),
            CombinatorInner::Option(p) => p.gen_combinator_expr(name, mode, ctx),
        }
    }
}

impl Codegen for ConstraintIntCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let int_type = format!("{}", self.combinator);
        if !ctx.top_level {
            int_type
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {int_type};\n"),
                Mode::Exec(_) => {
                    format!("pub type {name} = {int_type};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {int_type};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        fn gen_constraints(c: &IntConstraint) -> String {
            match c {
                IntConstraint::Single(constraint_elem) => gen_constraint_elem(constraint_elem),
                IntConstraint::Set(cs) => cs
                    .iter()
                    .map(gen_constraint_elem)
                    .collect::<Vec<_>>()
                    .join(" || "),
                IntConstraint::Neg(c) => {
                    format!("!({})", gen_constraints(c))
                }
            }
        }
        fn gen_constraint_elem(c: &ConstraintElem) -> String {
            match c {
                ConstraintElem::Single(n) => format!("(i == {})", n),
                ConstraintElem::Range { start, end } => {
                    if let Some(start) = start {
                        if let Some(end) = end {
                            format!("(i >= {} && i <= {})", start, end)
                        } else {
                            format!("(i >= {})", start)
                        }
                    } else if let Some(end) = end {
                        format!("(i <= {})", end)
                    } else {
                        panic!("a range constraint must have at least one bound")
                    }
                }
            }
        }
        let endianness = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        let int_type = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => "U8".to_string(),
            IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
            IntCombinator::BtcVarint => "BtcVarint".to_string(),
            IntCombinator::ULEB128 => "UnsignedLEB128".to_string(),
            IntCombinator::Signed(..) => unimplemented!(),
        };
        if let Some(constraint) = &self.constraint {
            let hash = compute_hash(self);
            let pred_defn = format!("pub struct Predicate{};\n", hash);
            // reflexive view for the predicate
            let impl_view = format!(
                r#"impl View for Predicate{hash} {{
    type V = Self;

    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}
"#
            );
            // impl SpecPred
            let input_type = format!("{}", self.combinator);
            let (spec_cast, cast) = match input_type.as_str() {
                "u24" => (".spec_as_u32()", ".as_u32()"),
                "VarInt" => (".spec_as_usize()", ".as_usize()"),
                _ => ("", ""),
            };
            let constraints = gen_constraints(constraint);
            let impl_spec_pred = format!(
                r#"impl SpecPred<{input_type}> for Predicate{hash} {{
    open spec fn spec_apply(&self, i: &{input_type}) -> bool {{
        let i = (*i){spec_cast};
        {constraints}
    }}
}}
"#
            );
            let impl_exec_pred = format!(
                r#"impl Pred<{input_type}> for Predicate{hash} {{
    fn apply(&self, i: &{input_type}) -> bool {{
        let i = (*i){cast};
        {constraints}
    }}
}}
"#
            );
            let additional_code = match mode {
                Mode::Spec => "".to_string(),
                _ => {
                    if ctx.constraint_int_combs.insert(hash) {
                        pred_defn + &impl_view + &impl_exec_pred + &impl_spec_pred
                    } else {
                        "".to_string()
                    }
                }
            };
            (
                format!("Refined<{}, Predicate{}>", int_type, hash),
                additional_code,
            )
        } else {
            (int_type, "".to_string())
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let endianess = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        let int_type = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => "U8".to_string(),
            IntCombinator::Unsigned(t) => format!("U{}{}", t, endianess),
            IntCombinator::BtcVarint => "BtcVarint".to_string(),
            IntCombinator::ULEB128 => "UnsignedLEB128".to_string(),
            IntCombinator::Signed(..) => unimplemented!(),
        };
        if let Some(constraint) = &self.constraint {
            let combinator_expr = format!(
                "Refined {{ inner: {}, predicate: Predicate{} }}",
                int_type,
                compute_hash(self)
            );
            (combinator_expr, "".to_string())
        } else {
            let combinator_expr = int_type;
            (combinator_expr, "".to_string())
        }
    }
}

impl Codegen for BytesCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let type_name = match mode {
            Mode::Spec => "Seq<u8>".to_string(),
            Mode::Exec(_) => "&'a [u8]".to_string(),
        };
        if !ctx.top_level {
            type_name
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {type_name};\n"),
                Mode::Exec(_) => {
                    format!("pub type {name}<'a> = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        match &self.len {
            LengthSpecifier::Const(len) => (format!("bytes::Fixed<{}>", len), "".to_string()),
            LengthSpecifier::Dependent(..) => ("bytes::Variable".to_string(), "".to_string()),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let into = match mode {
            Mode::Spec => ".spec_into()",
            _ => ".ex_into()",
        };
        match &self.len {
            LengthSpecifier::Const(len) => {
                let combinator_expr = format!("bytes::Fixed::<{}>", len);
                (combinator_expr, "".to_string())
            }
            LengthSpecifier::Dependent(depend_id) => {
                let combinator_expr = format!("bytes::Variable({}{})", depend_id, into);
                (combinator_expr, "".to_string())
            }
        }
    }
}

impl Codegen for TailCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        if !ctx.top_level {
            match mode {
                Mode::Spec => "Seq<u8>".to_string(),
                Mode::Exec(LifetimeAnn::Some) => "&'a [u8]".to_string(),
                _ => "Vec<u8>".to_string(),
            }
        } else {
            panic!("`Tail` should not be a top-level definition")
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        if !ctx.top_level {
            ("bytes::Tail".to_string(), "".to_string())
        } else {
            panic!("`Tail` should not be a top-level definition")
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        ("bytes::Tail".to_string(), "".to_string())
    }
}

impl Codegen for CombinatorInvocation {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        // Check if this is invoking a non-exhaustive enum
        if let Some(CombinatorSig {
            resolved_combinator,
            ..
        }) = ctx
            .global_ctx
            .combinators
            .iter()
            .find(|sig| sig.name == self.func)
        {
            if let CombinatorInner::Enum(enum_comb) = &resolved_combinator {
                if let EnumCombinator::NonExhaustive { inferred, .. } = enum_comb {
                    // For non-exhaustive enums, use the primitive type directly
                    if !ctx.top_level {
                        return format!("{}", inferred);
                    } else {
                        return "".to_string();
                    }
                }
            }
        }
        let invocked = snake_to_upper_caml(&self.func);
        let invocked = match mode {
            Mode::Spec => format!("Spec{}", invocked),
            Mode::Exec(_) => invocked.to_owned(),
        };
        let lifetime = match mode {
            Mode::Exec(LifetimeAnn::Some) => {
                let lifetime = ctx.msg_lifetimes.get(&self.func).unwrap_or_else(|| {
                    panic!(
                        "format lifetime not found for combinator invocation: {}",
                        self.func
                    )
                });
                match lifetime {
                    LifetimeAnn::Some => "<'a>",
                    LifetimeAnn::None => "",
                }
            }
            _ => "",
        };
        if !ctx.top_level {
            format!("{}{}", invocked, lifetime)
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {invocked};\n"),
                Mode::Exec(_) => {
                    format!("pub type {name}{lifetime} = {invocked}{lifetime};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {invocked}{lifetime};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let invocked = snake_to_upper_caml(&self.func);
        match mode {
            Mode::Spec => (format!("Spec{invocked}Combinator"), "".to_string()),
            _ => (format!("{invocked}Combinator"), "".to_string()),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let invocked = match mode {
            Mode::Spec => format!("spec_{}", &self.func),
            Mode::Exec(_) => self.func.to_owned(),
        };
        let args = &self
            .args
            .iter()
            .map(|arg| {
                if let Param::Dependent(arg) = arg {
                    arg.to_string()
                } else {
                    unimplemented!()
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let combinator_expr = format!("{}({})", invocked, args);
        (combinator_expr, "".to_string())
    }
}

fn gen_aliases(types: &[String], name: &str, mode: Mode, surrounding: (&str, &str)) -> String {
    if types.len() <= 1 {
        return String::new();
    }
    let (left, right) = surrounding;
    (1..types.len())
        .map(|i| {
            let alias_name = match mode {
                Mode::Spec => format!("Spec{name}CombinatorAlias{}", i),
                _ => format!("{name}CombinatorAlias{}", i),
            };
            let current_type = &types[i];
            let previous_type = if i == 1 {
                types[i - 1].clone()
            } else {
                match mode {
                    Mode::Spec => format!("Spec{name}CombinatorAlias{}", i - 1),
                    _ => format!("{name}Combinator{}", i - 1),
                }
            };
            format!("type {alias_name} = {left}{current_type}, {previous_type}{right};",)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn rsplit_dependent_fields_at(
    fields: &[StructField],
    offset: usize,
) -> (&[StructField], &[StructField]) {
    fields.split_at(
        fields
            .iter()
            .rev()
            .skip(offset)
            .position(|field| matches!(field, StructField::Dependent { .. }))
            .map(|i| fields.len() - (i + offset))
            .unwrap_or(0),
    )
}

/// split the fields into halves based on the dependent fields
/// e.g.
/// - `[Ordinary, Dependent, Ordinary, Dependent, Ordinary] -> [[Ordinary, Dependent, Ordinary, Dependent], [Ordinary]]`
/// - `[Ordinary, Dependent, Ordinary, Dependent] -> [[Ordinary, Dependent], [Ordinary, Dependent]]`
fn split_at_dependent_field(fields: &[StructField]) -> (&[StructField], &[StructField]) {
    let (fst, snd) = rsplit_dependent_fields_at(fields, 0);
    if snd.is_empty() {
        // last dependent field is the last field of the struct
        // split at the second last dependent field instead
        rsplit_dependent_fields_at(fields, 1)
    } else {
        (fst, snd)
    }
}

/// build nested pairs of various kinds from fields using custom left and right delimiters
fn custom_build_nested_pairs(
    fields: &[StructField],
    into_pairs: &mut impl FnMut(&[StructField]) -> String,
    l: &impl Fn(usize) -> String,
    r: &impl Fn(usize) -> String,
    depth: usize,
) -> String {
    let (fst, snd) = split_at_dependent_field(fields);
    if fst.is_empty() {
        into_pairs(snd)
    } else {
        format!(
            "{}{}, {}{}",
            l(depth),
            custom_build_nested_pairs(fst, into_pairs, l, r, depth + 1),
            into_pairs(snd),
            r(depth)
        )
    }
}

/// build nested pairs of various kinds from fields
fn build_nested_pairs(
    fields: &[StructField],
    into_pairs: &mut impl FnMut(&[StructField]) -> String,
    l: &str,
    r: &str,
) -> String {
    custom_build_nested_pairs(fields, into_pairs, &|_| l.into(), &|_| r.into(), 0)
}

/// get the label and message type from a struct field by destructing the field and calling `combinator.gen_msg_type`
fn label_and_msg_type_from_field(
    field: &StructField,
    mode: Mode,
    ctx: &CodegenCtx,
) -> (String, String) {
    match field {
        StructField::Ordinary { label, combinator }
        | StructField::Dependent { label, combinator } => {
            let field_type = combinator.gen_msg_type("", mode, &ctx.disable_top_level());
            (label.to_string(), field_type)
        }
        StructField::Const { label, combinator } => {
            let field_type = combinator.gen_msg_type("", mode, &ctx.disable_top_level());
            (label.to_string(), field_type)
        }
    }
}

impl StructCombinator {
    /// check if the struct has dependent fields
    fn has_dependent_fields(&self) -> bool {
        self.0
            .iter()
            .any(|field| matches!(field, StructField::Dependent { .. }))
    }
}

impl Codegen for StructCombinator {
    /// assuming all structs are top-level definitions
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let msg_type_name = match mode {
            Mode::Spec => format!("Spec{}", name),
            Mode::Exec(_) => name.to_string(),
        };
        let lifetime_ann = match mode {
            Mode::Exec(LifetimeAnn::Some) => "<'a>",
            _ => "",
        };
        let derive = match mode {
            Mode::Exec(_) => "#[derive(Debug, Clone, PartialEq, Eq)]\n",
            _ => "",
        };
        let (labels, field_types) = self
            .0
            .iter()
            .map(|field| label_and_msg_type_from_field(field, mode, ctx))
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let msg_type_fields = std::iter::zip(&labels, &field_types)
            .map(|(label, field_type)| format!("    pub {}: {},", label, field_type))
            .collect::<Vec<_>>()
            .join("\n");
        let impl_view = match mode {
            Mode::Spec => "".to_string(),
            Mode::Exec(_) => {
                let view_lifetime = match mode {
                    Mode::Exec(LifetimeAnn::Some) => "<'_>",
                    Mode::Exec(LifetimeAnn::None) => "",
                    _ => unreachable!(),
                };
                let view_fields = labels
                    .iter()
                    .map(|label| format!("            {}: self.{}@,", label, label))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    r#"
impl View for {msg_type_name}{view_lifetime} {{
    type V = Spec{name};

    open spec fn view(&self) -> Self::V {{
        Spec{name} {{
{view_fields}
        }}
    }}
}}"#
                )
            }
        };
        let mut into_msg_type_pairs = |fields: &[StructField]| {
            fmt_in_pairs(
                &fields
                    .iter()
                    .map(|field| {
                        let (_, field_type) = label_and_msg_type_from_field(field, mode, ctx);
                        field_type
                    })
                    .collect::<Vec<_>>(),
                "",
                Bracket::Parentheses,
            )
        };
        let mut into_msg_ref_type_pairs = |fields: &[StructField]| {
            fmt_in_pairs(
                &fields
                    .iter()
                    .map(|field| {
                        let (_, field_type) = label_and_msg_type_from_field(field, mode, ctx);
                        "&'a ".to_string() + &field_type
                    })
                    .collect::<Vec<_>>(),
                "",
                Bracket::Parentheses,
            )
        };
        let msg_type_pairs = build_nested_pairs(&self.0, &mut into_msg_type_pairs, "(", ")");
        let msg_ref_type_pairs =
            build_nested_pairs(&self.0, &mut into_msg_ref_type_pairs, "(", ")");
        let from_trait = match mode {
            Mode::Spec => "SpecFrom",
            _ => "From",
        };
        let from_fn_sig_for_msg_type = match mode {
            Mode::Spec => {
                format!("open spec fn spec_from(m: {msg_type_name}Inner) -> {msg_type_name}")
            }
            _ => format!("fn ex_from(m: {msg_type_name}Inner) -> {msg_type_name}"),
        };
        let mut into_field_access_pairs = |fields: &[StructField]| {
            fmt_in_pairs(
                &fields
                    .iter()
                    .map(|field| {
                        let (label, _) = label_and_msg_type_from_field(field, mode, ctx);
                        match mode {
                            Mode::Spec => format!("m.{}", label),
                            Mode::Exec(_) => format!("&m.{}", label),
                        }
                    })
                    .collect::<Vec<_>>(),
                "",
                Bracket::Parentheses,
            )
        };
        let field_access_pairs =
            build_nested_pairs(&self.0, &mut into_field_access_pairs, "(", ")");
        let from_fn_sig_for_msg_type_inner = match mode {
            Mode::Spec => {
                format!("open spec fn spec_from(m: {msg_type_name}) -> {msg_type_name}Inner")
            }
            _ => format!("fn ex_from(m: &'a {msg_type_name}) -> {msg_type_name}InnerRef<'a>"),
        };
        let mut into_field_name_pairs = |fields: &[StructField]| {
            fmt_in_pairs(
                &fields
                    .iter()
                    .map(|field| {
                        let (label, _) = label_and_msg_type_from_field(field, mode, ctx);
                        label
                    })
                    .collect::<Vec<_>>(),
                "",
                Bracket::Parentheses,
            )
        };
        let field_name_pairs = build_nested_pairs(&self.0, &mut into_field_name_pairs, "(", ")");
        let field_names = labels.join(", ");
        let mapper_impl = match mode {
            Mode::Spec => "".to_string(),
            _ => gen_mapper(name, &msg_type_name, lifetime_ann),
        };
        format!(
            r#"{derive}
pub struct {msg_type_name}{lifetime_ann} {{
{msg_type_fields}
}}"#
        ) + &(if matches!(ctx.flags, CodegenOpts::All | CodegenOpts::Impls) {
            format!(
                r#"
{impl_view}
pub type {msg_type_name}Inner{lifetime_ann} = {msg_type_pairs};
"#
            ) + &(match mode {
                Mode::Spec => format!(
                    r#"

impl {from_trait}<{msg_type_name}> for {msg_type_name}Inner {{
    {from_fn_sig_for_msg_type_inner} {{
        {field_access_pairs}
    }}
}}
"#
                ),
                _ => format!(
                    r#"
pub type {msg_type_name}InnerRef<'a> = {msg_ref_type_pairs};
impl<'a> {from_trait}<&'a {msg_type_name}{lifetime_ann}> for {msg_type_name}InnerRef<'a> {{
    {from_fn_sig_for_msg_type_inner} {{
        {field_access_pairs}
    }}
}}
"#
                ),
            }) + &format!(
                r#"
impl{lifetime_ann} {from_trait}<{msg_type_name}Inner{lifetime_ann}> for {msg_type_name}{lifetime_ann} {{
    {from_fn_sig_for_msg_type} {{
        let {field_name_pairs} = m;
        {msg_type_name} {{ {field_names} }}
    }}
}}
{mapper_impl}"#,
            )
        } else {
            "".to_string()
        })
    }

    /// assuming all structs are top-level definitions
    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        // TODO: this is ugly, need to refactor
        let old_top_level = ctx.top_level;
        ctx.top_level = false;
        let name = &snake_to_upper_caml(name);
        fn comb_type_and_code_from_field(
            field: &StructField,
            name: &str,
            mode: Mode,
            ctx: &mut CodegenCtx,
        ) -> (String, String) {
            match field {
                StructField::Ordinary { label, combinator }
                | StructField::Dependent { label, combinator } => {
                    let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                    combinator.gen_combinator_type(name, mode, ctx)
                }
                StructField::Const { label, combinator } => {
                    let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                    combinator.gen_combinator_type(name, mode, ctx)
                }
            }
        }
        // need to first get the additional code because `ctx.constraint_int_combs` is updated
        // each time `gen_combinator_type` is called
        let mut additional_code = self
            .0
            .iter()
            .map(|field| comb_type_and_code_from_field(field, name, mode, ctx).1)
            .collect::<Vec<_>>()
            .join("");
        let mut combinator_types = |fields: &[StructField]| {
            fields
                .iter()
                // .map(|field| comb_type_and_code_from_field(field, name, mode, ctx).0)
                .map(|field| comb_type_and_code_from_field(field, name, mode, ctx).0)
                .collect::<Vec<_>>()
        };

        if split_at_dependent_field(&self.0).0.is_empty() {
            // no dependent fields
            // we implement the combinator wrappers here to "cache" Rust's trait resolution
            let combinator_types = combinator_types(&self.0);
            let combinator_types_rev = combinator_types
                .clone()
                .into_iter()
                .rev()
                .collect::<Vec<_>>();
            match mode {
                Mode::Spec => {
                    let aliases = gen_aliases(&combinator_types_rev, name, mode, ("(", ")"));
                    additional_code += &aliases;
                }
                _ => {
                    let aliases = gen_aliases(&combinator_types_rev, name, mode, ("(", ")"));
                    let wrappers = (1..combinator_types.len())
                        .map(|i| {
                            format!(
                                r#"
struct {name}Combinator{i}({name}CombinatorAlias{i});
impl View for {name}Combinator{i} {{
    type V = Spec{name}CombinatorAlias{i};
    closed spec fn view(&self) -> Self::V {{ self.0@ }}
}}
impl_wrapper_combinator!({name}Combinator{i}, {name}CombinatorAlias{i});
"#
                            )
                        })
                        .collect::<Vec<_>>()
                        .join("");
                    additional_code += &aliases;
                    additional_code += &wrappers;
                }
            }
            // restore the top level flag
            ctx.top_level = old_top_level;
            let mapped_inner = if combinator_types.len() == 1 {
                combinator_types[0].clone()
            } else {
                match mode {
                    Mode::Spec => {
                        format!("Spec{name}CombinatorAlias{}", combinator_types.len() - 1)
                    }
                    _ => format!("{name}Combinator{}", combinator_types.len() - 1),
                }
            };
            (
                format!("Mapped<{}, {}Mapper>", mapped_inner, name),
                additional_code,
            )
        } else {
            let mut into_comb_type_pairs = |fields: &[StructField]| {
                fmt_in_pairs(&combinator_types(fields), "", Bracket::Parentheses)
            };
            let mapped_inner = match mode {
                Mode::Spec => {
                    build_nested_pairs(&self.0, &mut into_comb_type_pairs, "SpecPair<", ">")
                }
                _ => custom_build_nested_pairs(
                    &self.0,
                    &mut into_comb_type_pairs,
                    &|_| "Pair<".into(),
                    &|depth| format!(", {name}Cont{depth}>"),
                    0,
                ),
            };
            // restore the top level flag
            ctx.top_level = old_top_level;
            (
                format!("Mapped<{}, {}Mapper>", mapped_inner, name),
                additional_code,
            )
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        fn gen_inner_expr_and_code_from_fields(
            fields: &[StructField],
            name: &str,
            mode: Mode,
            ctx: &CodegenCtx,
        ) -> (Vec<String>, Vec<String>) {
            fields
                .iter()
                .map(|field| match field {
                    StructField::Ordinary { combinator, label }
                    | StructField::Dependent { combinator, label } => combinator
                        .gen_combinator_expr(
                            &lower_snake_to_upper_snake(&(name.to_owned() + label)),
                            mode,
                            ctx,
                        ),
                    StructField::Const { label, combinator } => {
                        let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                        combinator.gen_combinator_expr(name, mode, ctx)
                    }
                })
                .unzip()
        }
        fn gen_combinator_expr_helper(
            fields: &[StructField],
            name: &str,
            mode: Mode,
            ctx: &CodegenCtx,
            depth: usize,
        ) -> (String, String) {
            let (fst, snd) = split_at_dependent_field(fields);
            if fst.is_empty() {
                let (inner, additional_code): (Vec<String>, Vec<String>) =
                    gen_inner_expr_and_code_from_fields(snd, name, mode, ctx);
                (
                    fmt_in_pairs(&inner, "", Bracket::Parentheses),
                    additional_code.join(""),
                )
            } else {
                let (fst_expr, fst_code) =
                    gen_combinator_expr_helper(fst, name, mode, ctx, depth + 1);
                let mut into_msg_type_pairs = |fields: &[StructField]| {
                    fmt_in_pairs(
                        &fields
                            .iter()
                            .map(|field| label_and_msg_type_from_field(field, mode, ctx).1)
                            .collect::<Vec<_>>(),
                        "",
                        Bracket::Parentheses,
                    )
                };
                let mut into_msg_ref_type_pairs = |fields: &[StructField]| {
                    fmt_in_pairs(
                        &fields
                            .iter()
                            .map(|field| {
                                "&'x ".to_string()
                                    + &label_and_msg_type_from_field(field, mode, ctx).1
                            })
                            .collect::<Vec<_>>(),
                        "",
                        Bracket::Parentheses,
                    )
                };
                let mut into_binding_pairs = |fields: &[StructField]| {
                    fmt_in_pairs(
                        &fields
                            .iter()
                            .map(|field| match field {
                                StructField::Ordinary { .. } | StructField::Const { .. } => {
                                    "_".to_string()
                                }

                                StructField::Dependent { label, .. } => label.to_string(),
                            })
                            .collect::<Vec<_>>(),
                        "",
                        Bracket::Parentheses,
                    )
                };
                let mut into_binding_pairs_only_dependent = |fields: &[StructField]| {
                    fmt_in_pairs(
                        &fields
                            .iter()
                            .filter_map(|field| match field {
                                StructField::Dependent { label, .. } => Some(label.to_string()),
                                _ => None,
                            })
                            .collect::<Vec<_>>(),
                        "",
                        Bracket::Parentheses,
                    )
                };
                let mut into_binding_pairs_only_dependent_deref = |fields: &[StructField]| {
                    fmt_in_pairs(
                        &fields
                            .iter()
                            .filter_map(|field| match field {
                                StructField::Dependent { label, .. } => Some(format!("*{}", label)),
                                _ => None,
                            })
                            .collect::<Vec<_>>(),
                        "",
                        Bracket::Parentheses,
                    )
                };
                let fst_msg_type_pairs =
                    build_nested_pairs(fst, &mut into_msg_type_pairs, "(", ")");
                let fst_msg_ref_type_pairs =
                    build_nested_pairs(fst, &mut into_msg_ref_type_pairs, "(", ")");
                let fst_binding_pairs = build_nested_pairs(fst, &mut into_binding_pairs, "(", ")");
                let fst_binding_pairs_only_dependent =
                    build_nested_pairs(fst, &mut into_binding_pairs_only_dependent, "(", ")");
                let fst_binding_pairs_only_dependent_deref =
                    build_nested_pairs(fst, &mut into_binding_pairs_only_dependent_deref, "(", ")");
                let (snd_combinator_types, (snd_exprs, snd_code)): (Vec<_>, (Vec<_>, Vec<_>)) = snd
                    .iter()
                    .map(|field| match field {
                        StructField::Ordinary { combinator, label }
                        | StructField::Dependent { combinator, label } => {
                            let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                            (
                                combinator
                                    .gen_combinator_type(name, mode, &mut ctx.disable_top_level())
                                    .0,
                                combinator.gen_combinator_expr(
                                    name,
                                    mode,
                                    &ctx.disable_top_level(),
                                ),
                            )
                        }
                        _ => todo!(),
                    })
                    .unzip();
                let snd_combinator_types =
                    fmt_in_pairs(&snd_combinator_types, "", Bracket::Parentheses);
                let snd_exprs = fmt_in_pairs(&snd_exprs, "", Bracket::Parentheses);
                let snaked_name = upper_camel_to_snake(name);
                let expr = match mode {
                    Mode::Spec => {
                        format!(
                            r#"Pair::spec_new({fst_expr}, |deps| spec_{snaked_name}_cont{depth}(deps))"#,
                        )
                    }
                    _ => {
                        format!(r#"Pair::new({fst_expr}, {name}Cont{depth})"#,)
                    }
                };
                let additional_code = match mode {
                    Mode::Spec => {
                        format!(
                            r#"
pub open spec fn spec_{snaked_name}_cont{depth}(deps: {fst_msg_type_pairs}) -> {snd_combinator_types} {{
    let {fst_binding_pairs} = deps;
    {snd_exprs}
}}

impl View for {name}Cont{depth} {{
    type V = spec_fn({fst_msg_type_pairs}) -> {snd_combinator_types};

    open spec fn view(&self) -> Self::V {{
        |deps: {fst_msg_type_pairs}| {{
            spec_{snaked_name}_cont{depth}(deps)
        }}
    }}
}}
"#
                        )
                    }
                    _ => {
                        format!(
                            r#"
pub struct {name}Cont{depth};
type {name}Cont{depth}Type<'a, 'b> = &'b {fst_msg_type_pairs};
type {name}Cont{depth}SType<'a, 'x> = {fst_msg_ref_type_pairs};
type {name}Cont{depth}Input<'a, 'b, 'x> = POrSType<{name}Cont{depth}Type<'a, 'b>, {name}Cont{depth}SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<{name}Cont{depth}Input<'a, 'b, 'x>> for {name}Cont{depth} {{
    type Output = {snd_combinator_types};

    open spec fn requires(&self, deps: {name}Cont{depth}Input<'a, 'b, 'x>) -> bool {{ true }}

    open spec fn ensures(&self, deps: {name}Cont{depth}Input<'a, 'b, 'x>, o: Self::Output) -> bool {{
        o@ == spec_{snaked_name}_cont{depth}(deps@)
    }}

    fn apply(&self, deps: {name}Cont{depth}Input<'a, 'b, 'x>) -> Self::Output {{
        match deps {{
            POrSType::P(deps) => {{
                let {fst_binding_pairs} = *deps;
                {snd_exprs}
            }}
            POrSType::S(deps) => {{
                let {fst_binding_pairs} = deps;
                let {fst_binding_pairs_only_dependent} = {fst_binding_pairs_only_dependent_deref};
                {snd_exprs}
            }}
        }}
    }}
}}"#
                        )
                    }
                };
                (expr, fst_code + &snd_code.join("") + &additional_code)
            }
        }
        if split_at_dependent_field(&self.0).0.is_empty() {
            // no dependent fields
            // we use the combinator wrappers here (used to "cache" Rust's trait resolution)
            let (inner, additional_code): (Vec<String>, Vec<String>) =
                gen_inner_expr_and_code_from_fields(&self.0, name, mode, ctx);
            let inner = match mode {
                Mode::Spec => fmt_in_pairs(&inner, "", Bracket::Parentheses),
                _ => fmt_in_pairs_statefull(
                    &inner,
                    &|depth| format!("{name}Combinator{depth}"),
                    Bracket::DoubleParentheses,
                    1,
                ),
            };
            (
                format!(
                    r#"
    Mapped {{
        inner: {inner},
        mapper: {name}Mapper,
    }}"#,
                ),
                additional_code.join(""),
            )
        } else {
            let (inner, additional_code) = gen_combinator_expr_helper(&self.0, name, mode, ctx, 0);
            (
                format!(
                    r#"
    Mapped {{
        inner: {inner},
        mapper: {name}Mapper,
    }}"#,
                ),
                additional_code,
            )
        }
    }
}

impl Codegen for EnumCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        match &self {
            EnumCombinator::NonExhaustive { enums, inferred } => {
                // u24 constants would be declared as u32
                let inferred = match format!("{inferred}").as_str() {
                    "u24" => "u32".to_string(),
                    other => other.to_string(),
                };
                if !ctx.top_level {
                    panic!("`Enum` should be a top-level definition")
                } else {
                    match mode {
                        Mode::Spec => {
                            // For spec mode, do nothing
                            "".to_string()
                        }
                        Mode::Exec(..) => {
                            // For exec mode, generate the module with both SPEC and exec constants
                            let module_decl = format!("pub mod {name} {{\n    use super::*;\n");

                            // Generate constants inside the module
                            let spec_const_decl = enums
                                .iter()
                                .map(
                                    |Enum {
                                         name: variant_name,
                                         value,
                                     }| {
                                        format!(
                                            "    pub spec const SPEC_{variant_name}: {inferred} = {value};"
                                        )
                                    },
                                )
                                .collect::<Vec<_>>()
                                .join("\n");
                            let exec_static_decl = enums
                                .iter()
                                .map(|Enum { name: variant_name, value }| {
                                    format!("    pub exec const {variant_name}: {inferred} ensures {variant_name} == SPEC_{variant_name} {{ {value} }}")
                                })
                                .collect::<Vec<_>>()
                                .join("\n");

                            let module_close = "}\n";

                            format!("{module_decl}{spec_const_decl}\n{exec_static_decl}\n{module_close}")
                        }
                    }
                }
            }
            EnumCombinator::Exhaustive { enums, inferred } => {
                // since the spec and exec types are the same, we only need to
                // generate one of them
                if matches!(mode, Mode::Exec(..)) {
                    if !ctx.top_level {
                        panic!("`Enum` should be a top-level definition")
                    } else {
                        let msg_type_name = name;
                        let enum_variants = enums
                            .iter()
                            .map(|e| format!("{e}"))
                            .collect::<Vec<_>>()
                            .join(",\n");
                        let spec_const_decl = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                format!("pub spec const SPEC_{msg_type_name}_{name}: {inferred} = {value};")
                            })
                            .collect::<Vec<_>>()
                            .join("\n");
                        let exec_static_decl = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                format!("pub exec static EXEC_{msg_type_name}_{name}: {inferred} ensures EXEC_{msg_type_name}_{name} == SPEC_{msg_type_name}_{name} {{ {value} }}")
                            })
                            .collect::<Vec<_>>()
                            .join("\n");
                        let try_from_int_match_arms = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                format!("{}{} => Ok({}::{}),", value, inferred, msg_type_name, name)
                            })
                            .collect::<Vec<_>>()
                            .join("\n            ");
                        let (spec_try_from_enum_match_arms, try_from_enum_match_arms): (
                            Vec<_>,
                            Vec<_>,
                        ) = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                (
                                    format!("{msg_type_name}::{name} => Ok(SPEC_{msg_type_name}_{name}),",),
                                    format!("{msg_type_name}::{name} => Ok(&EXEC_{msg_type_name}_{name}),",),
                                )
                            })
                            .unzip();
                        let (spec_try_from_enum_match_arms, try_from_enum_match_arms) = (
                            spec_try_from_enum_match_arms.join("\n            "),
                            try_from_enum_match_arms.join("\n            "),
                        );
                        format!(
                            r#"
{spec_const_decl}
{exec_static_decl}

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum {msg_type_name} {{
    {enum_variants}
}}
pub type Spec{msg_type_name} = {msg_type_name};

pub type {msg_type_name}Inner = {inferred};

pub type {msg_type_name}InnerRef<'a> = &'a {inferred};
"#
                        ) + &(if matches!(ctx.flags, CodegenOpts::All | CodegenOpts::Impls) {
                            format!(
                                r#"
impl View for {msg_type_name} {{
    type V = Self;

    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}

impl SpecTryFrom<{msg_type_name}Inner> for {msg_type_name} {{
    type Error = ();

    open spec fn spec_try_from(v: {msg_type_name}Inner) -> Result<{msg_type_name}, ()> {{
        match v {{
            {try_from_int_match_arms}
            _ => Err(()),
        }}
    }}
}}

impl SpecTryFrom<{msg_type_name}> for {msg_type_name}Inner {{
    type Error = ();

    open spec fn spec_try_from(v: {msg_type_name}) -> Result<{msg_type_name}Inner, ()> {{
        match v {{
            {spec_try_from_enum_match_arms}
        }}
    }}
}}

impl TryFrom<{msg_type_name}Inner> for {msg_type_name} {{
    type Error = ();

    fn ex_try_from(v: {msg_type_name}Inner) -> Result<{msg_type_name}, ()> {{
        match v {{
            {try_from_int_match_arms}
            _ => Err(()),
        }}
    }}
}}

impl<'a> TryFrom<&'a {msg_type_name}> for {msg_type_name}InnerRef<'a> {{
    type Error = ();

    fn ex_try_from(v: &'a {msg_type_name}) -> Result<{msg_type_name}InnerRef<'a>, ()> {{
        match v {{
            {try_from_enum_match_arms}
        }}
    }}
}}

pub struct {msg_type_name}Mapper;

impl View for {msg_type_name}Mapper {{
    type V = Self;

    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}

impl SpecPartialIso for {msg_type_name}Mapper {{
    type Src = {msg_type_name}Inner;
    type Dst = {msg_type_name};
}}

impl SpecPartialIsoProof for {msg_type_name}Mapper {{
    proof fn spec_iso(s: Self::Src) {{ 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {{
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        }});
    }}

    proof fn spec_iso_rev(s: Self::Dst) {{ 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {{
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        }});
    }}
}}

impl<'a> PartialIso<'a> for {msg_type_name}Mapper {{
    type Src = {msg_type_name}Inner;
    type Dst = {msg_type_name};
    type RefSrc = {msg_type_name}InnerRef<'a>;
}}
"#
                            )
                        } else {
                            "".to_string()
                        })
                    }
                } else {
                    "".to_string()
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let endianness = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        match &self {
            EnumCombinator::Exhaustive { enums, inferred } => {
                let int_type = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                    _ => unreachable!(),
                };
                (
                    format!("TryMap<{}, {}Mapper>", int_type, name),
                    "".to_string(),
                )
            }
            EnumCombinator::NonExhaustive { enums, inferred } => match inferred {
                IntCombinator::Unsigned(8) => ("U8".to_string(), "".to_string()),
                IntCombinator::Unsigned(t) => (format!("U{}{}", t, endianness), "".to_string()),
                IntCombinator::Signed(..) => unimplemented!(),
                _ => unreachable!(),
            },
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let endianness = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        let spec = match mode {
            Mode::Spec => "Spec",
            _ => "",
        };
        match &self {
            EnumCombinator::Exhaustive { enums, inferred } => {
                let int_type = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                    _ => unreachable!(),
                };
                let combinator_expr =
                    format!("TryMap {{ inner: {}, mapper: {}Mapper }}", int_type, name);
                (combinator_expr, "".to_string())
            }
            EnumCombinator::NonExhaustive { enums, inferred } => {
                let int_combinator = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                    _ => unreachable!(),
                };
                let combinator_expr = int_combinator;
                (combinator_expr, "".to_string())
            }
        }
    }
}

impl Codegen for ChoiceCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let variants = match &self.choices {
            Choices::Enums(enums) => enums
                .iter()
                .map(|(label, combinator)| {
                    let variant_type = combinator.gen_msg_type("", mode, &ctx.disable_top_level());
                    let label = if label == "_" { "Unrecognized" } else { label };
                    (label.to_string(), variant_type)
                })
                .collect::<Vec<_>>(),
            Choices::Ints(ints) => ints
                .iter()
                .enumerate()
                .map(|(i, (_, combinator))| {
                    let variant_name = format!("Variant{}", i);
                    let variant_type = combinator.gen_msg_type("", mode, &ctx.disable_top_level());
                    (variant_name, variant_type)
                })
                .collect::<Vec<_>>(),
            Choices::Arrays(arrays) => arrays
                .iter()
                .enumerate()
                .map(|(i, (_, combinator))| {
                    let variant_name = format!("Variant{}", i);
                    let variant_type = combinator.gen_msg_type("", mode, &ctx.disable_top_level());
                    (variant_name, variant_type)
                })
                .collect::<Vec<_>>(),
        };
        let msg_type_name = match mode {
            Mode::Spec => format!("Spec{}", name),
            Mode::Exec(_) => name.to_string(),
        };
        let lifetime_ann = match mode {
            Mode::Exec(LifetimeAnn::Some) => "<'a>",
            _ => "",
        };
        let derive = match mode {
            Mode::Exec(_) => "#[derive(Debug, Clone, PartialEq, Eq)]\n",
            _ => "",
        };
        let nominal_sum = variants
            .iter()
            .map(|(label, variant_type)| format!("    {}({}),", label, variant_type))
            .collect::<Vec<_>>()
            .join("\n");
        let structural_sum = fmt_in_pairs(
            &variants
                .iter()
                .map(|(_, variant_type)| variant_type)
                .collect::<Vec<_>>(),
            "Either",
            Bracket::Angle,
        );
        let ref_structural_sum = fmt_in_pairs(
            &variants
                .iter()
                .map(|(_, variant_type)| format!("&'a {}", variant_type))
                .collect::<Vec<_>>(),
            "Either",
            Bracket::Angle,
        );
        // impl View for exec enums
        let impl_view = {
            let impl_view_body = variants
                .iter()
                .map(|(label, variant_type)| {
                    format!(
                        "            {}::{}(m) => Spec{}::{}(m@),",
                        msg_type_name, label, name, label
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                r#"
impl{lifetime_ann} View for {msg_type_name}{lifetime_ann} {{
    type V = Spec{msg_type_name};
    open spec fn view(&self) -> Self::V {{
        match self {{
{impl_view_body}
        }}
    }}
}}
"#
            )
        };
        // impl (Spec)From
        let trait_name = match mode {
            Mode::Spec => "SpecFrom",
            _ => "From",
        };
        let assoc_func_name = match mode {
            Mode::Spec => "spec_from",
            _ => "ex_from",
        };
        assert!(
            variants.len() >= 2,
            "`Choice` should have at least two variants"
        );
        let nested_eithers = gen_nested_eithers(variants.len(), "m");
        let impl_inner_from_body = std::iter::zip(&variants, &nested_eithers)
            .map(|((label, _), nested)| {
                format!("            {}::{}(m) => {},", msg_type_name, label, nested)
            })
            .collect::<Vec<_>>()
            .join("\n");
        let impl_inner_from = match mode {
            Mode::Spec => {
                format!(
                    r#"    open spec fn {assoc_func_name}(m: {msg_type_name}) -> {msg_type_name}Inner {{
        match m {{
{impl_inner_from_body}
        }}
    }}
"#
                )
            }
            Mode::Exec(_) => format!(
                r#"    fn {assoc_func_name}(m: &'a {msg_type_name}{lifetime_ann}) -> {msg_type_name}InnerRef<'a> {{
        match m {{
{impl_inner_from_body}
        }}
    }}
"#
            ),
        };
        let impl_from_inner_body = std::iter::zip(&variants, &nested_eithers)
            .map(|((label, _), nested)| {
                format!("            {} => {}::{}(m),", nested, msg_type_name, label)
            })
            .collect::<Vec<_>>()
            .join("\n");
        let impl_from_inner = match mode {
            Mode::Spec => format!(
                r#"    open spec fn {assoc_func_name}(m: {msg_type_name}Inner) -> {msg_type_name} {{
        match m {{
{impl_from_inner_body}
        }}
    }}
"#
            ),
            Mode::Exec(_) => format!(
                r#"    fn {assoc_func_name}(m: {msg_type_name}Inner{lifetime_ann}) -> {msg_type_name}{lifetime_ann} {{
        match m {{
{impl_from_inner_body}
        }}
    }}
    "#
            ),
        };
        let impl_mapper = match mode {
            Mode::Exec(_) => &gen_mapper(name, &msg_type_name, lifetime_ann),
            Mode::Spec => "",
        };
        format!(
            r#"
{derive}pub enum {msg_type_name}{lifetime_ann} {{
{nominal_sum}
}}

pub type {msg_type_name}Inner{lifetime_ann} = {structural_sum};
"#
        ) + &(if matches!(mode, Mode::Exec(_)) {
            format!(
                r#"
pub type {msg_type_name}InnerRef<'a> = {ref_structural_sum};
"#
            )
        } else {
            "".to_string()
        }) + &(if matches!(ctx.flags, CodegenOpts::All | CodegenOpts::Impls) {
            (match mode {
                Mode::Spec => format!(
                    r#"
impl {trait_name}<{msg_type_name}{lifetime_ann}> for {msg_type_name}Inner {{
{impl_inner_from}
}}

                "#
                ),
                Mode::Exec(_) => format!(
                    r#"
{impl_view}

impl<'a> {trait_name}<&'a {msg_type_name}{lifetime_ann}> for {msg_type_name}InnerRef<'a> {{
{impl_inner_from}
}}
"#
                ),
            }) + &format!(
                r#"
impl{lifetime_ann} {trait_name}<{msg_type_name}Inner{lifetime_ann}> for {msg_type_name}{lifetime_ann} {{
{impl_from_inner}
}}

{impl_mapper}
"#
            )
        } else {
            "".to_string()
        })
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let name = &snake_to_upper_caml(name);
        let mut is_wrapper = false;
        let (combinator_types, additional_code): (Vec<String>, Vec<String>) = match &self.choices {
            Choices::Enums(enums) => enums
                .iter()
                .map(|(label, combinator)| {
                    if matches!(
                        combinator,
                        Combinator {
                            inner: CombinatorInner::Invocation(..),
                            and_then: _
                        }
                    ) {
                        is_wrapper = true;
                    }
                    let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                    combinator.gen_combinator_type(name, mode, &mut ctx.disable_top_level())
                })
                .map(|(t, code)| {
                    if self.depend_id.is_some() {
                        (format!("Cond<{}>", t), code)
                    } else {
                        (t, code)
                    }
                })
                .unzip(),
            Choices::Ints(ints) => ints
                .iter()
                .map(|(_, combinator)| {
                    combinator.gen_combinator_type(name, mode, &mut ctx.disable_top_level())
                })
                .map(|(t, code)| (format!("Cond<{}>", t), code))
                .unzip(),
            Choices::Arrays(arrays) => arrays
                .iter()
                .map(|(_, combinator)| {
                    combinator.gen_combinator_type(name, mode, &mut ctx.disable_top_level())
                })
                .map(|(t, code)| (format!("Cond<{}>", t), code))
                .unzip(),
        };
        // we implement the combinator wrappers here to "cache" Rust's trait resolution
        // let inner = fmt_in_pairs(&combinator_types, "Choice", Bracket::Angle);

        let mapped_inner = if combinator_types.len() == 1 {
            combinator_types[0].clone()
        } else {
            match mode {
                Mode::Spec => {
                    format!("Spec{name}CombinatorAlias{}", combinator_types.len() - 1)
                }
                _ => format!("{name}Combinator{}", combinator_types.len() - 1),
            }
        };
        let mut additional_code = additional_code.join("");

        let combinator_types_rev = combinator_types
            .clone()
            .into_iter()
            .rev()
            .collect::<Vec<_>>();
        match mode {
            Mode::Spec => {
                let aliases = gen_aliases(&combinator_types_rev, name, mode, ("Choice<", ">"));
                additional_code += &aliases;
            }
            _ => {
                let aliases = gen_aliases(&combinator_types_rev, name, mode, ("Choice<", ">"));
                let wrappers = (1..combinator_types.len())
                    .map(|i| {
                        format!(
                            r#"
struct {name}Combinator{i}({name}CombinatorAlias{i});
impl View for {name}Combinator{i} {{
    type V = Spec{name}CombinatorAlias{i};
    closed spec fn view(&self) -> Self::V {{ self.0@ }}
}}
impl_wrapper_combinator!({name}Combinator{i}, {name}CombinatorAlias{i});
"#
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("");
                additional_code += &aliases;
                additional_code += &wrappers;
            }
        }

        // generate DisjointFrom impls if
        // 1. it's a non-dependent choice
        // 2. the variants are "combinator wrappers" (i.e. format invocations)
        let disjointness_proof = if self.depend_id.is_none() && is_wrapper {
            match mode {
                Mode::Spec => {
                    // generate disjointness proof for every pair of variants in `combinator_types`
                    // e.g. for `Choice<A, Choice<B, Choice<C, D>>>`, generate
                    // `impl DisjointFrom<A> for D`,
                    // `impl DisjointFrom<B> for D`,
                    // `impl DisjointFrom<C> for D`
                    // `impl DisjointFrom<A> for C`,
                    // `impl DisjointFrom<B> for C`
                    // `impl DisjointFrom<A> for B`
                    let mut disjointness_proof = vec![];
                    let len = combinator_types.len();
                    for i in 0..len {
                        for j in i + 1..len {
                            disjointness_proof.push(format!(
                                r#"
impl DisjointFrom<{}> for {} {{
    closed spec fn disjoint_from(&self, other: &{}) -> bool
    {{ self.0.disjoint_from(&other.0) }}
    proof fn parse_disjoint_on(&self, other: &{}, buf: Seq<u8>) 
    {{ self.0.parse_disjoint_on(&other.0, buf); }}
}}"#,
                                combinator_types[i],
                                combinator_types[j],
                                combinator_types[i],
                                combinator_types[i]
                            ));
                        }
                    }
                    disjointness_proof.join("\n")
                }
                _ => "".to_string(),
            }
        } else {
            "".to_string()
        };
        (
            format!("Mapped<{}, {}Mapper>", mapped_inner, name),
            additional_code + &disjointness_proof,
        )
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        fn pattern_to_boolexpr(
            pattern: &ConstraintElem,
            mode: Mode,
            depend_id: &str,
            spec_cast: &str,
            cast: &str,
        ) -> String {
            match pattern {
                ConstraintElem::Range { start, end } => match (start, end) {
                    (Some(start), Some(end)) => match mode {
                        Mode::Spec => format!(
                            "{}{} >= {} && {}{} <= {}",
                            depend_id, spec_cast, start, depend_id, spec_cast, end
                        ),
                        _ => format!(
                            "{}{} >= {} && {}{} <= {}",
                            depend_id, cast, start, depend_id, cast, end
                        ),
                    },
                    (Some(start), None) => match mode {
                        Mode::Spec => format!("{}{} >= {}", depend_id, spec_cast, start),
                        _ => format!("{}{} >= {}", depend_id, cast, start),
                    },
                    (None, Some(end)) => match mode {
                        Mode::Spec => format!("{}{} <= {}", depend_id, spec_cast, end),
                        _ => format!("{}{} <= {}", depend_id, cast, end),
                    },
                    (None, None) => unreachable!(),
                },
                ConstraintElem::Single(value) => match mode {
                    Mode::Spec => format!("{}{} == {}", depend_id, spec_cast, value),
                    _ => format!("{}{} == {}", depend_id, cast, value),
                },
            }
        }
        let (combinator_exprs, additional_code): (Vec<String>, Vec<String>) = match &self.depend_id
        {
            Some(depend_id) => {
                // find the corresponding combinator of `depend_id`
                let combinator = ctx
                    .param_defns
                    .iter()
                    .find_map(|param_defn| match param_defn {
                        ParamDefn::Dependent { name, combinator } if name == depend_id => {
                            Some(combinator)
                        }
                        _ => None,
                    })
                    .unwrap();
                match combinator {
                    // invocation to an enum
                    CombinatorInner::Invocation(CombinatorInvocation {
                        func: enum_name, ..
                    }) => {
                        match &self.choices {
                            Choices::Enums(variants) => variants
                                .iter()
                                .map(|(variant, combinator)| {
                                    let (inner, code) =
                                        combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level());
                                    let bool_exp = match ctx.global_ctx.enums.get(enum_name.as_str()).unwrap()
                                    {
                                        EnumCombinator::NonExhaustive { enums, inferred } => {
                                            let (spec_cast, cast) = match inferred {
                                                IntCombinator::Unsigned(24) => (".spec_as_u32()", ".as_u32()"),
                                                _ => ("", ""),
                                            };
                                            let upper_caml_name = snake_to_upper_caml(enum_name);
                                            if variant == "_" {
                                                // default case; the negation of all other cases
                                                let other_variants = variants.iter().filter_map(|(variant, _)| {
                                                    if variant == "_" {
                                                        None
                                                    } else {
                                                        // Use module::constant syntax
                                                        Some(match mode {
                                                            Mode::Spec => format!("{}{} == {}::SPEC_{}", depend_id, spec_cast, upper_caml_name, variant),
                                                            _ => format!("{}{} == {}::{}", depend_id, cast, upper_caml_name, variant)
                                                        })
                                                    }
                                                }).collect::<Vec<_>>();
                                                format!("!({})", other_variants.join(" || "))
                                            } else {
                                                // Use module::constant syntax
                                                match mode {
                                                    Mode::Spec => format!("{}{} == {}::SPEC_{}", depend_id, spec_cast, upper_caml_name, variant),
                                                    _ => format!("{}{} == {}::{}", depend_id, cast, upper_caml_name, variant)
                                                }
                                            }
                                        }
                                        EnumCombinator::Exhaustive { .. } => {
                                            let upper_caml_name = snake_to_upper_caml(enum_name);
                                            format!(
                                                "{} == {}::{}",
                                                depend_id, upper_caml_name, variant
                                            )
                                        }
                                    };
                                    (
                                        format!("Cond {{ cond: {}, inner: {} }}", bool_exp, inner),
                                        code,
                                    )
                                })
                                .unzip(),
                            Choices::Ints(ints)=> ints
                                .iter()
                                .map(|(variant, combinator)| {
                                    let (inner, code) =
                                        combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level());
                                    let bool_exp = match variant {
                                        Some(pattern) => {
                                            pattern_to_boolexpr(pattern, mode, depend_id, "", "")
                                        }
                                        None => {
                                             // default case; the negation of all other cases
                                             let other_variants = ints
                                                 .iter()
                                                 .filter_map(|(variant, _)| {
                                                    variant.as_ref().map(|variant| {
                                                        pattern_to_boolexpr(variant, mode, depend_id, "", "")
                                                    })
                                                 })
                                                 .collect::<Vec<_>>();
                                             format!("!({})", other_variants.join(" || "))
                                        }
                                    };
                                    (
                                        format!("Cond {{ cond: {}, inner: {} }}", bool_exp, inner),
                                        code,
                                    )
                                })
                                .unzip(),
                            Choices::Arrays(..) => unreachable!(),
                        }
                    }
                    // bytes
                    CombinatorInner::Bytes(BytesCombinator { len }) => {
                        match &self.choices {
                            Choices::Arrays(arrays)=> arrays
                                .iter()
                                .map(|(variant, combinator)| {
                                    let (inner, code) =
                                        combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level());
                                    let bool_exp = match variant {
                                        ConstArray::Int(ints) => {
                                            let ints = ints.iter().map(|i| format!("{}u8", i)).collect::<Vec<_>>().join(", ");
                                            match mode {
                                                Mode::Spec => format!("{} == seq![{}]", depend_id, ints),
                                                _ => format!("compare_slice({}, {}.as_slice())", depend_id, variant),
                                            }
                                        }
                                        ConstArray::Wildcard => {
                                                 // default case; the negation of all other cases
                                             let other_variants = arrays
                                                 .iter()
                                                 .filter_map(|(variant, _)| {
                                                    match variant {
                                                          ConstArray::Int(ints) => {
                                                            let ints = ints.iter().map(|i| format!("{}u8", i)).collect::<Vec<_>>().join(", ");
                                                            match mode {
                                                                Mode::Spec => Some(format!("{} == seq![{}]", depend_id, ints)),
                                                                _ => Some(format!(
                                                                    "compare_slice({}, {}.as_slice())",
                                                                    depend_id, variant
                                                                ))
                                                            }
                                                        }
                                                        _ => None
                                                        }
                                                 })
                                                 .collect::<Vec<_>>();
                                             format!("!({})", other_variants.join(" || "))
                                        }
                                        _ => unimplemented!(),
                                    };
                                    (
                                        format!("Cond {{ cond: {}, inner: {} }}", bool_exp, inner),
                                        code,
                                    )
                                })
                                .unzip(),
                            Choices::Ints(..) | Choices::Enums(..) => unreachable!(),
                        }
                    }
                    // ints
                    CombinatorInner::ConstraintInt(ConstraintIntCombinator { combinator: int_type, .. }) => {
                        match &self.choices {
                            Choices::Ints(ints)=> ints
                                .iter()
                                .map(|(variant, combinator)| {
                                    let (inner, code) =
                                        combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level());
                                    let (spec_cast, cast) = match int_type {
                                        IntCombinator::Unsigned(24) => (".spec_as_u32()", ".as_u32()"),
                                        IntCombinator::BtcVarint => (".spec_as_usize()", ".as_usize()"),
                                        _ => ("", ""),
                                    };
                                    let bool_exp = match variant {
                                        Some(pattern) => {
                                            pattern_to_boolexpr(pattern, mode, depend_id, spec_cast, cast)
                                        }
                                        None => {
                                             // default case; the negation of all other cases
                                             let other_variants = ints
                                                 .iter()
                                                 .filter_map(|(variant, _)| {
                                                    variant.as_ref().map(|variant| {
                                                        pattern_to_boolexpr(variant, mode, depend_id, spec_cast, cast)
                                                    })
                                                 })
                                                 .collect::<Vec<_>>();
                                             format!("!({})", other_variants.join(" || "))
                                        }
                                    };
                                    (
                                        format!("Cond {{ cond: {}, inner: {} }}", bool_exp, inner),
                                        code,
                                    )
                                })
                                .unzip(),
                            Choices::Arrays(..) | Choices::Enums(..) => unreachable!(),
                        }
                    }
                    _ => unreachable!(
                        "Unexpected combinator type for dependent id: {}. We currently only support dependent fields on enum, int, and bytes, got {}.",
                        depend_id, combinator
                    ),
                }
            }
            None => {
                let Choices::Enums(choices) = &self.choices else {
                    // already type-checked that when there's no dependent id, the choices must be enums
                    unreachable!()
                };
                choices
                    .iter()
                    .map(|(label, combinator)| {
                        let name = &lower_snake_to_upper_snake(&(name.to_owned() + label));
                        combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level())
                    })
                    .unzip()
            }
        };
        let ord_choice_constructor = match mode {
            Mode::Spec => "Choice",
            _ => "Choice::new",
        };
        // let inner = fmt_in_pairs(
        //     &combinator_exprs,
        //     ord_choice_constructor,
        //     Bracket::Parentheses,
        // );
        let inner = match mode {
            Mode::Spec => fmt_in_pairs(&combinator_exprs, "Choice", Bracket::Parentheses),
            _ => fmt_in_pairs_statefull(
                &combinator_exprs,
                &|depth| format!("{name}Combinator{depth}"),
                Bracket::ChoiceParentheses,
                1,
            ),
        };
        let combinator_expr = format!("Mapped {{ inner: {}, mapper: {}Mapper }}", inner, name);
        (combinator_expr, additional_code.join(""))
    }
}

fn gen_mapper(name: &str, msg_type_name: &str, lifetime_ann: &str) -> String {
    format!(
        r#"
pub struct {name}Mapper;
impl View for {name}Mapper {{
    type V = Self;
    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}
impl SpecIso for {name}Mapper {{
    type Src = Spec{name}Inner;
    type Dst = Spec{name};
}}
impl SpecIsoProof for {name}Mapper {{
    proof fn spec_iso(s: Self::Src) {{
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }}
    proof fn spec_iso_rev(s: Self::Dst) {{
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }}
}}
impl<'a> Iso<'a> for {name}Mapper {{
    type Src = {msg_type_name}Inner{lifetime_ann};
    type Dst = {msg_type_name}{lifetime_ann};
    type RefSrc = {msg_type_name}InnerRef<'a>;
}}"#
    )
}

impl Codegen for ArrayCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inner = &self
            .combinator
            .gen_msg_type("", mode, &ctx.disable_top_level());

        let type_name = match mode {
            Mode::Spec => format!("Seq<{}>", inner),
            _ => format!("RepeatResult<{}>", inner),
        };
        if !ctx.top_level {
            type_name
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {type_name};\n"),
                Mode::Exec(LifetimeAnn::Some) => {
                    format!("pub type {name}<'a> = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
                Mode::Exec(LifetimeAnn::None) => {
                    format!("pub type {name} = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let inner = self
            .combinator
            .gen_combinator_type(name, mode, &mut ctx.disable_top_level());
        (format!("RepeatN<{}>", inner.0), inner.1)
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let into = match mode {
            Mode::Spec => ".spec_into()",
            _ => ".ex_into()",
        };
        let (inner, additional_code) =
            self.combinator
                .gen_combinator_expr(name, mode, &ctx.disable_top_level());
        match &self.len {
            LengthSpecifier::Const(len) => {
                (format!("RepeatN({}, {})", inner, len), additional_code)
            }
            LengthSpecifier::Dependent(depend_id) => (
                format!("RepeatN({}, {}{})", inner, depend_id, into),
                additional_code,
            ),
        }

        // let combinator_expr = format!("RepeatN({}, {}{})", inner.0, len, into);
        // (combinator_expr, inner.1)
    }
}

impl Codegen for VecCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_msg_type("", mode, &ctx.disable_top_level())
            }
        };

        let type_name = match mode {
            Mode::Spec => format!("Seq<{}>", inner),
            _ => format!("RepeatResult<{}>", inner),
        };
        if !ctx.top_level {
            type_name
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {type_name};\n"),
                Mode::Exec(LifetimeAnn::Some) => {
                    format!("pub type {name}<'a> = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
                Mode::Exec(LifetimeAnn::None) => {
                    format!("pub type {name} = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_combinator_type(name, mode, &mut ctx.disable_top_level())
            }
        };
        (format!("Repeat<{}>", inner.0), inner.1)
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_combinator_expr(name, mode, &ctx.disable_top_level())
            }
        };
        let combinator_expr = match mode {
            Mode::Spec => format!("Repeat({})", inner.0),
            _ => format!("Repeat::new({})", inner.0),
        };
        (combinator_expr, inner.1)
    }
}

impl Codegen for SepByCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }
}

impl Codegen for WrapCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inner = &self
            .combinator
            .gen_msg_type("", mode, &ctx.disable_top_level());

        if !ctx.top_level {
            inner.to_string()
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {inner};\n"),
                Mode::Exec(LifetimeAnn::Some) => {
                    format!("pub type {name}<'a> = {inner};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {inner};\n")
                }
                Mode::Exec(LifetimeAnn::None) => {
                    format!("pub type {name} = {inner};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {inner};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let prior = self
            .prior
            .iter()
            .enumerate()
            .map(|(i, combinator)| {
                let const_name = format!("{}_{}_FRONT", name, i);
                combinator.gen_combinator_type(
                    &const_name,
                    mode,
                    &mut CodegenCtx {
                        wrap: true,
                        top_level: false,
                        ..ctx.clone()
                    },
                )
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let inner = self
            .combinator
            .gen_combinator_type(name, mode, &mut ctx.disable_top_level());
        let post = self
            .post
            .iter()
            .enumerate()
            .map(|(i, combinator)| {
                let const_name = format!("{}_{}_BACK", name, i);
                combinator.gen_combinator_type(
                    &const_name,
                    mode,
                    &mut CodegenCtx {
                        wrap: true,
                        top_level: false,
                        ..ctx.clone()
                    },
                )
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let combinator_type = fmt_in_pairs(
            &prior
                .0
                .iter()
                .chain(std::iter::once(&inner.0))
                .collect::<Vec<_>>(),
            "Preceded",
            Bracket::Angle,
        );
        let combinator_type = fmt_in_pairs(
            &std::iter::once(&combinator_type)
                .chain(post.0.iter())
                .collect::<Vec<_>>(),
            "Terminated",
            Bracket::Angle,
        );
        (
            combinator_type,
            [prior.1, post.1].map(|s| s.join("\n")).join("\n") + &inner.1,
        )
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let prior = self
            .prior
            .iter()
            .enumerate()
            .map(|(i, combinator)| {
                let const_name = format!("{}_{}_FRONT", name, i);
                combinator.gen_combinator_expr(
                    &const_name,
                    mode,
                    &CodegenCtx {
                        wrap: true,
                        top_level: false,
                        ..ctx.clone()
                    },
                )
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let inner = self
            .combinator
            .gen_combinator_expr(name, mode, &ctx.disable_top_level());
        let post = self
            .post
            .iter()
            .enumerate()
            .map(|(i, combinator)| {
                let const_name = format!("{}_{}_BACK", name, i);
                combinator.gen_combinator_expr(
                    &const_name,
                    mode,
                    &CodegenCtx {
                        wrap: true,
                        top_level: false,
                        ..ctx.clone()
                    },
                )
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();
        let combinator_expr = fmt_in_pairs(
            &prior
                .0
                .iter()
                .chain(std::iter::once(&inner.0))
                .collect::<Vec<_>>(),
            "Preceded",
            Bracket::Parentheses,
        );
        let combinator_expr = fmt_in_pairs(
            &std::iter::once(&combinator_expr)
                .chain(post.0.iter())
                .collect::<Vec<_>>(),
            "Terminated",
            Bracket::Parentheses,
        );
        (
            combinator_expr,
            [prior.1, post.1].map(|s| s.join("")).join("") + &inner.1,
        )
    }
}

impl Codegen for ApplyCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }
}

impl Codegen for OptionCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inner = &self.0.gen_msg_type("", mode, &ctx.disable_top_level());

        let type_name = match mode {
            Mode::Spec => format!("Option<{}>", inner),
            _ => format!("Optional<{}>", inner),
        };
        if !ctx.top_level {
            type_name
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {type_name};\n"),
                Mode::Exec(LifetimeAnn::Some) => {
                    format!("pub type {name}<'a> = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
                Mode::Exec(LifetimeAnn::None) => {
                    format!("pub type {name} = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let inner = self
            .0
            .gen_combinator_type(name, mode, &mut ctx.disable_top_level());
        (format!("Opt<{}>", inner.0), inner.1)
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let inner = self
            .0
            .gen_combinator_expr(name, mode, &ctx.disable_top_level());
        let combinator_expr = match mode {
            Mode::Spec => format!("Opt({})", inner.0),
            _ => format!("Opt::new({})", inner.0),
        };
        (combinator_expr, inner.1)
    }
}

impl Codegen for ConstCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        match &self {
            ConstCombinator::ConstInt(c) => c.gen_msg_type(name, mode, ctx),
            ConstCombinator::ConstBytes(c) => c.gen_msg_type(name, mode, ctx),
            ConstCombinator::ConstArray(..) => todo!(),
            ConstCombinator::Vec(..) => todo!(),
            ConstCombinator::ConstStruct(..) => todo!(),
            ConstCombinator::ConstChoice(..) => todo!(),
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let invocked = match mode {
                    Mode::Spec => format!("Spec{}", name),
                    Mode::Exec(_) => name.to_owned(),
                };
                let lifetime = match mode {
                    Mode::Exec(LifetimeAnn::Some) => {
                        let lifetime = ctx.msg_lifetimes.get(name).unwrap_or_else(|| {
                            panic!(
                                "format lifetime not found for combinator invocation: {}",
                                name
                            )
                        });
                        match lifetime {
                            LifetimeAnn::Some => "<'a>",
                            LifetimeAnn::None => "",
                        }
                    }
                    _ => "",
                };
                if !ctx.top_level {
                    format!("{}{}", invocked, lifetime)
                } else {
                    match mode {
                        Mode::Spec => format!("pub type Spec{name} = {};\n", invocked),
                        Mode::Exec(..) => {
                            format!("pub type {name}{lifetime} = {invocked}{lifetime};\n",)
                                + &format!("pub type {name}Ref<'a> = &'a {invocked}{lifetime};\n")
                        }
                    }
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let (combinator_type, additional_code) = match &self {
            ConstCombinator::ConstInt(c) => c.gen_combinator_type(name, mode, ctx),
            ConstCombinator::ConstBytes(c) => c.gen_combinator_type(name, mode, ctx),
            ConstCombinator::ConstArray(..) => todo!(),
            ConstCombinator::Vec(..) => todo!(),
            ConstCombinator::ConstStruct(..) => todo!(),
            ConstCombinator::ConstChoice(..) => todo!(),
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let invocked = snake_to_upper_caml(name);
                match mode {
                    Mode::Spec => (format!("Spec{invocked}Combinator"), "".to_string()),
                    _ => (format!("{invocked}Combinator"), "".to_string()),
                }
            }
        };
        if !ctx.top_level {
            (combinator_type, additional_code)
        } else {
            let name = &snake_to_upper_caml(name);
            (
                match mode {
                    Mode::Spec => {
                        format!("pub type Spec{name}Combinator = {combinator_type};\n")
                    }
                    _ => format!("pub type {name}Combinator = {combinator_type};\n"),
                },
                additional_code,
            )
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        match &self {
            ConstCombinator::ConstInt(c) => c.gen_combinator_expr(name, mode, ctx),
            ConstCombinator::ConstBytes(c) => c.gen_combinator_expr(name, mode, ctx),
            ConstCombinator::ConstArray(..) => todo!(),
            ConstCombinator::Vec(..) => todo!(),
            ConstCombinator::ConstStruct(..) => todo!(),
            ConstCombinator::ConstChoice(..) => todo!(),
            ConstCombinator::ConstCombinatorInvocation(name) => {
                let invocked = match mode {
                    Mode::Spec => format!("spec_{}", name),
                    Mode::Exec(_) => name.to_owned(),
                };
                let combinator_expr = format!("{}()", invocked);
                (combinator_expr, "".to_string())
            }
        }
    }
}

impl Codegen for ConstIntCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let int_type = format!("{}", self.combinator);
        if !ctx.top_level {
            int_type
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {int_type};\n"),
                Mode::Exec(..) => {
                    format!("pub type {name} = {int_type};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {int_type};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let endianess = match ctx.endianess {
            Endianess::Big => "Be",
            Endianess::Little => "Le",
        };
        let (comb_type, tag_type) = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => ("U8".to_string(), "u8".to_string()),
            IntCombinator::Unsigned(t) => (format!("U{}{}", t, endianess), format!("u{}", t)),
            IntCombinator::Signed(..) => unimplemented!(),
            IntCombinator::BtcVarint => unimplemented!(),
            IntCombinator::ULEB128 => ("UnsignedLEB128".to_string(), "u64".to_string()),
        };
        let name = format!("{}_CONST", name);
        let const_decl = format!("pub const {}: {} = {};\n", name, tag_type, self.value);
        let additional_code = match mode {
            Mode::Spec => const_decl,
            _ => "".to_string(),
        };
        let combinator_type = if ctx.wrap {
            format!("Tag<{}, {}>", comb_type, tag_type)
        } else {
            format!("Refined<{}, TagPred<{}>>", comb_type, tag_type)
        };
        (combinator_type, additional_code)
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let name = format!("{}_CONST", name);
        let endianess = match ctx.endianess {
            Endianess::Big => "Be",
            Endianess::Little => "Le",
        };
        let int_type = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => "U8".to_string(),
            IntCombinator::Unsigned(t) => format!("U{}{}", t, endianess),
            IntCombinator::Signed(..) => unimplemented!(),
            IntCombinator::BtcVarint => unimplemented!(),
            IntCombinator::ULEB128 => "UnsignedLEB128".to_string(),
        };
        let combinator_expr = if ctx.wrap {
            match mode {
                Mode::Spec => format!("Tag::spec_new({}, {})", int_type, name),
                _ => format!("Tag::new({}, {})", int_type, name),
            }
        } else {
            format!(
                "Refined {{ inner: {}, predicate: TagPred({}) }}",
                int_type, name
            )
        };
        (combinator_expr, "".to_string())
    }
}

impl Codegen for ConstBytesCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let type_name = match mode {
            Mode::Spec => "Seq<u8>".to_string(),
            Mode::Exec(LifetimeAnn::Some) => "&'a [u8]".to_string(),
            _ => "Vec<u8>".to_string(),
        };
        if !ctx.top_level {
            type_name
        } else {
            match mode {
                Mode::Spec => format!("pub type Spec{name} = {type_name};\n"),
                Mode::Exec(..) => {
                    format!("pub type {name}<'a> = {type_name};\n")
                        + &format!("pub type {name}Ref<'a> = &'a {type_name};\n")
                }
            }
        }
    }

    fn gen_combinator_type(
        &self,
        name: &str,
        mode: Mode,
        ctx: &mut CodegenCtx,
    ) -> (String, String) {
        let len = self.len;
        let arr_val = format!("{}", self.values);
        let name = format!("{name}_CONST");
        let spec_const_decl = format!("pub spec const SPEC_{}: Seq<u8> = seq!{};", name, arr_val);
        let exec_const_decl = format!(
            r#"pub exec static {name}: [u8; {len}]
    ensures {name}@ == SPEC_{name},
{{
    let arr: [u8; {len}] = {arr_val};
    assert(arr@ == SPEC_{name});
    arr
}}
"#
        );
        let hash = compute_hash(&format!("{}", self.values));
        //         let predicate = format!(
        //             r#"
        // pub struct BytesPredicate{hash}<'a>(PhantomData<&'a ()>);
        // impl<'a> BytesPredicate{hash}<'a> {{
        //     pub closed spec fn spec_new() -> Self {{
        //         BytesPredicate{hash}(PhantomData)
        //     }}
        //     pub fn new() -> Self {{
        //         BytesPredicate{hash}(PhantomData)
        //     }}
        // }}
        // impl View for BytesPredicate{hash}<'_> {{
        //     type V = Self;
        //     open spec fn view(&self) -> Self::V {{
        //         *self
        //     }}
        // }}
        // impl SpecPred for BytesPredicate{hash}<'_> {{
        //     type Input = Seq<u8>;
        //
        //     open spec fn spec_apply(&self, i: &Self::Input) -> bool {{
        //         i == &SPEC_{name}
        //     }}
        // }}
        // impl<'a> Pred for BytesPredicate{hash}<'a> {{
        //     type Input = &'a [u8];
        //
        //     fn apply(&self, i: &Self::Input) -> bool {{
        //         compare_slice(i, {name}.as_slice())
        //     }}
        // }}
        // "#,
        //         );
        if ctx.wrap {
            match mode {
                Mode::Spec => (
                    format!("Tag<bytes::Fixed<{}>, Seq<u8>>", len),
                    spec_const_decl,
                ),
                _ => (
                    format!("Tag<bytes::Fixed<{}>, [u8; {len}]>", len),
                    exec_const_decl,
                ),
            }
        } else {
            match mode {
                Mode::Spec => (
                    format!("Refined<bytes::Fixed<{}>, TagPred<Seq<u8>>>", len),
                    spec_const_decl,
                ),
                _ => (
                    format!("Refined<bytes::Fixed<{}>, TagPred<[u8; {len}]>>", len),
                    exec_const_decl,
                ),
            }
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let name = format!("{name}_CONST");
        let combinator_expr = if ctx.wrap {
            match mode {
                Mode::Spec => format!("Tag::spec_new(bytes::Fixed::<{}>, SPEC_{})", self.len, name),
                _ => format!("Tag::new(bytes::Fixed::<{}>, {})", self.len, name),
            }
        } else {
            match mode {
                Mode::Spec => format!(
                    "Refined {{ inner: bytes::Fixed::<{}>, predicate: TagPred(SPEC_{}) }}",
                    self.len, name
                ),
                _ => format!(
                    "Refined {{ inner: bytes::Fixed::<{}>, predicate: TagPred({}) }}",
                    self.len, name
                ),
            }
        };
        (combinator_expr, "".to_string())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodegenOpts {
    All,
    Types,
    Impls,
    Anns,
}

const VEST_PRELUDE: &str = r#"
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest::regular::modifier::*;
use vest::regular::bytes;
use vest::regular::variant::*;
use vest::regular::sequence::*;
use vest::regular::repetition::*;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::utils::*;
use vest::properties::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::leb128::*;

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                closed spec fn ex_requires(&self) -> bool
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
                fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
                fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
            }
        } // verus!
    };
}
"#;

pub fn code_gen(ast: &[Definition], ctx: &GlobalCtx, flags: CodegenOpts) -> String {
    let mut codegen_ctx = CodegenCtx::with_ast(ast, ctx, flags);
    let mut code = String::new();
    let ast = filter_endianess(ast);
    let msg_lifetimes = &codegen_ctx.msg_lifetimes.clone();
    for defn in &ast {
        let msg_lifetime_ann = msg_lifetimes
            .get(match defn {
                Definition::Combinator { name, .. } => name,
                Definition::ConstCombinator { name, .. } => name,
                _ => unimplemented!(),
            })
            .unwrap();
        gen_msg_type_for_definition(defn, &mut code, *msg_lifetime_ann, &codegen_ctx);
        gen_combinator_type_for_definition(defn, &mut code, *msg_lifetime_ann, &mut codegen_ctx);
        gen_combinator_expr_for_definition(defn, &mut code, *msg_lifetime_ann, &mut codegen_ctx);
    }
    VEST_PRELUDE.to_string() + &format!("verus!{{\n{}\n}}\n", code)
}

fn filter_endianess(ast: &[Definition]) -> Vec<Definition> {
    ast.iter()
        .filter(|&defn| !matches!(defn, Definition::Endianess(_)))
        .cloned()
        .collect::<Vec<_>>()
}

fn gen_msg_type_for_definition(
    defn: &Definition,
    code: &mut String,
    lifetime_ann: LifetimeAnn,
    ctx: &CodegenCtx,
) {
    match defn {
        Definition::Combinator {
            name, combinator, ..
        } => {
            if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                code.push_str(&combinator.gen_msg_type(name, Mode::Spec, ctx));
            }
            if !matches!(ctx.flags, CodegenOpts::Anns) {
                code.push_str(&combinator.gen_msg_type(name, Mode::Exec(lifetime_ann), ctx));
            }
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                code.push_str(&const_combinator.gen_msg_type(name, Mode::Spec, ctx));
            }
            if !matches!(ctx.flags, CodegenOpts::Anns) {
                code.push_str(&const_combinator.gen_msg_type(name, Mode::Exec(lifetime_ann), ctx));
            }
        }
        _ => unimplemented!(),
    }
    code.push('\n');
}

fn gen_combinator_type_for_definition(
    defn: &Definition,
    code: &mut String,
    lifetime_ann: LifetimeAnn,
    ctx: &mut CodegenCtx,
) {
    match defn {
        Definition::Combinator {
            name,
            combinator,
            param_defns,
        } => {
            ctx.param_defns = param_defns.clone();
            if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                let (spec_combinator_type, spec_additional_code) =
                    combinator.gen_combinator_type(name, Mode::Spec, ctx);
                code.push_str(&spec_additional_code);
                code.push_str(&spec_combinator_type);
            }
            if matches!(ctx.flags, CodegenOpts::Impls | CodegenOpts::All) {
                let (exec_combinator_type, exec_additional_code) =
                    combinator.gen_combinator_type(name, Mode::Exec(lifetime_ann), ctx);
                code.push_str(&exec_additional_code);
                code.push_str(&exec_combinator_type);
            }
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                let (spec_combinator_type, spec_additional_code) =
                    const_combinator.gen_combinator_type(name, Mode::Spec, ctx);
                code.push_str(&spec_additional_code);
                code.push_str(&spec_combinator_type);
            }
            if matches!(ctx.flags, CodegenOpts::Impls | CodegenOpts::All) {
                let (exec_combinator_type, exec_additional_code) =
                    const_combinator.gen_combinator_type(name, Mode::Exec(lifetime_ann), ctx);
                code.push_str(&exec_additional_code);
                code.push_str(&exec_combinator_type);
            }
        }
        Definition::Endianess(_) => {}
    }
    code.push('\n');
}

fn gen_combinator_expr_for_definition(
    defn: &Definition,
    code: &mut String,
    lifetime_ann: LifetimeAnn,
    ctx: &mut CodegenCtx,
) {
    match defn {
        Definition::Combinator {
            name,
            combinator,
            param_defns,
        } => {
            ctx.param_defns = param_defns.clone();
            if param_defns.is_empty() {
                // no dependencies
                let upper_caml_name = snake_to_upper_caml(name);
                if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                    // spec
                    let (expr, additional_code) =
                        &combinator.gen_combinator_expr(&upper_caml_name, Mode::Spec, ctx);
                    code.push_str(&format!(
                        r#"
pub closed spec fn spec_{name}() -> Spec{upper_caml_name}Combinator {{
    Spec{upper_caml_name}Combinator({expr})
}}
{additional_code}
                "#
                    ));
                }
                if matches!(ctx.flags, CodegenOpts::Impls | CodegenOpts::All) {
                    // exec
                    let (expr, additional_code) = &combinator.gen_combinator_expr(
                        &upper_caml_name,
                        Mode::Exec(lifetime_ann),
                        ctx,
                    );
                    code.push_str(&format!(
                        r#"
pub fn {name}<'a>() -> (o: {upper_caml_name}Combinator)
    ensures o@ == spec_{name}(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{{
    let combinator = {upper_caml_name}Combinator({expr});
    assert({{
        &&& combinator@ == spec_{name}()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    }});
    combinator
}}

pub fn parse_{name}<'a>(input: &'a [u8]) -> (res: PResult<<{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_{name}().spec_parse(input@) == Some((n as int, v@)),
        spec_{name}().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_{name}().spec_parse(input@) is None,
        spec_{name}().spec_parse(input@) is None ==> res is Err,
{{
    let combinator = {name}();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}}

pub fn serialize_{name}<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_{name}().wf(v@),
    ensures
        o matches Ok(n) ==> {{
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_{name}().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_{name}().spec_serialize(v@))
        }},
{{
    let combinator = {name}();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}}

pub fn {name}_len<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_{name}().wf(v@),
        spec_{name}().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_{name}().spec_serialize(v@).len(),
{{
    let combinator = {name}();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}}
{additional_code}
                "#
                    ));
                }
            } else {
                // has dependencies
                let (dep_params_name, (dep_params_spec_type, dep_params_exec_type)): (
                    Vec<_>,
                    (Vec<_>, Vec<_>),
                ) = param_defns
                    .iter()
                    .filter_map(|param_defn| match param_defn {
                        ParamDefn::Dependent { name, combinator } => Some((name, combinator)),
                    })
                    .map(|(name, combinator)| {
                        (
                            name,
                            (
                                combinator.gen_msg_type("", Mode::Spec, &ctx.disable_top_level()),
                                combinator.gen_msg_type(
                                    "",
                                    Mode::Exec(lifetime_ann),
                                    &ctx.disable_top_level(),
                                ),
                            ),
                        )
                    })
                    .unzip();
                let upper_caml_name = snake_to_upper_caml(name);
                // spec
                if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                    let spec_params = std::iter::zip(&dep_params_name, &dep_params_spec_type)
                        .map(|(n, t)| format!("{}: {}", n, t))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let (expr, additional_code) =
                        &combinator.gen_combinator_expr(&upper_caml_name, Mode::Spec, ctx);
                    code.push_str(&format!(
                        r#"
pub closed spec fn spec_{name}({spec_params}) -> Spec{upper_caml_name}Combinator {{
    Spec{upper_caml_name}Combinator({expr})
}}
{additional_code}"#
                    ));
                }
                // exec
                if matches!(ctx.flags, CodegenOpts::Impls | CodegenOpts::All) {
                    let exec_params = std::iter::zip(&dep_params_name, &dep_params_exec_type)
                        .map(|(n, t)| format!("{}: {}", n, t))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let args_iter = dep_params_name.iter().map(|&n| n.to_string());
                    let args_view = args_iter
                        .clone()
                        .map(|n| n + "@")
                        .collect::<Vec<_>>()
                        .join(", ");
                    let args = args_iter.collect::<Vec<_>>().join(", ");
                    let (expr, additional_code) = &combinator.gen_combinator_expr(
                        &upper_caml_name,
                        Mode::Exec(lifetime_ann),
                        ctx,
                    );
                    code.push_str(&format!(
                        r#"
pub fn {name}<'a>({exec_params}) -> (o: {upper_caml_name}Combinator)
    ensures o@ == spec_{name}({args_view}),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{{
    let combinator = {upper_caml_name}Combinator({expr});
    assert({{
        &&& combinator@ == spec_{name}({args_view})
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    }});
    combinator
}}

pub fn parse_{name}<'a>(input: &'a [u8], {exec_params}) -> (res: PResult<<{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_{name}({args_view}).spec_parse(input@) == Some((n as int, v@)),
        spec_{name}({args_view}).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_{name}({args_view}).spec_parse(input@) is None,
        spec_{name}({args_view}).spec_parse(input@) is None ==> res is Err,
{{
    let combinator = {name}( {args} );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}}

pub fn serialize_{name}<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, {exec_params}) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_{name}({args_view}).wf(v@),
    ensures
        o matches Ok(n) ==> {{
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_{name}({args_view}).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_{name}({args_view}).spec_serialize(v@))
        }},
{{
    let combinator = {name}( {args} );
    combinator.serialize(v, data, pos)
}}

pub fn {name}_len<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, {exec_params}) -> (len: usize)
    requires
        spec_{name}({args_view}).wf(v@),
        spec_{name}({args_view}).spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_{name}({args_view}).spec_serialize(v@).len(),
{{
    let combinator = {name}( {args} );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}}
{additional_code}"#
                    ));
                }
            }
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            let upper_caml_name = snake_to_upper_caml(name);
            // spec
            if matches!(ctx.flags, CodegenOpts::Anns | CodegenOpts::All) {
                let (expr, additional_code) =
                    &const_combinator.gen_combinator_expr(&upper_caml_name, Mode::Spec, ctx);
                code.push_str(&format!(
                    r#"
pub closed spec fn spec_{name}() -> Spec{upper_caml_name}Combinator {{
    {expr}
}}
{additional_code}"#
                ));
            }
            if matches!(ctx.flags, CodegenOpts::Impls | CodegenOpts::All) {
                // exec
                let (expr, additional_code) = &const_combinator.gen_combinator_expr(
                    &upper_caml_name,
                    Mode::Exec(lifetime_ann),
                    ctx,
                );
                code.push_str(&format!(
                    r#"
pub fn {name}<'a>() -> (o: {upper_caml_name}Combinator)
    ensures o@ == spec_{name}(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{{
    let combinator = {expr};
    assert({{
        &&& combinator@ == spec_{name}()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    }});
    combinator
}}

pub fn parse_{name}<'a>(input: &'a [u8]) -> (res: PResult<<{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_{name}().spec_parse(input@) == Some((n as int, v@)),
        spec_{name}().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_{name}().spec_parse(input@) is None,
        spec_{name}().spec_parse(input@) is None ==> res is Err,
{{
    let combinator = {name}();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}}

pub fn serialize_{name}<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_{name}().wf(v@),
    ensures
        o matches Ok(n) ==> {{
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_{name}().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_{name}().spec_serialize(v@))
        }},
{{
    let combinator = {name}();
    combinator.serialize(v, data, pos)
}}

pub fn {name}_len<'a>(v: <{upper_caml_name}Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (len: usize)
    requires
        spec_{name}().wf(v@),
        spec_{name}().spec_serialize(v@).len() <= usize::MAX,
    ensures
        len == spec_{name}().spec_serialize(v@).len(),
{{
    let combinator = {name}();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}}
{additional_code}"#
                ));
            }
        }
        Definition::Endianess(_) => {}
    }
    code.push('\n');
}
