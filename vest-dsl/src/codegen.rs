// tempararily disable dead code warning
#![allow(dead_code)]
#![allow(unused_variables)]

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::{collections::HashMap, fmt::Display};

use crate::{
    ast::*,
    elab::build_call_graph,
    type_check::{infer_enum_type, GlobalCtx},
};

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
}

/// format a vector into pairs of tuples, optionally prepended by `prepend`
/// e.g. `["R1", "R2", "R3", "R4"] ==> "prepend(R1, prepend(R2, prepend(R3, R4)))"`
fn fmt_in_pairs<T: Display>(tuples: &[T], prepend: &str, bracket: Bracket) -> String {
    let (left, right) = match bracket {
        Bracket::Parentheses => ("(", ")"),
        Bracket::Angle => ("<", ">"),
        Bracket::Square => ("[", "]"),
    };
    match tuples.split_last() {
        None => String::new(),
        Some((last, rest)) => rest.iter().rfold(last.to_string(), |acc, t| {
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
    ExecOwned,
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

pub struct CodegenCtx<'a> {
    pub format_lifetimes: HashMap<String, LifetimeAnn>,
    pub enums: HashMap<&'a str, EnumCombinator>, // enum name -> enum combinator
    pub param_defns: Vec<ParamDefn>,
    pub endianess: Endianess,
}

impl<'a> CodegenCtx<'a> {
    pub fn new(
        format_lifetimes: HashMap<String, LifetimeAnn>,
        enums: HashMap<&'a str, EnumCombinator>,
        endianness: Endianess,
    ) -> Self {
        Self {
            format_lifetimes,
            enums,
            param_defns: Vec::new(),
            endianess: endianness,
        }
    }

    pub fn with_ast(ast: &[Definition], ctx: &'a GlobalCtx) -> Self {
        // first we need to determine which formats' types need lifetime annotations

        /// helper function to determine if a format needs lifetime annotations
        fn need_lifetime(combinator: &Combinator, ctx: &GlobalCtx) -> bool {
            use CombinatorInner::*;
            let resolved = ctx.resolve(combinator);
            // after resolving, we don't need to consider `and_then` or `invocation` anymore
            match resolved {
                Bytes(_) => true,
                Tail(_) => true,
                Struct(StructCombinator(fields)) => fields.iter().any(|field| match field {
                    StructField::Ordinary { combinator, .. } => need_lifetime(combinator, ctx),
                    StructField::Dependent { combinator, .. } => need_lifetime(combinator, ctx),
                    StructField::Const { combinator, .. } => need_lifetime_const(combinator),
                    _ => unimplemented!(),
                }),
                Wrap(WrapCombinator {
                    prior,
                    combinator,
                    post,
                }) => {
                    prior.iter().any(need_lifetime_const)
                        || need_lifetime(combinator, ctx)
                        || post.iter().any(need_lifetime_const)
                }
                Choice(ChoiceCombinator { choices, .. }) => match choices {
                    Choices::Enums(enums) => enums
                        .iter()
                        .any(|(_, combinator)| need_lifetime(combinator, ctx)),
                    Choices::Ints(ints) => ints
                        .iter()
                        .any(|(_, combinator)| need_lifetime(combinator, ctx)),
                    Choices::Arrays(arrays) => arrays
                        .iter()
                        .any(|(_, combinator)| need_lifetime(combinator, ctx)),
                },
                SepBy(SepByCombinator { combinator, sep }) => {
                    let combinator = Combinator {
                        inner: Vec(combinator.clone()),
                        and_then: None,
                    };
                    need_lifetime(&combinator, ctx) || need_lifetime_const(sep)
                }
                Vec(VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator)) => {
                    need_lifetime(combinator, ctx)
                }
                Array(ArrayCombinator { combinator, .. }) => need_lifetime(combinator, ctx),
                Option(OptionCombinator(combinator)) => need_lifetime(combinator, ctx),
                ConstraintInt(_) | Enum(_) | Apply(_) => false,
                Invocation(_) => unreachable!("invocation should be resolved by now"),
            }
        }

        /// helper function to determine if a const format needs lifetime annotations
        fn need_lifetime_const(const_combinator: &ConstCombinator) -> bool {
            match const_combinator {
                ConstCombinator::ConstArray(_) => true, // TODO: can be more fine-grained
                ConstCombinator::ConstBytes(_) => true, // TODO: can be more fine-grained
                ConstCombinator::ConstStruct(ConstStructCombinator(fields)) => {
                    fields.iter().any(need_lifetime_const)
                }
                ConstCombinator::ConstChoice(ConstChoiceCombinator(choices)) => choices
                    .iter()
                    .any(|ConstChoice { combinator, .. }| need_lifetime_const(combinator)),
                ConstCombinator::Vec(combinator) => need_lifetime_const(combinator),
                ConstCombinator::ConstInt(_) | ConstCombinator::ConstCombinatorInvocation(_) => {
                    false
                }
            }
        }
        // init the format lifetimes with None
        let mut format_lifetimes: HashMap<String, LifetimeAnn> = HashMap::new();
        for defn in ast {
            match defn {
                Definition::Combinator { name, .. } => {
                    format_lifetimes.insert(name.to_string(), LifetimeAnn::None);
                }
                Definition::ConstCombinator { name, .. } => {
                    format_lifetimes.insert(name.to_string(), LifetimeAnn::None);
                }
                _ => {}
            }
        }

        // default endianness is little
        let mut endianness = Endianess::Little;
        let call_graph = build_call_graph(ast);
        // NOTE: by now ast should already be topologically sorted
        ast.iter().for_each(|defn| match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                // let invocations = call_graph.get(name).unwrap();
                let lifetime = if need_lifetime(combinator, ctx) {
                    LifetimeAnn::Some
                } else {
                    LifetimeAnn::None
                };
                format_lifetimes.insert(name.to_string(), lifetime);
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
            } => {
                let invocations = call_graph.get(name).unwrap();
                let lifetime = if invocations
                    .iter()
                    .any(|name| format_lifetimes.get(name).unwrap() == &LifetimeAnn::Some)
                    || need_lifetime_const(const_combinator)
                {
                    LifetimeAnn::Some
                } else {
                    LifetimeAnn::None
                };
                format_lifetimes.insert(name.to_string(), lifetime);
            }
            Definition::Endianess(end) => {
                endianness = *end;
            }
            _ => {}
        });

        Self::new(format_lifetimes, ctx.enums.clone(), endianness)
    }
}

trait Codegen {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String;
    /// will generate a pair of (combinator type, additional code), where additional code can be
    /// - refined predicates for `ConstraintInt`
    /// - constant int and array declarations
    /// - type declaration for continuations of dependent structs
    /// - additional code recursively generated from the inner combinators for `Struct` and `Choice`
    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String);
    /// will generate a pair of (combinator expr, additional code), where additional code can be
    /// - the continuation of the second half of a dependent struct
    /// - additional code recursively generated from the inner combinators
    ///
    /// The `name` parameter is used to
    /// - generate the wrapper type for the combinator definition
    /// - refer to the XXXMapper
    /// - refer to the `UPPER_CAML` const int for `ConstIntCombinator`
    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String);
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

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let name = &snake_to_upper_caml(name);
        let spec = match mode {
            Mode::Spec => "Spec",
            _ => "",
        };
        let wrapper_code = || match mode {
            Mode::Spec => format!(
                r#"
pub struct Spec{name}Combinator(Spec{name}CombinatorAlias);

impl SpecCombinator for Spec{name}Combinator {{
    type SpecResult = Spec{name};
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    {{ self.0.spec_parse(s) }}
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    {{ self.0.spec_serialize(v) }}
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    {{ self.0.spec_parse_wf(s) }}

}}
impl SecureSpecCombinator for Spec{name}Combinator {{
    open spec fn is_prefix_secure() -> bool 
    {{ Spec{name}CombinatorAlias::is_prefix_secure() }}
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    {{ self.0.theorem_serialize_parse_roundtrip(v) }}
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {{ self.0.theorem_parse_serialize_roundtrip(buf) }}
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {{ self.0.lemma_prefix_secure(s1, s2) }}
}}
"#
            ),
            Mode::Exec(_) => {
                let lifetime_ann = match mode {
                    Mode::Exec(LifetimeAnn::Some) => "<'a>",
                    _ => "",
                };
                format!(
                    r#"
pub struct {name}Combinator({name}CombinatorAlias);

impl View for {name}Combinator {{
    type V = Spec{name}Combinator;
    closed spec fn view(&self) -> Self::V {{ Spec{name}Combinator(self.0@) }}
}}
impl Combinator for {name}Combinator {{
    type Result<'a> = {name}{lifetime_ann};
    type Owned = {name}Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    {{ self.0.spec_length() }}
    fn length(&self) -> Option<usize> 
    {{ self.0.length() }}
    closed spec fn parse_requires(&self) -> bool 
    {{ self.0.parse_requires() }}
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    {{ self.0.parse(s) }}
    closed spec fn serialize_requires(&self) -> bool 
    {{ self.0.serialize_requires() }}
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {{ self.0.serialize(v, data, pos) }}
}} 
"#
                )
            }
            _ => "".to_string(),
        };
        if let Some(and_then) = &self.and_then {
            let (comb_type, additional_code) = self.inner.gen_combinator_type(name, mode, ctx); // must be `Bytes` or `Tail`
            let (and_then_comb_type, and_then_additional_code) =
                and_then.inner.gen_combinator_type(name, mode, ctx);
            if name.is_empty() {
                (
                    format!("AndThen<{comb_type}, {and_then_comb_type}>"),
                    additional_code + &and_then_additional_code,
                )
            } else {
                (
                    format!(
                        "pub type {spec}{name}CombinatorAlias = AndThen<{comb_type}, {and_then_comb_type}>;\n"
                    ),
                    additional_code + &and_then_additional_code + &wrapper_code(),
                )
            }
        } else if name.is_empty() {
            self.inner.gen_combinator_type(name, mode, ctx)
        } else {
            let (combinator_type, additional_code) =
                self.inner.gen_combinator_type(name, mode, ctx);
            (
                format!("pub type {spec}{name}CombinatorAlias = {combinator_type};\n"),
                additional_code + &wrapper_code(),
            )
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        if let Some(and_then) = &self.and_then {
            let (comb_expr, additional_code) =
                self.inner.gen_combinator_expr(false, name, mode, ctx);
            let (and_then_comb_expr, and_then_additional_code) =
                and_then.inner.gen_combinator_expr(false, name, mode, ctx);
            let combinator_expr = format!("AndThen({}, {})", comb_expr, and_then_comb_expr);
            (combinator_expr, additional_code + &and_then_additional_code)
        } else {
            self.inner.gen_combinator_expr(top_level, name, mode, ctx)
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

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Bytes(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Tail(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Invocation(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Struct(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Enum(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Choice(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Array(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Vec(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::SepBy(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Wrap(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Apply(p) => p.gen_combinator_type(name, mode, ctx),
            CombinatorInner::Option(p) => p.gen_combinator_type(name, mode, ctx),
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Bytes(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Tail(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Invocation(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Struct(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Enum(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Choice(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Array(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Vec(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::SepBy(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Wrap(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Apply(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
            CombinatorInner::Option(p) => p.gen_combinator_expr(top_level, name, mode, ctx),
        }
    }
}

impl Codegen for ConstraintIntCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, _ctx: &CodegenCtx) -> String {
        let int_type = format!("{}", self.combinator);
        if name.is_empty() {
            int_type
        } else {
            let type_alias_name = match mode {
                Mode::Spec => &format!("Spec{}", name),
                Mode::Exec(_) => name,
                Mode::ExecOwned => &format!("{}Owned", name),
            };

            format!("pub type {} = {};\n", type_alias_name, int_type)
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
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
            IntCombinator::Signed(..) => unimplemented!(),
        };
        if let Some(constraint) = &self.constraint {
            let hash = compute_hash(constraint);
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
            let (spec_as_u32, as_u32) = if input_type == "u24" {
                (".spec_as_u32()", ".as_u32()")
            } else {
                ("", "")
            };
            let constraints = gen_constraints(constraint);
            let impl_spec_pred = format!(
                r#"impl SpecPred for Predicate{hash} {{
    type Input = {input_type};

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {{
        let i = (*i){spec_as_u32};
        if {constraints} {{
            true
        }} else {{
            false
        }}
    }}
}}
"#
            );
            let impl_exec_pred = format!(
                r#"impl Pred for Predicate{hash} {{
    type Input<'a> = {input_type};
    type InputOwned = {input_type};

    fn apply(&self, i: &Self::Input<'_>) -> bool {{
        let i = (*i){as_u32};
        if {constraints} {{
            true
        }} else {{
            false
        }}
    }}
}}
"#
            );
            let additional_code = match mode {
                Mode::Spec => impl_spec_pred,
                _ => pred_defn + &impl_view + &impl_exec_pred,
            };
            (
                format!("Refined<{}, Predicate{}>", int_type, hash),
                additional_code,
            )
        } else {
            (int_type, "".to_string())
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let endianess = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        let int_type = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => "U8".to_string(),
            IntCombinator::Unsigned(t) => format!("U{}{}", t, endianess),
            IntCombinator::Signed(..) => unimplemented!(),
        };
        if let Some(constraint) = &self.constraint {
            let combinator_expr = format!(
                "Refined {{ inner: {}, predicate: Predicate{} }}",
                int_type,
                compute_hash(constraint)
            );
            (combinator_expr, "".to_string())
        } else {
            let combinator_expr = int_type;
            (combinator_expr, "".to_string())
        }
    }
}

impl Codegen for BytesCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, _ctx: &CodegenCtx) -> String {
        let type_name = match mode {
            Mode::Spec => "Seq<u8>".to_string(),
            Mode::Exec(LifetimeAnn::Some) => "&'a [u8]".to_string(),
            _ => "Vec<u8>".to_string(),
        };
        if name.is_empty() {
            type_name
        } else {
            let type_alias_name = match mode {
                Mode::Spec => &format!("Spec{}", name),
                Mode::Exec(LifetimeAnn::Some) => &format!("{}{}", name, "<'a>"),
                Mode::Exec(LifetimeAnn::None) => name,
                Mode::ExecOwned => &format!("{}Owned", name),
            };
            format!("pub type {} = {};\n", type_alias_name, type_name)
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        match &self.len {
            LengthSpecifier::Const(len) => (format!("BytesN<{}>", len), "".to_string()),
            LengthSpecifier::Dependent(..) => ("Bytes".to_string(), "".to_string()),
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let into = match mode {
            Mode::Spec => ".spec_into()",
            _ => ".ex_into()",
        };
        match &self.len {
            LengthSpecifier::Const(len) => {
                let combinator_expr = format!("BytesN::<{}>", len);
                (combinator_expr, "".to_string())
            }
            LengthSpecifier::Dependent(depend_id) => {
                let combinator_expr = format!("Bytes({}{})", depend_id, into);
                (combinator_expr, "".to_string())
            }
        }
    }
}

impl Codegen for TailCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        if name.is_empty() {
            match mode {
                Mode::Spec => "Seq<u8>".to_string(),
                Mode::Exec(LifetimeAnn::Some) => "&'a [u8]".to_string(),
                _ => "Vec<u8>".to_string(),
            }
        } else {
            panic!("`Tail` should not be a top-level definition")
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        if name.is_empty() {
            ("Tail".to_string(), "".to_string())
        } else {
            panic!("`Tail` should not be a top-level definition")
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        ("Tail".to_string(), "".to_string())
    }
}

impl Codegen for CombinatorInvocation {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let invocked = snake_to_upper_caml(&self.func);
        let invocked = match mode {
            Mode::Spec => format!("Spec{}", invocked),
            Mode::Exec(_) => invocked.to_owned(),
            Mode::ExecOwned => format!("{}Owned", invocked),
        };
        let lifetime = match mode {
            Mode::Exec(LifetimeAnn::Some) => {
                let lifetime = ctx.format_lifetimes.get(&self.func).unwrap_or_else(|| {
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
        if name.is_empty() {
            format!("{}{}", invocked, lifetime)
        } else {
            let name = match mode {
                Mode::Spec => format!("Spec{}", name),
                Mode::Exec(_) => name.to_owned(),
                Mode::ExecOwned => format!("{}Owned", name),
            };
            format!(
                "pub type {}{} = {}{};\n",
                name, lifetime, invocked, lifetime
            )
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let invocked = snake_to_upper_caml(&self.func);
        let spec = match mode {
            Mode::Spec => "Spec",
            _ => "",
        };
        (format!("{spec}{invocked}Combinator"), "".to_string())
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let invocked = match mode {
            Mode::Spec => format!("spec_{}", &self.func),
            Mode::Exec(_) => self.func.to_owned(),
            _ => unreachable!(),
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

#[derive(Debug)]
enum FieldKind {
    Ordinary,
    Dependent,
}

impl StructCombinator {
    /// divide the fields into two halves based on the last dependent field (if any)
    fn split_at_last_dependent(&self) -> (&[StructField], &[StructField]) {
        self.0.split_at(
            self.0
                .iter()
                .rposition(|field| matches!(field, StructField::Dependent { .. }))
                .map(|i| i + 1)
                .unwrap_or(0),
        )
    }
}

impl Codegen for StructCombinator {
    /// assuming all structs are top-level definitions
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let mut code = String::new();

        let msg_type_name = match mode {
            Mode::Spec => format!("Spec{}", name),
            Mode::Exec(_) => name.to_string(),
            Mode::ExecOwned => format!("{}Owned", name),
        };
        let lifetime_ann = match mode {
            Mode::Exec(LifetimeAnn::Some) => "<'a>",
            _ => "",
        };
        let derive = match mode {
            Mode::Exec(_) => "#[derive(Debug, Clone, PartialEq, Eq)]\n",
            _ => "",
        };
        // generate the struct
        code.push_str(&format!(
            "{}pub struct {}{} {{\n",
            derive, msg_type_name, lifetime_ann
        ));
        let mut fields = Vec::new();
        for field in &self.0 {
            match field {
                StructField::Ordinary { label, combinator } => {
                    let field_type = combinator.gen_msg_type("", mode, ctx);
                    code.push_str(&format!("    pub {}: {},\n", label, &field_type));
                    fields.push((FieldKind::Ordinary, label.to_string(), field_type));
                }
                StructField::Dependent { label, combinator } => {
                    let field_type = combinator.gen_msg_type("", mode, ctx);
                    code.push_str(&format!("    pub {}: {},\n", label, &field_type));
                    fields.push((FieldKind::Dependent, label.to_string(), field_type));
                }
                StructField::Const { label, combinator } => {
                    let field_type = combinator.gen_msg_type("", mode, ctx);
                    code.push_str(&format!("    pub {}: {},\n", label, &field_type));
                    fields.push((FieldKind::Ordinary, label.to_string(), field_type));
                }
                _ => todo!(),
            }
        }
        code.push_str("}\n");

        // NOTE: this is for the sake of simplicity, we can do better
        let (fst, snd) = fields.split_at(
            fields
                .iter()
                .rposition(|(kind, _, _)| matches!(kind, FieldKind::Dependent))
                .map(|i| i + 1)
                .unwrap_or(0),
        );

        // generate the struct inner
        let msg_type_inner_name = msg_type_name.clone() + "Inner";
        let msg_type_inner = if fst.is_empty() {
            fmt_in_pairs(
                &snd.iter()
                    .map(|(_, _, field_type)| field_type)
                    .collect::<Vec<_>>(),
                "",
                Bracket::Parentheses,
            )
        } else {
            format!(
                "({}, {})",
                fmt_in_pairs(
                    &fst.iter()
                        .map(|(_, _, field_type)| field_type)
                        .collect::<Vec<_>>(),
                    "",
                    Bracket::Parentheses
                ),
                fmt_in_pairs(
                    &snd.iter()
                        .map(|(_, _, field_type)| field_type)
                        .collect::<Vec<_>>(),
                    "",
                    Bracket::Parentheses
                ),
            )
        };
        code.push_str(&format!(
            "pub type {}{} = {};\n",
            msg_type_inner_name, lifetime_ann, msg_type_inner
        ));

        // impl View for exec struct(s)
        match mode {
            Mode::Exec(_) | Mode::ExecOwned => {
                let lifetime = match mode {
                    Mode::Exec(LifetimeAnn::Some) => "<'_>",
                    Mode::Exec(LifetimeAnn::None) => "",
                    Mode::ExecOwned => "",
                    _ => unreachable!(),
                };
                code.push_str(&format!(
                    r#"impl View for {}{} {{
    type V = Spec{};
    open spec fn view(&self) -> Self::V {{
        Spec{} {{
"#,
                    msg_type_name, lifetime, name, name
                ));
                for (_, label, _) in &fields {
                    code.push_str(&format!("            {}: self.{}@,\n", label, label));
                }
                code.push_str("        }\n    }\n}\n");
            }
            Mode::Spec => {}
        }

        // impl (Spec)From
        let trait_name = match mode {
            Mode::Spec => "SpecFrom",
            _ => "From",
        };
        let assoc_func_name = match mode {
            Mode::Spec => "spec_from",
            _ => "ex_from",
        };
        // ["a", "b", "c", "d"]
        let field_names_fst = fst.iter().map(|(_, name, _)| name).collect::<Vec<_>>();
        let field_names_snd = snd.iter().map(|(_, name, _)| name).collect::<Vec<_>>();
        // ["m.a", "m.b", "m.c", "m.d"]
        let dot_field_names_fst = field_names_fst
            .iter()
            .map(|name| format!("m.{}", name))
            .collect::<Vec<_>>();
        let dot_field_names_snd = field_names_snd
            .iter()
            .map(|name| format!("m.{}", name))
            .collect::<Vec<_>>();
        // "(((m.a, m.b), m.c), m.d)", "(((a, b), c), d)"
        let (inner_constructor, inner_destructor) = if fst.is_empty() {
            (
                fmt_in_pairs(&dot_field_names_snd, "", Bracket::Parentheses),
                fmt_in_pairs(&field_names_snd, "", Bracket::Parentheses),
            )
        } else {
            (
                format!(
                    "({}, {})",
                    fmt_in_pairs(&dot_field_names_fst, "", Bracket::Parentheses),
                    fmt_in_pairs(&dot_field_names_snd, "", Bracket::Parentheses)
                ),
                format!(
                    "({}, {})",
                    fmt_in_pairs(&field_names_fst, "", Bracket::Parentheses),
                    fmt_in_pairs(&field_names_snd, "", Bracket::Parentheses)
                ),
            )
        };
        code.push_str(&format!(
            "impl{} {}<{}{}> for {}{} {{\n",
            lifetime_ann,
            trait_name,
            msg_type_name,
            lifetime_ann,
            msg_type_inner_name,
            lifetime_ann
        ));
        match mode {
            Mode::Spec => {
                code.push_str(&format!(
                    "    open spec fn {}(m: {}) -> {} {{\n        {}\n    }}\n",
                    assoc_func_name, msg_type_name, msg_type_inner_name, inner_constructor
                ));
            }
            _ => {
                code.push_str(&format!(
                    "    fn {}(m: {}{}) -> {}{} {{\n        {}\n    }}\n",
                    assoc_func_name,
                    msg_type_name,
                    lifetime_ann,
                    msg_type_inner_name,
                    lifetime_ann,
                    inner_constructor
                ));
            }
        }
        code.push_str("}\n");

        code.push_str(&format!(
            "impl{} {}<{}{}> for {}{} {{\n",
            lifetime_ann,
            trait_name,
            msg_type_inner_name,
            lifetime_ann,
            msg_type_name,
            lifetime_ann
        ));
        match mode {
            Mode::Spec => {
                code.push_str(&format!(
                    r#"    open spec fn {}(m: {}) -> {} {{
        let {} = m;
        {} {{
"#,
                    assoc_func_name,
                    msg_type_inner_name,
                    msg_type_name,
                    inner_destructor,
                    msg_type_name
                ));
            }
            _ => {
                code.push_str(&format!(
                    r#"    fn {}(m: {}{}) -> {}{} {{
        let {} = m;
        {} {{
"#,
                    assoc_func_name,
                    msg_type_inner_name,
                    lifetime_ann,
                    msg_type_name,
                    lifetime_ann,
                    inner_destructor,
                    msg_type_name
                ));
            }
        }
        for (_, label, _) in &fields {
            code.push_str(&format!("            {},\n", label));
        }

        code.push_str("        }\n    }\n");
        code.push_str("}\n");

        // impl Mapper for Exec
        if let Mode::Exec(_) = mode {
            code.push_str(&gen_mapper(name, &msg_type_name, lifetime_ann));
        }

        code
    }

    /// assuming all structs are top-level definitions
    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let (fst, snd) = self.split_at_last_dependent();
        let combinator_type_from_field = |field: &StructField| match field {
            StructField::Ordinary { combinator, .. }
            | StructField::Dependent { combinator, .. } => {
                combinator.gen_combinator_type("", mode, ctx)
            }
            StructField::Const { label, combinator } => {
                let name = &lower_snake_to_upper_snake(&(name.to_owned() + "_" + label));
                combinator.gen_combinator_type(name, mode, ctx)
            }
            _ => todo!(),
        };
        if fst.is_empty() {
            // no dependent fields
            let snd_comb_types = snd
                .iter()
                .map(combinator_type_from_field)
                .map(|(t, _)| t)
                .collect::<Vec<_>>();
            let inner = fmt_in_pairs(&snd_comb_types, "", Bracket::Parentheses);
            let additional_code = snd
                .iter()
                .map(combinator_type_from_field)
                .map(|(_, code)| code)
                .collect::<Vec<_>>()
                .join("");
            (
                format!("Mapped<{}, {}Mapper>", inner, name),
                additional_code,
            )
        } else {
            let (fst, snd) = (
                fst.iter()
                    .map(combinator_type_from_field)
                    .collect::<Vec<_>>(),
                snd.iter()
                    .map(combinator_type_from_field)
                    .collect::<Vec<_>>(),
            );
            let (fst_comb_type, snd_comb_types) = (
                fmt_in_pairs(
                    &fst.iter().map(|(t, _)| t).collect::<Vec<_>>(),
                    "",
                    Bracket::Parentheses,
                ),
                fmt_in_pairs(
                    &snd.iter().map(|(t, _)| t).collect::<Vec<_>>(),
                    "",
                    Bracket::Parentheses,
                ),
            );
            let inner = match mode {
                Mode::Spec => format!("SpecDepend<{fst_comb_type}, {snd_comb_types}>"),
                _ => format!("Depend<{fst_comb_type}, {snd_comb_types}, {name}Cont>"),
            };
            let cont_struct = match mode {
                Mode::Spec => "".to_string(),
                _ => format!("pub struct {}Cont;", name),
            };
            let additional_code = fst
                .iter()
                .chain(snd.iter())
                .map(|(_, code)| code.to_string())
                .collect::<Vec<_>>()
                .join("");
            (
                format!("Mapped<{}, {}Mapper>", inner, name),
                additional_code + &cont_struct,
            )
        }
    }

    fn gen_combinator_expr(
        &self,
        _top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let (fst, snd) = self.split_at_last_dependent();
        if fst.is_empty() {
            // no dependent fields
            let (inner, additional_code): (Vec<String>, Vec<String>) = snd
                .iter()
                .map(|field| match field {
                    StructField::Ordinary { combinator, label }
                    | StructField::Dependent { combinator, label } => combinator
                        .gen_combinator_expr(
                            false,
                            &snake_to_upper_caml(&(name.to_owned() + "_" + label)),
                            mode,
                            ctx,
                        ),
                    StructField::Const { label, combinator } => {
                        let name = &lower_snake_to_upper_snake(&(name.to_owned() + "_" + label));
                        combinator.gen_combinator_expr(false, name, mode, ctx)
                    }
                    _ => todo!(),
                })
                .unzip();
            (
                format!(
                    "Mapped {{ inner: {}, mapper: {}Mapper }}",
                    fmt_in_pairs(&inner, "", Bracket::Parentheses),
                    name
                ),
                additional_code.join(""),
            )
        } else {
            // struct has dependent fields
            type Nested<T> = (Vec<T>, (Vec<T>, (Vec<T>, Vec<T>)));
            let (fst_bindings, (fst_msg_types, (fst_exprs, fst_code))): Nested<_> = fst
                .iter()
                .map(|field| match field {
                    StructField::Ordinary { combinator, .. } => (
                        "_".to_owned(),
                        (
                            combinator.gen_msg_type("", mode, ctx),
                            combinator.gen_combinator_expr(false, "", mode, ctx),
                        ),
                    ),
                    StructField::Dependent { label, combinator } => (
                        label.to_owned(),
                        (
                            combinator.gen_msg_type("", mode, ctx),
                            combinator.gen_combinator_expr(false, "", mode, ctx),
                        ),
                    ),
                    StructField::Const { label, combinator } => {
                        let name = &lower_snake_to_upper_snake(&(name.to_owned() + "_" + label));
                        (
                            "_".to_owned(),
                            (
                                combinator.gen_msg_type("", mode, ctx),
                                combinator.gen_combinator_expr(false, name, mode, ctx),
                            ),
                        )
                    }
                    _ => todo!(),
                })
                .unzip();
            let fst_bindings = fmt_in_pairs(&fst_bindings, "", Bracket::Parentheses);
            let fst_msg_type = fmt_in_pairs(&fst_msg_types, "", Bracket::Parentheses);
            let (snd_combinator_types, (snd_exprs, snd_code)): (Vec<_>, (Vec<_>, Vec<_>)) = snd
                .iter()
                .map(|field| match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => (
                        combinator.gen_combinator_type("", mode, ctx).0,
                        combinator.gen_combinator_expr(false, "", mode, ctx),
                    ),
                    _ => todo!(),
                })
                .unzip();
            let snd_combinator_types =
                fmt_in_pairs(&snd_combinator_types, "", Bracket::Parentheses);
            let snd_exprs = fmt_in_pairs(&snd_exprs, "", Bracket::Parentheses);
            let snaked_name = upper_camel_to_snake(name);
            let fst_expr = fmt_in_pairs(&fst_exprs, "", Bracket::Parentheses);
            let expr = match mode {
                Mode::Spec => {
                    format!(
                        r#"
    Mapped {{
        inner: SpecDepend {{
            fst: {fst_expr},
            snd: |deps| spec_{snaked_name}_cont(deps),
        }},
        mapper: {name}Mapper,
    }}
"#,
                    )
                }
                _ => {
                    format!(
                        r#"
    Mapped {{
        inner: Depend {{
            fst: {fst_expr},
            snd: {name}Cont,
            spec_snd: Ghost(|deps| spec_{snaked_name}_cont(deps)),
        }},
        mapper: {name}Mapper,
    }}
"#,
                    )
                }
            };
            let additional_code = match mode {
                Mode::Spec => {
                    format!(
                        r#"
pub open spec fn spec_{snaked_name}_cont(deps: {fst_msg_type}) -> {snd_combinator_types} {{
    let {fst_bindings} = deps;
    {snd_exprs}
}}
"#
                    )
                }
                _ => {
                    format!(
                        r#"
impl Continuation<{fst_msg_type}> for {name}Cont {{
    type Output = {snd_combinator_types};

    open spec fn requires(&self, deps: {fst_msg_type}) -> bool {{
        true
    }}

    open spec fn ensures(&self, deps: {fst_msg_type}, o: Self::Output) -> bool {{
        o@ == spec_{snaked_name}_cont(deps@)
    }}

    fn apply(&self, deps: {fst_msg_type}) -> Self::Output {{
        let {fst_bindings} = deps;
        {snd_exprs}
    }}
}}
"#
                    )
                }
            };
            (
                expr,
                fst_code.join("") + &snd_code.join("") + &additional_code,
            )
        }
    }
}

impl Codegen for EnumCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, _ctx: &CodegenCtx) -> String {
        match &self {
            EnumCombinator::NonExhaustive { enums } => {
                let inferred = infer_enum_type(enums);
                if name.is_empty() {
                    panic!("`Enum` should be a top-level definition")
                } else {
                    // alias to the inferred type
                    let alias_name = match mode {
                        Mode::Spec => format!("Spec{}", name),
                        Mode::Exec(..) => name.to_string(),
                        Mode::ExecOwned => format!("{}Owned", name),
                    };
                    format!("pub type {} = {};\n", alias_name, inferred)
                }
            }
            EnumCombinator::Exhaustive { enums } => {
                // since the spec, exec, and exec_owned types are the same, we only need to
                // generate one of them
                if let Mode::Spec = mode {
                    let inferred = infer_enum_type(enums);
                    if name.is_empty() {
                        panic!("`Enum` should be a top-level definition")
                    } else {
                        let msg_type_name = name;
                        let enum_variants = enums
                            .iter()
                            .map(|e| format!("{e}"))
                            .collect::<Vec<_>>()
                            .join(",\n");
                        let try_from_int_match_arms = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                format!("{}{} => Ok({}::{}),", value, inferred, msg_type_name, name)
                            })
                            .collect::<Vec<_>>()
                            .join("\n            ");
                        let try_from_enum_match_arms = enums
                            .iter()
                            .map(|Enum { name, value }| {
                                format!("{}::{} => Ok({}{}),", msg_type_name, name, value, inferred)
                            })
                            .collect::<Vec<_>>()
                            .join("\n            ");
                        format!(
                            r#"
#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum {msg_type_name} {{
    {enum_variants}
}}
pub type Spec{msg_type_name} = {msg_type_name};
pub type {msg_type_name}Owned = {msg_type_name};

pub type {msg_type_name}Inner = {inferred};

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
            {try_from_enum_match_arms}
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

impl TryFrom<{msg_type_name}> for {msg_type_name}Inner {{
    type Error = ();

    fn ex_try_from(v: {msg_type_name}) -> Result<{msg_type_name}Inner, ()> {{
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

impl SpecTryFromInto for {msg_type_name}Mapper {{
    type Src = {msg_type_name}Inner;
    type Dst = {msg_type_name};

    proof fn spec_iso(s: Self::Src) {{}}

    proof fn spec_iso_rev(s: Self::Dst) {{}}
}}

impl TryFromInto for {msg_type_name}Mapper {{
    type Src<'a> = {msg_type_name}Inner;
    type Dst<'a> = {msg_type_name};

    type SrcOwned = {msg_type_name}Inner;
    type DstOwned = {msg_type_name};
}}
"#
                        )
                    }
                } else {
                    "".to_string()
                }
            }
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let endianness = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        match &self {
            EnumCombinator::Exhaustive { enums } => {
                let inferred = infer_enum_type(enums);
                let int_type = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                };
                (
                    format!("TryMap<{}, {}Mapper>", int_type, name),
                    "".to_string(),
                )
            }
            EnumCombinator::NonExhaustive { enums } => {
                let inferred = infer_enum_type(enums);
                match inferred {
                    IntCombinator::Unsigned(8) => ("U8".to_string(), "".to_string()),
                    IntCombinator::Unsigned(t) => (format!("U{}{}", t, endianness), "".to_string()),
                    IntCombinator::Signed(..) => unimplemented!(),
                }
            }
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let endianness = match ctx.endianess {
            Endianess::Little => "Le",
            Endianess::Big => "Be",
        };
        let spec = match mode {
            Mode::Spec => "Spec",
            _ => "",
        };
        match &self {
            EnumCombinator::Exhaustive { enums } => {
                let inferred = infer_enum_type(enums);
                let int_type = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                };
                let combinator_expr =
                    format!("TryMap {{ inner: {}, mapper: {}Mapper }}", int_type, name);
                (combinator_expr, "".to_string())
            }
            EnumCombinator::NonExhaustive { enums } => {
                let inferred = infer_enum_type(enums);
                let int_combinator = match inferred {
                    IntCombinator::Unsigned(8) => "U8".to_string(),
                    IntCombinator::Unsigned(t) => format!("U{}{}", t, endianness),
                    IntCombinator::Signed(..) => unimplemented!(),
                };
                let combinator_expr = int_combinator;
                (combinator_expr, "".to_string())
            }
        }
    }
}

impl Codegen for ChoiceCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let mut code = String::new();
        match &self.choices {
            Choices::Enums(enums) => {
                let msg_type_name = match mode {
                    Mode::Spec => format!("Spec{}", name),
                    Mode::Exec(_) => name.to_string(),
                    Mode::ExecOwned => format!("{}Owned", name),
                };
                let lifetime_ann = match mode {
                    Mode::Exec(LifetimeAnn::Some) => "<'a>",
                    _ => "",
                };
                let derive = match mode {
                    Mode::Exec(_) => "#[derive(Debug, Clone, PartialEq, Eq)]\n",
                    _ => "",
                };
                // generate the enum
                code.push_str(&format!(
                    "{}pub enum {}{} {{\n",
                    derive, msg_type_name, lifetime_ann
                ));
                let mut variants = Vec::new();
                for (label, combinator) in enums {
                    let variant_type = combinator.gen_msg_type("", mode, ctx);
                    let label = if label == "_" { "Unrecognized" } else { label };
                    code.push_str(&format!("    {}({}),\n", label, variant_type));
                    variants.push((label.to_string(), variant_type));
                }
                code.push_str("}\n");

                // generate the enum inner
                let msg_type_inner_name = msg_type_name.clone() + "Inner";
                code.push_str(&format!(
                    "pub type {}{} = {};\n",
                    msg_type_inner_name,
                    lifetime_ann,
                    fmt_in_pairs(
                        &variants
                            .iter()
                            .map(|(_, variant_type)| variant_type)
                            .collect::<Vec<_>>(),
                        "Either",
                        Bracket::Angle
                    ),
                ));

                // impl View for exec enums
                match mode {
                    Mode::Exec(_) | Mode::ExecOwned => {
                        let lifetime = match mode {
                            Mode::Exec(LifetimeAnn::Some) => "<'_>",
                            Mode::Exec(LifetimeAnn::None) => "",
                            Mode::ExecOwned => "",
                            _ => unreachable!(),
                        };
                        code.push_str(&format!(
                            r#"impl View for {}{} {{
    type V = Spec{};
    open spec fn view(&self) -> Self::V {{
        match self {{
"#,
                            msg_type_name, lifetime, name
                        ));
                        for (label, _) in &variants {
                            code.push_str(&format!(
                                "            {}::{}(m) => Spec{}::{}(m@),\n",
                                msg_type_name, label, name, label
                            ));
                        }
                        code.push_str("        }\n    }\n}\n");
                    }
                    Mode::Spec => {}
                }

                // impl (Spec)From
                let trait_name = match mode {
                    Mode::Spec => "SpecFrom",
                    _ => "From",
                };
                let assoc_func_name = match mode {
                    Mode::Spec => "spec_from",
                    _ => "ex_from",
                };
                if variants.len() < 2 {
                    panic!("`Choice` should have at least two variants")
                }
                let nested_eithers = gen_nested_eithers(variants.len(), "m");
                code.push_str(&format!(
                    "impl{} {}<{}{}> for {}{} {{\n",
                    lifetime_ann,
                    trait_name,
                    msg_type_name,
                    lifetime_ann,
                    msg_type_inner_name,
                    lifetime_ann
                ));
                match mode {
                    Mode::Spec => {
                        code.push_str(&format!(
                            "    open spec fn {}(m: {}) -> {} {{\n        match m {{\n",
                            assoc_func_name, msg_type_name, msg_type_inner_name
                        ));
                    }
                    _ => {
                        code.push_str(&format!(
                            "    fn {}(m: {}{}) -> {}{} {{\n        match m {{\n",
                            assoc_func_name,
                            msg_type_name,
                            lifetime_ann,
                            msg_type_inner_name,
                            lifetime_ann
                        ));
                    }
                }
                std::iter::zip(&variants, &nested_eithers).for_each(|((label, _), nested)| {
                    code.push_str(&format!(
                        "            {}::{}(m) => {},\n",
                        msg_type_name, label, nested
                    ));
                });
                code.push_str("        }\n    }\n");
                code.push_str("}\n");

                code.push_str(&format!(
                    "impl{} {}<{}{}> for {}{} {{\n",
                    lifetime_ann,
                    trait_name,
                    msg_type_inner_name,
                    lifetime_ann,
                    msg_type_name,
                    lifetime_ann
                ));
                match mode {
                    Mode::Spec => {
                        code.push_str(&format!(
                            "    open spec fn {}(m: {}) -> {} {{\n        match m {{\n",
                            assoc_func_name, msg_type_inner_name, msg_type_name
                        ));
                    }
                    _ => {
                        code.push_str(&format!(
                            "    fn {}(m: {}{}) -> {}{} {{\n        match m {{\n",
                            assoc_func_name,
                            msg_type_inner_name,
                            lifetime_ann,
                            msg_type_name,
                            lifetime_ann
                        ));
                    }
                }
                std::iter::zip(&variants, &nested_eithers).for_each(|((label, _), nested)| {
                    code.push_str(&format!(
                        "            {} => {}::{}(m),\n",
                        nested, msg_type_name, label
                    ));
                });
                code.push_str("        }\n    }\n");
                code.push_str("}\n");

                // impl Mapper for Exec
                if let Mode::Exec(_) = mode {
                    code.push_str(&gen_mapper(name, &msg_type_name, lifetime_ann));
                }
            }
            Choices::Ints(..) => todo!(),
            Choices::Arrays(..) => todo!(),
        }
        code
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        if self.depend_id.is_some() {
            let (combinator_types, additional_code): (Vec<String>, Vec<String>) =
                match &self.choices {
                    Choices::Enums(enums) => enums
                        .iter()
                        .map(|(_, combinator)| combinator.gen_combinator_type("", mode, ctx))
                        .map(|(t, code)| (format!("Cond<{}>", t), code))
                        .unzip(),
                    // .collect::<Vec<(String, String)>>()
                    Choices::Ints(..) => todo!(),
                    Choices::Arrays(..) => todo!(),
                };

            let inner = fmt_in_pairs(&combinator_types, "OrdChoice", Bracket::Angle);
            (
                format!("Mapped<{}, {}Mapper>", inner, name),
                additional_code.join(""),
            )
        } else {
            unimplemented!()
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        if let Some(depend_id) = &self.depend_id {
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
            // must be an invocation to an enum
            if let CombinatorInner::Invocation(CombinatorInvocation {
                func: enum_name, ..
            }) = &combinator
            {
                let (combinator_exprs, additional_code): (Vec<String>, Vec<String>) =
                    match &self.choices {
                        Choices::Enums(enums) => enums
                            .iter()
                            .map(|(variant, combinator)| {
                                let (inner, code) =
                                    combinator.gen_combinator_expr(false, "", mode, ctx);
                                let bool_exp = match ctx.enums.get(enum_name.as_str()).unwrap() {
                                    EnumCombinator::NonExhaustive { enums } => {
                                        if variant == "_" {
                                            // default case; the negation of all other cases
                                            let other_variants = enums
                                                .iter()
                                                .filter_map(|Enum { name, value }| {
                                                    if name == "_" {
                                                        None
                                                    } else {
                                                        Some(format!("{} == {}", depend_id, value))
                                                    }
                                                })
                                                .collect::<Vec<_>>();
                                            format!("!({})", other_variants.join(" || "))
                                        } else {
                                            let value = enums
                                                .iter()
                                                .find_map(|Enum { name, value }| {
                                                    if name == variant {
                                                        Some(value.to_string())
                                                    } else {
                                                        None
                                                    }
                                                })
                                                .unwrap();
                                            format!("{} == {}", depend_id, value)
                                        }
                                    }
                                    EnumCombinator::Exhaustive { .. } => {
                                        let upper_caml_name = snake_to_upper_caml(enum_name);
                                        format!("{} == {}::{}", depend_id, upper_caml_name, variant)
                                    }
                                };
                                (
                                    format!("Cond {{ cond: {}, inner: {} }}", bool_exp, inner),
                                    code,
                                )
                            })
                            .unzip(),
                        Choices::Ints(..) => todo!(),
                        Choices::Arrays(..) => todo!(),
                    };
                let inner = fmt_in_pairs(&combinator_exprs, "OrdChoice", Bracket::Parentheses);
                let combinator_expr =
                    format!("Mapped {{ inner: {}, mapper: {}Mapper }}", inner, name);
                (combinator_expr, additional_code.join(""))
            } else {
                panic!("unexpected combinator type for dependent id: {}. Maybe something wrong with type checking 🙀", depend_id)
            }
        } else {
            unimplemented!()
        }
    }
}

fn gen_mapper(name: &str, msg_type_name: &str, lifetime_ann: &str) -> String {
    format!(
        r#"pub struct {}Mapper;
impl View for {}Mapper {{
    type V = Self;
    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}
impl SpecIso for {}Mapper {{
    type Src = Spec{}Inner;
    type Dst = Spec{};
    proof fn spec_iso(s: Self::Src) {{
    }}
    proof fn spec_iso_rev(s: Self::Dst) {{
    }}
}}
impl Iso for {}Mapper {{
    type Src<'a> = {}Inner{};
    type Dst<'a> = {}{};
    type SrcOwned = {}OwnedInner;
    type DstOwned = {}Owned;
}}
"#,
        name,
        name,
        name,
        name,
        name,
        name,
        msg_type_name,
        lifetime_ann,
        msg_type_name,
        lifetime_ann,
        name,
        name
    )
}

impl Codegen for ArrayCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        todo!()
    }
}

impl Codegen for VecCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_msg_type("", mode, ctx)
            }
        };

        let type_name = match mode {
            Mode::Spec => format!("Seq<{}>", inner),
            _ => format!("RepeatResult<{}>", inner),
        };
        if name.is_empty() {
            type_name
        } else {
            let type_alias_name = match mode {
                Mode::Spec => &format!("Spec{}", name),
                Mode::Exec(LifetimeAnn::Some) => &format!("{}{}", name, "<'a>"),
                Mode::Exec(LifetimeAnn::None) => name,
                Mode::ExecOwned => &format!("{}Owned", name),
            };
            format!("pub type {} = {};\n", type_alias_name, type_name)
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_combinator_type("", mode, ctx)
            }
        };
        (format!("Repeat<{}>", inner.0), inner.1)
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let spec = match mode {
            Mode::Spec => "Spec",
            _ => "",
        };
        let inner = match self {
            VecCombinator::Vec1(combinator) | VecCombinator::Vec(combinator) => {
                combinator.gen_combinator_expr(false, "", mode, ctx)
            }
        };
        let combinator_expr = format!("Repeat({})", inner.0);
        (combinator_expr, inner.1)
    }
}

impl Codegen for SepByCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        todo!()
    }
}

impl Codegen for WrapCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        todo!()
    }
}

impl Codegen for ApplyCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        todo!()
    }
}

impl Codegen for OptionCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        todo!()
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        todo!()
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
            ConstCombinator::ConstCombinatorInvocation(..) => todo!(),
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        match &self {
            ConstCombinator::ConstInt(c) => c.gen_combinator_type(name, mode, ctx),
            ConstCombinator::ConstBytes(c) => c.gen_combinator_type(name, mode, ctx),
            ConstCombinator::ConstArray(..) => todo!(),
            ConstCombinator::Vec(..) => todo!(),
            ConstCombinator::ConstStruct(..) => todo!(),
            ConstCombinator::ConstChoice(..) => todo!(),
            ConstCombinator::ConstCombinatorInvocation(..) => todo!(),
        }
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        match &self {
            ConstCombinator::ConstInt(c) => c.gen_combinator_expr(false, name, mode, ctx),
            ConstCombinator::ConstBytes(c) => c.gen_combinator_expr(false, name, mode, ctx),
            ConstCombinator::ConstArray(..) => todo!(),
            ConstCombinator::Vec(..) => todo!(),
            ConstCombinator::ConstStruct(..) => todo!(),
            ConstCombinator::ConstChoice(..) => todo!(),
            ConstCombinator::ConstCombinatorInvocation(..) => todo!(),
        }
    }
}

impl Codegen for ConstIntCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        format!("{}", self.combinator)
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let endianess = match ctx.endianess {
            Endianess::Big => "Be",
            Endianess::Little => "Le",
        };
        let (comb_type, tag_type) = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => ("U8".to_string(), "u8".to_string()),
            IntCombinator::Unsigned(t) => (format!("U{}{}", t, endianess), format!("u{}", t)),
            IntCombinator::Signed(..) => unimplemented!(),
        };
        let const_decl = format!("pub const {}: {} = {};\n", name, tag_type, self.value);
        let additional_code = match mode {
            Mode::Spec => const_decl,
            _ => "".to_string(),
        };
        (
            format!("Refined<{}, TagPred<{}>>", comb_type, tag_type),
            additional_code,
        )
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        let endianess = match ctx.endianess {
            Endianess::Big => "Be",
            Endianess::Little => "Le",
        };
        let int_type = match &self.combinator {
            IntCombinator::Unsigned(t) if *t == 8 => "U8".to_string(),
            IntCombinator::Unsigned(t) => format!("U{}{}", t, endianess),
            IntCombinator::Signed(..) => unimplemented!(),
        };
        (
            format!(
                "Refined {{ inner: {}, predicate: TagPred({}) }}",
                int_type, name
            ),
            "".to_string(),
        )
    }
}

impl Codegen for ConstBytesCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        match mode {
            Mode::Spec => "Seq<u8>".to_string(),
            Mode::Exec(LifetimeAnn::Some) => "&'a [u8]".to_string(),
            _ => "Vec<u8>".to_string(),
        }
    }

    fn gen_combinator_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> (String, String) {
        let len = self.len;
        let arr_val = format!("{}", self.values);
        let spec_const_decl = format!("pub spec const SPEC_{}: Seq<u8> = seq!{};", name, arr_val);
        let exec_const_decl = format!(
            r#"pub exec const {name}: [u8; {len}]
    ensures {name}@ == SPEC_{name},
{{
    let arr: [u8; {len}] = {arr_val};
    assert(arr@ == SPEC_{name});
    arr
}}
"#
        );
        let hash = compute_hash(&format!("{}", self.values));
        let predicate = format!(
            r#"pub struct BytesPredicate{hash};
impl View for BytesPredicate{hash} {{
    type V = Self;
    open spec fn view(&self) -> Self::V {{
        *self
    }}
}}
impl SpecPred for BytesPredicate{hash} {{
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {{
        i == &SPEC_{name}
    }}
}}
impl Pred for BytesPredicate{hash} {{
    type Input<'a> = &'a [u8];
    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> bool {{
        compare_slice(i, {name}.as_slice())
    }}
}}
"#,
        );
        let additional_code = match mode {
            Mode::Spec => spec_const_decl,
            _ => exec_const_decl + &predicate,
        };
        (
            format!("Refined<BytesN<{}>, BytesPredicate{}>", len, hash),
            additional_code,
        )
    }

    fn gen_combinator_expr(
        &self,
        top_level: bool,
        name: &str,
        mode: Mode,
        ctx: &CodegenCtx,
    ) -> (String, String) {
        (
            format!(
                "Refined {{ inner: BytesN::<{}>, predicate: BytesPredicate{} }}",
                self.len,
                compute_hash(&format!("{}", self.values))
            ),
            "".to_string(),
        )
    }
}

pub fn code_gen(ast: &[Definition], ctx: &GlobalCtx) -> String {
    let mut codegen_ctx = CodegenCtx::with_ast(ast, ctx);
    let mut code = String::new();
    let ast = filter_endianess(ast);
    gen_msg_type(&ast, &mut code, &codegen_ctx);
    gen_combinator_type(&ast, &mut code, &mut codegen_ctx);
    gen_combinator_expr(&ast, &mut code, &mut codegen_ctx);
    // gen_parser_and_serializer(&ast, &mut code, &codegen_ctx);
    "#![allow(unused_imports)]\n".to_string()
        + "use vstd::prelude::*;\n"
        + "use vest::properties::*;\n"
        + "use vest::utils::*;\n"
        + "use vest::regular::map::*;\n"
        + "use vest::regular::tag::*;\n"
        + "use vest::regular::choice::*;\n"
        + "use vest::regular::cond::*;\n"
        + "use vest::regular::uints::*;\n"
        + "use vest::regular::tail::*;\n"
        + "use vest::regular::bytes::*;\n"
        + "use vest::regular::bytes_n::*;\n"
        + "use vest::regular::depend::*;\n"
        + "use vest::regular::and_then::*;\n"
        + "use vest::regular::refined::*;\n"
        + "use vest::regular::repeat::*;\n"
        + &format!("verus!{{\n{}\n}}\n", code)
}

fn filter_endianess(ast: &[Definition]) -> Vec<Definition> {
    ast.iter()
        .filter(|&defn| !matches!(defn, Definition::Endianess(_)))
        .cloned()
        .collect::<Vec<_>>()
}

fn gen_msg_type(ast: &[Definition], code: &mut String, ctx: &CodegenCtx) {
    for defn in ast {
        let lifetime_ann = ctx
            .format_lifetimes
            .get(match defn {
                Definition::Combinator { name, .. } => name,
                Definition::ConstCombinator { name, .. } => name,
                _ => unimplemented!(),
            })
            .unwrap();
        gen_msg_type_definition(defn, code, *lifetime_ann, ctx);
    }
}

fn gen_msg_type_definition(
    defn: &Definition,
    code: &mut String,
    lifetime_ann: LifetimeAnn,
    ctx: &CodegenCtx,
) {
    match defn {
        Definition::Combinator {
            name, combinator, ..
        } => {
            code.push_str(&combinator.gen_msg_type(name, Mode::Spec, ctx));
            code.push_str(&combinator.gen_msg_type(name, Mode::Exec(lifetime_ann), ctx));
            code.push_str(&combinator.gen_msg_type(name, Mode::ExecOwned, ctx));
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            unimplemented!("Top-level const format is not supported yet");
        }
        _ => unimplemented!(),
    }
    code.push('\n');
}

fn gen_combinator_type(ast: &[Definition], code: &mut String, ctx: &mut CodegenCtx) {
    for defn in ast {
        let lifetime_ann = ctx
            .format_lifetimes
            .get(match defn {
                Definition::Combinator { name, .. } => name,
                Definition::ConstCombinator { name, .. } => name,
                _ => unimplemented!(),
            })
            .unwrap();
        gen_combinator_type_for_definition(defn, code, *lifetime_ann, ctx);
    }
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
            let (spec_combinator_type, spec_additional_code) =
                combinator.gen_combinator_type(name, Mode::Spec, ctx);
            let (exec_combinator_type, exec_additional_code) =
                combinator.gen_combinator_type(name, Mode::Exec(lifetime_ann), ctx);
            code.push_str(&spec_additional_code);
            code.push_str(&spec_combinator_type);
            code.push_str(&exec_additional_code);
            code.push_str(&exec_combinator_type);
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            unimplemented!("Top-level const format is not supported yet");
        }
        Definition::Endianess(_) => {}
        _ => unimplemented!(),
    }
    code.push('\n');
}

fn gen_combinator_expr(ast: &[Definition], code: &mut String, ctx: &mut CodegenCtx) {
    for defn in ast {
        gen_combinator_expr_for_definition(defn, code, ctx);
    }
}

fn gen_combinator_expr_for_definition(defn: &Definition, code: &mut String, ctx: &mut CodegenCtx) {
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
                // spec
                let (expr, additional_code) =
                    &combinator.gen_combinator_expr(true, &upper_caml_name, Mode::Spec, ctx);
                code.push_str(&format!(
                    r#"
pub closed spec fn spec_{name}() -> Spec{upper_caml_name}Combinator {{
    Spec{upper_caml_name}Combinator({expr})
}}
{additional_code} "#
                ));
                // exec
                let (expr, additional_code) = &combinator.gen_combinator_expr(
                    true,
                    &upper_caml_name,
                    Mode::Exec(LifetimeAnn::None),
                    ctx,
                );
                code.push_str(&format!(
                    r#"
pub fn {name}() -> (o: {upper_caml_name}Combinator)
    ensures o@ == spec_{name}(),
{{
    {upper_caml_name}Combinator({expr})
}}
{additional_code} "#
                ));
            } else {
                // has dependencies
                let lifetime_ann = ctx
                    .format_lifetimes
                    .get(match defn {
                        Definition::Combinator { name, .. } => name,
                        Definition::ConstCombinator { name, .. } => name,
                        _ => unimplemented!(),
                    })
                    .unwrap();
                let (dep_params_name, (dep_params_spec_type, dep_params_exec_type)): (
                    Vec<_>,
                    (Vec<_>, Vec<_>),
                ) = param_defns
                    .iter()
                    .filter_map(|param_defn| match param_defn {
                        ParamDefn::Dependent { name, combinator } => Some((name, combinator)),
                        _ => None,
                    })
                    .map(|(name, combinator)| {
                        (
                            name,
                            (
                                combinator.gen_msg_type("", Mode::Spec, ctx),
                                combinator.gen_msg_type("", Mode::Exec(*lifetime_ann), ctx),
                            ),
                        )
                    })
                    .unzip();
                let upper_caml_name = snake_to_upper_caml(name);
                // spec
                let spec_params = std::iter::zip(&dep_params_name, &dep_params_spec_type)
                    .map(|(n, t)| format!("{}: {}", n, t))
                    .collect::<Vec<_>>()
                    .join(", ");
                let (expr, additional_code) =
                    &combinator.gen_combinator_expr(true, &upper_caml_name, Mode::Spec, ctx);
                code.push_str(&format!(
                    r#"
pub closed spec fn spec_{name}({spec_params}) -> Spec{upper_caml_name}Combinator {{
    Spec{upper_caml_name}Combinator({expr})
}}
{additional_code} "#
                ));
                // exec
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
                    true,
                    &upper_caml_name,
                    Mode::Exec(*lifetime_ann),
                    ctx,
                );
                code.push_str(&format!(
                    r#"
pub fn {name}{lifetime_ann}({exec_params}) -> (o: {upper_caml_name}Combinator)
    ensures o@ == spec_{name}({args_view}),
{{
    {upper_caml_name}Combinator({expr})
}}
{additional_code} "#
                ));
            }
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            unimplemented!("Top-level const format is not supported yet");
        }
        Definition::Endianess(_) => {}
        _ => unimplemented!(),
    }
    code.push('\n');
}

fn gen_parser_and_serializer(ast: &[Definition], code: &mut String, ctx: &CodegenCtx) {
    for defn in ast {
        gen_parser_and_serializer_for_definition(defn, code, ctx);
    }
}

fn gen_parser_and_serializer_for_definition(
    defn: &Definition,
    code: &mut String,
    ctx: &CodegenCtx,
) {
    let lifetime_ann = ctx
        .format_lifetimes
        .get(match defn {
            Definition::Combinator { name, .. } => name,
            Definition::ConstCombinator { name, .. } => name,
            _ => unimplemented!(),
        })
        .unwrap();
    match defn {
        Definition::Combinator {
            name,
            combinator,
            param_defns,
        } => {
            let (dep_params_name, (dep_params_spec_type, dep_params_exec_type)): (
                Vec<_>,
                (Vec<_>, Vec<_>),
            ) = param_defns
                .iter()
                .filter_map(|param_defn| match param_defn {
                    ParamDefn::Dependent { name, combinator } => Some((name, combinator)),
                    _ => None,
                })
                .map(|(name, combinator)| {
                    (
                        name,
                        (
                            combinator.gen_msg_type("", Mode::Spec, ctx),
                            combinator.gen_msg_type("", Mode::Exec(*lifetime_ann), ctx),
                        ),
                    )
                })
                .unzip();
            let dep_spec_params = std::iter::zip(&dep_params_name, &dep_params_spec_type)
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect::<Vec<_>>()
                .join(", ");
            let dep_exec_params = std::iter::zip(&dep_params_name, &dep_params_exec_type)
                .map(|(n, t)| format!("{}: {}", n, t))
                .collect::<Vec<_>>()
                .join(", ");
            let dep_args = dep_params_name
                .iter()
                .map(|&n| n.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            let dep_args_view = dep_params_name
                .iter()
                .map(|&n| n.to_string() + "@")
                .collect::<Vec<_>>()
                .join(", ");
            let upper_caml_name = snake_to_upper_caml(name);
            let (exec_body, spec_body) = (
                format!("{}({})", name, dep_args),
                format!("spec_{}({})", name, dep_args),
            );
            let lifetime = match lifetime_ann {
                LifetimeAnn::Some => "<'_>",
                LifetimeAnn::None => "",
            };
            let spec_params = if dep_spec_params.is_empty() {
                "".to_string()
            } else {
                format!(", {}", dep_spec_params)
            };
            let exec_params = if dep_exec_params.is_empty() {
                "".to_string()
            } else {
                format!(", {}", dep_exec_params)
            };
            let args_view = if dep_args_view.is_empty() {
                "".to_string()
            } else {
                format!(", {}", dep_args_view)
            };
            // spec
            code.push_str(&format!(
                r#"pub open spec fn parse_spec_{name}(i: Seq<u8>{spec_params}) -> Result<(usize, Spec{upper_caml_name}), ()> {{
    {spec_body}.spec_parse(i)
}}
pub open spec fn serialize_spec_{name}(msg: Spec{upper_caml_name}{spec_params}) -> Result<Seq<u8>, ()> {{
    {spec_body}.spec_serialize(msg)
}}
"#));
            // exec
            code.push_str(&format!(
                r#"pub fn parse_{name}(i: &[u8]{exec_params}) -> (o: Result<(usize, {upper_caml_name}{lifetime}), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_{name}(i@{args_view}) matches Ok(r_) && r@ == r_,
{{
    let c = {exec_body};
    assert(c.parse_requires());
    c.parse(i)
}}

pub fn serialize_{name}(msg: {upper_caml_name}{lifetime}, data: &mut Vec<u8>, pos: usize{exec_params}) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {{
            &&& serialize_spec_{name}(msg@{args_view}) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        }},
{{
    let c = {exec_body};
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}}
"#));
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            unimplemented!("Top-level const format is not supported yet");
        }
        _ => unimplemented!(),
    }
}
