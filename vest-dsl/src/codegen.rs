// tempararily disable dead code warning
#![allow(dead_code)]

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

#[derive(Debug, Clone, Copy)]
enum Bracket {
    Parentheses,
    Angle,
    Square,
}

/// format a vector into pairs of tuples, optionally prepended by `prepend`
/// e.g. `["R1", "R2", "R3", "R4"] ==> "prepend(prepend(prepend(R1, R2), R3), R4)"`
fn fmt_in_pairs<T: Display>(tuples: &[T], prepend: &str, bracket: Bracket) -> String {
    let (left, right) = match bracket {
        Bracket::Parentheses => ("(", ")"),
        Bracket::Angle => ("<", ">"),
        Bracket::Square => ("[", "]"),
    };
    tuples.iter().skip(1).fold(tuples[0].to_string(), |acc, t| {
        format!("{}{}{}, {}{}", prepend, left, acc, t, right)
    })
}

/// generate nested `Either`s based on the number of variants and a variable name
/// - The [`num_of_variants`] should be at least 2
///
/// ## Examples
/// ==== `gen_nested_eithers(0, "m")` ====
/// Either::Left(m)
/// Either::Right(m)
/// ==== `gen_nested_eithers(1, "m")` ====
/// Either::Left(Either::Left(m))
/// Either::Left(Either::Right(m))
/// Either::Right(m)
/// ==== `gen_nested_eithers(2, "m")` ====
/// Either::Left(Either::Left(Either::Left(m)))
/// Either::Left(Either::Left(Either::Right(m)))
/// Either::Left(Either::Right(m))
fn gen_nested_eithers(num_of_variants: usize, var_name: &str) -> Vec<String> {
    if num_of_variants == 2 {
        vec![
            format!("Either::Left({})", var_name),
            format!("Either::Right({})", var_name),
        ]
    } else {
        gen_nested_eithers(num_of_variants - 1, var_name)
            .iter()
            .map(|nested| format!("Either::Left({})", nested))
            .chain(std::iter::once(format!("Either::Right({})", var_name)))
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

pub struct CodegenCtx<'a> {
    pub format_lifetimes: HashMap<String, LifetimeAnn>,
    pub enums: HashMap<&'a str, HashMap<&'a str, i128>>, // enum name -> variant name -> value
    pub param_defns: Vec<ParamDefn>,
}

impl<'a> CodegenCtx<'a> {
    pub fn new(
        format_lifetimes: HashMap<String, LifetimeAnn>,
        enums: HashMap<&'a str, HashMap<&'a str, i128>>,
    ) -> Self {
        Self {
            format_lifetimes,
            enums,
            param_defns: Vec::new(),
        }
    }

    pub fn with_ast(ast: &[Definition], ctx: &'a GlobalCtx) -> Self {
        // first we need to determine which formats' types need lifetime annotations

        /// helper function to determine if a format needs lifetime annotations
        fn need_lifetime(combinator: &Combinator) -> bool {
            use CombinatorInner::*;
            match &combinator.inner {
                Bytes(_) => true,
                Tail(_) => true,
                Struct(StructCombinator(fields)) => fields.iter().any(|field| match field {
                    StructField::Ordinary { combinator, .. } => need_lifetime(combinator),
                    StructField::Dependent { combinator, .. } => need_lifetime(combinator),
                    _ => false,
                }),
                Wrap(WrapCombinator {
                    prior,
                    combinator,
                    post,
                }) => {
                    prior.iter().any(need_lifetime_const)
                        || need_lifetime(combinator)
                        || post.iter().any(need_lifetime_const)
                }
                Choice(ChoiceCombinator { choices, .. }) => match choices {
                    Choices::Enums(enums) => enums
                        .iter()
                        .any(|(_, combinator)| need_lifetime(combinator)),
                    Choices::Ints(ints) => {
                        ints.iter().any(|(_, combinator)| need_lifetime(combinator))
                    }
                    Choices::Arrays(arrays) => arrays
                        .iter()
                        .any(|(_, combinator)| need_lifetime(combinator)),
                },
                SepBy(SepByCombinator { combinator, sep }) => {
                    let combinator = Combinator {
                        inner: Vec(combinator.clone()),
                        and_then: None,
                    };
                    need_lifetime(&combinator) || need_lifetime_const(sep)
                }
                Vec(VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator)) => {
                    need_lifetime(combinator)
                }
                Array(ArrayCombinator { combinator, .. }) => need_lifetime(combinator),
                Option(OptionCombinator(combinator)) => need_lifetime(combinator),
                ConstraintInt(_) | Enum(_) | Apply(_) | Invocation(_) => false,
            }
        }

        /// helper function to determine if a const format needs lifetime annotations
        fn need_lifetime_const(const_combinator: &ConstCombinator) -> bool {
            match const_combinator {
                ConstCombinator::ConstArray(_) => true, // TODO: can be more fine-grained
                ConstCombinator::ConstBytes(ConstBytesCombinator { len, .. }) => *len > 16, // TODO: adjust this threshold
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
        let mut format_lifetimes: HashMap<String, LifetimeAnn> = ast
            .iter()
            .map(|defn| match defn {
                Definition::Combinator { name, .. } => (name.to_string(), LifetimeAnn::None),
                Definition::ConstCombinator { name, .. } => (name.to_string(), LifetimeAnn::None),
                _ => unimplemented!(),
            })
            .collect();

        let call_graph = build_call_graph(ast);
        // NOTE: by now ast should already be topologically sorted
        ast.iter().for_each(|defn| match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                let invocations = call_graph.get(name).unwrap();
                let lifetime = if invocations
                    .iter()
                    .any(|name| format_lifetimes.get(name).unwrap() == &LifetimeAnn::Some)
                    || need_lifetime(combinator)
                {
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
            _ => {}
        });

        Self::new(format_lifetimes, ctx.enums.clone())
    }
}

trait Codegen {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String;
    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String;
    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String;
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        let name = &snake_to_upper_caml(name);
        if let Some(and_then) = &self.and_then {
            if name.is_empty() {
                format!(
                    "AndThen<{}, {}>",
                    self.inner.gen_combinator_type(name, ctx), // must be `Bytes` or `Tail`
                    and_then.gen_combinator_type(name, ctx)
                )
            } else {
                format!(
                    "pub type {}Combinator = AndThen<{}, {}>;\n",
                    name,
                    self.inner.gen_combinator_type(name, ctx), // must be `Bytes` or `Tail`
                    and_then.inner.gen_combinator_type(name, ctx)
                )
            }
        } else if name.is_empty() {
            self.inner.gen_combinator_type(name, ctx)
        } else {
            format!(
                "pub type {}Combinator = {};\n",
                name,
                self.inner.gen_combinator_type(name, ctx)
            )
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        if let Some(and_then) = &self.and_then {
            format!(
                "AndThen({}, {})",
                self.inner.gen_combinator_expr(name, mode, ctx),
                and_then.gen_combinator_expr(name, mode, ctx)
            )
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        match self {
            CombinatorInner::ConstraintInt(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Bytes(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Tail(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Invocation(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Struct(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Enum(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Choice(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Array(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Vec(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::SepBy(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Wrap(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Apply(p) => p.gen_combinator_type(name, ctx),
            CombinatorInner::Option(p) => p.gen_combinator_type(name, ctx),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
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
    fn gen_msg_type(&self, name: &str, _mode: Mode, _ctx: &CodegenCtx) -> String {
        let int_type = format!("{}", self.combinator);
        if name.is_empty() {
            int_type
        } else {
            format!("pub type {} = {};\n", name, int_type)
        }
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        match &self.combinator {
            IntCombinator::Unsigned(t) => format!("U{}", t),
            IntCombinator::Signed(..) => unimplemented!(),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        self.gen_combinator_type(name, ctx)
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        match &self.len {
            LengthSpecifier::Const(len) => format!("BytesN<{}>", len),
            LengthSpecifier::Dependent(..) => "Bytes".to_string(),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        match &self.len {
            LengthSpecifier::Const(len) => format!("BytesN::<{}>", len),
            LengthSpecifier::Dependent(depend_id) => format!("Bytes({} as usize)", depend_id),
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        if name.is_empty() {
            "Tail".to_string()
        } else {
            panic!("`Tail` should not be a top-level definition")
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        "Tail".to_string()
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
            format!(
                "pub type {}{} = {}{};\n",
                name, lifetime, invocked, lifetime
            )
        }
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        let invocked = snake_to_upper_caml(&self.func);
        format!("{}Combinator", invocked)
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
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
        format!("{}({})", invocked, args)
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
        // generate the struct
        code.push_str(&format!(
            "pub struct {}{} {{\n",
            msg_type_name, lifetime_ann
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
                    todo!()
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
    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        let (fst, snd) = self.split_at_last_dependent();
        let combinator_type_from_field = |field: &StructField| match field {
            StructField::Ordinary { combinator, .. }
            | StructField::Dependent { combinator, .. } => combinator.gen_combinator_type("", ctx),
            _ => todo!(),
        };
        if fst.is_empty() {
            // no dependent fields
            let snd = snd
                .iter()
                .map(combinator_type_from_field)
                .collect::<Vec<_>>();
            let inner = fmt_in_pairs(&snd, "", Bracket::Parentheses);
            format!("Mapped<{}, {}Mapper>", inner, name)
        } else {
            let (fst, snd) = (
                fst.iter()
                    .map(combinator_type_from_field)
                    .collect::<Vec<_>>(),
                snd.iter()
                    .map(combinator_type_from_field)
                    .collect::<Vec<_>>(),
            );
            let inner = format!(
                "SpecDepend<{}, {}>",
                fmt_in_pairs(&fst, "", Bracket::Parentheses),
                fmt_in_pairs(&snd, "", Bracket::Parentheses)
            );
            format!("Mapped<{}, {}Mapper>", inner, name)
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let (fst, snd) = self.split_at_last_dependent();
        if fst.is_empty() {
            // no dependent fields
            let snd = snd
                .iter()
                .map(|field| match field {
                    StructField::Ordinary { combinator, .. }
                    | StructField::Dependent { combinator, .. } => {
                        combinator.gen_combinator_expr("", mode, ctx)
                    }
                    _ => todo!(),
                })
                .collect::<Vec<_>>();
            format!(
                "Mapped {{ inner: {}, mapper: {}Mapper }}",
                fmt_in_pairs(&snd, "", Bracket::Parentheses),
                name
            )
        } else {
            unreachable!("Should not be called for struct with dependent fields")
        }
    }
}

impl Codegen for EnumCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, _ctx: &CodegenCtx) -> String {
        let inferred = infer_enum_type(&self.enums);
        if name.is_empty() {
            format!("{}", inferred)
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        let inferred = infer_enum_type(&self.enums);
        match inferred {
            IntCombinator::Unsigned(t) => format!("U{}", t),
            IntCombinator::Signed(..) => unimplemented!(),
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        let inferred = infer_enum_type(&self.enums);
        match inferred {
            IntCombinator::Unsigned(t) => format!("U{}", t),
            IntCombinator::Signed(..) => unimplemented!(),
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
                // generate the enum
                code.push_str(&format!("pub enum {}{} {{\n", msg_type_name, lifetime_ann));
                let mut variants = Vec::new();
                for (label, combinator) in enums {
                    let variant_type = combinator.gen_msg_type("", mode, ctx);
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
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
                let enums = ctx
                    .enums
                    .get(enum_name.as_str())
                    .unwrap()
                    .iter()
                    .map(|(&name, &value)| Enum {
                        name: name.to_string(),
                        value,
                    })
                    .collect::<Vec<_>>();
                let inferred = infer_enum_type(&enums);
                let combinator_types = match &self.choices {
                    Choices::Enums(enums) => enums
                        .iter()
                        .map(|(_, combinator)| combinator.gen_combinator_type("", ctx))
                        .map(|t| format!("Cond<{}, {}, {}>", inferred, inferred, t))
                        .collect::<Vec<_>>(),
                    Choices::Ints(..) => todo!(),
                    Choices::Arrays(..) => todo!(),
                };
                let inner = fmt_in_pairs(&combinator_types, "OrdChoice", Bracket::Angle);
                format!("Mapped<{}, {}Mapper>", inner, name)
            } else {
                panic!("unexpected combinator type for dependent id: {}. Maybe something wrong with type checking 🙀", depend_id)
            }
        } else {
            unimplemented!()
        }
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
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
                let ints = ctx
                    .enums
                    .get(enum_name.as_str())
                    .unwrap()
                    .iter()
                    .map(|(_, &value)| value)
                    .collect::<Vec<_>>();
                let combinator_exprs = match &self.choices {
                    Choices::Enums(enums) => std::iter::zip(enums, ints)
                        .map(|((_, combinator), i)| {
                            let inner = combinator.gen_combinator_expr("", mode, ctx);
                            format!(
                                "Cond {{ lhs: {}, rhs: {}, inner: {} }}",
                                depend_id, i, inner
                            )
                        })
                        .collect::<Vec<_>>(),
                    Choices::Ints(..) => todo!(),
                    Choices::Arrays(..) => todo!(),
                };
                let inner = fmt_in_pairs(&combinator_exprs, "OrdChoice", Bracket::Parentheses);
                format!("Mapped {{ inner: {}, mapper: {}Mapper }}", inner, name)
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

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

impl Codegen for VecCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

impl Codegen for SepByCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

impl Codegen for WrapCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

impl Codegen for ApplyCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

impl Codegen for OptionCombinator {
    fn gen_msg_type(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_type(&self, name: &str, ctx: &CodegenCtx) -> String {
        todo!()
    }

    fn gen_combinator_expr(&self, name: &str, mode: Mode, ctx: &CodegenCtx) -> String {
        todo!()
    }
}

pub fn code_gen(ast: &[Definition], ctx: &GlobalCtx) -> String {
    let mut codegen_ctx = CodegenCtx::with_ast(ast, ctx);
    let mut code = String::new();
    gen_msg_type(ast, &mut code, &codegen_ctx);
    gen_combinator_type(ast, &mut code, &mut codegen_ctx);
    gen_combinator_expr(ast, &mut code, &mut codegen_ctx);
    gen_parser_and_serializer(ast, &mut code, &codegen_ctx);
    "#![allow(unused_imports)]\n".to_string()
        + "use vstd::prelude::*;\n"
        + "use vest::properties::*;\n"
        + "use vest::utils::*;\n"
        + "use vest::regular::map::*;\n"
        + "use vest::regular::choice::*;\n"
        + "use vest::regular::cond::*;\n"
        + "use vest::regular::uints::*;\n"
        + "use vest::regular::tail::*;\n"
        + "use vest::regular::bytes::*;\n"
        + "use vest::regular::bytes_n::*;\n"
        + "use vest::regular::depend::*;\n"
        + "use vest::regular::and_then::*;\n"
        + &format!("verus!{{\n{}\n}}\n", code)
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
            todo!()
        }
        _ => unimplemented!(),
    }
    code.push('\n');
}

fn gen_combinator_type(ast: &[Definition], code: &mut String, ctx: &mut CodegenCtx) {
    for defn in ast {
        gen_combinator_type_for_definition(defn, code, ctx);
    }
}

fn gen_combinator_type_for_definition(defn: &Definition, code: &mut String, ctx: &mut CodegenCtx) {
    match defn {
        Definition::Combinator {
            name,
            combinator,
            param_defns,
        } => {
            ctx.param_defns = param_defns.clone();
            code.push_str(&combinator.gen_combinator_type(name, ctx));
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            todo!()
        }
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
            // check for struct with dependent fields
            if let CombinatorInner::Struct(struct_combinator) = &combinator.inner {
                if !struct_combinator.split_at_last_dependent().0.is_empty() {
                    // due to technical issues in Verus, we don't generate combinator expressions for formats with dependent fields
                    // instead, we generate parsing and serialization functions directly
                    return;
                }
            }
            ctx.param_defns = param_defns.clone();
            if param_defns.is_empty() {
                // no dependencies
                let upper_caml_name = snake_to_upper_caml(name);
                // spec
                code.push_str(&format!(
                    "pub open spec fn spec_{}() -> {}Combinator {{\n",
                    name, upper_caml_name
                ));
                code.push_str(&combinator.gen_combinator_expr(&upper_caml_name, Mode::Spec, ctx));
                code.push_str("}\n");
                // exec
                code.push_str(&format!(
                    "pub fn {}() -> (o: {}Combinator)\n    ensures o@ == spec_{}(),\n{{\n",
                    name, upper_caml_name, name
                ));
                code.push_str(&combinator.gen_combinator_expr(
                    &upper_caml_name,
                    Mode::Exec(LifetimeAnn::None),
                    ctx,
                ));
                code.push_str("}\n");
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
                code.push_str(&format!(
                    "pub open spec fn spec_{}({}) -> {}Combinator {{\n",
                    name,
                    std::iter::zip(&dep_params_name, dep_params_spec_type)
                        .map(|(n, t)| format!("{}: {}", n, t))
                        .collect::<Vec<_>>()
                        .join(", "),
                    upper_caml_name
                ));
                code.push_str(&combinator.gen_combinator_expr(&upper_caml_name, Mode::Spec, ctx));
                code.push_str("}\n");
                // exec
                code.push_str(&format!(
                    "pub fn {}{}({}) -> (o: {}Combinator)\n    ensures o@ == spec_{}({}),\n{{\n",
                    name,
                    match lifetime_ann {
                        LifetimeAnn::Some => "<'a>",
                        LifetimeAnn::None => "",
                    },
                    std::iter::zip(&dep_params_name, dep_params_exec_type)
                        .map(|(n, t)| format!("{}: {}", n, t))
                        .collect::<Vec<_>>()
                        .join(", "),
                    upper_caml_name,
                    name,
                    dep_params_name
                        .iter()
                        .map(|&n| n.to_string() + "@")
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                code.push_str(&combinator.gen_combinator_expr(
                    &upper_caml_name,
                    Mode::Exec(*lifetime_ann),
                    ctx,
                ));
                code.push_str("}\n");
            }
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            todo!()
        }
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
            let (exec_body, spec_body) = match &combinator.inner {
                CombinatorInner::Struct(struct_combinator) => {
                    let exec_mode = Mode::Exec(*lifetime_ann);
                    let (fst, snd) = struct_combinator.split_at_last_dependent();
                    if !fst.is_empty() {
                        // struct has dependent fields
                        let (fst_bindings, (fst_msg_types, (fst_exprs, fst_spec_exprs))): (
                            Vec<_>,
                            (Vec<_>, (Vec<_>, Vec<_>)),
                        ) = fst
                            .iter()
                            .map(|field| match field {
                                StructField::Ordinary { combinator, .. } => (
                                    "_",
                                    (
                                        combinator.gen_msg_type("", exec_mode, ctx),
                                        (
                                            combinator.gen_combinator_expr("", exec_mode, ctx),
                                            combinator.gen_combinator_expr("", Mode::Spec, ctx),
                                        ),
                                    ),
                                ),
                                StructField::Dependent { label, combinator } => (
                                    label.as_str(),
                                    (
                                        combinator.gen_msg_type("", exec_mode, ctx),
                                        (
                                            combinator.gen_combinator_expr("", exec_mode, ctx),
                                            combinator.gen_combinator_expr("", Mode::Spec, ctx),
                                        ),
                                    ),
                                ),
                                _ => todo!(),
                            })
                            .unzip();
                        let (snd_combinator_types, (snd_exprs, snd_spec_exprs)): (
                            Vec<_>,
                            (Vec<_>, Vec<_>),
                        ) = snd
                            .iter()
                            .map(|field| match field {
                                StructField::Ordinary { combinator, .. }
                                | StructField::Dependent { combinator, .. } => (
                                    combinator.gen_combinator_type("", ctx),
                                    (
                                        combinator.gen_combinator_expr("", exec_mode, ctx),
                                        combinator.gen_combinator_expr("", Mode::Spec, ctx),
                                    ),
                                ),
                                _ => todo!(),
                            })
                            .unzip();
                        let spec_body = format!(
                            r#"    let fst = {};
    let snd = |deps| {{
        let {} = deps;
        {}
    }};
    Mapped {{ inner: SpecDepend {{ fst, snd }}, mapper: {}Mapper }}"#,
                            fmt_in_pairs(&fst_spec_exprs, "", Bracket::Parentheses),
                            fmt_in_pairs(&fst_bindings, "", Bracket::Parentheses),
                            fmt_in_pairs(&snd_spec_exprs, "", Bracket::Parentheses),
                            upper_caml_name
                        );
                        // exec
                        let exec_body = format!(
                            r#"    let ghost spec_snd = |deps| {{
        let {} = deps;
        {}
    }};
    let fst = {};
    let snd = |deps: {}| -> (o: {}) 
        ensures
            o@ == spec_snd(deps@),
    {{
        let {} = deps;
        {}
    }};
    Mapped {{ inner: Depend {{ fst, snd, spec_snd: Ghost(spec_snd) }}, mapper: {}Mapper }}"#,
                            fmt_in_pairs(&fst_bindings, "", Bracket::Parentheses),
                            fmt_in_pairs(&snd_spec_exprs, "", Bracket::Parentheses),
                            fmt_in_pairs(&fst_exprs, "", Bracket::Parentheses),
                            fmt_in_pairs(&fst_msg_types, "", Bracket::Parentheses),
                            fmt_in_pairs(&snd_combinator_types, "", Bracket::Parentheses),
                            fmt_in_pairs(&fst_bindings, "", Bracket::Parentheses),
                            fmt_in_pairs(&snd_exprs, "", Bracket::Parentheses),
                            upper_caml_name
                        );
                        (exec_body, spec_body)
                    } else {
                        (
                            format!("{}({})", name, dep_args),
                            format!("spec_{}({})", name, dep_args),
                        )
                    }
                }
                _ => (
                    format!("{}({})", name, dep_args),
                    format!("spec_{}({})", name, dep_args),
                ),
            };
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
                r#"pub fn parse_{name}(i: &[u8]{exec_params}) -> (o: Result<(usize, {upper_caml_name}{lifetime}), ()>)
    ensures
        o matches Ok(r) ==> parse_spec_{name}(i@{args_view}) matches Ok(r_) && r@ == r_,
{{
    {exec_body}.parse(i)
}}

pub fn serialize_{name}(msg: {upper_caml_name}{lifetime}, data: &mut Vec<u8>, pos: usize{exec_params}) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {{
            &&& serialize_spec_{name}(msg@{args_view}) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        }},
{{
    {exec_body}.serialize(msg, data, pos)
}}
"#));
        }
        _ => unimplemented!(),
    }
}
