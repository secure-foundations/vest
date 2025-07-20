use crate::ast::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use ariadne::{Color, ColorGenerator, Fmt, Label, Report, ReportKind, Source};

#[derive(Debug, Clone)]
pub struct GlobalCtx<'ast> {
    pub combinators: HashSet<CombinatorSig<'ast>>,
    pub const_combinators: HashSet<&'ast str>,
    pub enums: HashMap<&'ast str, EnumCombinator<'ast>>, // enum name -> enum combinator
}

pub struct LocalCtx<'ast> {
    pub struct_fields: HashSet<String>,
    pub dependent_fields: HashMap<String, Combinator<'ast>>,
}

impl<'ast> LocalCtx<'ast> {
    pub fn new() -> Self {
        Self {
            struct_fields: HashSet::new(),
            dependent_fields: HashMap::new(),
        }
    }

    pub fn reset(&mut self) {
        self.struct_fields.clear();
        self.dependent_fields.clear();
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CombinatorSig<'ast> {
    pub name: &'ast str,
    pub param_defns: &'ast [ParamDefn<'ast>],
    /// Fully resolved combinator for a top-level combinator definition
    /// We need to resolve for two reasons:
    ///
    /// * Combinator invocations (aliases) will need to be resolved to the actual combinator
    /// * Combinators that contains `>>=` (and_then) will need to be resolved to whatever the
    ///   `and_then` combinator is. For example, if we have a combinator `a` that is defined as
    ///   `b >>= c`, the return type of `a` will be the return type of `c`.
    pub resolved_combinator: CombinatorInner<'ast>,
}

impl<'ast> GlobalCtx<'ast> {
    pub fn resolve(&self, combinator: &'ast Combinator) -> &CombinatorInner<'ast> {
        if let Some(and_then) = &combinator.and_then {
            self.resolve(and_then)
        } else {
            self.resolve_alias(&combinator.inner)
        }
    }
    pub fn resolve_alias(&self, combinator: &'ast CombinatorInner) -> &CombinatorInner<'ast> {
        match combinator {
            CombinatorInner::Invocation(CombinatorInvocation { func, .. }) => {
                let combinator_sig = self
                    .combinators
                    .iter()
                    .find(|sig| sig.name == func)
                    .unwrap_or_else(|| panic!("Combinator `{}` is not defined", func));
                &combinator_sig.resolved_combinator
            }
            combinator => combinator,
        }
    }
}

pub fn check<'ast>(
    ast: &'ast [Definition<'ast>],
    source: (&str, &Source),
) -> Result<GlobalCtx<'ast>, Box<dyn std::error::Error>> {
    let mut global_ctx = GlobalCtx {
        combinators: HashSet::new(),
        const_combinators: HashSet::new(),
        enums: HashMap::new(),
    };
    let mut local_ctx = LocalCtx::new();
    for defn in ast {
        match defn {
            Definition::Combinator {
                name,
                param_defns,
                combinator,
                span,
            } => {
                // Check for combinator invocations and `and_then`s and resolve them
                let resolved_combinator = global_ctx.resolve(combinator).to_owned();

                match global_ctx.combinators.iter().find(|sig| sig.name == name) {
                    Some(sig) => {
                        let mut color_gen = ColorGenerator::default();
                        Report::build(ReportKind::Error, (source.0, span.start()..span.end()))
                            .with_message(format!("Duplicate format definition `{}`", name))
                            .with_label(
                                Label::new((source.0, span.start()..span.end()))
                                    .with_message(format!("This format is defined twice"))
                                    .with_color(color_gen.next()),
                            )
                            .with_label(
                                Label::new((
                                    source.0,
                                    sig.resolved_combinator.as_span().start()
                                        ..sig.resolved_combinator.as_span().end(),
                                ))
                                .with_message(format!(
                                    "The {} format is already defined here",
                                    name
                                ))
                                .with_color(color_gen.next()),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(Box::new(std::io::Error::new(std::io::ErrorKind::Other, "")));
                    }
                    None => {
                        global_ctx.combinators.insert(CombinatorSig {
                            name,
                            param_defns,
                            resolved_combinator,
                        });
                    }
                }

                // if !global_ctx.combinators.insert(CombinatorSig {
                //     name,
                //     param_defns,
                //     resolved_combinator,
                // }) {
                //     panic!("Duplicate combinator definition `{}`", name);
                // }

                if let Combinator {
                    inner: CombinatorInner::Enum(enum_combinator),
                    ..
                } = combinator
                {
                    global_ctx.enums.insert(name, enum_combinator.clone());
                }
            }
            Definition::ConstCombinator { name, .. } => {
                global_ctx.const_combinators.insert(name);
            }
            Definition::Endianess(_) => {}
            _ => unimplemented!(),
        }
    }

    ast.iter()
        .for_each(|defn| check_defn(defn, &mut local_ctx, &global_ctx));

    Ok(global_ctx)
}

fn check_defn<'ast>(
    defn: &'ast Definition<'ast>,
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    local_ctx.reset();
    match defn {
        Definition::Combinator {
            param_defns,
            combinator,
            ..
        } => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx);
        }
        Definition::ConstCombinator {
            const_combinator, ..
        } => {
            check_const_combinator(const_combinator, local_ctx, global_ctx);
        }
        Definition::Endianess(_) => {}
        _ => unimplemented!(),
    }
}

fn check_const_combinator(
    const_combinator: &ConstCombinator,
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
) {
    use ConstCombinator::*;
    match const_combinator {
        ConstInt(ConstIntCombinator {
            combinator,
            value,
            span,
        }) => check_const_int_combinator(combinator, value),
        ConstArray(ConstArrayCombinator {
            combinator,
            len,
            values,
            span,
        }) => check_const_array_combinator(combinator, len, values),
        ConstBytes(ConstBytesCombinator { len, values, span }) => {
            check_const_bytes_combinator(len, values)
        }
        ConstStruct(ConstStructCombinator(const_combinators)) => {
            check_const_struct_combinator(const_combinators, local_ctx, global_ctx)
        }
        ConstChoice(ConstChoiceCombinator(const_choices)) => {
            check_const_choice_combinator(const_choices, local_ctx, global_ctx)
        }
        Vec(const_combinator) => check_const_combinator(const_combinator, local_ctx, global_ctx),
        ConstCombinatorInvocation(name) => {
            check_const_combinator_invocation(name, local_ctx, global_ctx)
        }
    }
}

fn check_const_struct_combinator(
    const_combinators: &[ConstCombinator],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
) {
    const_combinators.iter().for_each(|const_combinator| {
        check_const_combinator(const_combinator, local_ctx, global_ctx)
    });
}

fn check_const_array_combinator(combinator: &IntCombinator, len: &usize, values: &ConstArray) {
    match values {
        ConstArray::Int(int_vals) => {
            if int_vals.len() != *len {
                panic!(
                    "Length of array does not match the specified length (expected {}, got {})",
                    len,
                    int_vals.len()
                );
            }
            int_vals
                .iter()
                .for_each(|value| check_const_int_combinator(combinator, value));
        }
        ConstArray::Repeat(int_val, n) => {
            if *n != *len {
                panic!(
                    "Length of array does not match the specified length (expected {}, got {})",
                    len, n
                );
            }
            check_const_int_combinator(combinator, int_val);
        }
        ConstArray::Char(_) => panic!("Char array literals should be of type `[u8; N]`"),
        ConstArray::Wildcard => (),
    }
}

fn check_const_combinator_invocation(
    name: &str,
    _local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
) {
    if !global_ctx.const_combinators.contains(&name) {
        panic!("Const combinator `{}` is not defined", name);
    }
}

fn check_const_choice_combinator(
    const_choices: &[ConstChoice],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
) {
    const_choices
        .iter()
        .for_each(|ConstChoice { combinator, .. }| {
            check_const_combinator(combinator, local_ctx, global_ctx)
        });
}

fn check_const_bytes_combinator(len: &usize, values: &ConstArray) {
    match values {
        ConstArray::Int(int_vals) => {
            if int_vals.len() != *len {
                panic!(
                    "Length of array does not match the specified length (expected {}, got {})",
                    len,
                    int_vals.len()
                );
            }
            int_vals.iter().for_each(|value| {
                if *value < u8::MIN.into() || *value > u8::MAX.into() {
                    panic!("Value {} is out of range for u8", value);
                }
            });
        }
        ConstArray::Repeat(int_val, n) => {
            if *n != *len {
                panic!(
                    "Length of array does not match the specified length (expected {}, got {})",
                    len, n
                );
            }
            if *int_val < u8::MIN.into() || *int_val > u8::MAX.into() {
                panic!("Value {} is out of range for u8", int_val);
            }
        }
        ConstArray::Char(char_values) => {
            if char_values.len() != *len {
                panic!(
                    "Length of array does not match the specified length (expected {}, got {})",
                    len,
                    char_values.len()
                );
            }
        }
        ConstArray::Wildcard => (),
    }
}

fn check_const_int_combinator(combinator: &IntCombinator, value: &i128) {
    match combinator {
        IntCombinator::Signed(8) => {
            if *value < i8::MIN.into() || *value > i8::MAX.into() {
                panic!("Value {} is out of range for i8", value);
            }
        }
        IntCombinator::Signed(16) => {
            if *value < i16::MIN.into() || *value > i16::MAX.into() {
                panic!("Value {} is out of range for i16", value);
            }
        }
        IntCombinator::Signed(32) => {
            if *value < i32::MIN.into() || *value > i32::MAX.into() {
                panic!("Value {} is out of range for i32", value);
            }
        }
        IntCombinator::Signed(64) => {
            if *value < i64::MIN.into() || *value > i64::MAX.into() {
                panic!("Value {} is out of range for i64", value);
            }
        }
        IntCombinator::Unsigned(8) => {
            if *value < u8::MIN.into() || *value > u8::MAX.into() {
                panic!("Value {} is out of range for u8", value);
            }
        }
        IntCombinator::Unsigned(16) => {
            if *value < u16::MIN.into() || *value > u16::MAX.into() {
                panic!("Value {} is out of range for u16", value);
            }
        }
        IntCombinator::Unsigned(24) => {
            if *value < 0 || *value > 0xFFFFFF {
                panic!("Value {} is out of range for u24", value);
            }
        }
        IntCombinator::Unsigned(32) => {
            if *value < u32::MIN.into() || *value > u32::MAX.into() {
                panic!("Value {} is out of range for u32", value);
            }
        }
        IntCombinator::Unsigned(64) => {
            if *value < u64::MIN.into() || *value > u64::MAX.into() {
                panic!("Value {} is out of range for u64", value);
            }
        }
        IntCombinator::BtcVarint => {
            if *value < u64::MIN.into() || *value > u64::MAX.into() {
                panic!("Value {} is out of range for btc_varint", value);
            }
        }
        IntCombinator::ULEB128 => {
            if *value < 0 || *value > u64::MAX.into() {
                panic!("Value {} is out of range for uleb128", value);
            }
        }
        _ => panic!("Unsupported const int combinator"),
    }
}

fn check_combinator<'ast>(
    Combinator {
        inner,
        and_then,
        span,
    }: &Combinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    check_combinator_inner(inner, param_defns, local_ctx, global_ctx);
    if let Some(and_then) = and_then {
        check_combinator_inner_result_type(inner);
        check_combinator(and_then, param_defns, local_ctx, global_ctx);
    }
}

// must be a bytes combinator
fn check_combinator_inner_result_type(inner: &CombinatorInner) {
    use CombinatorInner::*;
    if let Bytes(_) | Tail(_) = inner {
    } else {
        panic!("Only `Bytes` or `Tail` combinator can be followed by `and_then`");
    }
}

fn check_combinator_inner<'ast>(
    inner: &CombinatorInner<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    use CombinatorInner::*;
    match inner {
        ConstraintInt(ConstraintIntCombinator {
            combinator,
            constraint,
            span,
        }) => check_constraint_int_combinator(combinator, constraint.as_ref()),
        Struct(StructCombinator {
            fields: struct_fields,
            span,
        }) => check_struct_combinator(struct_fields, param_defns, local_ctx, global_ctx),
        Wrap(WrapCombinator {
            prior,
            combinator,
            post,
            span,
        }) => check_wrap_combinator(prior, combinator, post, param_defns, local_ctx, global_ctx),
        Enum(
            EnumCombinator::Exhaustive { enums, span }
            | EnumCombinator::NonExhaustive { enums, span },
        ) => check_enum_combinator(enums, local_ctx, global_ctx),
        Choice(ChoiceCombinator {
            depend_id,
            choices,
            span,
        }) => check_choice_combinator(
            depend_id.as_ref(),
            choices,
            param_defns,
            local_ctx,
            global_ctx,
        ),
        SepBy(SepByCombinator { combinator, sep }) => {
            check_sep_by_combinator(combinator, sep, param_defns, local_ctx, global_ctx)
        }
        Vec(VecCombinator::Vec(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx)
        }
        Vec(VecCombinator::Vec1(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx)
        }
        Array(ArrayCombinator {
            combinator,
            len,
            span,
        }) => check_array_combinator(combinator, len, param_defns, local_ctx, global_ctx),
        Bytes(BytesCombinator { len, span }) => {
            check_bytes_combinator(len, param_defns, local_ctx, global_ctx)
        }
        Tail(TailCombinator { span }) => {}
        Apply(ApplyCombinator { stream, combinator }) => {
            check_apply_combinator(stream, combinator, param_defns, local_ctx, global_ctx)
        }
        Option(OptionCombinator(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx)
        }
        Invocation(CombinatorInvocation { func, args, span }) => {
            check_combinator_invocation(func, args, param_defns, local_ctx, global_ctx)
        }
        MacroInvocation { .. } => unreachable!("macro invocation should be resolved by now"),
    }
}

// pub struct CombinatorSig<'ast> {
//     pub name: &'ast str,
//     pub param_defns: &'ast [ParamDefn],
// }
// pub enum ParamDefn {
//     Stream {
//         name: String,
//     },
//     Dependent {
//         name: String,
//         combinator: CombinatorInner,
//     },
// }
// pub enum Param {
//     Stream(String),
//     Dependent(String),
// }
fn check_combinator_invocation<'ast>(
    name: &str,
    args: &[Param],
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    let combinator_sig = global_ctx
        .combinators
        .iter()
        .find(|sig| sig.name == name)
        .unwrap_or_else(|| panic!("Combinator `{}` is not defined", name));
    // check if lengths of args and param_defns match
    if args.len() != combinator_sig.param_defns.len() {
        panic!("Argument count mismatch");
    }
    zip(args, combinator_sig.param_defns).for_each(|(arg, param_defn)| match (arg, param_defn) {
        (Param::Stream(_), ParamDefn::Stream { .. }) => {}
        (Param::Dependent(depend_id), ParamDefn::Dependent { combinator, .. }) => {
            fn resolve_up_to_enums<'ast>(comb: CombinatorInner<'ast>) -> CombinatorInner<'ast> {
                match comb {
                    CombinatorInner::Enum(
                        EnumCombinator::Exhaustive { enums, span }
                        | EnumCombinator::NonExhaustive { enums, span },
                    ) => CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                        combinator: infer_enum_type(&enums),
                        constraint: None,
                        span: span.clone(),
                    }),
                    l => l.clone(),
                }
            }
            // 1. try to find `depend_id` in local_ctx
            if let Some(arg_combinator) = local_ctx.dependent_fields.get(depend_id) {
                let left = resolve_up_to_enums(global_ctx.resolve(arg_combinator).clone());
                let right = resolve_up_to_enums(global_ctx.resolve_alias(combinator).clone());
                if left != right {
                    panic!("Argument type mismatch: expected {}, got {}", left, right);
                }
            } else {
                // 2. try to find `depend_id` in param_defns
                let param_defn = param_defns
                    .iter()
                    .find(|param_defn| match param_defn {
                        ParamDefn::Dependent { name, .. } => name == depend_id,
                        _ => false,
                    })
                    .unwrap_or_else(|| {
                        panic!("`{}` is not found in current scope", depend_id);
                    });
                match param_defn {
                    ParamDefn::Dependent {
                        combinator: combinator_,
                        ..
                    } => {
                        let left =
                            resolve_up_to_enums(global_ctx.resolve_alias(combinator_).clone());
                        let right =
                            resolve_up_to_enums(global_ctx.resolve_alias(combinator).clone());
                        if left != right {
                            panic!(
                                "Argument type mismatch: expected {}, got {}",
                                combinator, combinator_
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
        _ => panic!("Argument type mismatch"),
    });
}

fn check_apply_combinator<'ast>(
    _stream: &str,
    combinator: &Combinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    check_combinator(combinator, param_defns, local_ctx, global_ctx);
}

fn check_bytes_combinator(
    len: &LengthSpecifier,
    param_defns: &[ParamDefn],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
) {
    match len {
        LengthSpecifier::Const(..) => {
            // nothing to check
        }
        LengthSpecifier::Dependent(depend_id) => {
            // 1. try to find `depend_id` in local_ctx
            if let Some(combinator) = local_ctx.dependent_fields.get(depend_id) {
                match global_ctx.resolve(combinator) {
                    CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                        combinator:
                            IntCombinator::Unsigned(_)
                            | IntCombinator::BtcVarint
                            | IntCombinator::ULEB128,
                        ..
                    }) => {}
                    _ => panic!("Length specifier must be an unsigned int"),
                }
            } else {
                // 2. try to find `depend_id` in param_defns
                let param_defn = param_defns
                    .iter()
                    .find(|param_defn| match param_defn {
                        ParamDefn::Dependent { name, .. } => name == depend_id,
                        _ => false,
                    })
                    .unwrap_or_else(|| {
                        panic!("`{}` is not found in current scope", depend_id);
                    });
                match param_defn {
                    ParamDefn::Dependent { combinator, .. } => {
                        match global_ctx.resolve_alias(combinator) {
                            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                                combinator: IntCombinator::Unsigned(_) | IntCombinator::BtcVarint,
                                ..
                            }) => {}
                            _ => panic!("Length specifier must be an unsigned int"),
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}

fn check_array_combinator<'ast>(
    combinator: &Combinator<'ast>,
    len: &LengthSpecifier,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    check_combinator(combinator, param_defns, local_ctx, global_ctx);
    check_bytes_combinator(len, param_defns, local_ctx, global_ctx);
}

fn check_sep_by_combinator<'ast>(
    combinator: &VecCombinator<'ast>,
    sep: &ConstCombinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    match combinator {
        VecCombinator::Vec(combinator) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx);
        }
        VecCombinator::Vec1(combinator) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx);
        }
    }
    check_const_combinator(sep, local_ctx, global_ctx);
}

fn check_choice_combinator<'ast>(
    depend_id: Option<&String>,
    choices: &Choices<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) {
    let get_combinator_from_depend_id = |depend_id: &str| {
        local_ctx
            .dependent_fields
            .get(depend_id)
            .map(|combinator| &combinator.inner)
            .unwrap_or_else(|| {
                param_defns
                    .iter()
                    .find_map(|param_defn| match param_defn {
                        ParamDefn::Dependent {
                            name,
                            combinator,
                            span,
                        } if name == depend_id => Some(combinator),
                        _ => None,
                    })
                    .unwrap_or_else(|| {
                        panic!("`{}` is not defined as a dependent field", depend_id);
                    })
            })
    };
    // if there isn't a depend_id, it must be an `enum` choice:
    if depend_id.is_none() && !matches!(choices, Choices::Enums(_)) {
        panic!("Labels for a non-dependent ordered choice must be `variant_id`");
    }
    match choices {
        Choices::Enums(enums) => {
            if let Some(depend_id) = depend_id {
                // check if depend_id a prior field in the struct or in the param_defns
                let combinator = get_combinator_from_depend_id(depend_id);
                // check if `combinator` is defined as an enum
                if let CombinatorInner::Invocation(CombinatorInvocation { func, .. }) = &combinator
                {
                    let enum_ = global_ctx.enums.get(func.as_str()).unwrap_or_else(|| {
                        panic!("Enum `{}` is not defined", func);
                    });
                    let (enum_variants, is_non_exhaustive) = match enum_ {
                        EnumCombinator::Exhaustive { enums, span } => (enums, false),
                        EnumCombinator::NonExhaustive { enums, span } => (enums, true),
                    };
                    // check for well-formed variants
                    let mut variants = HashSet::new();
                    for (variant, combinator) in enums {
                        if variant == "_" {
                            if !is_non_exhaustive {
                                panic!("Wildcard `_` is not allowed in an exhaustive choice");
                            } else {
                                continue;
                            }
                        } else if !enum_variants
                            .iter()
                            .any(|Enum { name, .. }| name == variant)
                        {
                            panic!("Enum variant `{}` is not defined", variant);
                        }

                        if !variants.insert(variant.as_str()) {
                            panic!("Duplicate variant `{}` in dependent choice", variant);
                        }
                        check_combinator(combinator, param_defns, local_ctx, global_ctx);
                    }
                    if !is_non_exhaustive {
                        // check for exhaustiveness
                        let defined_variants: HashSet<&str> = enum_variants
                            .iter()
                            .map(|Enum { name, .. }| name.as_str())
                            .collect();
                        if defined_variants != variants {
                            let missing_variants: Vec<&str> =
                                defined_variants.difference(&variants).copied().collect();
                            panic!(
                                "Missing variants in dependent choice: {}",
                                missing_variants.join(", ")
                            );
                        }
                    }
                } else {
                    panic!("Dependent field must be an enum");
                }
            } else {
                let mut labels = HashSet::new();
                enums.iter().for_each(|(label, combinator)| {
                    if !labels.insert(label.as_str()) {
                        panic!("Duplicate label `{}`", label);
                    }
                    check_combinator(combinator, param_defns, local_ctx, global_ctx);
                });
            }
        }
        Choices::Ints(ints) => {
            if let Some(depend_id) = depend_id {
                let combinator = get_combinator_from_depend_id(depend_id);
                // check if `combinator` is defined as an int
                if let CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                    combinator:
                        IntCombinator::Unsigned(_) | IntCombinator::BtcVarint | IntCombinator::ULEB128,
                    ..
                }) = combinator
                {
                    let int_combinator = match combinator {
                        CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                            combinator,
                            ..
                        }) => combinator.clone(),
                        _ => unreachable!(),
                    };
                    let mut int_variants = HashSet::new();
                    ints.iter().for_each(|(pattern, combinator)| {
                        if let Some(pattern) = pattern {
                            check_constraint_elem(&int_combinator, pattern);
                            if !int_variants.insert(pattern) {
                                panic!("Duplicate int variant `{}`", pattern);
                            }
                        }
                        check_combinator(combinator, param_defns, local_ctx, global_ctx);
                    });
                } else if let CombinatorInner::Invocation(CombinatorInvocation { func, .. }) =
                    combinator
                {
                    // check if it's non-exhaustive enum (which is equivalent to an int choice)
                    let enum_ = global_ctx.enums.get(func.as_str()).unwrap_or_else(|| {
                        panic!("Enum `{}` is not defined", func);
                    });
                    let is_non_exhaustive = match enum_ {
                        EnumCombinator::Exhaustive { .. } => false,
                        EnumCombinator::NonExhaustive { .. } => true,
                    };
                    if !is_non_exhaustive {
                        panic!(
                            "Enum `{}` is exhaustive, cannot be used as an int choice",
                            func
                        );
                    }
                    let enums = match enum_ {
                        EnumCombinator::Exhaustive { enums, span } => enums,
                        EnumCombinator::NonExhaustive { enums, span } => enums,
                    };
                    let int_combinator = infer_enum_type(enums);
                    let mut int_variants = HashSet::new();
                    ints.iter().for_each(|(pattern, combinator)| {
                        if let Some(pattern) = pattern {
                            check_constraint_elem(&int_combinator, pattern);
                            if !int_variants.insert(pattern) {
                                panic!("Duplicate int variant `{}`", pattern);
                            }
                        }
                        check_combinator(combinator, param_defns, local_ctx, global_ctx);
                    });
                } else {
                    panic!("Type mismatch: expected unsigned int, got {}", combinator);
                }
            } else {
                panic!("Ints are not allowed in a non-dependent choice");
            }
        }
        Choices::Arrays(arrays) => {
            if let Some(depend_id) = depend_id {
                let combinator = get_combinator_from_depend_id(depend_id);
                // check if `combinator` is defined as an array
                if let CombinatorInner::Array(ArrayCombinator { len, span, .. })
                | CombinatorInner::Bytes(BytesCombinator { len, span }) = combinator
                {
                    let LengthSpecifier::Const(len) = len.clone() else {
                        panic!("Length specifier must be constant");
                    };
                    let mut array_variants = HashSet::new();
                    arrays.iter().for_each(|(array, comb)| {
                        if !array_variants.insert(array) {
                            panic!("Duplicate array variant");
                        }
                        match array {
                            ConstArray::Int(elems) => {
                                if elems.len() != len {
                                    panic!(
                                        "Array length mismatch: expected {}, got {}",
                                        len,
                                        elems.len()
                                    );
                                }
                            }
                            ConstArray::Wildcard => (),
                            _ => unimplemented!(),
                        }
                        check_combinator(comb, param_defns, local_ctx, global_ctx);
                    });
                } else {
                    panic!("Type mismatch: expected array, got {}", combinator);
                }
            } else {
                panic!("Arrays are not allowed in a non-dependent choice");
            }
        }
    }
}

fn check_enum_combinator(enums: &[Enum], _local_ctx: &mut LocalCtx, _global_ctxx: &GlobalCtx) {
    let combinator = infer_enum_type(enums);
    enums.iter().for_each(|Enum { value, .. }| {
        check_const_int_combinator(&combinator, value);
    });
}

/// 1. if no negative values, use Unsigned
/// 2. infer the smallest possible type (e.g. if all values are in the range of u8, use u8)
/// 3. for now, support up to u64 and i64
pub fn infer_enum_type(enums: &[Enum]) -> IntCombinator {
    let (min, max) = enums
        .iter()
        .fold((i128::MAX, i128::MIN), |(min, max), Enum { value, .. }| {
            (min.min(*value), max.max(*value))
        });

    if min >= 0 {
        if max <= u8::MAX.into() {
            IntCombinator::Unsigned(8)
        } else if max <= u16::MAX.into() {
            IntCombinator::Unsigned(16)
        } else if max <= 0xFFFFFF {
            IntCombinator::Unsigned(24)
        } else if max <= u32::MAX.into() {
            IntCombinator::Unsigned(32)
        } else if max <= u64::MAX.into() {
            IntCombinator::Unsigned(64)
        } else {
            panic!("Enum values are out of range");
        }
    } else if min >= i8::MIN.into() && max <= i8::MAX.into() {
        IntCombinator::Signed(8)
    } else if min >= i16::MIN.into() && max <= i16::MAX.into() {
        IntCombinator::Signed(16)
    } else if min >= i32::MIN.into() && max <= i32::MAX.into() {
        IntCombinator::Signed(32)
    } else if min >= i64::MIN.into() && max <= i64::MAX.into() {
        IntCombinator::Signed(64)
    } else {
        panic!("Enum values are out of range");
    }
}

fn check_wrap_combinator<'ast>(
    prior: &[ConstCombinator],
    combinator: &Combinator<'ast>,
    post: &[ConstCombinator],
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx,
) {
    prior.iter().for_each(|const_combinator| {
        check_const_combinator(const_combinator, local_ctx, global_ctx)
    });
    check_combinator(combinator, param_defns, local_ctx, global_ctx);
    post.iter().for_each(|const_combinator| {
        check_const_combinator(const_combinator, local_ctx, global_ctx)
    });
}

fn check_struct_combinator<'ast>(
    struct_fields: &[StructField<'ast>],
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx,
) {
    struct_fields.iter().for_each(|field| match field {
        StructField::Stream(_) => {}
        StructField::Dependent {
            label,
            combinator,
            span,
        } => {
            if !local_ctx.dependent_fields.contains_key(label) {
                local_ctx
                    .dependent_fields
                    .insert(label.to_owned(), combinator.to_owned());
            } else {
                panic!("Duplicate dependent field `{}`", label);
            }
            if !local_ctx.struct_fields.insert(label.to_owned()) {
                panic!("Duplicate field name `{}`", label);
            }
            check_combinator(combinator, param_defns, local_ctx, global_ctx);
        }
        StructField::Const {
            combinator,
            label,
            span,
        } => {
            if !local_ctx.struct_fields.insert(label.to_owned()) {
                panic!("Duplicate field name `{}`", label);
            }
            check_const_combinator(combinator, local_ctx, global_ctx);
        }
        StructField::Ordinary {
            combinator,
            label,
            span,
        } => {
            if !local_ctx.struct_fields.insert(label.to_owned()) {
                panic!("Duplicate field name `{}`", label);
            }
            check_combinator(combinator, param_defns, local_ctx, global_ctx);
        }
    });
}

fn check_constraint_int_combinator(combinator: &IntCombinator, constraint: Option<&IntConstraint>) {
    match constraint {
        Some(IntConstraint::Single { elem, span }) => check_constraint_elem(combinator, elem),
        Some(IntConstraint::Set(constraints)) => constraints
            .iter()
            .for_each(|constraint| check_constraint_int_combinator(combinator, Some(constraint))),
        Some(IntConstraint::Neg(constraint)) => {
            check_constraint_int_combinator(combinator, Some(constraint))
        }
        None => {}
    }
}

fn check_constraint_elem(combinator: &IntCombinator, constraint_elem: &ConstraintElem) {
    match constraint_elem {
        ConstraintElem::Range { start, end } => match (start, end) {
            (Some(start), Some(end)) => {
                check_const_int_combinator(combinator, start);
                check_const_int_combinator(combinator, end);
                if start > end {
                    panic!("Invalid range constraint");
                }
            }
            (Some(start), None) => {
                check_const_int_combinator(combinator, start);
            }
            (None, Some(end)) => {
                check_const_int_combinator(combinator, end);
            }
            _ => panic!("Invalid range constraint"),
        },
        ConstraintElem::Single(value) => {
            check_const_int_combinator(combinator, value);
        }
    }
}
