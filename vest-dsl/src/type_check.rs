use crate::ast::*;
use crate::VestError;
use core::panic;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use ariadne::{Color, Label, Report, ReportKind, Source};
use pest::Span;

#[derive(Debug, Clone)]
pub struct GlobalCtx<'ast> {
    pub combinators: HashSet<CombinatorSig<'ast>>,
    pub const_combinators: HashSet<ConstCombinatorSig<'ast>>,
    pub enums: HashMap<&'ast str, EnumCombinator<'ast>>, // enum name -> enum combinator
    pub static_sizes: HashMap<String, usize>,
}

pub struct LocalCtx<'ast> {
    pub struct_fields: HashSet<Identifier<'ast>>,
    pub dependent_fields: HashMap<Identifier<'ast>, Combinator<'ast>>,
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
    pub name: Identifier<'ast>,
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ConstCombinatorSig<'ast> {
    pub name: Identifier<'ast>,
    pub resolved_combinator: ConstCombinator<'ast>,
}

impl<'ast> CombinatorSig<'ast> {
    pub fn as_span(&self) -> Span<'ast> {
        let body_span = self.resolved_combinator.as_span();
        let input = body_span.get_input();
        let mut start = self.name.span.start();
        let mut end = body_span.end();
        for param in self.param_defns {
            match param {
                ParamDefn::Dependent { span, .. } => {
                    start = start.min(span.start());
                    end = end.max(span.end());
                }
                _ => {}
            }
        }
        Span::new(input, start, end).expect("combinator signature span should be valid")
    }
}

impl<'ast> GlobalCtx<'ast> {
    // TODO: return `Result`
    pub fn resolve(&self, combinator: &'ast Combinator) -> &CombinatorInner<'ast> {
        if let Some(and_then) = &combinator.and_then {
            self.resolve(and_then)
        } else {
            self.resolve_alias(&combinator.inner)
        }
    }
    // TODO: return `Result` instead of panic
    pub fn resolve_alias(&self, combinator: &'ast CombinatorInner) -> &CombinatorInner<'ast> {
        match combinator {
            CombinatorInner::Invocation(CombinatorInvocation { func, .. }) => {
                let combinator_sig = self
                    .combinators
                    .iter()
                    .find(|sig| sig.name == *func)
                    .unwrap_or_else(|| panic!("Format `{}` is not defined", func));
                &combinator_sig.resolved_combinator
            }
            combinator => combinator,
        }
    }
    // TODO: return `Result` instead of panic
    pub fn resolve_const(&self, combinator: &'ast ConstCombinator) -> &ConstCombinator<'ast> {
        match combinator {
            ConstCombinator::ConstCombinatorInvocation { name, .. } => {
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

struct StaticSizeEnv<'ast> {
    formats: HashMap<&'ast str, &'ast Combinator<'ast>>,
    const_formats: HashMap<&'ast str, &'ast ConstCombinator<'ast>>,
    format_sizes: HashMap<String, Option<usize>>,
    const_sizes: HashMap<String, Option<usize>>,
    visiting_formats: HashSet<String>,
    visiting_consts: HashSet<String>,
}

impl<'ast> StaticSizeEnv<'ast> {
    fn new(ast: &'ast [Definition<'ast>]) -> Self {
        let mut formats = HashMap::new();
        let mut const_formats = HashMap::new();
        for defn in ast {
            match defn {
                Definition::Combinator {
                    name, combinator, ..
                } => {
                    formats.insert(name.name.as_str(), combinator);
                }
                Definition::ConstCombinator {
                    name,
                    const_combinator,
                    ..
                } => {
                    const_formats.insert(name.name.as_str(), const_combinator);
                }
                _ => {}
            }
        }

        let mut format_sizes = HashMap::new();
        for (name, size) in builtin_static_sizes() {
            format_sizes.insert(name.to_string(), Some(size));
        }

        Self {
            formats,
            const_formats,
            format_sizes,
            const_sizes: HashMap::new(),
            visiting_formats: HashSet::new(),
            visiting_consts: HashSet::new(),
        }
    }

    fn compute_all(mut self) -> HashMap<String, usize> {
        let format_names = self.formats.keys().copied().collect::<Vec<_>>();
        for name in format_names {
            let _ = self.format_size(name);
        }

        self.format_sizes
            .into_iter()
            .filter_map(|(name, size)| size.map(|size| (name, size)))
            .collect()
    }

    fn format_size(&mut self, name: &str) -> Option<usize> {
        if let Some(size) = self.format_sizes.get(name) {
            return *size;
        }

        let combinator = *self.formats.get(name)?;
        let name = name.to_string();
        if !self.visiting_formats.insert(name.clone()) {
            self.format_sizes.insert(name, None);
            return None;
        }

        let size = self.combinator_size(combinator);
        self.visiting_formats.remove(&name);
        self.format_sizes.insert(name, size);
        size
    }

    fn const_format_size(&mut self, name: &str) -> Option<usize> {
        if let Some(size) = self.const_sizes.get(name) {
            return *size;
        }

        let combinator = *self.const_formats.get(name)?;
        let name = name.to_string();
        if !self.visiting_consts.insert(name.clone()) {
            self.const_sizes.insert(name, None);
            return None;
        }

        let size = self.const_combinator_size(combinator);
        self.visiting_consts.remove(&name);
        self.const_sizes.insert(name, size);
        size
    }

    fn combinator_size(&mut self, combinator: &Combinator<'ast>) -> Option<usize> {
        // `>>=` reparses the bytes from `inner`, so it does not change the consumed size.
        self.combinator_inner_size(&combinator.inner)
    }

    fn combinator_inner_size(&mut self, inner: &CombinatorInner<'ast>) -> Option<usize> {
        use CombinatorInner::*;

        match inner {
            ConstraintInt(combinator) => int_combinator_static_size(&combinator.combinator),
            ConstraintEnum(combinator) => self.format_size(&combinator.combinator.func.name),
            Struct(StructCombinator { fields, .. }) => {
                fields.iter().try_fold(0usize, |acc, field| {
                    let field_size = match field {
                        StructField::Ordinary { combinator, .. }
                        | StructField::Dependent { combinator, .. } => {
                            self.combinator_size(combinator)
                        }
                        StructField::Const { combinator, .. } => {
                            self.const_combinator_size(combinator)
                        }
                        StructField::Stream(..) => None,
                    }?;
                    acc.checked_add(field_size)
                })
            }
            Wrap(WrapCombinator {
                prior,
                combinator,
                post,
                ..
            }) => {
                let prior_size = prior.iter().try_fold(0usize, |acc, combinator| {
                    acc.checked_add(self.const_combinator_size(combinator)?)
                })?;
                let inner_size = self.combinator_size(combinator)?;
                let post_size = post.iter().try_fold(0usize, |acc, combinator| {
                    acc.checked_add(self.const_combinator_size(combinator)?)
                })?;
                prior_size.checked_add(inner_size)?.checked_add(post_size)
            }
            Enum(enum_comb) => enum_static_size(enum_comb),
            Choice(ChoiceCombinator { choices, .. }) => self.choice_size(choices),
            SepBy(..) | Vec(..) | Tail(..) | Option(..) => None,
            Array(ArrayCombinator {
                combinator, len, ..
            }) => {
                let elem_size = self.combinator_size(combinator)?;
                let len = self.length_expr_size(len)?;
                elem_size.checked_mul(len)
            }
            Bytes(BytesCombinator { len, .. }) => self.length_expr_size(len),
            Apply(ApplyCombinator { combinator, .. }) => self.combinator_size(combinator),
            Invocation(CombinatorInvocation { func, .. }) => self.format_size(&func.name),
            MacroInvocation { .. } => unreachable!("macro invocation should be resolved by now"),
        }
    }

    fn const_combinator_size(&mut self, combinator: &ConstCombinator<'ast>) -> Option<usize> {
        use ConstCombinator::*;

        match combinator {
            Vec(..) => None,
            ConstArray(ConstArrayCombinator {
                combinator, len, ..
            }) => int_combinator_static_size(combinator)?.checked_mul(*len),
            ConstBytes(ConstBytesCombinator { len, .. }) => Some(*len),
            ConstInt(ConstIntCombinator { combinator, .. }) => {
                int_combinator_static_size(combinator)
            }
            ConstEnum(ConstEnumCombinator { combinator, .. }) => {
                self.format_size(&combinator.func.name)
            }
            ConstStruct(ConstStructCombinator(fields)) => {
                fields.iter().try_fold(0usize, |acc, field| {
                    acc.checked_add(self.const_combinator_size(field)?)
                })
            }
            ConstChoice(ConstChoiceCombinator(choices)) => {
                let sizes = choices
                    .iter()
                    .map(|choice| self.const_combinator_size(&choice.combinator))
                    .collect::<std::vec::Vec<_>>();
                common_static_size(sizes.into_iter())
            }
            ConstCombinatorInvocation { name, .. } => self.const_format_size(&name.name),
        }
    }

    fn choice_size(&mut self, choices: &Choices<'ast>) -> Option<usize> {
        match choices {
            Choices::Enums(choices) => common_static_size(
                choices
                    .iter()
                    .map(|(_, combinator)| self.combinator_size(combinator)),
            ),
            Choices::Ints(choices) => common_static_size(
                choices
                    .iter()
                    .map(|(_, combinator)| self.combinator_size(combinator)),
            ),
            Choices::Arrays(choices) => common_static_size(
                choices
                    .iter()
                    .map(|(_, combinator)| self.combinator_size(combinator)),
            ),
        }
    }

    fn length_expr_size(&mut self, len: &LengthExpr<'ast>) -> Option<usize> {
        match len {
            LengthExpr::Const { value, .. } => Some(*value),
            LengthExpr::Dependent(..) => None,
            LengthExpr::SizeOf { format_name, .. } => self.format_size(&format_name.name),
            LengthExpr::BinOp {
                op, left, right, ..
            } => {
                let left = self.length_expr_size(left)?;
                let right = self.length_expr_size(right)?;
                match op {
                    ArithOp::Add => left.checked_add(right),
                    ArithOp::Sub => left.checked_sub(right),
                    ArithOp::Mul => left.checked_mul(right),
                    ArithOp::Div => left.checked_div(right),
                }
            }
        }
    }
}

fn builtin_static_sizes() -> [(&'static str, usize); 10] {
    [
        ("u8", 1),
        ("i8", 1),
        ("u16", 2),
        ("i16", 2),
        ("u24", 3),
        ("i24", 3),
        ("u32", 4),
        ("i32", 4),
        ("u64", 8),
        ("i64", 8),
    ]
}

fn int_combinator_static_size(combinator: &IntCombinator) -> Option<usize> {
    match combinator {
        IntCombinator::Unsigned(8) | IntCombinator::Signed(8) => Some(1),
        IntCombinator::Unsigned(16) | IntCombinator::Signed(16) => Some(2),
        IntCombinator::Unsigned(24) | IntCombinator::Signed(24) => Some(3),
        IntCombinator::Unsigned(32) | IntCombinator::Signed(32) => Some(4),
        IntCombinator::Unsigned(64) | IntCombinator::Signed(64) => Some(8),
        IntCombinator::BtcVarint | IntCombinator::ULEB128 => None,
        _ => None,
    }
}

fn enum_static_size(enum_comb: &EnumCombinator<'_>) -> Option<usize> {
    let enums = match enum_comb {
        EnumCombinator::Exhaustive { enums, .. } | EnumCombinator::NonExhaustive { enums, .. } => {
            enums
        }
    };
    int_combinator_static_size(&resolve_enum_type(enums))
}

fn common_static_size(sizes: impl IntoIterator<Item = Option<usize>>) -> Option<usize> {
    let mut sizes = sizes.into_iter();
    let first = sizes.next()??;
    for size in sizes {
        if size? != first {
            return None;
        }
    }
    Some(first)
}

fn eval_const_length_expr(
    len: &LengthExpr<'_>,
    static_sizes: &HashMap<String, usize>,
) -> Option<usize> {
    match len {
        LengthExpr::Const { value, .. } => Some(*value),
        LengthExpr::Dependent(..) => None,
        LengthExpr::SizeOf { format_name, .. } => static_sizes.get(&format_name.name).copied(),
        LengthExpr::BinOp {
            op, left, right, ..
        } => {
            let left = eval_const_length_expr(left, static_sizes)?;
            let right = eval_const_length_expr(right, static_sizes)?;
            match op {
                ArithOp::Add => left.checked_add(right),
                ArithOp::Sub => left.checked_sub(right),
                ArithOp::Mul => left.checked_mul(right),
                ArithOp::Div => left.checked_div(right),
            }
        }
    }
}

fn span_as_range(span: &Span) -> std::ops::Range<usize> {
    span.start()..span.end()
}

macro_rules! report_unbound_field {
    ($source:expr, $span:expr, $depend_id:expr) => {
        Report::build(ReportKind::Error, ($source.0, span_as_range($span)))
            .with_message("unbound dependent field")
            .with_label(
                Label::new(($source.0, span_as_range(&$depend_id.span)))
                    .with_message(format!("`@{}` is not found in current scope", $depend_id))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint($source)
            .unwrap();
    };
}

pub fn check<'ast>(
    ast: &'ast [Definition<'ast>],
    source: (&str, &Source),
) -> Result<GlobalCtx<'ast>, VestError> {
    let mut global_ctx = GlobalCtx {
        combinators: HashSet::new(),
        const_combinators: HashSet::new(),
        enums: HashMap::new(),
        static_sizes: HashMap::new(),
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

                match global_ctx.combinators.iter().find(|sig| &sig.name == name) {
                    Some(sig) => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message(format!("duplicate format definition `{}`", name))
                            .with_label(
                                Label::new((source.0, span_as_range(span)))
                                    .with_message(format!("This format is defined twice"))
                                    .with_color(Color::Red),
                            )
                            .with_label(
                                Label::new((
                                    source.0,
                                    span_as_range(&sig.resolved_combinator.as_span()),
                                ))
                                .with_message(format!(
                                    "The {} format is already defined here",
                                    name
                                ))
                                .with_color(Color::Yellow),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                    None => {
                        global_ctx.combinators.insert(CombinatorSig {
                            name: name.clone(),
                            param_defns,
                            resolved_combinator,
                        });
                    }
                }

                if let Combinator {
                    inner: CombinatorInner::Enum(enum_combinator),
                    ..
                } = combinator
                {
                    global_ctx
                        .enums
                        .insert(name.name.as_str(), enum_combinator.clone());
                }
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
                span,
            } => {
                // resolve the const combinator
                let resolved_combinator = global_ctx.resolve_const(const_combinator).to_owned();

                match global_ctx
                    .const_combinators
                    .iter()
                    .find(|sig| &sig.name == name)
                {
                    Some(sig) => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message(format!("duplicate const format definition `{}`", name))
                            .with_label(
                                Label::new((source.0, span_as_range(span)))
                                    .with_message(format!("This const format is defined twice"))
                                    .with_color(Color::Red),
                            )
                            .with_label(
                                Label::new((
                                    source.0,
                                    span_as_range(&sig.resolved_combinator.as_span()),
                                ))
                                .with_message(format!(
                                    "The {} const format is already defined here",
                                    name
                                ))
                                .with_color(Color::Yellow),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                    None => {
                        global_ctx.const_combinators.insert(ConstCombinatorSig {
                            name: name.clone(),
                            resolved_combinator,
                        });
                    }
                }
            }
            Definition::Endianess(_) => {}
            _ => unimplemented!(),
        }
    }

    global_ctx.static_sizes = StaticSizeEnv::new(ast).compute_all();

    for defn in ast {
        check_defn(defn, &mut local_ctx, &global_ctx, source)?;
    }

    Ok(global_ctx)
}

fn check_defn<'ast>(
    defn: &'ast Definition<'ast>,
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    local_ctx.reset();
    match defn {
        Definition::Combinator {
            param_defns,
            combinator,
            ..
        } => check_combinator(combinator, param_defns, local_ctx, global_ctx, source),
        Definition::ConstCombinator {
            const_combinator, ..
        } => check_const_combinator(const_combinator, local_ctx, global_ctx, source),
        Definition::Endianess(_) => Ok(()),
        _ => unimplemented!(),
    }
}

fn check_const_combinator<'ast>(
    const_combinator: &ConstCombinator<'ast>,
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    use ConstCombinator::*;
    match const_combinator {
        ConstInt(ConstIntCombinator {
            combinator,
            value,
            span,
        }) => check_const_int_combinator(combinator, value, span, source),
        ConstEnum(ConstEnumCombinator {
            combinator,
            variant,
            span,
        }) => check_const_enum_combinator(combinator, variant, span, local_ctx, global_ctx, source),
        ConstArray(combinator) => check_const_array_combinator(combinator, source),
        ConstBytes(combinator) => check_const_bytes_combinator(combinator, source),
        ConstStruct(ConstStructCombinator(const_combinators)) => {
            check_const_struct_combinator(const_combinators, local_ctx, global_ctx, source)
        }
        ConstChoice(ConstChoiceCombinator(const_choices)) => {
            check_const_choice_combinator(const_choices, local_ctx, global_ctx, source)
        }
        Vec(const_combinator) => {
            check_const_combinator(const_combinator, local_ctx, global_ctx, source)
        }
        ConstCombinatorInvocation { name, span } => {
            check_const_combinator_invocation(name, *span, local_ctx, global_ctx, source)
        }
    }
}

fn check_const_struct_combinator<'ast>(
    const_combinators: &[ConstCombinator<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    for const_combinator in const_combinators {
        check_const_combinator(const_combinator, local_ctx, global_ctx, source)?;
    }
    Ok(())
}

fn check_const_array_combinator(
    ConstArrayCombinator {
        combinator,
        len,
        values,
        span,
    }: &ConstArrayCombinator,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match values {
        ConstArray::Int {
            ints: int_vals,
            span: array_span,
        } => {
            if int_vals.len() != *len {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("mismatched array length")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                        "Length of array does not match the specified length (expected {}, got {})",
                        len,
                        int_vals.len()
                    ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                Err(VestError::TypeError)
            } else {
                for value in int_vals {
                    check_const_int_combinator(combinator, value, array_span, source)?;
                }
                Ok(())
            }
        }
        ConstArray::Repeat {
            repeat: int_val,
            count,
            span: array_span,
        } => {
            if *count != *len {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("mismatched array length")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                        "Length of array does not match the specified length (expected {}, got {})",
                        len, count
                    ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                Err(VestError::TypeError)
            } else {
                check_const_int_combinator(combinator, int_val, array_span, source)
            }
        }
        ConstArray::Char {
            span: array_span, ..
        } => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("mismatched array type")
                .with_label(
                    Label::new((source.0, span_as_range(array_span)))
                        .with_message("char array literals should be of type `[u8; N]`")
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
        ConstArray::Wildcard => Ok(()),
    }
}

fn check_const_combinator_invocation<'ast>(
    name: &Identifier<'ast>,
    span: Span<'ast>,
    _local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match global_ctx
        .const_combinators
        .iter()
        .find(|sig| sig.name == *name)
    {
        Some(..) => Ok(()),
        None => {
            Report::build(ReportKind::Error, (source.0, span_as_range(&span)))
                .with_message("undefined const format")
                .with_label(
                    Label::new((source.0, span_as_range(&span)))
                        .with_message("This const format is not defined")
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_const_choice_combinator<'ast>(
    const_choices: &[ConstChoice<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    for ConstChoice { combinator, .. } in const_choices {
        check_const_combinator(combinator, local_ctx, global_ctx, source)?;
    }
    Ok(())
}

fn check_const_enum_combinator<'ast>(
    combinator: &CombinatorInvocation<'ast>,
    variant: &Identifier<'ast>,
    span: &Span,
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    // Reuse combinator invocation checks (no params allowed unless in scope)
    check_combinator_invocation(combinator, &[], local_ctx, global_ctx, source)?;
    let binding = CombinatorInner::Invocation(combinator.clone());
    let resolved = global_ctx.resolve_alias(&binding);
    match resolved {
        CombinatorInner::Enum(enum_comb) => {
            let variants = match enum_comb {
                EnumCombinator::Exhaustive { enums, .. }
                | EnumCombinator::NonExhaustive { enums, .. } => enums,
            };
            if variants.iter().any(|Enum { name, .. }| name == variant) {
                Ok(())
            } else {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("undefined enum variant")
                    .with_label(
                        Label::new((source.0, span_as_range(&variant.span)))
                            .with_message(format!("`{}` is not a variant of this enum", variant))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                Err(VestError::TypeError)
            }
        }
        other => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("type mismatch")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("Const enum value applied to a non-enum type")
                        .with_color(Color::Red),
                )
                .with_label(
                    Label::new((source.0, span_as_range(&other.as_span())))
                        .with_message("This is the resolved type")
                        .with_color(Color::Yellow),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_const_bytes_combinator(
    combinator: &ConstBytesCombinator,
    source: (&str, &Source),
) -> Result<(), VestError> {
    let ConstBytesCombinator { len, values, span } = combinator;
    match values {
        ConstArray::Int {
            ints: int_vals,
            span: array_span,
        } => {
            if int_vals.len() != *len {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("mismatched byte array length")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                                "Length of byte array does not match the specified length (expected {}, got {})",
                                len, int_vals.len()
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
            for value in int_vals {
                if *value < u8::MIN.into() || *value > u8::MAX.into() {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("byte value out of range")
                        .with_label(
                            Label::new((source.0, span_as_range(array_span)))
                                .with_message(format!(
                                    "Value {} is out of range for u8 (expected 0-255)",
                                    value
                                ))
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    // panic!("Value {} is out of range for u8", value);
                    return Err(VestError::TypeError);
                }
            }
        }
        ConstArray::Repeat {
            repeat: int_val,
            count,
            span: array_span,
        } => {
            if *count != *len {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("mismatched byte array length")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                                "Length of byte array does not match the specified length (expected {}, got {})",
                                len, count
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
            if *int_val < u8::MIN.into() || *int_val > u8::MAX.into() {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("byte value out of range")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                                "Value {} is out of range for u8 (expected 0-255)",
                                int_val
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        }
        ConstArray::Char {
            chars,
            span: array_span,
        } => {
            if chars.len() != *len {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("mismatched char array length")
                    .with_label(
                        Label::new((source.0, span_as_range(array_span)))
                            .with_message(format!(
                                "Length of char array does not match the specified length (expected {}, got {})",
                                len, chars.len()
                            ))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        }
        ConstArray::Wildcard => {}
    }
    Ok(())
}

fn check_const_int_combinator(
    combinator: &IntCombinator,
    value: &i128,
    span: &Span,
    source: (&str, &Source),
) -> Result<(), VestError> {
    macro_rules! report_const_int_error {
        ($label_msg:expr) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("value out of range")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message($label_msg)
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        };
    }
    match combinator {
        IntCombinator::Signed(8) => {
            if *value < i8::MIN.into() || *value > i8::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for i8 (expected -128 to 127)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Signed(16) => {
            if *value < i16::MIN.into() || *value > i16::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for i16 (expected -32768 to 32767)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Signed(32) => {
            if *value < i32::MIN.into() || *value > i32::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for i32 (expected -2147483648 to 2147483647)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Signed(64) => {
            if *value < i64::MIN.into() || *value > i64::MAX.into() {
                report_const_int_error!(
                    format!(
                        "Value {} is out of range for i64 (expected -9223372036854775808 to 9223372036854775807)",
                        value
                    )
                );
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(8) => {
            if *value < u8::MIN.into() || *value > u8::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for u8 (expected 0 to 255)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(16) => {
            if *value < u16::MIN.into() || *value > u16::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for u16 (expected 0 to 65535)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(24) => {
            if *value < 0 || *value > 0xFFFFFF {
                report_const_int_error!(format!(
                    "Value {} is out of range for u24 (expected 0 to 16777215)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(32) => {
            if *value < u32::MIN.into() || *value > u32::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for u32 (expected 0 to 4294967295)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(64) => {
            if *value < u64::MIN.into() || *value > u64::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for u64 (expected 0 to 18446744073709551615)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::BtcVarint => {
            if *value < u64::MIN.into() || *value > u64::MAX.into() {
                report_const_int_error!(format!(
                    "Value {} is out of range for btc_varint (expected 0 to 18446744073709551615)",
                    value
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::ULEB128 => {
            if *value < 0 || *value > u64::MAX.into() {
                report_const_int_error!(format!("Value {} is out of range for uleb128", value));
                return Err(VestError::TypeError);
            }
        }
        _ => return Err(VestError::TypeError),
        // panic!("Unsupported const int combinator"),
    }
    Ok(())
}

fn check_combinator<'ast>(
    Combinator {
        inner,
        and_then,
        span: _,
    }: &Combinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    check_combinator_inner(inner, param_defns, local_ctx, global_ctx, source)?;
    if let Some(and_then) = and_then {
        check_combinator_inner_result_type(inner, source)?;
        check_combinator(and_then, param_defns, local_ctx, global_ctx, source)
    } else {
        Ok(())
    }
}

// must be a bytes combinator
fn check_combinator_inner_result_type(
    inner: &CombinatorInner,
    source: (&str, &Source),
) -> Result<(), VestError> {
    use CombinatorInner::*;
    match inner {
        Bytes(_) | Tail(_) => Ok(()),
        _ => {
            let span = inner.as_span();
            Report::build(ReportKind::Error, (source.0, span_as_range(&span)))
                .with_message("invalid format for `>>=`")
                .with_label(
                    Label::new((source.0, span_as_range(&span)))
                        .with_message(
                            "Only `[u8; N]` or `Tail` formats can be re-interpreted by `>>=`",
                        )
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_combinator_inner<'ast>(
    inner: &CombinatorInner<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    use CombinatorInner::*;
    match inner {
        ConstraintInt(ConstraintIntCombinator {
            combinator,
            constraint,
            span: _,
        }) => check_constraint_int_combinator(combinator, constraint.as_ref(), source),
        ConstraintEnum(ConstraintEnumCombinator {
            combinator,
            constraint,
            span,
        }) => check_constraint_enum_combinator(
            combinator,
            constraint,
            param_defns,
            local_ctx,
            global_ctx,
            span,
            source,
        ),
        Struct(StructCombinator {
            fields: struct_fields,
            span,
        }) => check_struct_combinator(
            struct_fields,
            span,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        Wrap(WrapCombinator {
            prior,
            combinator,
            post,
            span: _,
        }) => check_wrap_combinator(
            prior,
            combinator,
            post,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        Enum(
            EnumCombinator::Exhaustive { enums, span }
            | EnumCombinator::NonExhaustive { enums, span },
        ) => check_enum_combinator(enums, local_ctx, global_ctx, *span, source),
        Choice(ChoiceCombinator {
            depend_id,
            choices,
            span,
        }) => check_choice_combinator(
            depend_id,
            choices,
            span,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        SepBy(SepByCombinator { combinator, sep }) => {
            check_sep_by_combinator(combinator, sep, param_defns, local_ctx, global_ctx, source)
        }
        Vec(VecCombinator::Vec(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
        }
        Vec(VecCombinator::Vec1(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
        }
        Array(ArrayCombinator {
            combinator,
            len,
            span,
        }) => check_array_combinator(
            combinator,
            len,
            span,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        Bytes(BytesCombinator { len, span }) => {
            check_bytes_combinator(len, span, param_defns, local_ctx, global_ctx, source)
        }
        Tail(TailCombinator { .. }) => Ok(()),
        Apply(ApplyCombinator { stream, combinator }) => check_apply_combinator(
            stream,
            combinator,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        Option(OptionCombinator(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
        }
        Invocation(combinator) => {
            check_combinator_invocation(combinator, param_defns, local_ctx, global_ctx, source)
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
    combinator: &CombinatorInvocation<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    let CombinatorInvocation {
        func: name,
        args,
        span,
    } = combinator;
    match global_ctx.combinators.iter().find(|sig| sig.name == *name) {
        None => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("undefined format")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!("Format `{}` is not defined", name))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
            return Err(VestError::TypeError);
        }
        Some(combinator_sig) => {
            if args.len() != combinator_sig.param_defns.len() {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("argument count mismatch")
                    .with_label(
                        Label::new((source.0, span_as_range(span)))
                            .with_message(format!(
                                "Expected {} arguments, got {}",
                                combinator_sig.param_defns.len(),
                                args.len()
                            ))
                            .with_color(Color::Red),
                    )
                    .with_label(
                        Label::new((source.0, span_as_range(&combinator_sig.as_span())))
                            .with_message(format!(
                                "The arguments for format `{}` are defined here",
                                combinator_sig.name
                            ))
                            .with_color(Color::Yellow),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }

            for (arg, param_defn) in zip(args, combinator_sig.param_defns) {
                match (arg, param_defn) {
                    (Param::Stream(_), ParamDefn::Stream { .. }) => {}
                    (Param::Dependent(depend_id), ParamDefn::Dependent { combinator, .. }) => {
                        fn resolve_up_to_enums<'ast>(
                            comb: CombinatorInner<'ast>,
                        ) -> CombinatorInner<'ast> {
                            match comb {
                                CombinatorInner::Enum(
                                    EnumCombinator::Exhaustive { enums, span }
                                    | EnumCombinator::NonExhaustive { enums, span },
                                ) => CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                                    combinator: resolve_enum_type(&enums),
                                    constraint: None,
                                    span: span.clone(),
                                }),
                                l => l.clone(),
                            }
                        }
                        // 1. try to find `depend_id` in local_ctx
                        if let Some(arg_combinator) = local_ctx.dependent_fields.get(depend_id) {
                            let left =
                                resolve_up_to_enums(global_ctx.resolve(arg_combinator).clone());
                            let right =
                                resolve_up_to_enums(global_ctx.resolve_alias(combinator).clone());
                            if left != right {
                                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                    .with_message("argument type mismatch")
                                    .with_label(
                                        Label::new((source.0, span_as_range(span)))
                                            .with_message(format!(
                                                "Expected {}, got {}",
                                                combinator, arg_combinator
                                            ))
                                            .with_color(Color::Red),
                                    )
                                    .with_label(
                                        Label::new((
                                            source.0,
                                            span_as_range(&combinator_sig.as_span()),
                                        ))
                                        .with_message(format!(
                                            "Format `{}` is defined here",
                                            combinator_sig.name
                                        ))
                                        .with_color(Color::Yellow),
                                    )
                                    .with_label(
                                        Label::new((source.0, span_as_range(&arg_combinator.span)))
                                            .with_message(format!(
                                                "Field `@{}` is defined here",
                                                depend_id
                                            ))
                                            .with_color(Color::Yellow),
                                    )
                                    .finish()
                                    .eprint(source)
                                    .unwrap();
                                return Err(VestError::TypeError);
                            }
                        } else {
                            // 2. try to find `depend_id` in param_defns
                            let param_defn =
                                param_defns.iter().find(|param_defn| match param_defn {
                                    ParamDefn::Dependent { name, .. } => name == depend_id,
                                    _ => false,
                                });
                            match param_defn {
                                Some(ParamDefn::Dependent {
                                    combinator: combinator_,
                                    ..
                                }) => {
                                    let left = resolve_up_to_enums(
                                        global_ctx.resolve_alias(combinator_).clone(),
                                    );
                                    let right = resolve_up_to_enums(
                                        global_ctx.resolve_alias(combinator).clone(),
                                    );
                                    if left != right {
                                        Report::build(
                                            ReportKind::Error,
                                            (source.0, span_as_range(span)),
                                        )
                                        .with_message("argument type mismatch")
                                        .with_label(
                                            Label::new((source.0, span_as_range(span)))
                                                .with_message(format!(
                                                    "Expected {}, got {}",
                                                    combinator, combinator_
                                                ))
                                                .with_color(Color::Red),
                                        )
                                        .with_label(
                                            Label::new((
                                                source.0,
                                                span_as_range(&combinator_sig.as_span()),
                                            ))
                                            .with_message(format!(
                                                "Format `{}` is defined here",
                                                combinator_sig.name
                                            ))
                                            .with_color(Color::Yellow),
                                        )
                                        .with_label(
                                            Label::new((
                                                source.0,
                                                span_as_range(&combinator_.as_span()),
                                            ))
                                            .with_message(format!(
                                                "Parameter `@{}` is defined here",
                                                depend_id
                                            ))
                                            .with_color(Color::Yellow),
                                        )
                                        .finish()
                                        .eprint(source)
                                        .unwrap();
                                        return Err(VestError::TypeError);
                                    }
                                }
                                _ => {
                                    report_unbound_field!(source, span, depend_id);
                                    return Err(VestError::TypeError);
                                }
                            }
                        }
                    }
                    _ => return Err(VestError::TypeError),
                }
            }
        }
    }
    Ok(())
}

fn check_apply_combinator<'ast>(
    _stream: &Identifier<'ast>,
    combinator: &Combinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
}

fn check_length_expr<'ast>(
    len: &LengthExpr<'ast>,
    span: &Span<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match len {
        LengthExpr::Const { .. } => Ok(()),
        LengthExpr::Dependent(depend_id) => check_dependent_id_is_valid_length(
            depend_id,
            span,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
        LengthExpr::SizeOf {
            format_name,
            span: size_span,
        } => {
            if global_ctx.static_sizes.contains_key(&format_name.name) {
                return Ok(());
            }

            if let Some(sig) = global_ctx
                .combinators
                .iter()
                .find(|sig| sig.name == *format_name)
            {
                Report::build(ReportKind::Error, (source.0, span_as_range(size_span)))
                    .with_message("format does not have a statically-known size")
                    .with_label(
                        Label::new((source.0, span_as_range(size_span)))
                            .with_message(format!("`{}` depends on runtime values", format_name))
                            .with_color(Color::Red),
                    )
                    .with_label(
                        Label::new((source.0, span_as_range(&sig.as_span())))
                            .with_message(format!("`{}` is defined here", format_name))
                            .with_color(Color::Yellow),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }

            {
                Report::build(ReportKind::Error, (source.0, span_as_range(size_span)))
                    .with_message("undefined format in size expression")
                    .with_label(
                        Label::new((source.0, span_as_range(size_span)))
                            .with_message(format!("`{}` is not defined", format_name))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        }
        LengthExpr::BinOp { left, right, .. } => {
            check_length_expr(left, span, param_defns, local_ctx, global_ctx, source)?;
            check_length_expr(right, span, param_defns, local_ctx, global_ctx, source)
        }
    }
}

fn check_dependent_id_is_valid_length<'ast>(
    depend_id: &DependentId<'ast>,
    span: &Span<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    // For simple dependent ids (no nested access), check in local_ctx and param_defns
    if depend_id.is_simple() {
        let root_id = depend_id.to_identifier();

        // 1. try to find in local_ctx
        if let Some(combinator) = local_ctx.dependent_fields.get(&root_id) {
            return check_combinator_is_unsigned_int(
                global_ctx.resolve(combinator),
                &depend_id.full_path(),
                span,
                &combinator.span,
                source,
            );
        }

        // 2. try to find in param_defns
        let param_defn = param_defns.iter().find(|param_defn| match param_defn {
            ParamDefn::Dependent { name, .. } => name == &root_id,
            _ => false,
        });

        match param_defn {
            Some(ParamDefn::Dependent { combinator, .. }) => {
                return check_combinator_is_unsigned_int(
                    global_ctx.resolve_alias(combinator),
                    &depend_id.full_path(),
                    span,
                    &combinator.as_span(),
                    source,
                );
            }
            _ => {
                report_unbound_field!(source, span, root_id);
                return Err(VestError::TypeError);
            }
        }
    }

    // For nested access (@hdr.field), we need to resolve through the struct
    let root_id = Identifier {
        name: depend_id.root.clone(),
        span: depend_id.span,
    };

    // Find the root field
    let root_combinator = if let Some(combinator) = local_ctx.dependent_fields.get(&root_id) {
        global_ctx.resolve(combinator)
    } else {
        let param_defn = param_defns.iter().find(|param_defn| match param_defn {
            ParamDefn::Dependent { name, .. } => name == &root_id,
            _ => false,
        });
        match param_defn {
            Some(ParamDefn::Dependent { combinator, .. }) => global_ctx.resolve_alias(combinator),
            _ => {
                report_unbound_field!(source, span, root_id);
                return Err(VestError::TypeError);
            }
        }
    };

    // Navigate through nested fields
    let mut current_combinator = root_combinator;
    for (i, field_name) in depend_id.path.iter().enumerate() {
        match current_combinator {
            CombinatorInner::Struct(struct_comb) => {
                let field = struct_comb.fields.iter().find(|f| match f {
                    StructField::Dependent { label, .. } => label.name == *field_name,
                    _ => false,
                });
                match field {
                    Some(StructField::Dependent { combinator, .. }) => {
                        if i == depend_id.path.len() - 1 {
                            // Final field - check it's an unsigned int
                            return check_combinator_is_unsigned_int(
                                global_ctx.resolve(combinator),
                                &depend_id.full_path(),
                                span,
                                &combinator.span,
                                source,
                            );
                        } else {
                            current_combinator = global_ctx.resolve(combinator);
                        }
                    }
                    _ => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("invalid nested field access")
                            .with_label(
                                Label::new((source.0, span_as_range(&depend_id.span)))
                                    .with_message(format!(
                                        "field `{}` is not a dependent field in the struct",
                                        field_name
                                    ))
                                    .with_color(Color::Red),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                }
            }
            CombinatorInner::Invocation(inv) => {
                // Resolve the invocation and continue
                let sig = global_ctx
                    .combinators
                    .iter()
                    .find(|sig| sig.name == inv.func);
                if let Some(sig) = sig {
                    current_combinator = &sig.resolved_combinator;
                    // Retry this field with the resolved combinator
                    return check_nested_field_in_combinator(
                        current_combinator,
                        &depend_id.path[i..],
                        depend_id,
                        span,
                        global_ctx,
                        source,
                    );
                } else {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("cannot resolve type for nested access")
                        .with_label(
                            Label::new((source.0, span_as_range(&depend_id.span)))
                                .with_message(format!("cannot resolve type of `{}`", inv.func))
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            }
            _ => {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("invalid nested field access")
                    .with_label(
                        Label::new((source.0, span_as_range(&depend_id.span)))
                            .with_message("nested field access requires a struct type")
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        }
    }

    Ok(())
}

fn check_nested_field_in_combinator<'ast>(
    combinator: &CombinatorInner<'ast>,
    remaining_path: &[String],
    depend_id: &DependentId<'ast>,
    span: &Span<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    if remaining_path.is_empty() {
        return check_combinator_is_unsigned_int(
            combinator,
            &depend_id.full_path(),
            span,
            &depend_id.span,
            source,
        );
    }

    match combinator {
        CombinatorInner::Struct(struct_comb) => {
            let field_name = &remaining_path[0];
            let field = struct_comb.fields.iter().find(|f| match f {
                StructField::Dependent { label, .. } => label.name == *field_name,
                _ => false,
            });
            match field {
                Some(StructField::Dependent { combinator, .. }) => {
                    check_nested_field_in_combinator(
                        global_ctx.resolve(combinator),
                        &remaining_path[1..],
                        depend_id,
                        span,
                        global_ctx,
                        source,
                    )
                }
                _ => {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("invalid nested field access")
                        .with_label(
                            Label::new((source.0, span_as_range(&depend_id.span)))
                                .with_message(format!(
                                    "field `{}` is not a dependent field",
                                    field_name
                                ))
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    Err(VestError::TypeError)
                }
            }
        }
        _ => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid nested field access")
                .with_label(
                    Label::new((source.0, span_as_range(&depend_id.span)))
                        .with_message("nested field access requires a struct type")
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_combinator_is_unsigned_int(
    combinator: &CombinatorInner,
    field_path: &str,
    span: &Span,
    def_span: &Span,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match combinator {
        CombinatorInner::ConstraintInt(ConstraintIntCombinator {
            combinator:
                IntCombinator::Unsigned(_) | IntCombinator::BtcVarint | IntCombinator::ULEB128,
            ..
        }) => Ok(()),
        _ => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid length specifier")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!(
                            "`@{}` is not a valid length specifier, expected an unsigned int",
                            field_path
                        ))
                        .with_color(Color::Red),
                )
                .with_label(
                    Label::new((source.0, span_as_range(def_span)))
                        .with_message(format!("Field `@{}` is defined here", field_path))
                        .with_color(Color::Yellow),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_bytes_combinator<'ast>(
    len: &LengthExpr<'ast>,
    span: &Span<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    check_length_expr(len, span, param_defns, local_ctx, global_ctx, source)
}

fn check_array_combinator<'ast>(
    combinator: &Combinator<'ast>,
    len: &LengthSpecifier<'ast>,
    span: &Span<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
    check_bytes_combinator(len, span, param_defns, local_ctx, global_ctx, source)
}

fn check_sep_by_combinator<'ast>(
    combinator: &VecCombinator<'ast>,
    sep: &ConstCombinator<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match combinator {
        VecCombinator::Vec(combinator) | VecCombinator::Vec1(combinator) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
        }
    }
    check_const_combinator(sep, local_ctx, global_ctx, source)
}

impl<'ast> Choices<'ast> {
    pub fn get_span_for_fst_tag(&self) -> Span<'ast> {
        match self {
            Choices::Enums(enums) => enums
                .first()
                .map(|(id, _)| id.span)
                .unwrap_or_else(|| panic!("Choices::Enums should not be empty")),
            Choices::Ints(ints) => ints
                .first()
                .map(|(elem_opt, _)| {
                    elem_opt.as_ref().map_or_else(
                        || panic!("First choice in Choices::Ints should not be wildcard"),
                        |elem| elem.as_span(),
                    )
                })
                .unwrap_or_else(|| panic!("Choices::Ints should not be empty")),
            Choices::Arrays(arrays) => arrays
                .first()
                .map(|(array, _)| array.as_span())
                .unwrap_or_else(|| panic!("Choices::Arrays should not be empty")),
        }
    }
}

impl<'ast> ConstraintElem<'ast> {
    pub fn overlap(&self, other: &ConstraintElem<'ast>) -> bool {
        match (self, other) {
            (
                ConstraintElem::Range { start, end, .. },
                ConstraintElem::Range {
                    start: o_start,
                    end: o_end,
                    ..
                },
            ) => {
                let self_start = start.unwrap_or(i128::MIN);
                let self_end = end.unwrap_or(i128::MAX);
                let other_start = o_start.unwrap_or(i128::MIN);
                let other_end = o_end.unwrap_or(i128::MAX);
                !(self_end < other_start || other_end < self_start)
            }
            (ConstraintElem::Single { elem, .. }, ConstraintElem::Single { elem: o_elem, .. }) => {
                elem == o_elem
            }
            (ConstraintElem::Range { start, end, .. }, ConstraintElem::Single { elem, .. }) => {
                let self_start = start.unwrap_or(i128::MIN);
                let self_end = end.unwrap_or(i128::MAX);
                *elem >= self_start && *elem <= self_end
            }
            (ConstraintElem::Single { elem, .. }, ConstraintElem::Range { start, end, .. }) => {
                let self_start = start.unwrap_or(i128::MIN);
                let self_end = end.unwrap_or(i128::MAX);
                *elem >= self_start && *elem <= self_end
            }
        }
    }
}

fn check_choice_combinator<'ast>(
    depend_id: &Option<Identifier<'ast>>,
    choices: &Choices<'ast>,
    span: &Span,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    let get_combinator_from_depend_id = |depend_id| -> Result<&CombinatorInner<'ast>, VestError> {
        local_ctx
            .dependent_fields
            .get(depend_id)
            .map(|combinator| &combinator.inner)
            .or_else(|| {
                param_defns.iter().find_map(|param_defn| match param_defn {
                    ParamDefn::Dependent {
                        name,
                        combinator,
                        span,
                    } if name == depend_id => Some(combinator),
                    _ => None,
                })
            })
            .ok_or_else(|| {
                report_unbound_field!(source, span, depend_id);
                VestError::TypeError
            })
    };
    // if there isn't a depend_id, it must be an `enum` choice:
    if depend_id.is_none() && !matches!(choices, Choices::Enums(_)) {
        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
            .with_message("invalid choice format")
            .with_label(
                Label::new((source.0, span_as_range(span)))
                    .with_message("Labels for a non-dependent ordered choice must be `variant_id`")
                    .with_color(Color::Red),
            )
            .with_label(
                Label::new((source.0, span_as_range(&choices.get_span_for_fst_tag())))
                    .with_message("This label is not a `variant_id`")
                    .with_color(Color::Yellow),
            )
            .finish()
            .eprint(source)
            .unwrap();
        return Err(VestError::TypeError);
    }
    fn resolve_enum_from<'ast>(
        comb: &'ast CombinatorInner<'ast>,
        global_ctx: &'ast GlobalCtx<'ast>,
    ) -> Option<&'ast EnumCombinator<'ast>> {
        match comb {
            CombinatorInner::Enum(e) => Some(e),
            CombinatorInner::ConstraintEnum(ConstraintEnumCombinator { combinator, .. }) => {
                global_ctx
                    .combinators
                    .iter()
                    .find(|sig| sig.name == combinator.func)
                    .and_then(|sig| match &sig.resolved_combinator {
                        CombinatorInner::Enum(e) => Some(e),
                        _ => None,
                    })
            }
            _ => None,
        }
    }
    match choices {
        Choices::Enums(enums) => {
            if let Some(depend_id) = depend_id {
                // check if depend_id a prior field in the struct or in the param_defns
                let combinator = get_combinator_from_depend_id(depend_id)?;
                let combinator = combinator.clone();
                check_combinator_inner(&combinator, param_defns, local_ctx, global_ctx, source)?;
                let combinator = global_ctx.resolve_alias(&combinator);
                // check if `combinator` is defined as an enum
                if let Some(enum_) = resolve_enum_from(combinator, global_ctx) {
                    let (enum_variants, is_non_exhaustive) = match enum_ {
                        EnumCombinator::Exhaustive { enums, .. } => (enums, false),
                        EnumCombinator::NonExhaustive { enums, .. } => (enums, true),
                    };
                    // check for well-formed variants
                    let mut variants = HashSet::new();
                    for (variant, combinator) in enums {
                        if variant.name == "_" {
                            if !is_non_exhaustive {
                                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                            .with_message("invalid choice variant")
                                            .with_label(
                                                Label::new((source.0, span_as_range(&variant.span)))
                                                    .with_message("Wildcard `_` is not allowed in an exhaustive choice")
                                                    .with_color(Color::Red),
                                            )
                                            .with_label(
                                                Label::new((source.0, span_as_range(span)))
                                                    .with_message(format!("This choice should only contain variants {}",
                                                        enum_variants
                                                            .iter()
                                                            .map(|Enum { name, .. }| format!(
                                                                "`{}`",
                                                                &name.name
                                                            ))
                                                            .collect::<Vec<_>>()
                                                            .join(", ")
                                                        ))
                                                    .with_color(Color::Yellow),
                                            )
                                            .finish()
                                            .eprint(source)
                                            .unwrap();
                                return Err(VestError::TypeError);
                            } else {
                                continue;
                            }
                        } else if !enum_variants
                            .iter()
                            .any(|Enum { name, .. }| name == variant)
                        {
                            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                .with_message("invalid choice variant")
                                .with_label(
                                    Label::new((source.0, span_as_range(&variant.span)))
                                        .with_message(format!(
                                            "Enum variant `{}` is undefined",
                                            &variant.name
                                        ))
                                        .with_color(Color::Red),
                                )
                                .with_label(
                                    Label::new((source.0, span_as_range(span)))
                                        .with_message(format!(
                                            "This choice should only contain variants {}",
                                            enum_variants
                                                .iter()
                                                .map(|Enum { name, .. }| format!(
                                                    "`{}`",
                                                    &name.name
                                                ))
                                                .collect::<Vec<_>>()
                                                .join(", ")
                                        ))
                                        .with_color(Color::Yellow),
                                )
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                        if !variants.insert(variant.name.as_str()) {
                            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                .with_message("duplicate choice variant")
                                .with_labels(enums.iter().map(|(label, _)| {
                                    Label::new((source.0, span_as_range(&label.span)))
                                        .with_color(Color::Yellow)
                                }))
                                .with_label(
                                    Label::new((source.0, span_as_range(&variant.span)))
                                        .with_message(format!("Duplicate variant",))
                                        .with_color(Color::Red),
                                )
                                .with_label(
                                    Label::new((source.0, span_as_range(span)))
                                        .with_message(format!(
                                            "Multiple variants `{}` found in a choice format",
                                            variant.name
                                        ))
                                        .with_color(Color::Red),
                                )
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                        check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
                    }
                    if !is_non_exhaustive {
                        // check for exhaustiveness
                        let defined_variants = enum_variants
                            .iter()
                            .map(|Enum { name, .. }| name.name.as_str())
                            .collect::<HashSet<_>>();
                        if defined_variants != variants {
                            let missing_variants: Vec<&str> =
                                defined_variants.difference(&variants).copied().collect();
                            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                .with_message("non-exhaustive choice")
                                .with_label(
                                    Label::new((source.0, span_as_range(span)))
                                        .with_message(format!(
                                            "Missing variants: {}",
                                            missing_variants.join(", ")
                                        ))
                                        .with_color(Color::Red),
                                )
                                .with_labels(missing_variants.iter().filter_map(|variant| {
                                    enum_variants.iter().find_map(|Enum { name, .. }| {
                                        if &name.name == variant {
                                            Some(
                                                Label::new((source.0, span_as_range(&name.span)))
                                                    .with_message(format!(
                                                        "Variant `{}` is defined here",
                                                        variant
                                                    ))
                                                    .with_color(Color::Yellow),
                                            )
                                        } else {
                                            None
                                        }
                                    })
                                }))
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                    }
                } else {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("type mismatch")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "Expected an enum type for `@{}`, got {}",
                                    depend_id, combinator
                                ))
                                .with_color(Color::Red),
                        )
                        .with_label(
                            Label::new((source.0, span_as_range(&combinator.as_span())))
                                .with_message(format!("This is `@{}`'s type", depend_id,))
                                .with_color(Color::Yellow),
                        )
                        .with_labels(enums.iter().map(|(label, _)| {
                            Label::new((source.0, span_as_range(&label.span)))
                                .with_color(Color::Yellow)
                        }))
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            } else {
                let mut labels = HashSet::new();
                for (label, combinator) in enums {
                    if !labels.insert(label.name.as_str()) {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("duplicate choice variant")
                            .with_labels(enums.iter().map(|(label, _)| {
                                Label::new((source.0, span_as_range(&label.span)))
                                    .with_color(Color::Yellow)
                            }))
                            .with_label(
                                Label::new((source.0, span_as_range(&label.span)))
                                    .with_message(format!("Duplicate variant `{}`", label.name))
                                    .with_color(Color::Red),
                            )
                            .with_label(
                                Label::new((source.0, span_as_range(span)))
                                    .with_message(format!(
                                        "Multiple variants `{}` found in a choice format",
                                        label.name
                                    ))
                                    .with_color(Color::Red),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                    check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
                }
            }
        }
        Choices::Ints(ints) => {
            if let Some(depend_id) = depend_id {
                let combinator = get_combinator_from_depend_id(depend_id)?;
                let combinator = combinator.clone();
                check_combinator_inner(&combinator, param_defns, local_ctx, global_ctx, source)?;
                let combinator = global_ctx.resolve_alias(&combinator);
                let check_overlap = |patterns: Vec<&ConstraintElem<'_>>| -> Result<(), VestError> {
                    for (i, pattern_i) in patterns.iter().enumerate() {
                        for (j, pattern_j) in patterns.iter().enumerate().skip(i + 1) {
                            if pattern_i.overlap(pattern_j) {
                                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                    .with_message("overlapping int patterns")
                                    .with_label(
                                        Label::new((source.0, span_as_range(span)))
                                            .with_message(format!(
                                                "Pattern #{} and #{} overlap",
                                                i, j
                                            ))
                                            .with_color(Color::Red),
                                    )
                                    .with_label(
                                        Label::new((source.0, span_as_range(&pattern_i.as_span())))
                                            .with_message(format!("Pattern #{}", i))
                                            .with_color(Color::Yellow),
                                    )
                                    .with_label(
                                        Label::new((source.0, span_as_range(&pattern_j.as_span())))
                                            .with_message(format!("Pattern #{}", j))
                                            .with_color(Color::Yellow),
                                    )
                                    .with_labels(ints.iter().filter_map(|(elem_opt, _)| {
                                        elem_opt.as_ref().map(|elem| {
                                            Label::new((source.0, span_as_range(&elem.as_span())))
                                                .with_color(Color::Yellow)
                                        })
                                    }))
                                    .finish()
                                    .eprint(source)
                                    .unwrap();
                                return Err(VestError::TypeError);
                            }
                        }
                    }
                    Ok(())
                };
                // check if `combinator` is defined as an int
                if let CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                    combinator:
                        int_combinator @ (IntCombinator::Unsigned(_)
                        | IntCombinator::BtcVarint
                        | IntCombinator::ULEB128),
                    ..
                }) = combinator
                {
                    let int_combinator = int_combinator.clone();
                    let mut patterns = Vec::new();
                    for (pattern, combinator) in ints {
                        if let Some(pattern) = pattern {
                            check_constraint_elem(&int_combinator, pattern, source)?;
                            patterns.push(pattern);
                        }
                        check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
                    }
                    // check non of the patterns overlap
                    check_overlap(patterns)?;
                } else if let Some(enum_) = resolve_enum_from(combinator, global_ctx) {
                    // check if it's non-exhaustive enum (which is equivalent to an int choice)
                    match enum_ {
                        EnumCombinator::NonExhaustive { enums, .. } => {
                            let int_combinator = resolve_enum_type(enums);
                            let mut patterns = Vec::new();
                            for (pattern, combinator) in ints {
                                if let Some(pattern) = pattern {
                                    check_constraint_elem(&int_combinator, pattern, source)?;
                                    patterns.push(pattern);
                                }
                                check_combinator(
                                    combinator,
                                    param_defns,
                                    local_ctx,
                                    global_ctx,
                                    source,
                                )?;
                            }
                            // check non of the patterns overlap
                            check_overlap(patterns)?;
                        }
                        EnumCombinator::Exhaustive { .. } => {
                            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                .with_message("type mismatch")
                                .with_label(
                                    Label::new((source.0, span_as_range(span)))
                                        .with_message("Invalid choice format")
                                        .with_color(Color::Red),
                                )
                                .with_label(
                                    Label::new((source.0, span_as_range(&depend_id.span)))
                                    .with_message(format!(
                                        "`@{}` is defined as an exhaustive enum, cannot be used in an int choice", depend_id
                                        ))
                                    .with_color(Color::Red),
                                )
                                .with_labels(ints.iter().map(|(elem_opt, _)| {
                                    elem_opt
                                        .as_ref()
                                        .map(|elem| {
                                            Label::new((source.0, span_as_range(&elem.as_span())))
                                                .with_color(Color::Yellow)
                                        })
                                        .unwrap_or_else(|| Label::new((source.0, span_as_range(span))))
                                }))
                                .with_help("Use a non-exhaustive enum instead, or use an int format")
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                    }
                } else {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("type mismatch")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "Expected an unsigned int for `@{}`, got {}",
                                    depend_id, combinator
                                ))
                                .with_color(Color::Red),
                        )
                        .with_label(
                            Label::new((source.0, span_as_range(&combinator.as_span())))
                                .with_message(format!("This is `@{}`'s type", depend_id))
                                .with_color(Color::Yellow),
                        )
                        .with_labels(ints.iter().map(|(elem_opt, _)| {
                            elem_opt
                                .as_ref()
                                .map(|elem| {
                                    Label::new((source.0, span_as_range(&elem.as_span())))
                                        .with_color(Color::Yellow)
                                })
                                .unwrap_or_else(|| Label::new((source.0, span_as_range(span))))
                        }))
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            } else {
                unreachable!("Relevant checks should have been performed earlier");
            }
        }
        Choices::Arrays(arrays) => {
            if let Some(depend_id) = depend_id {
                let combinator = get_combinator_from_depend_id(depend_id)?;
                let combinator = combinator.clone();
                check_combinator_inner(&combinator, param_defns, local_ctx, global_ctx, source)?;
                let combinator = global_ctx.resolve_alias(&combinator);
                // check if `combinator` is defined as an array
                if let CombinatorInner::Array(ArrayCombinator {
                    len,
                    span: array_span,
                    ..
                })
                | CombinatorInner::Bytes(BytesCombinator {
                    len,
                    span: array_span,
                }) = combinator
                {
                    let Some(len) = eval_const_length_expr(len, &global_ctx.static_sizes) else {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("invalid array type")
                            .with_label(
                                Label::new((source.0, span_as_range(span)))
                                    .with_message("Cannot pattern match on a variable-length type")
                                    .with_color(Color::Red),
                            )
                            .with_label(
                                Label::new((source.0, span_as_range(array_span)))
                                    .with_message(format!(
                                        "This is `@{}`'s type, which is not a fixed-length array",
                                        depend_id
                                    ))
                                    .with_color(Color::Yellow),
                            )
                            .with_labels(arrays.iter().map(|(array, _)| {
                                Label::new((source.0, span_as_range(&array.as_span())))
                                    .with_color(Color::Yellow)
                            }))
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    };
                    let mut array_variants = HashSet::new();
                    for (array, comb) in arrays {
                        if !array_variants.insert(array) {
                            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                .with_message("duplicate choice variant")
                                .with_labels(arrays.iter().map(|(array, _)| {
                                    Label::new((source.0, span_as_range(&array.as_span())))
                                        .with_color(Color::Yellow)
                                }))
                                .with_label(
                                    Label::new((source.0, span_as_range(&array.as_span())))
                                        .with_message(format!("Duplicate variant `{}`", array))
                                        .with_color(Color::Red),
                                )
                                .with_label(
                                    Label::new((source.0, span_as_range(span)))
                                        .with_message(format!(
                                            "Multiple variants `{}` found in a choice format",
                                            array
                                        ))
                                        .with_color(Color::Red),
                                )
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                        macro_rules! report_len_mismatch {
                            ($array:expr, $exp_len:expr, $got_len:expr) => {
                                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                                    .with_message("type mismatch")
                                    .with_label(
                                        Label::new((source.0, span_as_range(span)))
                                            .with_message("Invalid choice format")
                                            .with_color(Color::Red),
                                    )
                                    .with_label(
                                        Label::new((source.0, span_as_range(&array.as_span())))
                                            .with_message(format!(
                                                "Expected length {}, got {}",
                                                $exp_len, $got_len
                                            ))
                                            .with_color(Color::Red),
                                    )
                                    .with_label(
                                        Label::new((
                                            source.0,
                                            span_as_range(&combinator.as_span()),
                                        ))
                                        .with_message(format!("This is `@{}`'s type", depend_id))
                                        .with_color(Color::Yellow),
                                    )
                                    .finish()
                                    .eprint(source)
                                    .unwrap();
                            };
                        }
                        match array {
                            ConstArray::Int { ints, .. } => {
                                if ints.len() != len {
                                    report_len_mismatch!(array, len, ints.len());
                                    return Err(VestError::TypeError);
                                }
                            }
                            ConstArray::Char { chars, .. } => {
                                if chars.len() != len {
                                    report_len_mismatch!(array, len, chars.len());
                                    return Err(VestError::TypeError);
                                }
                            }
                            ConstArray::Repeat { count, .. } => {
                                if *count != len {
                                    report_len_mismatch!(array, len, *count);
                                    return Err(VestError::TypeError);
                                }
                            }
                            ConstArray::Wildcard => (),
                        }
                        check_combinator(comb, param_defns, local_ctx, global_ctx, source)?;
                    }
                } else {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("type mismatch")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "Expected an array type for `@{}`, got {}",
                                    depend_id, combinator
                                ))
                                .with_color(Color::Red),
                        )
                        .with_label(
                            Label::new((source.0, span_as_range(&combinator.as_span())))
                                .with_message(format!("This is `@{}`'s type", depend_id))
                                .with_color(Color::Yellow),
                        )
                        .with_labels(arrays.iter().map(|(array, _)| {
                            Label::new((source.0, span_as_range(&array.as_span())))
                                .with_color(Color::Yellow)
                        }))
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            } else {
                unreachable!("Relevant checks should have been performed earlier");
            }
        }
    }
    Ok(())
}

fn check_enum_combinator(
    enums: &[Enum],
    _local_ctx: &mut LocalCtx,
    _global_ctxx: &GlobalCtx,
    span: Span,
    source: (&str, &Source),
) -> Result<(), VestError> {
    // Check that type annotations are consistent:
    // all present type suffixes must agree (unsuffixed values are allowed).
    let first_annotated = enums.iter().find(|e| e.type_annotation.is_some());
    if let Some(first) = first_annotated {
        let expected_ty = first.type_annotation.as_ref().unwrap();
        for e in enums {
            if let Some(ref ty) = e.type_annotation {
                if ty != expected_ty {
                    let msg = format!(
                        "Inconsistent type annotations: `{}` has type suffix `{}` but `{}` has `{}`",
                        first.name, expected_ty, e.name, ty
                    );
                    Report::build(ReportKind::Error, (source.0, span_as_range(&e.span)))
                        .with_message("inconsistent enum type annotations")
                        .with_label(
                            Label::new((source.0, span_as_range(&e.span)))
                                .with_message(&msg)
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            }
        }
    }

    let combinator = resolve_enum_type(enums);
    for Enum { value, .. } in enums {
        check_const_int_combinator(&combinator, value, &span, source)?;
    }
    Ok(())
}

/// Resolve the underlying integer type for an enum.
pub fn resolve_enum_type(enums: &[Enum]) -> IntCombinator {
    if let Some(first) = enums.iter().find_map(|e| e.type_annotation.as_ref()) {
        first.clone()
    } else {
        infer_enum_type(enums)
    }
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
    prior: &[ConstCombinator<'ast>],
    combinator: &Combinator<'ast>,
    post: &[ConstCombinator<'ast>],
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    for const_combinator in prior {
        check_const_combinator(const_combinator, local_ctx, global_ctx, source)?;
    }
    check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
    for const_combinator in post {
        check_const_combinator(const_combinator, local_ctx, global_ctx, source)?;
    }
    Ok(())
}

fn check_struct_combinator<'ast>(
    struct_fields: &[StructField<'ast>],
    span: &Span,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx,
    source: (&str, &Source),
) -> Result<(), VestError> {
    macro_rules! report_duplicate_field {
        ($label:expr, $field_span:expr) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("duplicate field name")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("Invalid struct format")
                        .with_color(Color::Red),
                )
                .with_label(
                    Label::new((source.0, span_as_range($field_span)))
                        .with_message(format!("Duplicate field name `{}`", $label))
                        .with_color(Color::Yellow),
                )
                .with_labels(local_ctx.struct_fields.iter().map(|name| {
                    Label::new((source.0, span_as_range(&name.span))).with_color(Color::Yellow)
                }))
                .finish()
                .eprint(source)
                .unwrap();
        };
    }
    for field in struct_fields {
        match field {
            StructField::Stream(_) => {}
            StructField::Dependent {
                label,
                combinator,
                span: field_span,
            } => {
                if !local_ctx.dependent_fields.contains_key(label) {
                    local_ctx
                        .dependent_fields
                        .insert(label.to_owned(), combinator.to_owned());
                } else {
                    report_duplicate_field!(label, field_span);
                    return Err(VestError::TypeError);
                }
                if !local_ctx.struct_fields.insert(label.to_owned()) {
                    report_duplicate_field!(label, field_span);
                    return Err(VestError::TypeError);
                }
                check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
            }
            StructField::Const {
                combinator,
                label,
                span: field_span,
            } => {
                if !local_ctx.struct_fields.insert(label.to_owned()) {
                    report_duplicate_field!(label, field_span);
                    return Err(VestError::TypeError);
                }
                check_const_combinator(combinator, local_ctx, global_ctx, source)?;
            }
            StructField::Ordinary {
                combinator,
                label,
                span: field_span,
            } => {
                if !local_ctx.struct_fields.insert(label.to_owned()) {
                    report_duplicate_field!(label, field_span);
                    return Err(VestError::TypeError);
                }
                check_combinator(combinator, param_defns, local_ctx, global_ctx, source)?;
            }
        }
    }
    Ok(())
}

fn check_constraint_int_combinator(
    combinator: &IntCombinator,
    constraint: Option<&IntConstraint>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match constraint {
        Some(IntConstraint::Single { elem, span: _ }) => {
            check_constraint_elem(combinator, elem, source)?;
        }
        Some(IntConstraint::Set(constraints)) => {
            for constraint in constraints {
                check_constraint_elem(combinator, constraint, source)?;
            }
        }
        // constraints
        //     .iter()
        //     .for_each(|constraint| check_constraint_int_combinator(combinator, Some(constraint))),
        Some(IntConstraint::Neg(constraint)) => {
            check_constraint_int_combinator(combinator, Some(constraint), source)?;
        }
        None => {}
    }
    Ok(())
}

fn check_constraint_enum_combinator<'ast>(
    combinator: &CombinatorInvocation<'ast>,
    constraint: &EnumConstraint<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    span: &Span,
    source: (&str, &Source),
) -> Result<(), VestError> {
    // First ensure the invocation is well-formed
    check_combinator_invocation(combinator, param_defns, local_ctx, global_ctx, source)?;
    // Resolve the invocation target
    let resolved = global_ctx
        .combinators
        .iter()
        .find(|sig| sig.name == combinator.func)
        .map(|sig| &sig.resolved_combinator);
    match resolved {
        Some(CombinatorInner::Enum(enum_comb)) => {
            check_enum_constraint(enum_comb, constraint, span, source)
        }
        Some(other) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("type mismatch")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("Enum constraint applied to a non-enum type")
                        .with_color(Color::Red),
                )
                .with_label(
                    Label::new((source.0, span_as_range(&other.as_span())))
                        .with_message("This is the resolved type")
                        .with_color(Color::Yellow),
                )
                .finish()
                .eprint(source)
                .unwrap();
            Err(VestError::TypeError)
        }
        None => {
            Report::build(
                ReportKind::Error,
                (source.0, span_as_range(&combinator.span)),
            )
            .with_message("undefined format")
            .with_label(
                Label::new((source.0, span_as_range(&combinator.span)))
                    .with_message(format!("Format `{}` is not defined", combinator.func))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(source)
            .unwrap();
            Err(VestError::TypeError)
        }
    }
}

fn check_enum_constraint<'ast>(
    enum_comb: &EnumCombinator<'ast>,
    constraint: &'ast EnumConstraint<'ast>,
    span: &Span,
    source: (&str, &Source),
) -> Result<(), VestError> {
    let variants = match enum_comb {
        EnumCombinator::Exhaustive { enums, .. } | EnumCombinator::NonExhaustive { enums, .. } => {
            enums
        }
    };
    let report_missing_variant = |ident: &Identifier<'ast>| {
        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
            .with_message("undefined enum variant in constraint")
            .with_label(
                Label::new((source.0, span_as_range(&ident.span)))
                    .with_message(format!("`{}` is not a variant of this enum", ident))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(source)
            .unwrap();
    };
    fn collect_variants<'a>(c: &'a EnumConstraint<'a>, out: &mut Vec<&'a Identifier<'a>>) {
        match c {
            EnumConstraint::Single { elem, .. } => out.push(elem),
            EnumConstraint::Set(vs) => out.extend(vs.iter()),
            EnumConstraint::Neg(inner) => collect_variants(inner, out),
        }
    }
    let mut elems = Vec::new();
    collect_variants(constraint, &mut elems);
    // membership check
    for ident in elems {
        if !variants.iter().any(|Enum { name, .. }| name == ident) {
            report_missing_variant(ident);
            return Err(VestError::TypeError);
        }
    }
    // duplicate check for sets
    if let EnumConstraint::Set(vs) = constraint {
        let mut seen = HashSet::new();
        for ident in vs {
            if !seen.insert(&ident.name) {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("duplicate enum variant in constraint")
                    .with_label(
                        Label::new((source.0, span_as_range(&ident.span)))
                            .with_message(format!("Duplicate variant `{}`", ident.name))
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        }
    }
    Ok(())
}

fn check_constraint_elem(
    combinator: &IntCombinator,
    constraint_elem: &ConstraintElem,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match constraint_elem {
        ConstraintElem::Range { start, end, span } => match (start, end) {
            (Some(start), Some(end)) => {
                check_const_int_combinator(combinator, start, span, source)?;
                check_const_int_combinator(combinator, end, span, source)?;
                if start > end {
                    Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                        .with_message("invalid range constraint")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "Start value {} is greater than end value {}",
                                    start, end
                                ))
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
            }
            (Some(start), None) => {
                check_const_int_combinator(combinator, start, span, source)?;
            }
            (None, Some(end)) => {
                check_const_int_combinator(combinator, end, span, source)?;
            }
            _ => {
                Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                    .with_message("invalid range constraint")
                    .with_label(
                        Label::new((source.0, span_as_range(span)))
                            .with_message("Range must have at least one bound")
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(source)
                    .unwrap();
                return Err(VestError::TypeError);
            }
        },
        ConstraintElem::Single { elem, span } => {
            check_const_int_combinator(combinator, elem, span, source)?;
        }
    }
    Ok(())
}
