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
            let ParamDefn::Dependent { span, .. } = param;
            start = start.min(span.start());
            end = end.max(span.end());
        }
        Span::new(input, start, end).expect("combinator signature span should be valid")
    }
}

impl<'ast> GlobalCtx<'ast> {
    // TODO: return `Result`
    pub fn resolve<'a>(&'a self, combinator: &'a Combinator<'ast>) -> &'a CombinatorInner<'ast> {
        if let Some(and_then) = &combinator.and_then {
            self.resolve(and_then)
        } else {
            self.resolve_alias(&combinator.inner)
        }
    }
    // TODO: return `Result` instead of panic
    pub fn resolve_alias<'a>(
        &'a self,
        combinator: &'a CombinatorInner<'ast>,
    ) -> &'a CombinatorInner<'ast> {
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
            Vec(..) | Tail(..) | Option(..) => None,
            Array(ArrayCombinator {
                combinator, len, ..
            }) => {
                let elem_size = self.combinator_size(combinator)?;
                let len = self.length_expr_size(len)?;
                elem_size.checked_mul(len)
            }
            Bytes(BytesCombinator { len, .. }) => self.length_expr_size(len),
            Invocation(CombinatorInvocation { func, .. }) => self.format_size(&func.name),
            MacroInvocation { .. } => unreachable!("macro invocation should be resolved by now"),
            Bits(bits_comb) => {
                let mut total_width = 0usize;
                for field in &bits_comb.fields {
                    let w = bit_field_combinator_width(field.combinator(), &self.formats)?;
                    total_width = total_width.checked_add(w)?;
                }
                if total_width % 8 == 0 {
                    Some(total_width / 8)
                } else {
                    None
                }
            }
        }
    }

    fn const_combinator_size(&mut self, combinator: &ConstCombinator<'ast>) -> Option<usize> {
        use ConstCombinator::*;

        match combinator {
            ConstBytes(ConstBytesCombinator { len, .. }) => Some(*len),
            ConstInt(ConstIntCombinator { combinator, .. }) => {
                int_combinator_static_size(combinator)
            }
            ConstEnum(ConstEnumCombinator { combinator, .. }) => {
                self.format_size(&combinator.func.name)
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

fn report_undefined_format_name(name: &Identifier, source: (&str, &Source)) -> VestError {
    Report::build(ReportKind::Error, (source.0, span_as_range(&name.span)))
        .with_message("undefined format")
        .with_label(
            Label::new((source.0, span_as_range(&name.span)))
                .with_message(format!("Format `{}` is not defined", name))
                .with_color(Color::Red),
        )
        .finish()
        .eprint(source)
        .unwrap();
    VestError::TypeError
}

fn report_undefined_const_format_name(name: &Identifier, source: (&str, &Source)) -> VestError {
    Report::build(ReportKind::Error, (source.0, span_as_range(&name.span)))
        .with_message("undefined const format")
        .with_label(
            Label::new((source.0, span_as_range(&name.span)))
                .with_message(format!("Const format `{}` is not defined", name))
                .with_color(Color::Red),
        )
        .finish()
        .eprint(source)
        .unwrap();
    VestError::TypeError
}

fn report_alias_cycle(name: &Identifier, source: (&str, &Source)) -> VestError {
    Report::build(ReportKind::Error, (source.0, span_as_range(&name.span)))
        .with_message("cyclic format alias")
        .with_label(
            Label::new((source.0, span_as_range(&name.span)))
                .with_message(format!(
                    "Format `{}` is defined as a cyclic alias, which has no concrete type",
                    name
                ))
                .with_color(Color::Red),
        )
        .finish()
        .eprint(source)
        .unwrap();
    VestError::TypeError
}

/// Resolve a combinator to its head-normal-form [`CombinatorInner`] by following
/// `>>=` to its final result type and following invocation aliases, using a
/// *complete* map of every definition in the file.
///
/// Because it resolves against the full set of definitions rather than whatever
/// has been processed so far, the result is independent of the order in which
/// definitions appear. Undefined invocations and cyclic aliases produce a proper
/// type error instead of panicking.
fn resolve_combinator_to_inner<'ast>(
    combinator: &'ast Combinator<'ast>,
    raw: &HashMap<&str, &'ast Combinator<'ast>>,
    source: (&str, &Source),
    visiting: &mut Vec<&'ast str>,
) -> Result<CombinatorInner<'ast>, VestError> {
    if let Some(and_then) = &combinator.and_then {
        return resolve_combinator_to_inner(and_then, raw, source, visiting);
    }
    match &combinator.inner {
        CombinatorInner::Invocation(CombinatorInvocation { func, .. }) => {
            let Some(&target) = raw.get(func.name.as_str()) else {
                return Err(report_undefined_format_name(func, source));
            };
            if visiting.contains(&func.name.as_str()) {
                return Err(report_alias_cycle(func, source));
            }
            visiting.push(func.name.as_str());
            let resolved = resolve_combinator_to_inner(target, raw, source, visiting)?;
            visiting.pop();
            Ok(resolved)
        }
        other => Ok(other.clone()),
    }
}

/// Const-format analogue of [`resolve_combinator_to_inner`].
fn resolve_const_to_inner<'ast>(
    const_combinator: &'ast ConstCombinator<'ast>,
    raw: &HashMap<&str, &'ast ConstCombinator<'ast>>,
    source: (&str, &Source),
    visiting: &mut Vec<&'ast str>,
) -> Result<ConstCombinator<'ast>, VestError> {
    match const_combinator {
        ConstCombinator::ConstCombinatorInvocation { name, .. } => {
            let Some(&target) = raw.get(name.name.as_str()) else {
                return Err(report_undefined_const_format_name(name, source));
            };
            if visiting.contains(&name.name.as_str()) {
                return Err(report_alias_cycle(name, source));
            }
            visiting.push(name.name.as_str());
            let resolved = resolve_const_to_inner(target, raw, source, visiting)?;
            visiting.pop();
            Ok(resolved)
        }
        other => Ok(other.clone()),
    }
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

    // Collect every definition up front so that alias resolution can look up any
    // referenced format regardless of the order definitions appear in. This is
    // what lets the rest of the pipeline drop the topological pre-sort.
    let mut raw_combinators: HashMap<&str, &Combinator> = HashMap::new();
    let mut raw_consts: HashMap<&str, &ConstCombinator> = HashMap::new();
    for defn in ast {
        match defn {
            Definition::Combinator {
                name, combinator, ..
            } => {
                raw_combinators.insert(name.name.as_str(), combinator);
            }
            Definition::ConstCombinator {
                name,
                const_combinator,
                ..
            } => {
                raw_consts.insert(name.name.as_str(), const_combinator);
            }
            _ => {}
        }
    }

    let mut local_ctx = LocalCtx::new();
    for defn in ast {
        match defn {
            Definition::Combinator {
                name,
                param_defns,

                combinator,
                span,
            } => {
                // Resolve combinator invocations (aliases) and `and_then`s against
                // the complete definition set, so this no longer depends on order.
                let resolved_combinator =
                    resolve_combinator_to_inner(combinator, &raw_combinators, source, &mut Vec::new())?;

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
                // resolve the const combinator against the complete definition set
                let resolved_combinator =
                    resolve_const_to_inner(const_combinator, &raw_consts, source, &mut Vec::new())?;

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
        } => {
            for param in param_defns {
                let ParamDefn::Dependent { combinator: param_comb, .. } = param;
                let mut dummy_local_ctx = LocalCtx::new();
                check_combinator_inner(param_comb, &[], &mut dummy_local_ctx, global_ctx, source)?;
            }
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
        }
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
        ConstBytes(combinator) => check_const_bytes_combinator(combinator, source),
        ConstCombinatorInvocation { name, span } => {
            check_const_combinator_invocation(name, *span, local_ctx, global_ctx, source)
        }
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

fn check_const_enum_combinator<'ast>(
    combinator: &CombinatorInvocation<'ast>,
    variant: &Identifier<'ast>,
    span: &Span,
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<(), VestError> {
    // Reuse combinator invocation checks (no params allowed unless in scope)
    check_combinator_invocation(combinator, &[], local_ctx, global_ctx, source, false)?;
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
        IntCombinator::Signed(n) => {
            let n = *n;
            let min_val = if n >= 128 {
                i128::MIN
            } else {
                -(1i128 << (n - 1))
            };
            let max_val = if n >= 128 {
                i128::MAX
            } else {
                (1i128 << (n - 1)) - 1
            };
            if *value < min_val || *value > max_val {
                report_const_int_error!(format!(
                    "Value {} is out of range for i{} (expected {} to {})",
                    value, n, min_val, max_val
                ));
                return Err(VestError::TypeError);
            }
        }
        IntCombinator::Unsigned(n) => {
            let n = *n;
            let max_val = if n >= 128 {
                i128::MAX
            } else {
                (1i128 << n) - 1
            };
            if *value < 0 || *value > max_val {
                report_const_int_error!(format!(
                    "Value {} is out of range for u{} (expected 0 to {})",
                    value, n, max_val
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
        Vec(VecCombinator::Vec(combinator)) => {
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
        Option(OptionCombinator(combinator)) => {
            check_combinator(combinator, param_defns, local_ctx, global_ctx, source)
        }
        Invocation(combinator) => {
            check_combinator_invocation(combinator, param_defns, local_ctx, global_ctx, source, false)
        }
        MacroInvocation { .. } => unreachable!("macro invocation should be resolved by now"),
        Bits(bits_comb) => check_bits_combinator(
            bits_comb,
            &bits_comb.span,
            param_defns,
            local_ctx,
            global_ctx,
            source,
        ),
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
    is_in_bits: bool,
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
            if !is_in_bits {
                if let CombinatorInner::Enum(enum_comb) = &combinator_sig.resolved_combinator {
                    let enums = match enum_comb {
                        EnumCombinator::Exhaustive { enums, .. }
                        | EnumCombinator::NonExhaustive { enums, .. } => enums,
                    };
                    let inferred = resolve_enum_type(enums);
                    let is_byte_aligned = match inferred {
                        IntCombinator::Signed(bits) | IntCombinator::Unsigned(bits) => bits % 8 == 0,
                        IntCombinator::BtcVarint | IntCombinator::ULEB128 => true,
                    };
                    if !is_byte_aligned {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("bit-sized enum used outside of bitfield")
                            .with_label(
                                Label::new((source.0, span_as_range(span)))
                                    .with_message("bit-sized enums may only be used inside bits members")
                                    .with_color(Color::Red),
                            )
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                }
            }
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
                    (Param::Dependent(depend_id), ParamDefn::Dependent { combinator, .. }) => {
                        let arg_combinator = resolve_dependent_identifier(
                            depend_id,
                            param_defns,
                            local_ctx,
                            global_ctx,
                            source,
                        )?;
                        let expected = global_ctx.resolve_alias(combinator);
                        if !combinator_types_compatible(&arg_combinator, expected, global_ctx) {
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
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                    }
                }
            }
        }
    }
    Ok(())
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

#[derive(Debug, Clone)]
enum ResolveError {
    UnboundField(String),
    NotDependentField { field_name: String },
    NotDefinedInBitfield { field_name: String },
    BitfieldMembersNoNested,
    NestedRequiresStructOrBits,
    CannotResolveType(String),
}

fn emit_resolve_error(err: ResolveError, span: &Span, source: (&str, &Source)) -> VestError {
    match err {
        ResolveError::UnboundField(root_id) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("unbound field")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!("`@{}` is not found in current scope", root_id))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
        ResolveError::NotDependentField { field_name } => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid nested field access")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!("field `{}` is not a dependent field", field_name))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
        ResolveError::NotDefinedInBitfield { field_name } => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid nested field access")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!(
                            "field `{}` is not defined in the bitfield",
                            field_name
                        ))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
        ResolveError::BitfieldMembersNoNested => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid nested field access")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("bitfield members do not have nested fields")
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
        ResolveError::NestedRequiresStructOrBits => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("invalid nested field access")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("nested field access requires a struct or bits type")
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
        ResolveError::CannotResolveType(func_name) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("cannot resolve type for nested access")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message(format!("cannot resolve type of `{}`", func_name))
                        .with_color(Color::Red),
                )
                .finish()
                .eprint(source)
                .unwrap();
        }
    }
    VestError::TypeError
}

fn resolve_root<'ast>(
    root_id: &str,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) -> Result<CombinatorInner<'ast>, ResolveError> {
    if let Some(combinator) = local_ctx
        .dependent_fields
        .iter()
        .find(|(id, _)| id.name == root_id)
        .map(|(_, comb)| comb)
    {
        Ok(global_ctx.resolve(combinator).clone())
    } else {
        let param_defn = param_defns
            .iter()
            .find(|param_defn| matches!(param_defn, ParamDefn::Dependent { name, .. } if name.name == root_id));

        match param_defn {
            Some(ParamDefn::Dependent { combinator, .. }) => {
                Ok(global_ctx.resolve_alias(combinator).clone())
            }
            _ => Err(ResolveError::UnboundField(root_id.to_string())),
        }
    }
}

fn resolve_path<'ast>(
    root_combinator: CombinatorInner<'ast>,
    path: &[&str],
    global_ctx: &'ast GlobalCtx<'ast>,
) -> Result<CombinatorInner<'ast>, ResolveError> {
    let mut current_combinator = root_combinator;
    for (i, field_name) in path.iter().enumerate() {
        match current_combinator {
            CombinatorInner::Struct(struct_comb) => {
                let field = struct_comb.fields.iter().find(|f| match f {
                    StructField::Dependent { label, .. } | StructField::Ordinary { label, .. } => {
                        label.name == **field_name
                    }
                    _ => false,
                });
                match field {
                    Some(StructField::Dependent { combinator, .. })
                    | Some(StructField::Ordinary { combinator, .. }) => {
                        current_combinator = global_ctx.resolve(combinator).clone();
                    }
                    _ => {
                        return Err(ResolveError::NotDependentField {
                            field_name: field_name.to_string(),
                        });
                    }
                }
            }
            CombinatorInner::Bits(bits_comb) => {
                let field = bits_comb.fields.iter().find(|f| match f {
                    BitField::Dependent { label, .. } | BitField::Ordinary { label, .. } => {
                        label.name == **field_name
                    }
                });
                match field {
                    Some(BitField::Dependent { combinator, .. })
                    | Some(BitField::Ordinary { combinator, .. }) => {
                        if i == path.len() - 1 {
                            current_combinator = match combinator {
                                BitFieldCombinator::UInt {
                                    width,
                                    constraint,
                                    span,
                                } => CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                                    combinator: IntCombinator::Unsigned(*width),
                                    constraint: constraint.clone(),
                                    span: *span,
                                }),
                                BitFieldCombinator::Invocation(inv) => {
                                    let sig = global_ctx
                                        .combinators
                                        .iter()
                                        .find(|sig| sig.name == inv.func);
                                    if let Some(sig) = sig {
                                        sig.resolved_combinator.clone()
                                    } else {
                                        CombinatorInner::Invocation(inv.clone())
                                    }
                                }
                            };
                        } else {
                            return Err(ResolveError::BitfieldMembersNoNested);
                        }
                    }
                    None => {
                        return Err(ResolveError::NotDefinedInBitfield {
                            field_name: field_name.to_string(),
                        });
                    }
                }
            }
            CombinatorInner::Invocation(inv) => {
                let sig = global_ctx
                    .combinators
                    .iter()
                    .find(|sig| sig.name == inv.func);
                if let Some(sig) = sig {
                    current_combinator = sig.resolved_combinator.clone();
                    return resolve_path(current_combinator, &path[i..], global_ctx);
                } else {
                    return Err(ResolveError::CannotResolveType(inv.func.name.clone()));
                }
            }
            _ => {
                return Err(ResolveError::NestedRequiresStructOrBits);
            }
        }
    }
    Ok(current_combinator)
}

fn resolve_dependent_id_path<'ast>(
    root_id: &str,
    path: &[&str],
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) -> Result<CombinatorInner<'ast>, ResolveError> {
    let root_comb = resolve_root(root_id, param_defns, local_ctx, global_ctx)?;
    resolve_path(root_comb, path, global_ctx)
}

fn resolve_dependent_identifier<'a, 'ast>(
    depend_id: &'a Identifier<'ast>,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
    source: (&str, &Source),
) -> Result<CombinatorInner<'ast>, VestError> {
    let parts: Vec<&str> = depend_id.name.split('.').collect();
    let root_id = parts[0];
    let path = &parts[1..];
    match resolve_dependent_id_path(root_id, path, param_defns, local_ctx, global_ctx) {
        Ok(comb) => Ok(comb),
        Err(err) => Err(emit_resolve_error(err, &depend_id.span, source)),
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
    let root_id = depend_id.root.as_str();
    let path: Vec<&str> = depend_id.path.iter().map(|s| s.as_str()).collect();
    match resolve_dependent_id_path(root_id, &path, param_defns, local_ctx, global_ctx) {
        Ok(comb) => {
            check_combinator_is_unsigned_int(&comb, &depend_id.full_path(), span, span, source)
        }
        Err(err) => Err(emit_resolve_error(err, span, source)),
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

fn int_combinator_bounds(combinator: &IntCombinator) -> Option<(i128, i128)> {
    match combinator {
        IntCombinator::Signed(8) => Some((i8::MIN as i128, i8::MAX as i128)),
        IntCombinator::Signed(16) => Some((i16::MIN as i128, i16::MAX as i128)),
        IntCombinator::Signed(32) => Some((i32::MIN as i128, i32::MAX as i128)),
        IntCombinator::Signed(64) => Some((i64::MIN as i128, i64::MAX as i128)),
        IntCombinator::Unsigned(8) => Some((u8::MIN as i128, u8::MAX as i128)),
        IntCombinator::Unsigned(16) => Some((u16::MIN as i128, u16::MAX as i128)),
        IntCombinator::Unsigned(24) => Some((0, 0xFF_FFFF)),
        IntCombinator::Unsigned(32) => Some((u32::MIN as i128, u32::MAX as i128)),
        IntCombinator::Unsigned(64) | IntCombinator::BtcVarint | IntCombinator::ULEB128 => {
            Some((0, u64::MAX as i128))
        }
        _ => None,
    }
}

fn normalize_intervals(mut intervals: Vec<(i128, i128)>) -> Vec<(i128, i128)> {
    if intervals.is_empty() {
        return intervals;
    }
    intervals.sort_unstable_by_key(|(start, end)| (*start, *end));
    let mut merged: Vec<(i128, i128)> = Vec::with_capacity(intervals.len());
    for (start, end) in intervals {
        if let Some((_, last_end)) = merged.last_mut() {
            if start <= *last_end + 1 {
                *last_end = (*last_end).max(end);
                continue;
            }
        }
        merged.push((start, end));
    }
    merged
}

fn complement_intervals(domain: (i128, i128), intervals: &[(i128, i128)]) -> Vec<(i128, i128)> {
    let (domain_start, domain_end) = domain;
    let mut out = Vec::new();
    let mut cursor = domain_start;
    for (start, end) in intervals.iter().copied() {
        if cursor < start {
            out.push((cursor, start - 1));
        }
        cursor = end.saturating_add(1);
        if cursor > domain_end {
            break;
        }
    }
    if cursor <= domain_end {
        out.push((cursor, domain_end));
    }
    out
}

fn constraint_elem_intervals(elem: &ConstraintElem<'_>, domain: (i128, i128)) -> Vec<(i128, i128)> {
    let (domain_start, domain_end) = domain;
    let interval = match elem {
        ConstraintElem::Range { start, end, .. } => {
            (start.unwrap_or(domain_start), end.unwrap_or(domain_end))
        }
        ConstraintElem::Single { elem, .. } => (*elem, *elem),
    };
    let start = interval.0.max(domain_start);
    let end = interval.1.min(domain_end);
    if start <= end {
        vec![(start, end)]
    } else {
        vec![]
    }
}

fn int_constraint_intervals(
    combinator: &IntCombinator,
    constraint: Option<&IntConstraint<'_>>,
) -> Option<Vec<(i128, i128)>> {
    let domain = int_combinator_bounds(combinator)?;
    let intervals = match constraint {
        None => vec![domain],
        Some(IntConstraint::Single { elem, .. }) => constraint_elem_intervals(elem, domain),
        Some(IntConstraint::Set(elems)) => elems
            .iter()
            .flat_map(|elem| constraint_elem_intervals(elem, domain))
            .collect(),
        Some(IntConstraint::Neg(inner)) => {
            let inner = int_constraint_intervals(combinator, Some(inner.as_ref()))?;
            complement_intervals(domain, &inner)
        }
    };
    Some(normalize_intervals(intervals))
}

fn int_constraint_is_subset(
    combinator: &IntCombinator,
    arg: Option<&IntConstraint<'_>>,
    expected: Option<&IntConstraint<'_>>,
) -> bool {
    let Some(arg_intervals) = int_constraint_intervals(combinator, arg) else {
        return arg == expected;
    };
    let Some(expected_intervals) = int_constraint_intervals(combinator, expected) else {
        return arg == expected;
    };

    let mut j = 0usize;
    for (a_start, a_end) in arg_intervals {
        while j < expected_intervals.len() && expected_intervals[j].1 < a_start {
            j += 1;
        }
        if j == expected_intervals.len() {
            return false;
        }
        let (e_start, e_end) = expected_intervals[j];
        if e_start > a_start || e_end < a_end {
            return false;
        }
    }
    true
}

fn enum_variants<'ast>(enum_comb: &EnumCombinator<'ast>) -> HashSet<String> {
    match enum_comb {
        EnumCombinator::Exhaustive { enums, .. } | EnumCombinator::NonExhaustive { enums, .. } => {
            enums.iter().map(|e| e.name.name.clone()).collect()
        }
    }
}

fn enum_constraint_variants<'ast>(
    enum_comb: &EnumCombinator<'ast>,
    constraint: Option<&EnumConstraint<'ast>>,
) -> HashSet<String> {
    let universe = enum_variants(enum_comb);
    match constraint {
        None => universe,
        Some(EnumConstraint::Single { elem, .. }) => HashSet::from([elem.name.clone()]),
        Some(EnumConstraint::Set(vs)) => vs.iter().map(|v| v.name.clone()).collect(),
        Some(EnumConstraint::Neg(inner)) => {
            let inner = enum_constraint_variants(enum_comb, Some(inner.as_ref()));
            universe.difference(&inner).cloned().collect()
        }
    }
}

fn resolve_constraint_enum_target<'ast>(
    combinator: &ConstraintEnumCombinator<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) -> Option<&'ast EnumCombinator<'ast>> {
    global_ctx
        .combinators
        .iter()
        .find(|sig| sig.name == combinator.combinator.func)
        .and_then(|sig| match &sig.resolved_combinator {
            CombinatorInner::Enum(enum_comb) => Some(enum_comb),
            _ => None,
        })
}

fn combinator_types_compatible<'ast>(
    arg: &CombinatorInner<'ast>,
    expected: &CombinatorInner<'ast>,
    global_ctx: &'ast GlobalCtx<'ast>,
) -> bool {
    if arg == expected {
        return true;
    }
    match (arg, expected) {
        (
            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                combinator: arg_comb,
                constraint: arg_constraint,
                ..
            }),
            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                combinator: expected_comb,
                constraint: expected_constraint,
                ..
            }),
        ) => {
            arg_comb == expected_comb
                && int_constraint_is_subset(
                    arg_comb,
                    arg_constraint.as_ref(),
                    expected_constraint.as_ref(),
                )
        }
        (CombinatorInner::Enum(arg_enum), CombinatorInner::Enum(expected_enum)) => {
            arg_enum == expected_enum
        }
        (CombinatorInner::ConstraintEnum(arg_ce), CombinatorInner::Enum(expected_enum)) => {
            resolve_constraint_enum_target(arg_ce, global_ctx)
                .is_some_and(|arg_enum| arg_enum == expected_enum)
        }
        (CombinatorInner::ConstraintEnum(arg_ce), CombinatorInner::ConstraintEnum(expected_ce)) => {
            match (
                resolve_constraint_enum_target(arg_ce, global_ctx),
                resolve_constraint_enum_target(expected_ce, global_ctx),
            ) {
                (Some(arg_enum), Some(expected_enum)) if arg_enum == expected_enum => {
                    let arg_set = enum_constraint_variants(arg_enum, Some(&arg_ce.constraint));
                    let expected_set =
                        enum_constraint_variants(expected_enum, Some(&expected_ce.constraint));
                    arg_set.is_subset(&expected_set)
                }
                _ => false,
            }
        }
        _ => false,
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
    fn report_missing_wildcard<'ast>(
        span: &Span,
        source: (&str, &Source),
        kind: &str,
    ) -> VestError {
        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
            .with_message("non-exhaustive dependent choice")
            .with_label(
                Label::new((source.0, span_as_range(span)))
                    .with_message(format!(
                        "Dependent {} choices must include a wildcard `_` branch",
                        kind
                    ))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(source)
            .unwrap();
        VestError::TypeError
    }

    fn report_invalid_wildcard_position<'ast>(
        wildcard_span: &Span,
        span: &Span,
        source: (&str, &Source),
    ) -> VestError {
        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
            .with_message("invalid wildcard branch")
            .with_label(
                Label::new((source.0, span_as_range(wildcard_span)))
                    .with_message("Wildcard `_` must appear as the last branch")
                    .with_color(Color::Red),
            )
            .with_label(
                Label::new((source.0, span_as_range(span)))
                    .with_message("This dependent choice is matched top-to-bottom")
                    .with_color(Color::Yellow),
            )
            .finish()
            .eprint(source)
            .unwrap();
        VestError::TypeError
    }

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
                let combinator = resolve_dependent_identifier(
                    depend_id,
                    param_defns,
                    local_ctx,
                    global_ctx,
                    source,
                )?;
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
                    let wildcard_count = enums
                        .iter()
                        .filter(|(variant, _)| variant.name == "_")
                        .count();
                    if wildcard_count > 1 {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("duplicate wildcard branch")
                            .with_labels(enums.iter().filter(|(label, _)| label.name == "_").map(
                                |(label, _)| {
                                    Label::new((source.0, span_as_range(&label.span)))
                                        .with_color(Color::Yellow)
                                },
                            ))
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                    if let Some((idx, (variant, _))) = enums
                        .iter()
                        .enumerate()
                        .find(|(_, (variant, _))| variant.name == "_")
                    {
                        if idx + 1 != enums.len() {
                            return Err(report_invalid_wildcard_position(
                                &variant.span,
                                span,
                                source,
                            ));
                        }
                    }
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
                    } else if wildcard_count == 0 {
                        return Err(report_missing_wildcard(span, source, "enum"));
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
                let combinator = resolve_dependent_identifier(
                    depend_id,
                    param_defns,
                    local_ctx,
                    global_ctx,
                    source,
                )?;
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
                let wildcard_positions = ints
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, (pattern, _))| pattern.is_none().then_some(idx))
                    .collect::<Vec<_>>();
                match wildcard_positions.as_slice() {
                    [] => return Err(report_missing_wildcard(span, source, "int")),
                    [idx] if *idx + 1 == ints.len() => {}
                    [idx] => {
                        let wildcard_span = ints[*idx].1.span;
                        return Err(report_invalid_wildcard_position(
                            &wildcard_span,
                            span,
                            source,
                        ));
                    }
                    _ => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("duplicate wildcard branch")
                            .with_labels(wildcard_positions.iter().map(|idx| {
                                Label::new((source.0, span_as_range(&ints[*idx].1.span)))
                                    .with_color(Color::Yellow)
                            }))
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                }
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
                let combinator = resolve_dependent_identifier(
                    depend_id,
                    param_defns,
                    local_ctx,
                    global_ctx,
                    source,
                )?;
                let combinator = combinator.clone();
                check_combinator_inner(&combinator, param_defns, local_ctx, global_ctx, source)?;
                let combinator = global_ctx.resolve_alias(&combinator);
                let wildcard_positions = arrays
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, (pattern, _))| {
                        matches!(pattern, ConstArray::Wildcard).then_some(idx)
                    })
                    .collect::<Vec<_>>();
                match wildcard_positions.as_slice() {
                    [] => return Err(report_missing_wildcard(span, source, "array")),
                    [idx] if *idx + 1 == arrays.len() => {}
                    [idx] => {
                        let wildcard_span = arrays[*idx].0.as_span();
                        return Err(report_invalid_wildcard_position(
                            &wildcard_span,
                            span,
                            source,
                        ));
                    }
                    _ => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                            .with_message("duplicate wildcard branch")
                            .with_labels(wildcard_positions.iter().map(|idx| {
                                Label::new((source.0, span_as_range(&arrays[*idx].0.as_span())))
                                    .with_color(Color::Yellow)
                            }))
                            .finish()
                            .eprint(source)
                            .unwrap();
                        return Err(VestError::TypeError);
                    }
                }
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

fn bit_field_combinator_width(
    bfc: &BitFieldCombinator<'_>,
    formats: &HashMap<&str, &Combinator<'_>>,
) -> Option<usize> {
    match bfc {
        BitFieldCombinator::UInt { width, .. } => Some(*width as usize),
        BitFieldCombinator::Invocation(inv) => {
            let comb = formats.get(inv.func.name.as_str())?;
            match &comb.inner {
                CombinatorInner::Enum(enum_comb) => {
                    let enums = match enum_comb {
                        EnumCombinator::Exhaustive { enums, .. }
                        | EnumCombinator::NonExhaustive { enums, .. } => enums,
                    };
                    let backing = resolve_enum_type(enums);
                    Some(backing.logical_width() as usize)
                }
                _ => None,
            }
        }
    }
}

fn check_bits_combinator<'ast>(
    bits_comb: &BitsCombinator<'ast>,
    span: &Span,
    param_defns: &'ast [ParamDefn<'ast>],
    local_ctx: &mut LocalCtx<'ast>,
    global_ctx: &'ast GlobalCtx,
    source: (&str, &Source),
) -> Result<(), VestError> {
    macro_rules! report_duplicate_field {
        ($label:expr, $field_span:expr) => {
            Report::build(ReportKind::Error, (source.0, span_as_range(span)))
                .with_message("duplicate field name in bitfield")
                .with_label(
                    Label::new((source.0, span_as_range(span)))
                        .with_message("Invalid bits format")
                        .with_color(Color::Red),
                )
                .with_label(
                    Label::new((source.0, span_as_range($field_span)))
                        .with_message(format!("Duplicate field name `{}`", $label))
                        .with_color(Color::Yellow),
                )
                .finish()
                .eprint(source)
                .unwrap();
        };
    }

    let mut total_bits = 0usize;

    for field in &bits_comb.fields {
        let label = field.label();
        let combinator = field.combinator();
        let field_span = match field {
            BitField::Dependent { span, .. } | BitField::Ordinary { span, .. } => span,
        };

        if let BitField::Dependent { .. } = field {
            if !local_ctx.dependent_fields.contains_key(label) {
                local_ctx
                    .dependent_fields
                    .insert(label.to_owned(), combinator.as_combinator());
            } else {
                report_duplicate_field!(label, field_span);
                return Err(VestError::TypeError);
            }
        }

        if !local_ctx.struct_fields.insert(label.to_owned()) {
            report_duplicate_field!(label, field_span);
            return Err(VestError::TypeError);
        }

        match combinator {
            BitFieldCombinator::UInt {
                width,
                constraint,
                span: _,
            } => {
                if *width == 0 || *width > 64 {
                    Report::build(ReportKind::Error, (source.0, span_as_range(field_span)))
                        .with_message("invalid bitfield width")
                        .with_label(
                            Label::new((source.0, span_as_range(field_span)))
                                .with_message(format!(
                                    "width must be between 1 and 64, got {}",
                                    width
                                ))
                                .with_color(Color::Red),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                    return Err(VestError::TypeError);
                }
                total_bits = total_bits
                    .checked_add(*width as usize)
                    .ok_or(VestError::TypeError)?;

                if let Some(c) = constraint {
                    let int_comb = IntCombinator::Unsigned(*width);
                    check_constraint_int_combinator(&int_comb, Some(c), source)?;
                }
            }
            BitFieldCombinator::Invocation(inv) => {
                check_combinator_invocation(inv, param_defns, local_ctx, global_ctx, source, true)?;
                let resolved = global_ctx
                    .combinators
                    .iter()
                    .find(|sig| sig.name == inv.func)
                    .map(|sig| &sig.resolved_combinator);
                match resolved {
                    Some(CombinatorInner::Enum(enum_comb)) => {
                        let enums = match enum_comb {
                            EnumCombinator::Exhaustive { enums, .. }
                            | EnumCombinator::NonExhaustive { enums, .. } => enums,
                        };
                        let backing = resolve_enum_type(enums);
                        if !matches!(backing, IntCombinator::Unsigned(_)) {
                            Report::build(ReportKind::Error, (source.0, span_as_range(field_span)))
                                .with_message("invalid bitfield member")
                                .with_label(
                                    Label::new((source.0, span_as_range(field_span)))
                                        .with_message("bitfield enum must have an unsigned backing type")
                                        .with_color(Color::Red),
                                )
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                        let w = backing.logical_width() as usize;
                        if w == 0 || w > 64 {
                            Report::build(ReportKind::Error, (source.0, span_as_range(field_span)))
                                .with_message("invalid bitfield width for enum")
                                .with_label(
                                    Label::new((source.0, span_as_range(field_span)))
                                        .with_message(format!(
                                            "width must be between 1 and 64, got {}",
                                            w
                                        ))
                                        .with_color(Color::Red),
                                )
                                .finish()
                                .eprint(source)
                                .unwrap();
                            return Err(VestError::TypeError);
                        }
                        total_bits = total_bits.checked_add(w).ok_or(VestError::TypeError)?;
                    }
                    _ => {
                        Report::build(ReportKind::Error, (source.0, span_as_range(field_span)))
                            .with_message("invalid bitfield member")
                            .with_label(
                                Label::new((source.0, span_as_range(field_span)))
                                    .with_message("bitfield invocation must resolve to an enum")
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
    }

    if total_bits != 8
        && total_bits != 16
        && total_bits != 24
        && total_bits != 32
        && total_bits != 64
    {
        Report::build(ReportKind::Error, (source.0, span_as_range(span)))
            .with_message("invalid bitfield total width")
            .with_label(
                Label::new((source.0, span_as_range(span)))
                    .with_message(format!(
                        "total bits width must be 8, 16, 24, 32, or 64, got {} bits",
                        total_bits
                    ))
                    .with_color(Color::Red),
            )
            .finish()
            .eprint(source)
            .unwrap();
        return Err(VestError::TypeError);
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
    check_combinator_invocation(combinator, param_defns, local_ctx, global_ctx, source, false)?;
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
