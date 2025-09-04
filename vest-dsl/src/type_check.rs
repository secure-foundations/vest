use crate::ast::*;
use crate::VestError;
use core::panic;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::format;
use std::iter::zip;

use ariadne::{Color, ColorGenerator, Fmt, Label, Report, ReportKind, Source};
use pest::Span;

#[derive(Debug, Clone)]
pub struct GlobalCtx<'ast> {
    pub combinators: HashSet<CombinatorSig<'ast>>,
    pub const_combinators: HashSet<ConstCombinatorSig<'ast>>,
    pub enums: HashMap<&'ast str, EnumCombinator<'ast>>, // enum name -> enum combinator
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
    pub fn as_span(&self) -> Span {
        let (mut start, mut end) = (usize::MAX, 0);
        let input = self.resolved_combinator.as_span().get_input();
        for param in self.param_defns {
            match param {
                ParamDefn::Dependent { span, .. } => {
                    start = start.min(span.start());
                    end = end.max(span.end());
                }
                _ => {}
            }
        }
        Span::new(input, start, end).unwrap()
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

fn check_const_combinator(
    const_combinator: &ConstCombinator,
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
    source: (&str, &Source),
) -> Result<(), VestError> {
    use ConstCombinator::*;
    match const_combinator {
        ConstInt(ConstIntCombinator {
            combinator,
            value,
            span,
        }) => check_const_int_combinator(combinator, value, span, source),
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

fn check_const_struct_combinator(
    const_combinators: &[ConstCombinator],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
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

fn check_const_combinator_invocation(
    name: &Identifier,
    span: Span,
    _local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
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

fn check_const_choice_combinator(
    const_choices: &[ConstChoice],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
    source: (&str, &Source),
) -> Result<(), VestError> {
    for ConstChoice { combinator, .. } in const_choices {
        check_const_combinator(combinator, local_ctx, global_ctx, source)?;
    }
    Ok(())
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
        span,
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
            span,
        }) => check_constraint_int_combinator(combinator, constraint.as_ref(), source),
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
            span,
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
                                    combinator: infer_enum_type(&enums),
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

fn check_bytes_combinator(
    len: &LengthSpecifier,
    span: &Span,
    param_defns: &[ParamDefn],
    local_ctx: &mut LocalCtx,
    global_ctx: &GlobalCtx,
    source: (&str, &Source),
) -> Result<(), VestError> {
    match len {
        LengthSpecifier::Const(..) => {
            // nothing to check
            Ok(())
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
                    }) => Ok(()),
                    _ => {
                        Report::build(
                            ReportKind::Error,
                            (source.0, span_as_range(span)),
                        )
                        .with_message("invalid length specifier")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "`@{}` is not a valid length specifier, expected an unsigned int, got {}",
                                    depend_id, combinator
                                ))
                                .with_color(Color::Red),
                        )
                        .with_label(
                            Label::new((source.0, span_as_range(&combinator.span)))
                                .with_message(format!("Field `@{}` is defined here", depend_id))
                                .with_color(Color::Yellow),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                        Err(VestError::TypeError)
                    } // panic!("Length specifier must be an unsigned int"),
                }
            } else {
                // 2. try to find `depend_id` in param_defns
                let param_defn = param_defns.iter().find(|param_defn| match param_defn {
                    ParamDefn::Dependent { name, .. } => name == depend_id,
                    _ => false,
                });
                // .unwrap_or_else(|| {
                //     panic!("`{}` is not found in current scope", depend_id);
                // });
                match param_defn {
                    Some(ParamDefn::Dependent { combinator, .. }) => {
                        match global_ctx.resolve_alias(combinator) {
                            CombinatorInner::ConstraintInt(ConstraintIntCombinator {
                                combinator:
                                    IntCombinator::Unsigned(_)
                                    | IntCombinator::BtcVarint
                                    | IntCombinator::ULEB128,
                                ..
                            }) => Ok(()),
                            _ => {
                                Report::build(
                            ReportKind::Error,
                            (source.0, span_as_range(span)),
                        )
                        .with_message("invalid length specifier")
                        .with_label(
                            Label::new((source.0, span_as_range(span)))
                                .with_message(format!(
                                    "`@{}` is not a valid length specifier, expected an unsigned int, got {}",
                                    depend_id, combinator
                                ))
                                .with_color(Color::Red),
                        )
                        .with_label(
                            Label::new((source.0, span_as_range(&combinator.as_span())))
                                .with_message(format!("Parameter `@{}` is defined here", depend_id))
                                .with_color(Color::Yellow),
                        )
                        .finish()
                        .eprint(source)
                        .unwrap();
                                Err(VestError::TypeError)
                            } // panic!("Length specifier must be an unsigned int"),
                        }
                    }
                    _ => {
                        report_unbound_field!(source, span, depend_id);
                        Err(VestError::TypeError)
                    }
                }
            }
        }
    }
}

fn check_array_combinator<'ast>(
    combinator: &Combinator<'ast>,
    len: &LengthSpecifier,
    span: &Span,
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
    match choices {
        Choices::Enums(enums) => {
            if let Some(depend_id) = depend_id {
                // check if depend_id a prior field in the struct or in the param_defns
                let combinator = get_combinator_from_depend_id(depend_id)?;
                let combinator = combinator.clone();
                check_combinator_inner(&combinator, param_defns, local_ctx, global_ctx, source)?;
                let combinator = global_ctx.resolve_alias(&combinator);
                // check if `combinator` is defined as an enum
                if let CombinatorInner::Enum(enum_) = combinator {
                    let (enum_variants, is_non_exhaustive) = match enum_ {
                        EnumCombinator::Exhaustive { enums, span } => (enums, false),
                        EnumCombinator::NonExhaustive { enums, span } => (enums, true),
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
                } else if let CombinatorInner::Enum(enum_) = combinator {
                    // check if it's non-exhaustive enum (which is equivalent to an int choice)
                    match enum_ {
                        EnumCombinator::NonExhaustive { enums, span } => {
                            let int_combinator = infer_enum_type(enums);
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
                    let LengthSpecifier::Const(len) = len.clone() else {
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
    let combinator = infer_enum_type(enums);
    for Enum { value, .. } in enums {
        check_const_int_combinator(&combinator, value, &span, source)?;
    }
    Ok(())
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
        Some(IntConstraint::Single { elem, span }) => {
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
