//! Shared code-generation models and utility helpers.

use super::*;
use std::fmt::{self, Display, Write};

// Shared intermediate representations.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LengthBounds {
    pub(super) min: Option<usize>,
    pub(super) max: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct IntegerBounds {
    pub(super) min: Option<i64>,
    pub(super) max: Option<i64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IntegerRepr {
    I8,
    I16,
    General,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum TagShape {
    Tlv { constructed: bool },
    Untagged,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum NominalKind {
    TaggedExact { constructed: bool },
    TaggedIdentity { constructed: bool },
    UntaggedFinite(Vec<WireTag>),
    UntaggedAny,
    Untagged,
}

pub(super) fn angle_bracketed(parts: &[String]) -> String {
    if parts.is_empty() {
        String::new()
    } else {
        format!("<{}>", parts.join(", "))
    }
}

#[derive(Clone, Debug)]
pub(super) struct Rendered {
    pub(super) ty: String,
    pub(super) expr: String,
    pub(super) shape: TagShape,
    pub(super) proof: UnambiguityPlan,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct StartCertificate {
    pub(super) accepts_empty: bool,
    pub(super) tags: Option<BTreeSet<WireTag>>,
}

impl StartCertificate {
    pub(super) fn finite(tags: BTreeSet<WireTag>) -> Self {
        Self {
            accepts_empty: false,
            tags: Some(tags),
        }
    }

    pub(super) fn eof() -> Self {
        Self {
            accepts_empty: true,
            tags: Some(BTreeSet::new()),
        }
    }

    pub(super) fn open() -> Self {
        Self {
            accepts_empty: false,
            tags: None,
        }
    }

    pub(super) fn any_non_eoc() -> Self {
        let mut tags = BTreeSet::new();
        for class in 0u8..4 {
            for constructed in [false, true] {
                for number in 0u32..32 {
                    if !(class == 0 && !constructed && number == 0) {
                        tags.insert(WireTag {
                            class,
                            number,
                            constructed,
                        });
                    }
                }
            }
        }
        Self {
            accepts_empty: false,
            tags: Some(tags),
        }
    }

    pub(super) fn from_tag_domain(domain: &TagDomain) -> Self {
        match domain {
            TagDomain::Finite(tags) => Self::finite(tags.clone()),
            TagDomain::Open => Self::open(),
        }
    }

    pub(super) fn union(&self, other: &Self) -> Self {
        let tags = match (&self.tags, &other.tags) {
            (Some(left), Some(right)) => {
                let mut result = left.clone();
                result.extend(right.iter().cloned());
                Some(result)
            }
            _ => None,
        };
        Self {
            accepts_empty: self.accepts_empty || other.accepts_empty,
            tags,
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct UnambiguityPlan {
    pub(super) expr: String,
    pub(super) start: StartCertificate,
    pub(super) kind: UnambiguityKind,
}

#[derive(Clone, Debug)]
pub(super) enum UnambiguityKind {
    Leaf,
    Nominal,
    Transparent(Box<UnambiguityPlan>),
    Retagged(Box<UnambiguityPlan>),
    Pair(Box<UnambiguityPlan>, Box<UnambiguityPlan>),
    Choice(Box<UnambiguityPlan>, Box<UnambiguityPlan>),
    Optional(Box<UnambiguityPlan>, Box<UnambiguityPlan>),
    Defaulted(Box<UnambiguityPlan>, Box<UnambiguityPlan>),
    BerSequenceOf(Box<UnambiguityPlan>),
    Mapped(Box<UnambiguityPlan>),
}

impl UnambiguityPlan {
    pub(super) fn leaf(expr: impl Into<String>) -> Self {
        Self {
            expr: expr.into(),
            start: StartCertificate::open(),
            kind: UnambiguityKind::Leaf,
        }
    }

    pub(super) fn transparent(expr: String, child: UnambiguityPlan) -> Self {
        Self {
            expr,
            start: child.start.clone(),
            kind: UnambiguityKind::Transparent(Box::new(child)),
        }
    }

    pub(super) fn retagged(expr: String, child: UnambiguityPlan) -> Self {
        Self {
            expr,
            start: child.start.clone(),
            kind: UnambiguityKind::Retagged(Box::new(child)),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct RenderedDefault {
    pub(super) ty: String,
    pub(super) expr: String,
}

#[derive(Clone, Debug)]
pub(super) struct Names {
    pub(super) value: String,
    pub(super) spec: String,
    pub(super) format: String,
    pub(super) inner_format: String,
    pub(super) forward: String,
    pub(super) reverse: String,
    pub(super) predicate: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct WireTag {
    pub(super) class: u8,
    pub(super) number: u32,
    pub(super) constructed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TagDomain {
    Finite(BTreeSet<WireTag>),
    Open,
}

// Constraint validation and lowering.

pub(super) fn lookup_named_number<'a>(
    values: &'a [NamedNumber],
    name: &str,
    path: &str,
) -> Result<&'a NamedNumber, CodegenError> {
    values
        .iter()
        .find(|value| value.name == name)
        .ok_or_else(|| {
            CodegenError::new(
                path,
                format!("`{name}` is not a named value of the declared type"),
            )
        })
}

pub(super) fn legacy_size_bounds(
    constraint: &SizeConstraint,
    path: &str,
) -> Result<LengthBounds, CodegenError> {
    let bounds = match constraint {
        SizeConstraint::Fixed(size) => {
            let size = usize::try_from(*size).map_err(|_| {
                CodegenError::new(path, format!("SIZE value `{size}` does not fit usize"))
            })?;
            LengthBounds {
                min: Some(size),
                max: Some(size),
            }
        }
        SizeConstraint::Range(min, max) => LengthBounds {
            min: min
                .map(|value| {
                    usize::try_from(value).map_err(|_| {
                        CodegenError::new(
                            path,
                            format!("minimum SIZE `{value}` does not fit usize"),
                        )
                    })
                })
                .transpose()?,
            max: max
                .map(|value| {
                    usize::try_from(value).map_err(|_| {
                        CodegenError::new(
                            path,
                            format!("maximum SIZE `{value}` does not fit usize"),
                        )
                    })
                })
                .transpose()?,
        },
    };
    validate_length_bounds(bounds, path)
}

pub(super) fn string_size_bounds(
    constraint: &Constraint,
    path: &str,
) -> Result<LengthBounds, CodegenError> {
    if constraint.exception.is_some() {
        return Err(CodegenError::new(
            path,
            "exception specifications on SIZE constraints are not supported yet",
        ));
    }
    let ConstraintSpec::Subtype(SubtypeConstraint::SizeConstraint(inner)) = &constraint.spec else {
        return Err(CodegenError::new(
            path,
            "only OCTET STRING SIZE constraints are supported yet",
        ));
    };
    let bounds = match inner.as_ref() {
        SubtypeConstraint::SingleValue(value) => {
            let value = finite_size_value(value, path, "SIZE")?;
            LengthBounds {
                min: Some(value),
                max: Some(value),
            }
        }
        SubtypeConstraint::ValueRange { min, max } => LengthBounds {
            min: lower_size_bound(min, path)?,
            max: upper_size_bound(max, path)?,
        },
        _ => {
            return Err(CodegenError::new(
                path,
                "only fixed and ranged OCTET STRING SIZE constraints are supported yet",
            ));
        }
    };
    validate_length_bounds(bounds, path)
}

pub(super) fn integer_value_bounds(
    constraint: &Constraint,
    path: &str,
) -> Result<IntegerBounds, CodegenError> {
    if constraint.exception.is_some() {
        return Err(CodegenError::new(
            path,
            "exception specifications on INTEGER constraints are not supported yet",
        ));
    }
    let ConstraintSpec::Subtype(subtype) = &constraint.spec else {
        return Err(CodegenError::new(
            path,
            "only INTEGER value ranges are supported yet",
        ));
    };
    let bounds = match subtype {
        SubtypeConstraint::SingleValue(ConstraintValue::Integer(value)) => IntegerBounds {
            min: Some(*value),
            max: Some(*value),
        },
        SubtypeConstraint::ValueRange { min, max } => IntegerBounds {
            min: match min {
                ConstraintValue::Min => None,
                ConstraintValue::Integer(value) => Some(*value),
                ConstraintValue::Max | ConstraintValue::NamedValue(_) => {
                    return Err(CodegenError::new(
                        path,
                        "invalid or unresolved INTEGER lower bound",
                    ));
                }
            },
            max: match max {
                ConstraintValue::Max => None,
                ConstraintValue::Integer(value) => Some(*value),
                ConstraintValue::Min | ConstraintValue::NamedValue(_) => {
                    return Err(CodegenError::new(
                        path,
                        "invalid or unresolved INTEGER upper bound",
                    ));
                }
            },
        },
        _ => {
            return Err(CodegenError::new(
                path,
                "only fixed and ranged INTEGER constraints are supported yet",
            ));
        }
    };
    if matches!((bounds.min, bounds.max), (Some(min), Some(max)) if min > max) {
        return Err(CodegenError::new(
            path,
            "INTEGER constraint minimum exceeds maximum",
        ));
    }
    Ok(bounds)
}

pub(super) fn finite_size_value(
    value: &ConstraintValue,
    path: &str,
    description: &str,
) -> Result<usize, CodegenError> {
    let ConstraintValue::Integer(value) = value else {
        return Err(CodegenError::new(
            path,
            format!("{description} must be a non-negative integer"),
        ));
    };
    usize::try_from(*value).map_err(|_| {
        CodegenError::new(
            path,
            format!("{description} value `{value}` does not fit usize"),
        )
    })
}

pub(super) fn lower_size_bound(
    value: &ConstraintValue,
    path: &str,
) -> Result<Option<usize>, CodegenError> {
    match value {
        ConstraintValue::Min => Ok(None),
        ConstraintValue::Integer(_) => finite_size_value(value, path, "minimum SIZE").map(Some),
        _ => Err(CodegenError::new(
            path,
            "minimum SIZE must be an integer or MIN",
        )),
    }
}

pub(super) fn upper_size_bound(
    value: &ConstraintValue,
    path: &str,
) -> Result<Option<usize>, CodegenError> {
    match value {
        ConstraintValue::Max => Ok(None),
        ConstraintValue::Integer(_) => finite_size_value(value, path, "maximum SIZE").map(Some),
        _ => Err(CodegenError::new(
            path,
            "maximum SIZE must be an integer or MAX",
        )),
    }
}

pub(super) fn validate_length_bounds(
    bounds: LengthBounds,
    path: &str,
) -> Result<LengthBounds, CodegenError> {
    if matches!((bounds.min, bounds.max), (Some(min), Some(max)) if min > max) {
        return Err(CodegenError::new(
            path,
            "minimum SIZE is greater than maximum SIZE",
        ));
    }
    Ok(bounds)
}

// Generated Rust and Vest syntax rendering.

pub(super) fn primitive(ty: &str, expr: &str, constructed: bool) -> Rendered {
    Rendered {
        ty: ty.to_string(),
        expr: expr.to_string(),
        shape: TagShape::Tlv { constructed },
        proof: UnambiguityPlan::leaf(expr),
    }
}

pub(super) fn wrap_ref(rendered: Rendered) -> Rendered {
    let expr = format!("Ref({})", rendered.expr);
    Rendered {
        ty: format!("Ref<{}>", rendered.ty),
        proof: UnambiguityPlan::transparent(expr.clone(), rendered.proof),
        expr,
        shape: rendered.shape,
    }
}

pub(super) fn refine(
    rendered: Rendered,
    predicate_type: String,
    predicate_expr: String,
) -> Rendered {
    let expr = format!("Refined({}, {predicate_expr})", rendered.expr);
    Rendered {
        ty: format!("Refined<{}, {predicate_type}>", rendered.ty),
        proof: UnambiguityPlan::transparent(expr.clone(), rendered.proof),
        expr,
        shape: rendered.shape,
    }
}

pub(super) fn map_with_bimap(rendered: Rendered, forward: &str, reverse: &str) -> Rendered {
    let expr = if rendered.expr.contains('\n') {
        format!(
            "Mapped {{\n    inner:\n        {},\n    mapper: BiMap({forward}, {reverse}),\n}}",
            indent_continuation(&rendered.expr, 8),
        )
    } else {
        format!(
            "Mapped {{ inner: {}, mapper: BiMap({forward}, {reverse}) }}",
            rendered.expr
        )
    };
    Rendered {
        ty: format!("Mapped<{}, BiMap<{forward}, {reverse}>>", rendered.ty),
        proof: UnambiguityPlan {
            expr: expr.clone(),
            start: rendered.proof.start.clone(),
            kind: UnambiguityKind::Mapped(Box::new(rendered.proof)),
        },
        expr,
        shape: rendered.shape,
    }
}

/// Indent every line after the first one by `spaces` columns.
pub(super) fn indent_continuation(value: &str, spaces: usize) -> String {
    value.replace('\n', &format!("\n{}", " ".repeat(spaces)))
}

/// Render an outer list-like combinator around an already flattened chain.
pub(super) fn render_list_combinator(name: &str, inner: &str) -> String {
    format!("{name}(\n    {},\n)", indent_continuation(inner, 4))
}

/// Render one node of a balanced binary `CHOICE` tree.
pub(super) fn render_choice_combinator(left: &str, right: &str) -> String {
    format!(
        "CHOICE(\n    {},\n    {})",
        indent_continuation(left, 4),
        indent_continuation(right, 4),
    )
}

/// Replace rule-qualified expression items with local names and return the
/// imports needed to make those names available inside a generated function.
pub(super) fn localize_rule_items(expression: &str, rule: EncodingRules) -> (String, Vec<String>) {
    let prefix = format!("vest_lib::asn1::{}::", rule.module());
    let mut localized = String::with_capacity(expression.len());
    let mut items = BTreeSet::new();
    let mut remaining = expression;

    while let Some(index) = remaining.find(&prefix) {
        localized.push_str(&remaining[..index]);
        let after_prefix = &remaining[index + prefix.len()..];
        let item_len = after_prefix
            .bytes()
            .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            .count();
        if item_len == 0 {
            localized.push_str(&prefix);
            remaining = after_prefix;
            continue;
        }

        let item = &after_prefix[..item_len];
        localized.push_str(item);
        items.insert(item.to_string());
        remaining = &after_prefix[item_len..];
    }
    localized.push_str(remaining);

    (localized, items.into_iter().collect())
}

pub(super) fn render_local_rule_import(rule: EncodingRules, items: &[String]) -> Option<String> {
    match items {
        [] => None,
        [item] => Some(format!("use vest_lib::asn1::{}::{item};", rule.module(),)),
        _ => Some(format!(
            "use vest_lib::asn1::{}::{{{}}};",
            rule.module(),
            items.join(", "),
        )),
    }
}

pub(super) fn render_optionally_sized_string(
    unconstrained_type: &str,
    unconstrained_expr: &str,
    constraint: Option<&SizeConstraint>,
) -> Result<Rendered, CodegenError> {
    match constraint {
        Some(constraint) => Ok(render_sized_format(
            unconstrained_type,
            unconstrained_expr,
            legacy_size_bounds(constraint, unconstrained_expr)?,
        )),
        None => Ok(primitive(unconstrained_type, unconstrained_expr, false)),
    }
}

pub(super) fn render_sized_format(
    unconstrained_type: &str,
    unconstrained_expr: &str,
    bounds: LengthBounds,
) -> Rendered {
    let (predicate_type, predicate_expr) = render_size_predicate(bounds);
    refine(
        primitive(unconstrained_type, unconstrained_expr, false),
        predicate_type,
        predicate_expr,
    )
}

pub(super) fn render_size_predicate(bounds: LengthBounds) -> (String, String) {
    let has_min = bounds.min.is_some();
    let min = bounds.min.unwrap_or(0);
    let has_max = bounds.max.is_some();
    let max = bounds.max.unwrap_or(0);
    let predicate_type = format!("Size<{has_min}, {min}, {has_max}, {max}>");
    let predicate_expr = format!("Size::<{has_min}, {min}, {has_max}, {max}>");
    (predicate_type, predicate_expr)
}

pub(super) fn integer_repr(bounds: IntegerBounds) -> IntegerRepr {
    match (bounds.min, bounds.max) {
        (Some(min), Some(max)) if min >= i8::MIN as i64 && max <= i8::MAX as i64 => IntegerRepr::I8,
        (Some(min), Some(max)) if min >= i16::MIN as i64 && max <= i16::MAX as i64 => {
            IntegerRepr::I16
        }
        _ => IntegerRepr::General,
    }
}

pub(super) fn lifetime_declaration(has_lifetime: bool) -> &'static str {
    if has_lifetime {
        "<'a>"
    } else {
        ""
    }
}

pub(super) fn lifetime_application(has_lifetime: bool, lifetime: &str) -> String {
    if has_lifetime {
        format!("<{lifetime}>")
    } else {
        String::new()
    }
}

pub(super) fn impl_lifetime(has_lifetime: bool) -> &'static str {
    if has_lifetime {
        "<'a>"
    } else {
        ""
    }
}

pub(super) fn nested_type(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_type(rest)),
    }
}

pub(super) fn nested_pattern(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_pattern(rest)),
    }
}

pub(super) fn nested_expression(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_expression(rest)),
    }
}

pub(super) fn nested_sum_type(parts: &[String]) -> String {
    match parts {
        [] => "Never".to_string(),
        [only] => only.clone(),
        _ => {
            let middle = choice_split(parts.len());
            format!(
                "Sum<{}, {}>",
                nested_sum_type(&parts[..middle]),
                nested_sum_type(&parts[middle..]),
            )
        }
    }
}

pub(super) fn sum_pattern(index: usize, len: usize, binding: &str) -> String {
    if len == 1 {
        binding.to_string()
    } else {
        let middle = choice_split(len);
        if index < middle {
            format!("L({})", sum_pattern(index, middle, binding))
        } else {
            format!("R({})", sum_pattern(index - middle, len - middle, binding))
        }
    }
}

pub(super) fn sum_expression(index: usize, len: usize, value: &str) -> String {
    if len == 1 {
        value.to_string()
    } else {
        let middle = choice_split(len);
        if index < middle {
            format!("L({})", sum_expression(index, middle, value))
        } else {
            format!("R({})", sum_expression(index - middle, len - middle, value))
        }
    }
}

/// Split a CHOICE into a smaller remainder and a perfect right subtree.
///
/// Besides logarithmic depth, this orientation lets disjointness automation recursively peel
/// choices on the right without ever needing the reverse `choice-left` rule.
pub(super) fn choice_split(len: usize) -> usize {
    debug_assert!(len >= 2);
    let right_len = 1usize << ((usize::BITS - (len - 1).leading_zeros() - 1) as usize);
    len - right_len
}

pub(super) fn render_enum_number_match(
    values: &[NamedNumber],
    enum_name: &str,
    output: &mut CodeWriter,
    indent: usize,
) {
    let padding = " ".repeat(indent);
    output.line(format_args!("{padding}match value {{"));
    for value in values {
        output.line(format_args!(
            "{padding}    {}i16 => {enum_name}::{},",
            value.value,
            rust_variant_name(&value.name)
        ));
    }
    output.line(format_args!(
        "{padding}    _ => {enum_name}::{},",
        rust_variant_name(&values[0].name)
    ));
    output.line(format_args!("{padding}}}"));
}

pub(super) fn render_enum_value_match(
    values: &[NamedNumber],
    enum_name: &str,
    output: &mut CodeWriter,
    indent: usize,
) {
    let padding = " ".repeat(indent);
    output.line(format_args!("{padding}match value {{"));
    for value in values {
        output.line(format_args!(
            "{padding}    {enum_name}::{} => {}i16,",
            rust_variant_name(&value.name),
            value.value
        ));
    }
    output.line(format_args!("{padding}}}"));
}
pub(super) fn render_retag_helper(
    tag: &TagInfo,
    explicit: bool,
    inner: &str,
    qualified_explicit_rule: Option<EncodingRules>,
) -> String {
    let mut helper = match (&tag.class, explicit) {
        (TagClass::ContextSpecific, false) => "IMPLICIT",
        (TagClass::ContextSpecific, true) => "EXPLICIT",
        (TagClass::Application, false) => "IMPLICIT_APPLICATION",
        (TagClass::Application, true) => "EXPLICIT_APPLICATION",
        (TagClass::Private, false) => "IMPLICIT_PRIVATE",
        (TagClass::Private, true) => "EXPLICIT_PRIVATE",
        (TagClass::Universal, false) => {
            return format!("Implicit(Class::Universal, {}u64, {inner})", tag.number);
        }
        (TagClass::Universal, true) => "Explicit",
    }
    .to_string();
    if let Some(rule) = qualified_explicit_rule {
        helper = format!("vest_lib::asn1::{}::{helper}", rule.module());
    }
    if matches!(tag.class, TagClass::Universal) {
        return format!("{helper}(Class::Universal, {}u64, {inner})", tag.number);
    }
    format!("{helper}({}u64, {inner})", tag.number)
}

// Tag-domain and DER identifier analysis.

pub(super) fn domains_overlap(left: &TagDomain, right: &TagDomain) -> bool {
    match (left, right) {
        (TagDomain::Open, TagDomain::Finite(tags)) | (TagDomain::Finite(tags), TagDomain::Open) => {
            !tags.is_empty()
        }
        (TagDomain::Open, TagDomain::Open) => true,
        (TagDomain::Finite(left), TagDomain::Finite(right)) => {
            left.iter().any(|tag| right.contains(tag))
        }
    }
}

pub(super) fn union_domains(left: TagDomain, right: TagDomain) -> TagDomain {
    match (left, right) {
        (TagDomain::Open, _) | (_, TagDomain::Open) => TagDomain::Open,
        (TagDomain::Finite(mut left), TagDomain::Finite(right)) => {
            left.extend(right);
            TagDomain::Finite(left)
        }
    }
}

pub(super) fn der_identifier_octets(tag: &WireTag) -> Vec<u8> {
    let class_bits = tag.class << 6;
    let constructed_bit = if tag.constructed { 0x20 } else { 0 };
    if tag.number < 31 {
        return vec![class_bits | constructed_bit | tag.number as u8];
    }

    let mut number = tag.number;
    let mut encoded_number = vec![(number & 0x7f) as u8];
    number >>= 7;
    while number != 0 {
        encoded_number.push(((number & 0x7f) as u8) | 0x80);
        number >>= 7;
    }
    encoded_number.reverse();

    let mut octets = vec![class_bits | constructed_bit | 0x1f];
    octets.extend(encoded_number);
    octets
}

pub(super) fn tag_class_id(class: &TagClass) -> u8 {
    match class {
        TagClass::Universal => 0,
        TagClass::Application => 1,
        TagClass::ContextSpecific => 2,
        TagClass::Private => 3,
    }
}

// Infallible generated-source writer.

/// Small infallible emitter used by the code generator.
///
/// `String`'s formatter cannot fail, so the assertion is kept here rather than
/// repeated at every call site throughout the generator.
pub(super) struct CodeWriter {
    output: String,
}

impl CodeWriter {
    pub(super) fn new() -> Self {
        Self {
            output: String::new(),
        }
    }

    pub(super) fn line(&mut self, value: impl Display) {
        writeln!(&mut self.output, "{value}")
            .expect("writing generated code to a String cannot fail");
    }

    pub(super) fn blank_line(&mut self) {
        self.output.push('\n');
    }

    pub(super) fn finish(self) -> String {
        self.output
    }
}

impl Default for CodeWriter {
    fn default() -> Self {
        Self::new()
    }
}

impl Write for CodeWriter {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        self.output.push_str(value);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn code_writer_emits_lines_and_blank_lines() {
        let mut writer = CodeWriter::new();
        writer.line("first");
        writer.blank_line();
        writer.line(format_args!("{} {}", "second", 2));
        assert_eq!(writer.finish(), "first\n\nsecond 2\n");
    }

    #[test]
    fn pretty_prints_sequence_and_balanced_choice_trees() {
        let sequence = render_list_combinator("SEQUENCE", "REQUIRED(A,\nOPTIONAL(B,\nEof))");
        assert_eq!(
            sequence,
            "SEQUENCE(\n    REQUIRED(A,\n    OPTIONAL(B,\n    Eof)),\n)"
        );

        let left = render_choice_combinator("A", "B");
        let right = render_choice_combinator("C", "D");
        let choice = render_choice_combinator(&left, &right);
        assert_eq!(
            choice,
            "CHOICE(\n    CHOICE(\n        A,\n        B),\n    CHOICE(\n        C,\n        D))"
        );

        assert_eq!(
            nested_sum_type(&["A".into(), "B".into(), "C".into(), "D".into()]),
            "Sum<Sum<A, B>, Sum<C, D>>"
        );
        assert_eq!(sum_pattern(2, 4, "value"), "R(L(value))");
        assert_eq!(sum_expression(3, 4, "value"), "R(R(value))");
        assert_eq!(choice_split(3), 1);
        assert_eq!(choice_split(6), 2);
        assert_eq!(choice_split(9), 1);
        assert_eq!(
            nested_sum_type(&[
                "A".into(),
                "B".into(),
                "C".into(),
                "D".into(),
                "E".into(),
                "F".into(),
            ]),
            "Sum<Sum<A, B>, Sum<Sum<C, D>, Sum<E, F>>>"
        );

        let (localized, items) = localize_rule_items(
            "vest_lib::asn1::ber::SEQUENCE(vest_lib::asn1::ber::BER_END)",
            EncodingRules::Ber,
        );
        assert_eq!(localized, "SEQUENCE(BER_END)");
        assert_eq!(items, ["BER_END", "SEQUENCE"]);
        assert_eq!(
            render_local_rule_import(EncodingRules::Ber, &items).unwrap(),
            "use vest_lib::asn1::ber::{BER_END, SEQUENCE};"
        );
    }
}
