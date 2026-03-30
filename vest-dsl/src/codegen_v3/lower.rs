use std::collections::HashMap;

use crate::vestir::{
    self, ArrayCombinator, BytesCombinator, ChoiceCombinator, Choices, Combinator, CombinatorInner,
    CombinatorInvocation, ConstArray, ConstCombinator, ConstraintElem, ConstraintEnumCombinator,
    ConstraintIntCombinator, Definition, EnumCombinator, IntCombinator, OptionCombinator,
    ParamDefn, StructCombinator, StructField, VecCombinator, WrapCombinator,
};

use super::ir::{
    variant_name_from_tag, CodegenCtx, CombDef, CombIR, ConstDef, DispatchBranchIR, Endian,
    EnumVariantIR, ParamDef, PredicateIR, StructFieldIR, TagValue, UIntIR, UIntWidth,
};

type EnumBindings = HashMap<String, String>;

pub fn lower_definitions(defs: &[Definition], ctx: &mut CodegenCtx) -> Vec<CombDef> {
    for def in defs {
        match def {
            Definition::Endianess(vestir::Endianess::Little) => ctx.endian = Endian::Little,
            Definition::Endianess(vestir::Endianess::Big) => ctx.endian = Endian::Big,
            _ => {}
        }
    }

    defs.iter()
        .filter_map(|def| lower_definition(def, ctx))
        .collect()
}

fn lower_definition(def: &Definition, ctx: &CodegenCtx) -> Option<CombDef> {
    match def {
        Definition::Combinator {
            name,
            param_defns,
            combinator,
        } => Some(CombDef {
            name: name.clone(),
            params: lower_param_defns(param_defns, ctx),
            body: lower_combinator_in_env(
                combinator,
                ctx,
                &enum_bindings_from_params(param_defns, ctx),
            ),
            is_const: false,
            const_defs: extract_const_defs(name, combinator, ctx),
        }),
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => Some(CombDef {
            name: name.clone(),
            params: Vec::new(),
            body: lower_const_combinator(const_combinator, ctx),
            is_const: true,
            const_defs: Vec::new(),
        }),
        Definition::Endianess(_) => None,
    }
}

fn extract_const_defs(
    struct_name: &str,
    combinator: &Combinator,
    ctx: &CodegenCtx,
) -> Vec<ConstDef> {
    match &combinator.inner {
        CombinatorInner::Struct(s) => {
            s.0.iter()
                .filter_map(|field| match field {
                    StructField::Const { label, combinator } => {
                        extract_const_def_from_const_combinator(struct_name, label, combinator, ctx)
                    }
                    _ => None,
                })
                .collect()
        }
        CombinatorInner::Wrap(w) => extract_const_defs(struct_name, &w.combinator, ctx),
        _ => Vec::new(),
    }
}

fn extract_const_def_from_const_combinator(
    struct_name: &str,
    field_name: &str,
    combinator: &ConstCombinator,
    ctx: &CodegenCtx,
) -> Option<ConstDef> {
    match combinator {
        ConstCombinator::ConstInt(ci) => Some(ConstDef {
            name: format!(
                "{}{}_CONST",
                struct_name.to_ascii_uppercase(),
                field_name.to_ascii_uppercase()
            ),
            ty: int_combinator_to_uint_ty(&ci.combinator, ctx.endian)?,
            value: ci.value,
        }),
        _ => None,
    }
}

fn int_combinator_to_uint_ty(int_comb: &IntCombinator, endian: Endian) -> Option<UIntIR> {
    let width = match int_comb {
        IntCombinator::Unsigned(8) => UIntWidth::U8,
        IntCombinator::Unsigned(16) => UIntWidth::U16,
        IntCombinator::Unsigned(24) => UIntWidth::U24,
        IntCombinator::Unsigned(32) => UIntWidth::U32,
        IntCombinator::Unsigned(64) | IntCombinator::BtcVarint | IntCombinator::ULEB128 => {
            UIntWidth::U64
        }
        IntCombinator::Signed(_) | IntCombinator::Unsigned(_) => return None,
    };
    Some(UIntIR::new(width, endian))
}

fn lower_param_defns(params: &[ParamDefn], ctx: &CodegenCtx) -> Vec<ParamDef> {
    params
        .iter()
        .map(|param| match param {
            ParamDefn::Dependent { name, combinator } => ParamDef {
                name: name.clone(),
                ty: lower_combinator_inner_in_env(combinator, ctx, &EnumBindings::new()),
            },
        })
        .collect()
}

fn lower_combinator_in_env(
    comb: &Combinator,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    let inner = lower_combinator_inner_in_env(&comb.inner, ctx, enum_bindings);

    match &comb.and_then {
        Some(next) => {
            let next_ir = lower_combinator_in_env(next, ctx, enum_bindings);
            match inner {
                CombIR::Fixed { len } => CombIR::FixedLen {
                    len: vestir::LengthExpr::Const(len),
                    inner: Box::new(next_ir),
                },
                CombIR::Variable { len } => CombIR::FixedLen {
                    len,
                    inner: Box::new(next_ir),
                },
                len_comb => CombIR::AndThen {
                    len_comb: Box::new(len_comb),
                    inner: Box::new(next_ir),
                },
            }
        }
        None => inner,
    }
}

fn lower_combinator_inner_in_env(
    inner: &CombinatorInner,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    match inner {
        CombinatorInner::ConstraintInt(c) => lower_constraint_int(c, ctx),
        CombinatorInner::ConstraintEnum(c) => lower_constraint_enum(c),
        CombinatorInner::Struct(s) => lower_struct_in_env(s, ctx, enum_bindings),
        CombinatorInner::Wrap(w) => lower_wrap_in_env(w, ctx, enum_bindings),
        CombinatorInner::Enum(e) => lower_enum(e, ctx),
        CombinatorInner::Choice(c) => lower_choice_in_env(c, ctx, enum_bindings),
        CombinatorInner::Vec(v) => lower_vec_in_env(v, ctx, enum_bindings),
        CombinatorInner::Array(a) => lower_array_in_env(a, ctx, enum_bindings),
        CombinatorInner::Bytes(b) => lower_bytes(b),
        CombinatorInner::Tail(_) => CombIR::Tail,
        CombinatorInner::Option(o) => lower_option_in_env(o, ctx, enum_bindings),
        CombinatorInner::Invocation(i) => lower_invocation(i),
    }
}

fn lower_int_combinator(int_comb: &IntCombinator, endian: Endian) -> CombIR {
    match int_comb {
        IntCombinator::Unsigned(8) => CombIR::UInt(UIntIR::new(UIntWidth::U8, endian)),
        IntCombinator::Unsigned(16) => CombIR::UInt(UIntIR::new(UIntWidth::U16, endian)),
        IntCombinator::Unsigned(24) => CombIR::UInt(UIntIR::new(UIntWidth::U24, endian)),
        IntCombinator::Unsigned(32) => CombIR::UInt(UIntIR::new(UIntWidth::U32, endian)),
        IntCombinator::Unsigned(64) => CombIR::UInt(UIntIR::new(UIntWidth::U64, endian)),
        IntCombinator::Unsigned(n) => {
            todo!(
                "Unsupported unsigned integer size lowering is incomplete: {}",
                n
            )
        }
        IntCombinator::Signed(_) => todo!("Signed integer lowering is not implemented"),
        IntCombinator::BtcVarint => todo!("BtcVarint lowering is not implemented"),
        IntCombinator::ULEB128 => todo!("ULEB128 lowering is not implemented"),
    }
}

fn lower_constraint_int(comb: &ConstraintIntCombinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_int_combinator(&comb.combinator, ctx.endian);
    match &comb.constraint {
        Some(predicate) => CombIR::Refined {
            inner: Box::new(inner),
            predicate: PredicateIR::Int(predicate.clone()),
        },
        None => inner,
    }
}

fn lower_constraint_enum(comb: &ConstraintEnumCombinator) -> CombIR {
    CombIR::Refined {
        inner: Box::new(lower_invocation(&comb.combinator)),
        predicate: PredicateIR::Enum(comb.constraint.clone()),
    }
}

fn lower_struct_in_env(
    s: &StructCombinator,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    let fields = &s.0;
    if fields.is_empty() {
        return CombIR::Success;
    }

    if fields
        .iter()
        .any(|field| matches!(field, StructField::Dependent { .. }))
    {
        lower_struct_dependent(fields, ctx, enum_bindings)
    } else {
        lower_struct_simple(fields, ctx, enum_bindings)
    }
}

fn lower_struct_simple(
    fields: &[StructField],
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    lower_struct_fields_preserve_labels(fields, ctx, enum_bindings)
}

fn lower_struct_fields_preserve_labels(
    fields: &[StructField],
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    CombIR::Struct(
        fields
            .iter()
            .map(|field| {
                let comb = lower_struct_field_in_env(field, ctx, enum_bindings);
                StructFieldIR::new(
                    struct_field_label(field),
                    comb.clone(),
                    matches!(comb, CombIR::Tag { .. }),
                )
            })
            .collect(),
    )
}

fn lower_struct_dependent(
    fields: &[StructField],
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    if fields.is_empty() {
        return CombIR::Success;
    }

    let Some(first_dep_idx) = fields.iter().position(is_dependent_field) else {
        return lower_struct_simple(fields, ctx, enum_bindings);
    };

    // Lower any leading non-dependent fields as a simple struct, then recurse
    // and concat with the dependent lowering for the suffix.
    if first_dep_idx > 0 {
        let (prefix_fields, suffix_fields) = fields.split_at(first_dep_idx);
        let prefix = lower_struct_simple(prefix_fields, ctx, enum_bindings);
        let suffix = lower_struct_dependent(suffix_fields, ctx, enum_bindings);
        return concat_sequence(prefix, suffix);
    }

    // The leading dependent run becomes the `fst` side of the pair; everything
    // after it can depend on those bindings.
    let dep_prefix_len = fields
        .iter()
        .take_while(|field| is_dependent_field(field))
        .count();
    let (dep_fields, snd_fields) = fields.split_at(dep_prefix_len);

    if snd_fields.is_empty() {
        return lower_struct_simple(fields, ctx, enum_bindings);
    }

    let dep_names: Vec<_> = dep_fields.iter().map(struct_field_label).collect();

    let mut snd_enum_bindings = enum_bindings.clone();
    for field in dep_fields {
        if let Some((field_name, enum_name)) = field_enum_binding(field, ctx) {
            snd_enum_bindings.insert(field_name, enum_name);
        }
    }

    let fst = if dep_fields.len() == 1 {
        lower_struct_field_in_env(&dep_fields[0], ctx, enum_bindings)
    } else {
        lower_struct_simple(dep_fields, ctx, enum_bindings)
    };
    let snd = if snd_fields.len() == 1 {
        lower_struct_fields_preserve_labels(snd_fields, ctx, &snd_enum_bindings)
    } else {
        lower_struct_in_env(
            &StructCombinator(snd_fields.to_vec()),
            ctx,
            &snd_enum_bindings,
        )
    };

    CombIR::DepPair {
        fst: Box::new(fst),
        fst_bindings: dep_names,
        snd: Box::new(snd),
    }
}

fn is_dependent_field(field: &StructField) -> bool {
    matches!(field, StructField::Dependent { .. })
}

fn concat_sequence(prefix: CombIR, suffix: CombIR) -> CombIR {
    match prefix {
        CombIR::Success => suffix,
        CombIR::Seq(mut items) => {
            items.push(suffix);
            CombIR::Seq(items)
        }
        other => CombIR::Seq(vec![other, suffix]),
    }
}

fn lower_struct_field_in_env(
    field: &StructField,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    match field {
        StructField::Ordinary { combinator, .. } | StructField::Dependent { combinator, .. } => {
            lower_combinator_in_env(combinator, ctx, enum_bindings)
        }
        StructField::Const { combinator, .. } => lower_const_combinator(combinator, ctx),
    }
}

fn lower_wrap_in_env(w: &WrapCombinator, ctx: &CodegenCtx, enum_bindings: &EnumBindings) -> CombIR {
    let inner = lower_combinator_in_env(&w.combinator, ctx, enum_bindings);
    let with_prior = if let Some(prefix) = lower_const_sequence(&w.prior, ctx) {
        CombIR::Preceded {
            prefix: Box::new(prefix),
            inner: Box::new(inner),
        }
    } else {
        inner
    };

    if let Some(suffix) = lower_const_sequence(&w.post, ctx) {
        CombIR::Terminated {
            inner: Box::new(with_prior),
            suffix: Box::new(suffix),
        }
    } else {
        with_prior
    }
}

fn lower_const_sequence(consts: &[ConstCombinator], ctx: &CodegenCtx) -> Option<CombIR> {
    if consts.is_empty() {
        return None;
    }

    let mut items: Vec<_> = consts
        .iter()
        .map(|combinator| lower_const_combinator(combinator, ctx))
        .collect();
    Some(if items.len() == 1 {
        items.pop().unwrap()
    } else {
        CombIR::Seq(items)
    })
}

fn struct_field_label(field: &StructField) -> String {
    match field {
        StructField::Ordinary { label, .. }
        | StructField::Const { label, .. }
        | StructField::Dependent { label, .. } => label.clone(),
    }
}

fn field_enum_binding(field: &StructField, ctx: &CodegenCtx) -> Option<(String, String)> {
    let (label, combinator) = match field {
        StructField::Dependent { label, combinator }
        | StructField::Ordinary { label, combinator } => (label.clone(), combinator),
        StructField::Const { .. } => return None,
    };
    enum_binding_for_inner(label, &combinator.inner, ctx)
}

fn enum_bindings_from_params(params: &[ParamDefn], ctx: &CodegenCtx) -> EnumBindings {
    params
        .iter()
        .filter_map(|param| match param {
            ParamDefn::Dependent { name, combinator } => {
                enum_binding_for_inner(name.clone(), combinator, ctx)
            }
        })
        .collect()
}

fn enum_binding_for_inner(
    name: String,
    combinator: &CombinatorInner,
    ctx: &CodegenCtx,
) -> Option<(String, String)> {
    match combinator {
        CombinatorInner::Invocation(invocation) if ctx.is_enum_type(&invocation.func) => {
            Some((name, invocation.func.clone()))
        }
        CombinatorInner::ConstraintEnum(constraint) => {
            Some((name, constraint.combinator.func.clone()))
        }
        _ => None,
    }
}

fn lower_enum(comb: &EnumCombinator, ctx: &CodegenCtx) -> CombIR {
    match comb {
        EnumCombinator::Exhaustive { enums, inferred } => {
            let inner = lower_int_combinator(inferred, ctx.endian);
            let predicate = vestir::IntConstraint::Set(
                enums
                    .iter()
                    .map(|variant| ConstraintElem::Single(variant.value))
                    .collect(),
            );
            CombIR::Enum {
                inner: Box::new(inner),
                predicate,
                variants: enums
                    .iter()
                    .map(|variant| EnumVariantIR {
                        name: variant.name.clone(),
                        value: variant.value,
                    })
                    .collect(),
            }
        }
        EnumCombinator::NonExhaustive { inferred, .. } => {
            lower_int_combinator(inferred, ctx.endian)
        }
    }
}

fn lower_choice_in_env(
    comb: &ChoiceCombinator,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    let depend_id = comb
        .depend_id
        .as_deref()
        .expect("codegen_v3 only supports choose(@tag) lowering");
    lower_choice_with_tag(depend_id, &comb.choices, ctx, enum_bindings)
        .expect("codegen_v3 only supports dispatch-compatible choose branches")
}

fn lower_choice_with_tag(
    depend_id: &str,
    choices: &Choices,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> Option<CombIR> {
    let branches = match choices {
        Choices::Ints(choices) => {
            lower_tagged_choices(choices, ctx, enum_bindings, choice_int_tag_value)
        }
        Choices::Arrays(choices) => {
            lower_tagged_choices(choices, ctx, enum_bindings, choice_array_tag_value)
        }
        Choices::Enums(choices) => {
            let enum_ty = enum_bindings.get(depend_id)?;
            choices
                .iter()
                .enumerate()
                .map(|(idx, (variant, comb))| {
                    let tag = if variant == "_" {
                        TagValue::Wildcard
                    } else {
                        TagValue::Enum {
                            ty: enum_ty.clone(),
                            variant: variant.clone(),
                        }
                    };
                    Some(DispatchBranchIR {
                        variant_name: variant_name_from_tag(&tag, idx),
                        tag,
                        comb: lower_combinator_in_env(comb, ctx, enum_bindings),
                    })
                })
                .collect()
        }
    }?;

    Some(CombIR::Dispatch {
        tag: depend_id.to_string(),
        branches,
    })
}

fn lower_tagged_choices<T, F>(
    choices: &[(T, Combinator)],
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
    tag_of: F,
) -> Option<Vec<DispatchBranchIR>>
where
    F: Fn(&T) -> Option<TagValue>,
{
    choices
        .iter()
        .enumerate()
        .map(|(idx, (tag, comb))| {
            let tag = tag_of(tag)?;
            Some(DispatchBranchIR {
                variant_name: variant_name_from_tag(&tag, idx),
                tag,
                comb: lower_combinator_in_env(comb, ctx, enum_bindings),
            })
        })
        .collect()
}

fn choice_int_tag_value(tag: &Option<ConstraintElem>) -> Option<TagValue> {
    match tag {
        Some(ConstraintElem::Single(value)) => Some(TagValue::Int(*value)),
        Some(ConstraintElem::Range { .. }) | None => None,
    }
}

fn choice_array_tag_value(tag: &ConstArray) -> Option<TagValue> {
    const_array_to_bytes(tag).map(TagValue::Bytes)
}

fn lower_vec_in_env(v: &VecCombinator, ctx: &CodegenCtx, enum_bindings: &EnumBindings) -> CombIR {
    match v {
        VecCombinator::Vec(inner) => {
            CombIR::Repeat(Box::new(lower_combinator_in_env(inner, ctx, enum_bindings)))
        }
    }
}

fn lower_array_in_env(
    a: &ArrayCombinator,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    CombIR::RepeatN {
        inner: Box::new(lower_combinator_in_env(&a.combinator, ctx, enum_bindings)),
        count: a.len.clone(),
    }
}

fn lower_bytes(b: &BytesCombinator) -> CombIR {
    match &b.len {
        vestir::LengthExpr::Const(len) => CombIR::Fixed { len: *len },
        len => CombIR::Variable { len: len.clone() },
    }
}

fn lower_option_in_env(
    o: &OptionCombinator,
    ctx: &CodegenCtx,
    enum_bindings: &EnumBindings,
) -> CombIR {
    CombIR::Opt(Box::new(lower_combinator_in_env(&o.0, ctx, enum_bindings)))
}

fn lower_invocation(i: &CombinatorInvocation) -> CombIR {
    CombIR::Named {
        name: i.func.clone(),
        args: i.args.clone(),
    }
}

fn lower_const_combinator(c: &ConstCombinator, ctx: &CodegenCtx) -> CombIR {
    match c {
        ConstCombinator::ConstBytes(cb) => CombIR::Tag {
            inner: Box::new(CombIR::Fixed { len: cb.len }),
            value: TagValue::Bytes(const_array_bytes(&cb.values)),
        },
        ConstCombinator::ConstInt(ci) => CombIR::Tag {
            inner: Box::new(lower_int_combinator(&ci.combinator, ctx.endian)),
            value: TagValue::Int(ci.value),
        },
        ConstCombinator::ConstEnum(ce) => CombIR::Tag {
            inner: Box::new(lower_invocation(&ce.combinator)),
            value: TagValue::Enum {
                ty: ce.combinator.func.clone(),
                variant: ce.variant.clone(),
            },
        },
        ConstCombinator::ConstCombinatorInvocation(name) => CombIR::Named {
            name: name.clone(),
            args: Vec::new(),
        },
    }
}

fn const_array_bytes(values: &ConstArray) -> Vec<u8> {
    const_array_to_bytes(values).unwrap_or_default()
}

fn const_array_to_bytes(values: &ConstArray) -> Option<Vec<u8>> {
    match values {
        ConstArray::Char(bytes) => Some(bytes.clone()),
        ConstArray::Int(ints) => Some(ints.iter().map(|&value| value as u8).collect()),
        ConstArray::Repeat(value, count) => Some(vec![*value as u8; *count]),
        ConstArray::Wildcard => None,
    }
}
