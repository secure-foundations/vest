use crate::vestir::{
    self, ArrayCombinator, BytesCombinator, ChoiceCombinator, Choices, Combinator, CombinatorInner,
    CombinatorInvocation, ConstArray, ConstCombinator, ConstraintElem, ConstraintEnumCombinator,
    ConstraintIntCombinator, Definition, EnumCombinator, IntCombinator, OptionCombinator,
    ParamDefn, StructCombinator, StructField, VecCombinator, WrapCombinator,
};

use super::combir::{
    CodegenCtx, CombDef, CombIR, ConstDef, DepCombIR, Endian, IntConstraintIR, LenExpr, ParamDef,
    PredicateIR, TagRef, TagValue,
};

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
            name: name.to_string(),
            params: lower_param_defns(param_defns, ctx),
            body: lower_combinator(combinator, ctx),
            is_const: false,
            const_defs: extract_const_defs(name, combinator),
        }),
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => Some(CombDef {
            name: name.to_string(),
            params: Vec::new(),
            body: lower_const_combinator(const_combinator, ctx),
            is_const: true,
            const_defs: Vec::new(),
        }),
        Definition::Endianess(_) => None,
    }
}

fn extract_const_defs(struct_name: &str, combinator: &Combinator) -> Vec<ConstDef> {
    match &combinator.inner {
        CombinatorInner::Struct(s) => {
            s.0.iter()
                .filter_map(|field| match field {
                    StructField::Const { label, combinator } => {
                        extract_const_def_from_const_combinator(struct_name, label, combinator)
                    }
                    _ => None,
                })
                .collect()
        }
        CombinatorInner::Wrap(w) => extract_const_defs(struct_name, &w.combinator),
        _ => Vec::new(),
    }
}

fn extract_const_def_from_const_combinator(
    struct_name: &str,
    field_name: &str,
    combinator: &ConstCombinator,
) -> Option<ConstDef> {
    match combinator {
        ConstCombinator::ConstInt(ci) => {
            let ty = int_combinator_to_type(&ci.combinator);
            let const_name = format!(
                "{}{}_CONST",
                struct_name.to_ascii_uppercase(),
                field_name.to_ascii_uppercase()
            );
            Some(ConstDef {
                name: const_name,
                ty,
                value: ci.value,
            })
        }
        _ => None,
    }
}

fn int_combinator_to_type(int_comb: &IntCombinator) -> String {
    match int_comb {
        IntCombinator::Unsigned(n) => format!("u{}", n),
        IntCombinator::Signed(n) => format!("i{}", n),
        IntCombinator::BtcVarint | IntCombinator::ULEB128 => "u64".to_string(),
    }
}

fn lower_param_defns(params: &[ParamDefn], ctx: &CodegenCtx) -> Vec<ParamDef> {
    params
        .iter()
        .filter_map(|p| match p {
            ParamDefn::Dependent { name, combinator } => Some(ParamDef {
                name: name.clone(),
                ty: lower_combinator_inner(combinator, ctx),
            }),
        })
        .collect()
}

fn lower_combinator(comb: &Combinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_combinator_inner(&comb.inner, ctx);

    match &comb.and_then {
        Some(next) => {
            let next_ir = lower_combinator(next, ctx);
            match inner {
                CombIR::Fixed { len } => CombIR::FixedLen {
                    len: LenExpr::Const(len),
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

fn lower_combinator_inner(inner: &CombinatorInner, ctx: &CodegenCtx) -> CombIR {
    match inner {
        CombinatorInner::ConstraintInt(c) => lower_constraint_int(c, ctx),
        CombinatorInner::ConstraintEnum(c) => lower_constraint_enum(c, ctx),
        CombinatorInner::Struct(s) => lower_struct(s, ctx),
        CombinatorInner::Wrap(w) => lower_wrap(w, ctx),
        CombinatorInner::Enum(e) => lower_enum(e, ctx),
        CombinatorInner::Choice(c) => lower_choice(c, ctx),
        CombinatorInner::Vec(v) => lower_vec(v, ctx),
        CombinatorInner::Array(a) => lower_array(a, ctx),
        CombinatorInner::Bytes(b) => lower_bytes(b, ctx),
        CombinatorInner::Tail(_) => CombIR::Tail,
        CombinatorInner::Option(o) => lower_option(o, ctx),
        CombinatorInner::Invocation(i) => lower_invocation(i, ctx),
    }
}

fn lower_int_combinator(int_comb: &IntCombinator, endian: Endian) -> CombIR {
    match int_comb {
        IntCombinator::Unsigned(8) => CombIR::U8,
        IntCombinator::Unsigned(16) => CombIR::U16(endian),
        IntCombinator::Unsigned(24) => CombIR::U24(endian),
        IntCombinator::Unsigned(32) => CombIR::U32(endian),
        IntCombinator::Unsigned(64) => CombIR::U64(endian),
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
        Some(constraint) => CombIR::Refined {
            inner: Box::new(inner),
            predicate: PredicateIR::IntConstraint(constraint.clone()),
        },
        None => inner,
    }
}

fn lower_constraint_enum(comb: &ConstraintEnumCombinator, ctx: &CodegenCtx) -> CombIR {
    let _ = (comb, ctx);
    todo!("Enum constraint lowering is not implemented")
}

fn lower_struct(s: &StructCombinator, ctx: &CodegenCtx) -> CombIR {
    let fields = &s.0;

    if fields.is_empty() {
        return CombIR::Success;
    }

    let has_dependent = fields
        .iter()
        .any(|f| matches!(f, StructField::Dependent { .. }));

    if has_dependent {
        lower_struct_dependent(fields, ctx)
    } else {
        lower_struct_simple(fields, ctx)
    }
}

fn lower_struct_simple(fields: &[StructField], ctx: &CodegenCtx) -> CombIR {
    let combs = lower_struct_fields_preserve_labels(fields, ctx);
    match combs {
        CombIR::Tuple(mut elems) if elems.len() == 1 => elems.pop().unwrap().1,
        other => other,
    }
}

fn lower_struct_fields_preserve_labels(fields: &[StructField], ctx: &CodegenCtx) -> CombIR {
    CombIR::Tuple(
        fields
            .iter()
            .map(|field| {
                (
                    Some(struct_field_label(field)),
                    lower_struct_field(field, ctx),
                )
            })
            .collect(),
    )
}

fn lower_struct_dependent(fields: &[StructField], ctx: &CodegenCtx) -> CombIR {
    if fields.is_empty() {
        return CombIR::Success;
    }

    let first_dep_idx = fields
        .iter()
        .position(|f| matches!(f, StructField::Dependent { .. }))
        .unwrap_or(0);

    if first_dep_idx >= fields.len() - 1 {
        return lower_struct_simple(fields, ctx);
    }

    if first_dep_idx > 0 {
        let prefix = lower_struct_fields_preserve_labels(&fields[..first_dep_idx], ctx);
        let suffix = lower_struct(&StructCombinator(fields[first_dep_idx..].to_vec()), ctx);
        return concat_sequence(prefix, suffix);
    }

    let leading_dep_count = fields
        .iter()
        .take_while(|field| matches!(field, StructField::Dependent { .. }))
        .count();

    if leading_dep_count >= fields.len() {
        return lower_struct_simple(fields, ctx);
    }

    let dep_names: Vec<String> = fields[..leading_dep_count]
        .iter()
        .filter_map(|field| match field {
            StructField::Dependent { label, .. } => Some(label.clone()),
            _ => None,
        })
        .collect();

    let fst = if leading_dep_count == 1 {
        lower_struct_field(&fields[0], ctx)
    } else {
        lower_struct_simple(&fields[..leading_dep_count], ctx)
    };
    let snd_fields = &fields[leading_dep_count..];
    let snd_comb = if snd_fields.len() == 1 {
        lower_struct_fields_preserve_labels(snd_fields, ctx)
    } else {
        lower_struct(&StructCombinator(snd_fields.to_vec()), ctx)
    };

    let snd = if dep_names.is_empty() {
        DepCombIR::independent(snd_comb)
    } else {
        DepCombIR::dependent(snd_comb, dep_names)
    };

    CombIR::Pair {
        fst: Box::new(fst),
        snd: Box::new(snd),
    }
}

fn concat_sequence(prefix: CombIR, suffix: CombIR) -> CombIR {
    match prefix {
        CombIR::Success => suffix,
        CombIR::Tuple(mut elems) => {
            elems.push((None, suffix));
            CombIR::Tuple(elems)
        }
        other => CombIR::Tuple(vec![(None, other), (None, suffix)]),
    }
}

fn lower_struct_field(field: &StructField, ctx: &CodegenCtx) -> CombIR {
    match field {
        StructField::Ordinary { combinator, .. } | StructField::Dependent { combinator, .. } => {
            lower_combinator(combinator, ctx)
        }
        StructField::Const { combinator, .. } => lower_const_combinator(combinator, ctx),
    }
}

fn lower_wrap(w: &WrapCombinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_combinator(&w.combinator, ctx);

    let with_prior = if let Some(prior) = lower_const_sequence(&w.prior, ctx) {
        CombIR::Preceded {
            prefix: Box::new(prior),
            inner: Box::new(inner),
        }
    } else {
        inner
    };

    if let Some(post) = lower_const_sequence(&w.post, ctx) {
        CombIR::Terminated {
            inner: Box::new(with_prior),
            suffix: Box::new(post),
        }
    } else {
        with_prior
    }
}

fn lower_const_sequence(consts: &[ConstCombinator], ctx: &CodegenCtx) -> Option<CombIR> {
    if consts.is_empty() {
        return None;
    }

    let mut combs: Vec<(Option<String>, CombIR)> = consts
        .iter()
        .map(|c| (None, lower_const_combinator(c, ctx)))
        .collect();
    Some(if combs.len() == 1 {
        combs
            .pop()
            .expect("singleton const sequence has one element")
            .1
    } else {
        CombIR::Tuple(combs)
    })
}

fn struct_field_label(field: &StructField) -> String {
    match field {
        StructField::Ordinary { label, .. }
        | StructField::Const { label, .. }
        | StructField::Dependent { label, .. } => label.clone(),
    }
}

fn lower_enum(e: &EnumCombinator, ctx: &CodegenCtx) -> CombIR {
    match e {
        EnumCombinator::Exhaustive { enums, inferred } => {
            let inner = lower_int_combinator(inferred, ctx.endian);
            let valid_values: Vec<ConstraintElem> = enums
                .iter()
                .map(|e| ConstraintElem::Single(e.value))
                .collect();
            if valid_values.is_empty() {
                inner
            } else {
                CombIR::Refined {
                    inner: Box::new(inner),
                    predicate: PredicateIR::IntConstraint(IntConstraintIR::Set(valid_values)),
                }
            }
        }
        EnumCombinator::NonExhaustive { enums: _, inferred } => {
            lower_int_combinator(inferred, ctx.endian)
        }
    }
}

fn lower_choice(c: &ChoiceCombinator, ctx: &CodegenCtx) -> CombIR {
    if let Some(depend_id) = &c.depend_id {
        if let Some(choice) = lower_choice_with_tag(depend_id, &c.choices, ctx) {
            return choice;
        }
    }

    match &c.choices {
        Choices::Enums(choices) => lower_choice_combinators(choices, ctx),
        Choices::Ints(choices) => lower_choice_combinators(choices, ctx),
        Choices::Arrays(choices) => lower_choice_combinators(choices, ctx),
    }
}

fn lower_choice_combinators<T>(choices: &[(T, Combinator)], ctx: &CodegenCtx) -> CombIR {
    CombIR::Choice(
        choices
            .iter()
            .map(|(_, comb)| lower_combinator(comb, ctx))
            .collect(),
    )
}

fn lower_choice_with_tag(depend_id: &str, choices: &Choices, ctx: &CodegenCtx) -> Option<CombIR> {
    let tag = TagRef::Field(depend_id.to_string());

    let branches = match choices {
        Choices::Ints(choices) => lower_tagged_choices(choices, ctx, choice_int_tag_value),
        Choices::Arrays(choices) => lower_tagged_choices(choices, ctx, choice_array_tag_value),
        Choices::Enums(_) => None,
    }?;

    Some(CombIR::Dispatch { tag, branches })
}

fn lower_tagged_choices<T, F>(
    choices: &[(T, Combinator)],
    ctx: &CodegenCtx,
    tag_of: F,
) -> Option<Vec<(TagValue, CombIR)>>
where
    F: Fn(&T) -> Option<TagValue>,
{
    choices
        .iter()
        .map(|(tag, comb)| {
            let tag = tag_of(tag)?;
            Some((tag, lower_combinator(comb, ctx)))
        })
        .collect()
}

fn choice_int_tag_value(tag: &Option<ConstraintElem>) -> Option<TagValue> {
    match tag {
        Some(ConstraintElem::Single(v)) => Some(TagValue::Int(*v)),
        Some(ConstraintElem::Range { .. }) | None => None,
    }
}

fn choice_array_tag_value(tag: &ConstArray) -> Option<TagValue> {
    const_array_to_bytes(tag).map(TagValue::Bytes)
}

fn lower_vec(v: &VecCombinator, ctx: &CodegenCtx) -> CombIR {
    match v {
        VecCombinator::Vec(inner) => CombIR::Repeat(Box::new(lower_combinator(inner, ctx))),
    }
}

fn lower_array(a: &ArrayCombinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_combinator(&a.combinator, ctx);
    let count = a.len.clone();

    CombIR::RepeatN {
        inner: Box::new(inner),
        count,
    }
}

fn lower_bytes(b: &BytesCombinator, _ctx: &CodegenCtx) -> CombIR {
    match &b.len {
        LenExpr::Const(n) => CombIR::Fixed { len: *n },
        other => CombIR::Variable { len: other.clone() },
    }
}

fn lower_option(o: &OptionCombinator, ctx: &CodegenCtx) -> CombIR {
    CombIR::Opt(Box::new(lower_combinator(&o.0, ctx)))
}

fn lower_invocation(i: &CombinatorInvocation, _ctx: &CodegenCtx) -> CombIR {
    CombIR::Named {
        name: i.func.clone(),
        args: i.args.clone(),
    }
}

fn lower_const_combinator(c: &ConstCombinator, ctx: &CodegenCtx) -> CombIR {
    match c {
        ConstCombinator::ConstBytes(cb) => {
            let bytes = const_array_bytes(&cb.values);
            CombIR::Tag {
                inner: Box::new(CombIR::Fixed { len: cb.len }),
                value: TagValue::Bytes(bytes),
            }
        }
        ConstCombinator::ConstInt(ci) => {
            let inner = lower_int_combinator(&ci.combinator, ctx.endian);
            CombIR::Tag {
                inner: Box::new(inner),
                value: TagValue::Int(ci.value),
            }
        }
        ConstCombinator::ConstEnum(ce) => {
            let inner = lower_invocation(&ce.combinator, ctx);
            CombIR::Tag {
                inner: Box::new(inner),
                value: TagValue::Enum {
                    ty: ce.combinator.func.clone(),
                    variant: ce.variant.clone(),
                },
            }
        }
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
        ConstArray::Int(ints) => Some(ints.iter().map(|&i| i as u8).collect()),
        ConstArray::Repeat(val, count) => Some(vec![*val as u8; *count]),
        ConstArray::Wildcard => None,
    }
}
