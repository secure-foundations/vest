use std::collections::HashMap;

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

type EnumEnv = HashMap<String, String>;

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
            body: lower_combinator_in_env(combinator, ctx, &enum_env_from_params(param_defns, ctx)),
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
                ty: lower_combinator_inner_in_env(combinator, ctx, &EnumEnv::new()),
            }),
        })
        .collect()
}

fn lower_combinator_in_env(comb: &Combinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    let inner = lower_combinator_inner_in_env(&comb.inner, ctx, enum_env);

    match &comb.and_then {
        Some(next) => {
            let next_ir = lower_combinator_in_env(next, ctx, enum_env);
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

fn lower_combinator_inner_in_env(
    inner: &CombinatorInner,
    ctx: &CodegenCtx,
    enum_env: &EnumEnv,
) -> CombIR {
    match inner {
        CombinatorInner::ConstraintInt(c) => lower_constraint_int(c, ctx),
        CombinatorInner::ConstraintEnum(c) => lower_constraint_enum(c, ctx),
        CombinatorInner::Struct(s) => lower_struct_in_env(s, ctx, enum_env),
        CombinatorInner::Wrap(w) => lower_wrap_in_env(w, ctx, enum_env),
        CombinatorInner::Enum(e) => lower_enum(e, ctx),
        CombinatorInner::Choice(c) => lower_choice_in_env(c, ctx, enum_env),
        CombinatorInner::Vec(v) => lower_vec_in_env(v, ctx, enum_env),
        CombinatorInner::Array(a) => lower_array_in_env(a, ctx, enum_env),
        CombinatorInner::Bytes(b) => lower_bytes(b, ctx),
        CombinatorInner::Tail(_) => CombIR::Tail,
        CombinatorInner::Option(o) => lower_option_in_env(o, ctx, enum_env),
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

fn lower_struct_in_env(s: &StructCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    let fields = &s.0;

    if fields.is_empty() {
        return CombIR::Success;
    }

    let has_dependent = fields
        .iter()
        .any(|f| matches!(f, StructField::Dependent { .. }));

    if has_dependent {
        lower_struct_dependent(fields, ctx, enum_env)
    } else {
        lower_struct_simple(fields, ctx, enum_env)
    }
}

fn lower_struct_simple(fields: &[StructField], ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    let combs = lower_struct_fields_preserve_labels(fields, ctx, enum_env);
    match combs {
        CombIR::Tuple(mut elems) if elems.len() == 1 => elems.pop().unwrap().1,
        other => other,
    }
}

fn lower_struct_fields_preserve_labels(
    fields: &[StructField],
    ctx: &CodegenCtx,
    enum_env: &EnumEnv,
) -> CombIR {
    CombIR::Tuple(
        fields
            .iter()
            .map(|field| {
                (
                    Some(struct_field_label(field)),
                    lower_struct_field_in_env(field, ctx, enum_env),
                )
            })
            .collect(),
    )
}

fn lower_struct_dependent(fields: &[StructField], ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    if fields.is_empty() {
        return CombIR::Success;
    }

    let first_dep_idx = fields
        .iter()
        .position(|f| matches!(f, StructField::Dependent { .. }))
        .unwrap_or(0);

    if first_dep_idx >= fields.len() - 1 {
        return lower_struct_simple(fields, ctx, enum_env);
    }

    if first_dep_idx > 0 {
        let prefix = lower_struct_fields_preserve_labels(&fields[..first_dep_idx], ctx, enum_env);
        let suffix = lower_struct_in_env(
            &StructCombinator(fields[first_dep_idx..].to_vec()),
            ctx,
            enum_env,
        );
        return concat_sequence(prefix, suffix);
    }

    let leading_dep_count = fields
        .iter()
        .take_while(|field| matches!(field, StructField::Dependent { .. }))
        .count();

    if leading_dep_count >= fields.len() {
        return lower_struct_simple(fields, ctx, enum_env);
    }

    let dep_names: Vec<String> = fields[..leading_dep_count]
        .iter()
        .filter_map(|field| match field {
            StructField::Dependent { label, .. } => Some(label.clone()),
            _ => None,
        })
        .collect();

    let mut snd_enum_env = enum_env.clone();
    for field in &fields[..leading_dep_count] {
        if let Some((field_name, enum_name)) = field_enum_binding(field, ctx) {
            snd_enum_env.insert(field_name, enum_name);
        }
    }

    let fst = if leading_dep_count == 1 {
        lower_struct_field_in_env(&fields[0], ctx, enum_env)
    } else {
        lower_struct_simple(&fields[..leading_dep_count], ctx, enum_env)
    };
    let snd_fields = &fields[leading_dep_count..];
    let snd_comb = if snd_fields.len() == 1 {
        lower_struct_fields_preserve_labels(snd_fields, ctx, &snd_enum_env)
    } else {
        lower_struct_in_env(&StructCombinator(snd_fields.to_vec()), ctx, &snd_enum_env)
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

fn lower_struct_field_in_env(field: &StructField, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    match field {
        StructField::Ordinary { combinator, .. } | StructField::Dependent { combinator, .. } => {
            lower_combinator_in_env(combinator, ctx, enum_env)
        }
        StructField::Const { combinator, .. } => lower_const_combinator(combinator, ctx),
    }
}

fn lower_wrap_in_env(w: &WrapCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    let inner = lower_combinator_in_env(&w.combinator, ctx, enum_env);

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

fn field_enum_binding(field: &StructField, ctx: &CodegenCtx) -> Option<(String, String)> {
    let (label, combinator) = match field {
        StructField::Dependent { label, combinator }
        | StructField::Ordinary { label, combinator } => (label.clone(), combinator),
        StructField::Const { .. } => return None,
    };

    enum_binding_for_inner(label, &combinator.inner, ctx)
}

fn enum_env_from_params(params: &[ParamDefn], ctx: &CodegenCtx) -> EnumEnv {
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
        CombinatorInner::Invocation(invocation) if ctx.enum_names.contains(&invocation.func) => {
            Some((name, invocation.func.clone()))
        }
        CombinatorInner::ConstraintEnum(constraint) => {
            Some((name, constraint.combinator.func.clone()))
        }
        _ => None,
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
                CombIR::Enum {
                    inner: Box::new(CombIR::Refined {
                        inner: Box::new(inner),
                        predicate: PredicateIR::IntConstraint(IntConstraintIR::Set(valid_values)),
                    }),
                    variants: enums
                        .iter()
                        .map(|variant| (variant.name.clone(), variant.value))
                        .collect(),
                }
            }
        }
        EnumCombinator::NonExhaustive { enums: _, inferred } => {
            lower_int_combinator(inferred, ctx.endian)
        }
    }
}

fn lower_choice_in_env(c: &ChoiceCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    if let Some(depend_id) = &c.depend_id {
        if let Some(choice) = lower_choice_with_tag(depend_id, &c.choices, ctx, enum_env) {
            return choice;
        }
    }

    match &c.choices {
        Choices::Enums(choices) => lower_choice_combinators(choices, ctx, enum_env),
        Choices::Ints(choices) => lower_choice_combinators(choices, ctx, enum_env),
        Choices::Arrays(choices) => lower_choice_combinators(choices, ctx, enum_env),
    }
}

fn lower_choice_combinators<T>(
    choices: &[(T, Combinator)],
    ctx: &CodegenCtx,
    enum_env: &EnumEnv,
) -> CombIR {
    CombIR::Choice(
        choices
            .iter()
            .map(|(_, comb)| lower_combinator_in_env(comb, ctx, enum_env))
            .collect(),
    )
}

fn lower_choice_with_tag(
    depend_id: &str,
    choices: &Choices,
    ctx: &CodegenCtx,
    enum_env: &EnumEnv,
) -> Option<CombIR> {
    let tag = TagRef::Field(depend_id.to_string());

    let branches = match choices {
        Choices::Ints(choices) => {
            lower_tagged_choices(choices, ctx, enum_env, choice_int_tag_value)
        }
        Choices::Arrays(choices) => {
            lower_tagged_choices(choices, ctx, enum_env, choice_array_tag_value)
        }
        Choices::Enums(choices) => {
            let enum_ty = enum_env.get(depend_id)?;
            choices
                .iter()
                .map(|(variant, comb)| {
                    Some((
                        if variant == "_" {
                            TagValue::Wildcard
                        } else {
                            TagValue::Enum {
                                ty: enum_ty.clone(),
                                variant: variant.clone(),
                            }
                        },
                        lower_combinator_in_env(comb, ctx, enum_env),
                    ))
                })
                .collect()
        }
    }?;

    Some(CombIR::Dispatch { tag, branches })
}

fn lower_tagged_choices<T, F>(
    choices: &[(T, Combinator)],
    ctx: &CodegenCtx,
    enum_env: &EnumEnv,
    tag_of: F,
) -> Option<Vec<(TagValue, CombIR)>>
where
    F: Fn(&T) -> Option<TagValue>,
{
    choices
        .iter()
        .map(|(tag, comb)| {
            let tag = tag_of(tag)?;
            Some((tag, lower_combinator_in_env(comb, ctx, enum_env)))
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

fn lower_vec_in_env(v: &VecCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    match v {
        VecCombinator::Vec(inner) => {
            CombIR::Repeat(Box::new(lower_combinator_in_env(inner, ctx, enum_env)))
        }
    }
}

fn lower_array_in_env(a: &ArrayCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    let inner = lower_combinator_in_env(&a.combinator, ctx, enum_env);
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

fn lower_option_in_env(o: &OptionCombinator, ctx: &CodegenCtx, enum_env: &EnumEnv) -> CombIR {
    CombIR::Opt(Box::new(lower_combinator_in_env(&o.0, ctx, enum_env)))
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
