//! Lowering from VestIR to CombIR.

use crate::vestir::{
    self, ArrayCombinator, BytesCombinator, ChoiceCombinator, Choices, Combinator, CombinatorInner,
    CombinatorInvocation, ConstArray, ConstCombinator, ConstraintElem, ConstraintEnumCombinator,
    ConstraintIntCombinator, Definition, EnumCombinator, IntCombinator, OptionCombinator,
    ParamDefn, StructCombinator, StructField, VecCombinator, WrapCombinator,
};

use super::combir::{
    CodegenCtx, CombDef, CombIR, DepCombIR, Endian, IntConstraintIR, LenExpr, ParamDef,
    PredicateIR, TagRef, TagValue,
};

/// Lower a list of VestIR definitions to CombIR definitions.
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

/// Lower a single VestIR definition to a CombIR definition.
fn lower_definition(def: &Definition, ctx: &CodegenCtx) -> Option<CombDef> {
    match def {
        Definition::Combinator {
            name,
            param_defns,
            combinator,
        } => {
            let params = lower_param_defns(param_defns, ctx);
            let body = lower_combinator(combinator, ctx);
            Some(CombDef {
                name: name.clone(),
                params,
                body,
                is_const: false,
            })
        }
        Definition::ConstCombinator {
            name,
            const_combinator,
        } => {
            let body = lower_const_combinator(const_combinator, ctx);
            Some(CombDef {
                name: name.clone(),
                params: Vec::new(),
                body,
                is_const: true,
            })
        }
        Definition::Endianess(_) => None, // Already handled in first pass
    }
}

/// Lower parameter definitions.
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

/// Lower a combinator (with optional and_then chaining).
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

/// Lower a combinator inner (the main combinator without and_then).
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

/// Lower an integer combinator.
fn lower_int_combinator(int_comb: &IntCombinator, endian: Endian) -> CombIR {
    match int_comb {
        IntCombinator::Unsigned(8) => CombIR::U8,
        IntCombinator::Unsigned(16) => CombIR::U16(endian),
        IntCombinator::Unsigned(24) => CombIR::U24(endian),
        IntCombinator::Unsigned(32) => CombIR::U32(endian),
        IntCombinator::Unsigned(64) => CombIR::U64(endian),
        IntCombinator::Unsigned(n) => {
            todo!("Unsupported unsigned integer size lowering is incomplete: {}", n)
        }
        IntCombinator::Signed(_) => todo!("Signed integer lowering is not implemented"),
        IntCombinator::BtcVarint => todo!("BtcVarint lowering is not implemented"),
        IntCombinator::ULEB128 => todo!("ULEB128 lowering is not implemented"),
    }
}

/// Lower a constraint integer combinator.
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

/// Lower a constraint enum combinator.
fn lower_constraint_enum(comb: &ConstraintEnumCombinator, ctx: &CodegenCtx) -> CombIR {
    let _ = (comb, ctx);
    todo!("Enum constraint lowering is not implemented")
}

/// Lower a struct combinator.
fn lower_struct(s: &StructCombinator, ctx: &CodegenCtx) -> CombIR {
    let fields = &s.0;

    if fields.is_empty() {
        return CombIR::Success;
    }

    // Check if we have any dependent fields
    let has_dependent = fields
        .iter()
        .any(|f| matches!(f, StructField::Dependent { .. }));

    if has_dependent {
        // Need to use Pair for dependency handling
        lower_struct_dependent(fields, ctx)
    } else {
        // Can use simple tuple
        lower_struct_simple(fields, ctx)
    }
}

/// Lower a simple struct (no dependencies) to a tuple.
fn lower_struct_simple(fields: &[StructField], ctx: &CodegenCtx) -> CombIR {
    let combs: Vec<CombIR> = fields
        .iter()
        .filter_map(|field| match field {
            StructField::Ordinary { combinator, .. } => Some(lower_combinator(combinator, ctx)),
            StructField::Const { combinator, .. } => Some(lower_const_combinator(combinator, ctx)),
            StructField::Dependent { combinator, .. } => Some(lower_combinator(combinator, ctx)),
        })
        .collect();

    if combs.len() == 1 {
        combs.into_iter().next().unwrap()
    } else {
        CombIR::Tuple(combs)
    }
}

/// Lower a struct with dependent fields using Pair.
fn lower_struct_dependent(fields: &[StructField], ctx: &CodegenCtx) -> CombIR {
    if fields.is_empty() {
        return CombIR::Success;
    }

    let split_idx = fields
        .iter()
        .position(|f| matches!(f, StructField::Dependent { .. }))
        .unwrap_or(0);

    if split_idx >= fields.len() - 1 {
        return lower_struct_simple(fields, ctx);
    }

    if split_idx > 0 {
        let prefix = lower_struct_simple(&fields[..split_idx], ctx);
        let suffix = lower_struct(&StructCombinator(fields[split_idx..].to_vec()), ctx);
        return concat_sequence(prefix, suffix);
    }

    let dep_count = fields
        .iter()
        .take_while(|field| matches!(field, StructField::Dependent { .. }))
        .count();

    if dep_count >= fields.len() {
        return lower_struct_simple(fields, ctx);
    }

    let dep_names: Vec<String> = fields[..dep_count]
        .iter()
        .filter_map(|field| match field {
            StructField::Dependent { label, .. } => Some(label.clone()),
            _ => None,
        })
        .collect();

    let fst = if dep_count == 1 {
        lower_struct_field(&fields[0], ctx)
    } else {
        lower_struct_simple(&fields[..dep_count], ctx)
    };
    let snd_fields = &fields[dep_count..];
    let snd_comb = if snd_fields.len() == 1 {
        lower_struct_field(&snd_fields[0], ctx)
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
            elems.push(suffix);
            CombIR::Tuple(elems)
        }
        other => CombIR::Tuple(vec![other, suffix]),
    }
}

/// Lower a single struct field.
fn lower_struct_field(field: &StructField, ctx: &CodegenCtx) -> CombIR {
    match field {
        StructField::Ordinary { combinator, .. } | StructField::Dependent { combinator, .. } => {
            lower_combinator(combinator, ctx)
        }
        StructField::Const { combinator, .. } => lower_const_combinator(combinator, ctx),
    }
}

/// Lower a wrap combinator.
fn lower_wrap(w: &WrapCombinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_combinator(&w.combinator, ctx);

    // Handle prior (preceded) combinators
    let with_prior = if w.prior.is_empty() {
        inner
    } else {
        let prior_combs: Vec<CombIR> = w
            .prior
            .iter()
            .map(|c| lower_const_combinator(c, ctx))
            .collect();
        let prior = if prior_combs.len() == 1 {
            prior_combs.into_iter().next().unwrap()
        } else {
            CombIR::Tuple(prior_combs)
        };
        CombIR::Preceded {
            prefix: Box::new(prior),
            inner: Box::new(inner),
        }
    };

    // Handle post (terminated) combinators
    if w.post.is_empty() {
        with_prior
    } else {
        let post_combs: Vec<CombIR> = w
            .post
            .iter()
            .map(|c| lower_const_combinator(c, ctx))
            .collect();
        let post = if post_combs.len() == 1 {
            post_combs.into_iter().next().unwrap()
        } else {
            CombIR::Tuple(post_combs)
        };
        CombIR::Terminated {
            inner: Box::new(with_prior),
            suffix: Box::new(post),
        }
    }
}

/// Lower an enum combinator.
fn lower_enum(e: &EnumCombinator, ctx: &CodegenCtx) -> CombIR {
    // For now, enums are mapped to a refined integer with the valid values
    match e {
        EnumCombinator::Exhaustive { enums, inferred } => {
            let inner = lower_int_combinator(inferred, ctx.endian);
            // Create a constraint for valid enum values
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
            // Non-exhaustive enums just use the underlying integer type
            lower_int_combinator(inferred, ctx.endian)
        }
    }
}

/// Lower a choice combinator.
fn lower_choice(c: &ChoiceCombinator, ctx: &CodegenCtx) -> CombIR {
    if let Some(depend_id) = &c.depend_id {
        if let Some(choice) = lower_choice_with_tag(depend_id, &c.choices, ctx) {
            return choice;
        }
    }

    match &c.choices {
        Choices::Enums(choices) => CombIR::Choice(
            choices
                .iter()
                .map(|(_, comb)| lower_combinator(comb, ctx))
                .collect(),
        ),
        Choices::Ints(choices) => CombIR::Choice(
            choices
                .iter()
                .map(|(_, comb)| lower_combinator(comb, ctx))
                .collect(),
        ),
        Choices::Arrays(choices) => CombIR::Choice(
            choices
                .iter()
                .map(|(_, comb)| lower_combinator(comb, ctx))
                .collect(),
        ),
    }
}

fn lower_choice_with_tag(depend_id: &str, choices: &Choices, ctx: &CodegenCtx) -> Option<CombIR> {
    let tag = TagRef::Field(depend_id.to_string());

    let branches = match choices {
        Choices::Ints(choices) => choices
            .iter()
            .map(|(tag, comb)| {
                let value = match tag {
                    Some(ConstraintElem::Single(v)) => TagValue::Int(*v),
                    Some(ConstraintElem::Range { .. }) | None => return None,
                };
                Some((value, lower_combinator(comb, ctx)))
            })
            .collect::<Option<Vec<_>>>(),
        Choices::Arrays(choices) => choices
            .iter()
            .map(|(tag, comb)| {
                let value = match tag {
                    ConstArray::Char(bytes) => TagValue::Bytes(bytes.clone()),
                    ConstArray::Int(ints) => {
                        TagValue::Bytes(ints.iter().map(|&i| i as u8).collect())
                    }
                    ConstArray::Repeat(v, count) => TagValue::Bytes(vec![*v as u8; *count]),
                    ConstArray::Wildcard => return None,
                };
                Some((value, lower_combinator(comb, ctx)))
            })
            .collect::<Option<Vec<_>>>(),
        Choices::Enums(_) => None,
    }?;

    Some(CombIR::Dispatch { tag, branches })
}

/// Lower a vec combinator.
fn lower_vec(v: &VecCombinator, ctx: &CodegenCtx) -> CombIR {
    match v {
        VecCombinator::Vec(inner) => CombIR::Repeat(Box::new(lower_combinator(inner, ctx))),
    }
}

/// Lower an array combinator.
fn lower_array(a: &ArrayCombinator, ctx: &CodegenCtx) -> CombIR {
    let inner = lower_combinator(&a.combinator, ctx);
    let count = a.len.clone();

    CombIR::RepeatN {
        inner: Box::new(inner),
        count,
    }
}

/// Lower a bytes combinator.
fn lower_bytes(b: &BytesCombinator, _ctx: &CodegenCtx) -> CombIR {
    match &b.len {
        LenExpr::Const(n) => CombIR::Fixed { len: *n },
        other => CombIR::Variable { len: other.clone() },
    }
}

/// Lower an option combinator.
fn lower_option(o: &OptionCombinator, ctx: &CodegenCtx) -> CombIR {
    CombIR::Opt(Box::new(lower_combinator(&o.0, ctx)))
}

/// Lower a combinator invocation.
fn lower_invocation(i: &CombinatorInvocation, _ctx: &CodegenCtx) -> CombIR {
    CombIR::Named {
        name: i.func.clone(),
        args: i.args.clone(),
    }
}

/// Lower a const combinator.
fn lower_const_combinator(c: &ConstCombinator, ctx: &CodegenCtx) -> CombIR {
    match c {
        ConstCombinator::ConstBytes(cb) => {
            // Constant bytes are tags
            let bytes = match &cb.values {
                ConstArray::Char(b) => b.clone(),
                ConstArray::Int(ints) => ints.iter().map(|&i| i as u8).collect(),
                ConstArray::Repeat(val, count) => vec![*val as u8; *count],
                ConstArray::Wildcard => Vec::new(),
            };
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
