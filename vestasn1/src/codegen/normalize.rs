//! Frontend normalization and definition-global encoding-rule assignment.

use super::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub(super) fn assign_definition_rules(
    definitions: Vec<Definition>,
    values: &[SchemaValueAssignment],
    default_rule: EncodingRules,
    overrides: &BTreeMap<String, EncodingRules>,
) -> Result<
    (
        Vec<Definition>,
        BTreeMap<String, EncodingRules>,
        Vec<SchemaValueAssignment>,
    ),
    CodegenError,
> {
    let by_name = definitions
        .iter()
        .map(|definition| (definition.name.clone(), definition))
        .collect::<BTreeMap<_, _>>();
    for name in overrides.keys() {
        if !by_name.contains_key(name) {
            return Err(CodegenError::new(
                name,
                "encoding-rule override names an unknown ASN.1 definition",
            ));
        }
    }
    for definition in &definitions {
        let mut references = Vec::new();
        collect_type_refs(&definition.ty, &mut references);
        for reference in references {
            if !by_name.contains_key(reference) {
                return Err(CodegenError::new(
                    &definition.name,
                    format!("unknown ASN.1 type reference `{reference}`"),
                ));
            }
        }
    }

    // An override colors its definition and its transitive dependencies. Rules do not propagate
    // backwards to parents: an ordinary BER definition may therefore contain a DER child. Keep
    // one assignment per ASN.1 definition instead of specializing a shared definition once per
    // incoming rule context.
    let mut assigned = BTreeMap::<String, (EncodingRules, String)>::new();
    let mut pending = VecDeque::new();
    for (name, rule) in overrides {
        assigned.insert(name.clone(), (*rule, name.clone()));
        pending.push_back(name.clone());
    }

    while let Some(name) = pending.pop_front() {
        let (rule, origin) = assigned[&name].clone();
        let definition = by_name[&name];
        let mut references = Vec::new();
        collect_type_refs(&definition.ty, &mut references);
        for reference in references {
            // An explicit override is a rule boundary and has already seeded its own traversal.
            if overrides.contains_key(reference) {
                continue;
            }
            match assigned.get(reference) {
                Some((previous, previous_origin)) if *previous != rule => {
                    return Err(CodegenError::new(
                        reference,
                        format!(
                            "conflicting transitive encoding rules: override `{previous_origin}` requires {} while override `{origin}` requires {}",
                            previous.display(),
                            rule.display(),
                        ),
                    ));
                }
                Some(_) => {}
                None => {
                    assigned.insert(reference.to_string(), (rule, origin.clone()));
                    pending.push_back(reference.to_string());
                }
            }
        }
    }

    let rules = definitions
        .iter()
        .map(|definition| {
            let rule = assigned
                .get(&definition.name)
                .map(|(rule, _origin)| *rule)
                .unwrap_or(default_rule);
            (definition.name.clone(), rule)
        })
        .collect::<BTreeMap<_, _>>();

    // DER is recursively canonical. A BER child would make a nominally DER parent accept or emit
    // a non-DER encoding. BER parents may contain DER children because DER is a BER subset.
    for definition in &definitions {
        if rules[&definition.name] != EncodingRules::Der {
            continue;
        }
        let mut references = Vec::new();
        collect_type_refs(&definition.ty, &mut references);
        for reference in references {
            if rules[reference] == EncodingRules::Ber {
                return Err(CodegenError::new(
                    &definition.name,
                    format!(
                        "DER definition depends on BER definition `{reference}`; override the dependency to DER or make the parent BER",
                    ),
                ));
            }
        }
    }

    Ok((definitions, rules, values.to_vec()))
}

pub(super) fn normalize_definitions(module: &Module) -> Result<Vec<Definition>, CodegenError> {
    let mut used = module
        .definitions
        .iter()
        .map(|definition| definition.name.clone())
        .collect::<BTreeSet<_>>();
    if used.len() != module.definitions.len() {
        return Err(CodegenError::new(
            &module.name,
            "duplicate ASN.1 type definition",
        ));
    }

    let mut result = Vec::new();
    for definition in &module.definitions {
        let mut synthetics = Vec::new();
        let ty = lower_root_type(&definition.ty, &definition.name, &mut synthetics, &mut used)?;
        result.extend(synthetics);
        result.push(Definition {
            name: definition.name.clone(),
            ty,
        });
    }
    Ok(result)
}

pub(super) fn lower_root_type(
    ty: &Type,
    parent: &str,
    synthetics: &mut Vec<Definition>,
    used: &mut BTreeSet<String>,
) -> Result<Type, CodegenError> {
    Ok(match ty {
        Type::Sequence(fields) | Type::Set(fields) => {
            let lowered = fields
                .iter()
                .map(|field| {
                    let hint = format!("{parent}-{}", field.name);
                    Ok(SequenceField {
                        name: field.name.clone(),
                        ty: lower_child_type(&field.ty, &hint, synthetics, used)?,
                        optional: field.optional,
                        default: field.default.clone(),
                    })
                })
                .collect::<Result<Vec<_>, CodegenError>>()?;
            if matches!(ty, Type::Sequence(_)) {
                Type::Sequence(lowered)
            } else {
                Type::Set(lowered)
            }
        }
        Type::Choice(variants) => Type::Choice(
            variants
                .iter()
                .map(|variant| {
                    let hint = format!("{parent}-{}", variant.name);
                    Ok(ChoiceVariant {
                        name: variant.name.clone(),
                        ty: lower_child_type(&variant.ty, &hint, synthetics, used)?,
                    })
                })
                .collect::<Result<Vec<_>, CodegenError>>()?,
        ),
        Type::SequenceOf(inner, constraint) => Type::SequenceOf(
            Box::new(lower_child_type(
                inner,
                &format!("{parent}-item"),
                synthetics,
                used,
            )?),
            constraint.clone(),
        ),
        Type::SetOf(inner, constraint) => Type::SetOf(
            Box::new(lower_child_type(
                inner,
                &format!("{parent}-item"),
                synthetics,
                used,
            )?),
            constraint.clone(),
        ),
        Type::Tagged { tag, inner } => Type::Tagged {
            tag: tag.clone(),
            inner: Box::new(lower_child_type(inner, parent, synthetics, used)?),
        },
        Type::Constrained {
            base_type,
            constraint,
        } => Type::Constrained {
            base_type: Box::new(lower_child_type(base_type, parent, synthetics, used)?),
            constraint: constraint.clone(),
        },
        _ => ty.clone(),
    })
}

pub(super) fn lower_child_type(
    ty: &Type,
    hint: &str,
    synthetics: &mut Vec<Definition>,
    used: &mut BTreeSet<String>,
) -> Result<Type, CodegenError> {
    match ty {
        Type::Sequence(_) | Type::Set(_) | Type::Choice(_) | Type::Enumerated(_) => {
            if !used.insert(hint.to_string()) {
                return Err(CodegenError::new(
                    hint,
                    "generated helper type name collides with an ASN.1 definition",
                ));
            }
            let lowered = lower_root_type(ty, hint, synthetics, used)?;
            synthetics.push(Definition {
                name: hint.to_string(),
                ty: lowered,
            });
            Ok(Type::TypeRef(hint.to_string()))
        }
        _ => lower_root_type(ty, hint, synthetics, used),
    }
}

pub(super) fn collect_type_refs<'a>(ty: &'a Type, output: &mut Vec<&'a str>) {
    match ty {
        Type::Sequence(fields) | Type::Set(fields) => {
            for field in fields {
                collect_type_refs(&field.ty, output);
            }
        }
        Type::SequenceOf(inner, _)
        | Type::SetOf(inner, _)
        | Type::Tagged { inner, .. }
        | Type::Constrained {
            base_type: inner, ..
        } => collect_type_refs(inner, output),
        Type::Choice(variants) => {
            for variant in variants {
                collect_type_refs(&variant.ty, output);
            }
        }
        Type::TypeRef(name) => output.push(name),
        _ => {}
    }
}
