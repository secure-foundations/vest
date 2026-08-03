//! Frontend normalization and encoding-rule variant expansion.

use super::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

pub(super) fn expand_rule_variants(
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

    let mut needed = BTreeSet::<(String, EncodingRules)>::new();
    let mut pending = VecDeque::new();
    for definition in &definitions {
        let rule = overrides
            .get(&definition.name)
            .copied()
            .unwrap_or(default_rule);
        if needed.insert((definition.name.clone(), rule)) {
            pending.push_back((definition.name.clone(), rule));
        }
    }

    while let Some((name, rule)) = pending.pop_front() {
        let definition = by_name[&name];
        let mut references = Vec::new();
        collect_type_refs(&definition.ty, &mut references);
        for reference in references {
            if !by_name.contains_key(reference) {
                return Err(CodegenError::new(
                    &name,
                    format!("unknown ASN.1 type reference `{reference}`"),
                ));
            }
            let target_rule = overrides.get(reference).copied().unwrap_or(rule);
            if needed.insert((reference.to_string(), target_rule)) {
                pending.push_back((reference.to_string(), target_rule));
            }
        }
    }

    let mut rules_by_name = BTreeMap::<String, BTreeSet<EncodingRules>>::new();
    for (name, rule) in &needed {
        rules_by_name.entry(name.clone()).or_default().insert(*rule);
    }

    let mut used_names = definitions
        .iter()
        .map(|definition| definition.name.clone())
        .collect::<BTreeSet<_>>();
    let mut variant_names = BTreeMap::<(String, EncodingRules), String>::new();
    for definition in &definitions {
        let root_rule = overrides
            .get(&definition.name)
            .copied()
            .unwrap_or(default_rule);
        for rule in &rules_by_name[&definition.name] {
            let generated = if *rule == root_rule {
                definition.name.clone()
            } else {
                let suffix = match rule {
                    EncodingRules::Der => "der",
                    EncodingRules::Ber => "ber",
                };
                let base = format!("{}-{suffix}", definition.name);
                let mut candidate = base.clone();
                let mut index = 2usize;
                while !used_names.insert(candidate.clone()) {
                    candidate = format!("{base}-{index}");
                    index += 1;
                }
                candidate
            };
            variant_names.insert((definition.name.clone(), *rule), generated);
        }
    }

    let mut expanded = Vec::new();
    let mut rules = BTreeMap::new();
    for definition in &definitions {
        let root_rule = overrides
            .get(&definition.name)
            .copied()
            .unwrap_or(default_rule);
        let mut variants = rules_by_name[&definition.name]
            .iter()
            .copied()
            .collect::<Vec<_>>();
        variants.sort_by_key(|rule| (*rule != root_rule, *rule));
        for rule in variants {
            let name = variant_names[&(definition.name.clone(), rule)].clone();
            let ty = rewrite_rule_refs(&definition.ty, rule, overrides, &variant_names)?;
            rules.insert(name.clone(), rule);
            expanded.push(Definition { name, ty });
        }
    }

    let values = values
        .iter()
        .map(|assignment| {
            Ok(SchemaValueAssignment {
                name: assignment.name.clone(),
                ty: rewrite_rule_refs(&assignment.ty, default_rule, overrides, &variant_names)?,
                value: assignment.value.clone(),
            })
        })
        .collect::<Result<Vec<_>, CodegenError>>()?;

    Ok((expanded, rules, values))
}

pub(super) fn rewrite_rule_refs(
    ty: &Type,
    rule: EncodingRules,
    overrides: &BTreeMap<String, EncodingRules>,
    variant_names: &BTreeMap<(String, EncodingRules), String>,
) -> Result<Type, CodegenError> {
    Ok(match ty {
        Type::TypeRef(name) => {
            let target_rule = overrides.get(name).copied().unwrap_or(rule);
            let target = variant_names
                .get(&(name.clone(), target_rule))
                .ok_or_else(|| {
                    CodegenError::new(
                        name,
                        format!(
                            "missing {} variant while expanding encoding rules",
                            target_rule.display()
                        ),
                    )
                })?
                .clone();
            Type::TypeRef(target)
        }
        Type::Sequence(fields) | Type::Set(fields) => {
            let rewritten = fields
                .iter()
                .map(|field| {
                    Ok(SequenceField {
                        name: field.name.clone(),
                        ty: rewrite_rule_refs(&field.ty, rule, overrides, variant_names)?,
                        optional: field.optional,
                        default: field.default.clone(),
                    })
                })
                .collect::<Result<Vec<_>, CodegenError>>()?;
            if matches!(ty, Type::Sequence(_)) {
                Type::Sequence(rewritten)
            } else {
                Type::Set(rewritten)
            }
        }
        Type::Choice(variants) => Type::Choice(
            variants
                .iter()
                .map(|variant| {
                    Ok(ChoiceVariant {
                        name: variant.name.clone(),
                        ty: rewrite_rule_refs(&variant.ty, rule, overrides, variant_names)?,
                    })
                })
                .collect::<Result<Vec<_>, CodegenError>>()?,
        ),
        Type::SequenceOf(inner, constraint) => Type::SequenceOf(
            Box::new(rewrite_rule_refs(inner, rule, overrides, variant_names)?),
            constraint.clone(),
        ),
        Type::SetOf(inner, constraint) => Type::SetOf(
            Box::new(rewrite_rule_refs(inner, rule, overrides, variant_names)?),
            constraint.clone(),
        ),
        Type::Tagged { tag, inner } => Type::Tagged {
            tag: tag.clone(),
            inner: Box::new(rewrite_rule_refs(inner, rule, overrides, variant_names)?),
        },
        Type::Constrained {
            base_type,
            constraint,
        } => Type::Constrained {
            base_type: Box::new(rewrite_rule_refs(
                base_type,
                rule,
                overrides,
                variant_names,
            )?),
            constraint: constraint.clone(),
        },
        _ => ty.clone(),
    })
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
