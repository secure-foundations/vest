//! Schema analysis, lifetime inference, and validation.

use super::*;

impl<'a> Generator<'a> {
    pub(super) fn definition(&self, name: &str) -> Result<&Definition, CodegenError> {
        self.definition_index
            .get(name)
            .map(|index| &self.definitions[*index])
            .ok_or_else(|| {
                CodegenError::new(name, format!("unknown ASN.1 type reference `{name}`"))
            })
    }

    pub(super) fn compute_lifetimes(&mut self) -> Result<(), CodegenError> {
        for definition in &self.definitions {
            let borrows = self.type_borrows(
                &definition.ty,
                &mut BTreeSet::new(),
                self.rules[&definition.name],
            )?;
            self.borrows.insert(definition.name.clone(), borrows);
        }
        Ok(())
    }

    pub(super) fn type_borrows(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
    ) -> Result<bool, CodegenError> {
        Ok(match ty {
            Type::Integer(_, _) | Type::Real | Type::GeneralizedTime => true,
            Type::OctetString(_)
            | Type::BitString(_)
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::TeletexString(_)
            | Type::Any => rule == EncodingRules::Der,
            Type::NumericString(_) => rule == EncodingRules::Der,
            Type::BmpString(_) => false,
            Type::Sequence(fields) | Type::Set(fields) => {
                let mut borrows = false;
                for field in fields {
                    borrows |= self.type_borrows(&field.ty, visiting, rule)?;
                }
                borrows
            }
            Type::Choice(variants) => {
                let mut borrows = false;
                for variant in variants {
                    borrows |= self.type_borrows(&variant.ty, visiting, rule)?;
                }
                borrows
            }
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) | Type::Tagged { inner, .. } => {
                self.type_borrows(inner, visiting, rule)?
            }
            Type::Constrained {
                base_type: inner,
                constraint,
            } => {
                if matches!(inner.as_ref(), Type::Integer(None, _))
                    && integer_repr(integer_value_bounds(constraint, "INTEGER")?)
                        != IntegerRepr::General
                {
                    false
                } else {
                    self.type_borrows(inner, visiting, rule)?
                }
            }
            Type::TypeRef(name) => {
                if let Some(value) = self.borrows.get(name) {
                    *value
                } else {
                    if !visiting.insert(name.clone()) {
                        return Err(CodegenError::new(
                            name,
                            "recursive ASN.1 definitions require a VPS fixpoint combinator",
                        ));
                    }
                    let value =
                        self.type_borrows(&self.definition(name)?.ty, visiting, self.rules[name])?;
                    visiting.remove(name);
                    value
                }
            }
            Type::Boolean
            | Type::Null
            | Type::UtcTime
            | Type::Enumerated(_)
            | Type::ObjectIdentifier => false,
            Type::UniversalString(_) => false,
            Type::RelativeOid
            | Type::GeneralString(_)
            | Type::VisibleString(_)
            | Type::AnyDefinedBy(_)
            | Type::Class(_) => false,
        })
    }

    pub(super) fn validate(&self) -> Result<(), CodegenError> {
        for definition in &self.definitions {
            self.validate_type(
                &definition.ty,
                &definition.name,
                self.rules[&definition.name],
            )?;
        }

        let mut visiting = BTreeSet::new();
        let mut visited = BTreeSet::new();
        for definition in &self.definitions {
            self.detect_cycle(
                &definition.name,
                &mut visiting,
                &mut visited,
                &mut Vec::new(),
            )?;
        }

        let mut value_names = BTreeSet::new();
        for assignment in &self.values {
            if !value_names.insert(assignment.name.as_str()) {
                return Err(CodegenError::new(
                    &assignment.name,
                    "duplicate ASN.1 value assignment",
                ));
            }
            self.validate_value_assignment(assignment)?;
        }
        Ok(())
    }

    pub(super) fn validate_type(
        &self,
        ty: &Type,
        path: &str,
        rule: EncodingRules,
    ) -> Result<(), CodegenError> {
        match ty {
            Type::Sequence(fields) | Type::Set(fields) => {
                let mut rust_fields = BTreeMap::<String, String>::new();
                for field in fields {
                    let rust_name = rust_field_name(&field.name);
                    if let Some(previous) =
                        rust_fields.insert(rust_name.clone(), field.name.clone())
                    {
                        return Err(CodegenError::new(
                            path,
                            format!(
                                "fields `{previous}` and `{}` both generate Rust field `{rust_name}`",
                                field.name
                            ),
                        ));
                    }
                    let field_path = format!("{path}.{}", field.name);
                    self.validate_type(&field.ty, &field_path, rule)?;
                    if let Some(default) = &field.default {
                        self.render_default(&field.ty, default, &field_path)?;
                    }
                }
                self.validate_sequence_dispatch(fields, path, rule)?;
                if matches!(ty, Type::Set(_)) {
                    if rule != EncodingRules::Der {
                        return Err(CodegenError::new(
                            path,
                            "heterogeneous SET is supported only for DER schemas whose fields are already in canonical tag order",
                        ));
                    }
                    self.validate_set_order(fields, path, rule)?;
                }
            }
            Type::SequenceOf(inner, constraint) | Type::SetOf(inner, constraint) => {
                if let Some(constraint) = constraint {
                    legacy_size_bounds(constraint, path)?;
                }
                self.validate_type(inner, &format!("{path}[]"), rule)?;
            }
            Type::Choice(variants) => {
                if variants.is_empty() {
                    return Err(CodegenError::new(path, "an empty CHOICE has no encoding"));
                }
                let mut rust_variants = BTreeMap::<String, String>::new();
                let mut seen = TagDomain::Finite(BTreeSet::new());
                for variant in variants {
                    let rust_name = rust_variant_name(&variant.name);
                    if let Some(previous) =
                        rust_variants.insert(rust_name.clone(), variant.name.clone())
                    {
                        return Err(CodegenError::new(
                            path,
                            format!(
                                "variants `{previous}` and `{}` both generate Rust variant `{rust_name}`",
                                variant.name
                            ),
                        ));
                    }
                    let variant_path = format!("{path}.{}", variant.name);
                    self.validate_type(&variant.ty, &variant_path, rule)?;
                    if variants.len() > 1
                        && self.tag_shape(&variant.ty, &mut BTreeSet::new(), rule)?
                            == TagShape::Untagged
                    {
                        return Err(CodegenError::new(
                            &variant_path,
                            "an untagged CHOICE/open-type alternative must be explicitly tagged before it can participate in another CHOICE",
                        ));
                    }
                    let domain = self.tag_domain(&variant.ty, &mut BTreeSet::new(), rule)?;
                    if domains_overlap(&seen, &domain) {
                        return Err(CodegenError::new(
                            &variant_path,
                            "CHOICE alternative overlaps the tag domain of an earlier alternative",
                        ));
                    }
                    seen = union_domains(seen, domain);
                }
            }
            Type::TypeRef(name) => {
                self.definition(name)?;
            }
            Type::Integer(constraint, _) => {
                if constraint.is_some() {
                    return Err(CodegenError::new(
                        path,
                        "value-constrained INTEGER is not supported yet",
                    ));
                }
            }
            Type::Enumerated(values) => self.validate_enumerated(values, path)?,
            Type::OctetString(constraint) => {
                if let Some(constraint) = constraint {
                    legacy_size_bounds(constraint, path)?;
                }
            }
            Type::Utf8String(constraint)
            | Type::PrintableString(constraint)
            | Type::IA5String(constraint)
            | Type::TeletexString(constraint)
            | Type::BmpString(constraint) => {
                if let Some(constraint) = constraint {
                    legacy_size_bounds(constraint, path)?;
                }
            }
            Type::NumericString(constraint) | Type::UniversalString(constraint) => {
                if let Some(constraint) = constraint {
                    legacy_size_bounds(constraint, path)?;
                }
            }
            Type::BitString(constraint) => {
                if constraint.is_some() {
                    return Err(CodegenError::new(path, "BIT STRING SIZE constraints need a bit-length predicate and are not supported yet"));
                }
            }
            Type::Tagged { inner, .. } => self.validate_type(inner, path, rule)?,
            Type::Constrained {
                base_type,
                constraint,
            } => {
                self.validate_type(base_type, path, rule)?;
                match base_type.as_ref() {
                    Type::OctetString(None)
                    | Type::Utf8String(None)
                    | Type::PrintableString(None)
                    | Type::IA5String(None)
                    | Type::TeletexString(None)
                    | Type::BmpString(None)
                    | Type::NumericString(None)
                    | Type::UniversalString(None) => {
                        string_size_bounds(constraint, path)?;
                    }
                    Type::Integer(None, _) => {
                        integer_value_bounds(constraint, path)?;
                    }
                    _ => {
                        return Err(CodegenError::new(
                            path,
                            "only direct string SIZE and INTEGER range constraints are supported yet",
                        ));
                    }
                }
            }
            Type::RelativeOid => return self.unsupported(path, "RELATIVE-OID"),
            Type::GeneralString(_) => return self.unsupported(path, "GeneralString"),
            Type::VisibleString(_) => return self.unsupported(path, "VisibleString"),
            Type::AnyDefinedBy(_) => {
                return Err(CodegenError::new(
                    path,
                    "ANY DEFINED BY needs an information-object dispatch table and is not supported yet",
                ));
            }
            Type::Class(_) => {
                return Err(CodegenError::new(
                    path,
                    "ASN.1 information object classes are schema metadata, not encodable value types",
                ));
            }
            Type::Real
            | Type::ObjectIdentifier
            | Type::Any
            | Type::Boolean
            | Type::Null
            | Type::UtcTime
            | Type::GeneralizedTime => {}
        }
        Ok(())
    }

    pub(super) fn unsupported<T>(&self, path: &str, construct: &str) -> Result<T, CodegenError> {
        Err(CodegenError::new(
            path,
            format!("{construct} has no faithful vps_lib ASN.1 backend format yet"),
        ))
    }

    pub(super) fn backend_item(&self, rule: EncodingRules, item: &str) -> String {
        if self.mixed_rules {
            format!("vps_lib::asn1::{}::{item}", rule.module())
        } else {
            item.to_string()
        }
    }

    pub(super) fn render_constrained_integer(
        &self,
        bounds: IntegerBounds,
        rule: EncodingRules,
    ) -> Rendered {
        let has_min = bounds.min.is_some();
        let min = bounds.min.unwrap_or(0);
        let has_max = bounds.max.is_some();
        let max = bounds.max.unwrap_or(0);
        let predicate_type = format!("IntegerRange<{has_min}, {min}, {has_max}, {max}>");
        let predicate_expr = format!("IntegerRange::<{has_min}, {min}, {has_max}, {max}>");
        let (format_type, format_expr) = match integer_repr(bounds) {
            IntegerRepr::I8 => ("Integer8TlvFmt", "INTEGER8"),
            IntegerRepr::I16 => ("Integer16TlvFmt", "INTEGER16"),
            IntegerRepr::General => ("IntegerTlvFmt", "INTEGER"),
        };
        refine(
            primitive(
                &self.backend_item(rule, format_type),
                &self.backend_item(rule, format_expr),
                false,
            ),
            predicate_type,
            predicate_expr,
        )
    }

    pub(super) fn validate_enumerated(
        &self,
        values: &[NamedNumber],
        path: &str,
    ) -> Result<(), CodegenError> {
        if values.is_empty() {
            return Err(CodegenError::new(
                path,
                "an empty ENUMERATED has no valid values",
            ));
        }
        let mut names = BTreeMap::<String, String>::new();
        let mut numbers = BTreeSet::new();
        for value in values {
            let rust_name = rust_variant_name(&value.name);
            if let Some(previous) = names.insert(rust_name.clone(), value.name.clone()) {
                return Err(CodegenError::new(
                    path,
                    format!(
                        "ENUMERATED values `{previous}` and `{}` both generate Rust variant `{rust_name}`",
                        value.name
                    ),
                ));
            }
            if !numbers.insert(value.value) {
                return Err(CodegenError::new(
                    path,
                    format!("duplicate ENUMERATED numeric value `{}`", value.value),
                ));
            }
            i16::try_from(value.value).map_err(|_| {
                CodegenError::new(
                    path,
                    format!(
                        "ENUMERATED value `{}` is outside the currently generated i16 executable range",
                        value.value
                    ),
                )
            })?;
        }
        Ok(())
    }

    pub(super) fn validate_sequence_dispatch(
        &self,
        fields: &[SequenceField],
        path: &str,
        rule: EncodingRules,
    ) -> Result<(), CodegenError> {
        let mut suffix = TagDomain::Finite(BTreeSet::new());
        for field in fields.iter().rev() {
            let current = self.tag_domain(&field.ty, &mut BTreeSet::new(), rule)?;
            if field.optional || field.default.is_some() {
                if domains_overlap(&current, &suffix) {
                    return Err(CodegenError::new(
                        format!("{path}.{}", field.name),
                        "optional/defaulted field overlaps the first-tag domain of the remaining SEQUENCE fields",
                    ));
                }
                suffix = union_domains(current, suffix);
            } else {
                suffix = current;
            }
        }
        Ok(())
    }

    pub(super) fn validate_set_order(
        &self,
        fields: &[SequenceField],
        path: &str,
        rule: EncodingRules,
    ) -> Result<(), CodegenError> {
        let mut previous_max: Option<Vec<u8>> = None;
        for field in fields {
            let domain = self.tag_domain(&field.ty, &mut BTreeSet::new(), rule)?;
            let TagDomain::Finite(tags) = domain else {
                return Err(CodegenError::new(
                    format!("{path}.{}", field.name),
                    "a statically ordered DER SET field must have a finite outer-tag domain",
                ));
            };
            if tags.is_empty() {
                return Err(CodegenError::new(
                    format!("{path}.{}", field.name),
                    "a DER SET field has no possible outer tag",
                ));
            }
            let min = tags
                .iter()
                .map(der_identifier_octets)
                .min()
                .expect("non-empty tag domain");
            let max = tags
                .iter()
                .map(der_identifier_octets)
                .max()
                .expect("non-empty tag domain");
            if previous_max
                .as_ref()
                .is_some_and(|previous| previous >= &min)
            {
                return Err(CodegenError::new(
                    format!("{path}.{}", field.name),
                    "DER SET fields are not in strict canonical order by complete identifier octets",
                ));
            }
            previous_max = Some(max);
        }
        Ok(())
    }

    pub(super) fn detect_cycle(
        &self,
        name: &str,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        stack: &mut Vec<String>,
    ) -> Result<(), CodegenError> {
        if visited.contains(name) {
            return Ok(());
        }
        if !visiting.insert(name.to_string()) {
            let start = stack.iter().position(|entry| entry == name).unwrap_or(0);
            let mut cycle = stack[start..].to_vec();
            cycle.push(name.to_string());
            return Err(CodegenError::new(
                name,
                format!(
                    "recursive ASN.1 definitions require a VPS fixpoint combinator: {}",
                    cycle.join(" -> ")
                ),
            ));
        }
        stack.push(name.to_string());
        let mut references = Vec::new();
        collect_type_refs(&self.definition(name)?.ty, &mut references);
        for reference in references {
            self.detect_cycle(reference, visiting, visited, stack)?;
        }
        stack.pop();
        visiting.remove(name);
        visited.insert(name.to_string());
        Ok(())
    }

    pub(super) fn validate_value_assignment(
        &self,
        assignment: &SchemaValueAssignment,
    ) -> Result<(), CodegenError> {
        let (base, _) = self.resolve_base_type(&assignment.ty, &mut BTreeSet::new())?;
        match (base, &assignment.value) {
            (Type::Boolean, SchemaValue::Boolean(_)) => Ok(()),
            (Type::ObjectIdentifier, SchemaValue::ObjectIdentifier(_)) => Err(CodegenError::new(
                &assignment.name,
                "OBJECT IDENTIFIER value assignments are not supported yet",
            )),
            (Type::Integer(_, _named), SchemaValue::Integer(_)) => Ok(()),
            (Type::Integer(_, named), SchemaValue::Identifier(value)) => {
                lookup_named_number(named, value, &assignment.name).map(|_| ())
            }
            (Type::Enumerated(values), SchemaValue::Integer(value)) => {
                if values.iter().any(|entry| entry.value == *value) {
                    Ok(())
                } else {
                    Err(CodegenError::new(
                        &assignment.name,
                        format!("`{value}` is not a member of the declared ENUMERATED type"),
                    ))
                }
            }
            (Type::Enumerated(values), SchemaValue::Identifier(value)) => {
                lookup_named_number(values, value, &assignment.name).map(|_| ())
            }
            (Type::Real, _) => Err(CodegenError::new(
                &assignment.name,
                "REAL value assignments are not supported yet",
            )),
            _ => Err(CodegenError::new(
                &assignment.name,
                "value assignment does not match its declared scalar type",
            )),
        }
    }
}
