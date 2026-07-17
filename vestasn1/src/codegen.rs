//! Nominal Rust/Vest backend for the lossless ASN.1 frontend.
use crate::error::CodegenError;
use crate::frontend::{SchemaModule, SchemaValue, SchemaValueAssignment};
use crate::naming::{
    format_const_name, format_type_name, rust_field_name, rust_variant_name, spec_type_name,
    value_const_name, value_type_name,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use synta_codegen::ast::{
    ChoiceVariant, Constraint, ConstraintSpec, ConstraintValue, Definition, Module, NamedNumber,
    OidComponent, SequenceField, SizeConstraint, SubtypeConstraint, TagClass, TagInfo, Tagging,
    TaggingMode, Type,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LengthBounds {
    min: Option<usize>,
    max: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IntegerBounds {
    min: Option<i64>,
    max: Option<i64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TagShape {
    Tlv { constructed: bool },
    Untagged,
}

#[derive(Clone, Debug)]
struct Rendered {
    ty: String,
    expr: String,
    shape: TagShape,
}

#[derive(Clone, Debug)]
struct Names {
    value: String,
    spec: String,
    format: String,
    format_const: String,
    forward: String,
    reverse: String,
    predicate: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct WireTag {
    class: u8,
    number: u32,
    constructed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TagDomain {
    Finite(BTreeSet<WireTag>),
    Open,
}

pub fn generate(schema: &SchemaModule) -> Result<String, CodegenError> {
    Generator::new(schema)?.generate()
}

struct Generator<'a> {
    schema: &'a SchemaModule,
    module: &'a Module,
    definitions: Vec<Definition>,
    definition_index: BTreeMap<String, usize>,
    names: BTreeMap<String, Names>,
    borrows: BTreeMap<String, bool>,
}

impl<'a> Generator<'a> {
    fn new(schema: &'a SchemaModule) -> Result<Self, CodegenError> {
        let module = schema;
        if !module.imports.is_empty() {
            return Err(CodegenError::new(
                &module.name,
                "IMPORTS are not supported yet; module linking must be implemented before imported definitions can be generated faithfully",
            ));
        }
        if matches!(module.tagging_mode, Some(TaggingMode::Automatic)) {
            return Err(CodegenError::new(
                &module.name,
                "AUTOMATIC TAGS is not supported because synta-codegen does not retain the automatically assigned tags",
            ));
        }

        let definitions = normalize_definitions(module)?;
        let definition_index = definitions
            .iter()
            .enumerate()
            .map(|(index, definition)| (definition.name.clone(), index))
            .collect::<BTreeMap<_, _>>();
        let mut names = BTreeMap::new();
        let mut rust_types = BTreeMap::<String, String>::new();
        let mut rust_consts = BTreeMap::<String, String>::new();

        for definition in &definitions {
            let value = value_type_name(&definition.name);
            let spec = spec_type_name(&definition.name);
            let format = format_type_name(&definition.name);
            let format_const = format_const_name(&definition.name);
            for generated in [&value, &spec, &format] {
                if let Some(previous) =
                    rust_types.insert(generated.clone(), definition.name.clone())
                {
                    return Err(CodegenError::new(
                        &definition.name,
                        format!(
                            "generated Rust type name `{generated}` collides with definition `{previous}`"
                        ),
                    ));
                }
            }
            if let Some(previous) =
                rust_consts.insert(format_const.clone(), definition.name.clone())
            {
                return Err(CodegenError::new(
                    &definition.name,
                    format!(
                        "generated Rust constant name `{format_const}` collides with definition `{previous}`"
                    ),
                ));
            }
            names.insert(
                definition.name.clone(),
                Names {
                    forward: format!("{value}Forward"),
                    reverse: format!("{value}Reverse"),
                    predicate: format!("{value}Predicate"),
                    value,
                    spec,
                    format,
                    format_const,
                },
            );
        }

        for assignment in &schema.values {
            let constant = value_const_name(&assignment.name);
            if let Some(previous) = rust_consts.insert(constant.clone(), assignment.name.clone()) {
                return Err(CodegenError::new(
                    &assignment.name,
                    format!("generated Rust constant name `{constant}` collides with `{previous}`"),
                ));
            }
        }

        let mut generator = Self {
            schema,
            module,
            definitions,
            definition_index,
            names,
            borrows: BTreeMap::new(),
        };
        generator.compute_lifetimes()?;
        generator.validate()?;
        Ok(generator)
    }

    fn definition(&self, name: &str) -> Result<&Definition, CodegenError> {
        self.definition_index
            .get(name)
            .map(|index| &self.definitions[*index])
            .ok_or_else(|| {
                CodegenError::new(name, format!("unknown ASN.1 type reference `{name}`"))
            })
    }

    fn compute_lifetimes(&mut self) -> Result<(), CodegenError> {
        for definition in &self.definitions {
            let borrows = self.type_borrows(&definition.ty, &mut BTreeSet::new())?;
            self.borrows.insert(definition.name.clone(), borrows);
        }
        Ok(())
    }

    fn type_borrows(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<bool, CodegenError> {
        Ok(match ty {
            Type::Integer(_, _)
            | Type::OctetString(_)
            | Type::BitString(_)
            | Type::ObjectIdentifier
            | Type::Real
            | Type::Utf8String(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::TeletexString(_)
            | Type::BmpString(_)
            | Type::GeneralizedTime
            | Type::Any => true,
            Type::Sequence(fields) | Type::Set(fields) => {
                let mut borrows = false;
                for field in fields {
                    borrows |= self.type_borrows(&field.ty, visiting)?;
                }
                borrows
            }
            Type::Choice(variants) => {
                let mut borrows = false;
                for variant in variants {
                    borrows |= self.type_borrows(&variant.ty, visiting)?;
                }
                borrows
            }
            Type::SequenceOf(inner, _)
            | Type::SetOf(inner, _)
            | Type::Tagged { inner, .. }
            | Type::Constrained {
                base_type: inner, ..
            } => self.type_borrows(inner, visiting)?,
            Type::TypeRef(name) => {
                if let Some(value) = self.borrows.get(name) {
                    *value
                } else {
                    if !visiting.insert(name.clone()) {
                        return Err(CodegenError::new(
                            name,
                            "recursive ASN.1 definitions require a Vest fixpoint combinator",
                        ));
                    }
                    let value = self.type_borrows(&self.definition(name)?.ty, visiting)?;
                    visiting.remove(name);
                    value
                }
            }
            Type::Boolean | Type::Null | Type::UtcTime | Type::Enumerated(_) => false,
            Type::RelativeOid
            | Type::UniversalString(_)
            | Type::GeneralString(_)
            | Type::NumericString(_)
            | Type::VisibleString(_)
            | Type::AnyDefinedBy(_)
            | Type::Class(_) => false,
        })
    }

    fn validate(&self) -> Result<(), CodegenError> {
        for definition in &self.definitions {
            self.validate_type(&definition.ty, &definition.name)?;
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
        for assignment in &self.schema.values {
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

    fn validate_type(&self, ty: &Type, path: &str) -> Result<(), CodegenError> {
        match ty {
            Type::Sequence(fields) => {
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
                    self.validate_type(&field.ty, &field_path)?;
                    if let Some(default) = &field.default {
                        self.render_default(&field.ty, default, &field_path)?;
                    }
                }
                self.validate_sequence_dispatch(fields, path)?;
            }
            Type::SequenceOf(inner, constraint) => {
                if let Some(constraint) = constraint {
                    legacy_size_bounds(constraint, path)?;
                }
                self.validate_type(inner, &format!("{path}[]"))?;
            }
            Type::Set(_) => {
                return Err(CodegenError::new(
                    path,
                    "SET needs order-independent component parsing and is not supported yet",
                ));
            }
            Type::SetOf(_, _) => {
                return Err(CodegenError::new(
                    path,
                    "SET OF generation is disabled until a generic allocation-free DER ordering strategy is available",
                ));
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
                    self.validate_type(&variant.ty, &variant_path)?;
                    if variants.len() > 1
                        && self.tag_shape(&variant.ty, &mut BTreeSet::new())? == TagShape::Untagged
                    {
                        return Err(CodegenError::new(
                            &variant_path,
                            "an untagged CHOICE/open-type alternative must be explicitly tagged before it can participate in another CHOICE",
                        ));
                    }
                    let domain = self.tag_domain(&variant.ty, &mut BTreeSet::new())?;
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
                if constraint.is_some() {
                    legacy_size_bounds(constraint.as_ref().unwrap(), path)?;
                }
            }
            Type::BitString(constraint) => {
                if constraint.is_some() {
                    return Err(CodegenError::new(path, "BIT STRING SIZE constraints need a bit-length predicate and are not supported yet"));
                }
            }
            Type::Tagged { inner, .. } => self.validate_type(inner, path)?,
            Type::Constrained {
                base_type,
                constraint,
            } => {
                self.validate_type(base_type, path)?;
                match base_type.as_ref() {
                    Type::OctetString(None)
                    | Type::Utf8String(None)
                    | Type::PrintableString(None)
                    | Type::IA5String(None)
                    | Type::TeletexString(None)
                    | Type::BmpString(None) => { string_size_bounds(constraint, path)?; }
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
            Type::UniversalString(_) => return self.unsupported(path, "UniversalString"),
            Type::GeneralString(_) => return self.unsupported(path, "GeneralString"),
            Type::NumericString(_) => return self.unsupported(path, "NumericString"),
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

    fn unsupported<T>(&self, path: &str, construct: &str) -> Result<T, CodegenError> {
        Err(CodegenError::new(
            path,
            format!("{construct} has no faithful vest_lib2 ASN.1 backend format yet"),
        ))
    }

    fn validate_enumerated(&self, values: &[NamedNumber], path: &str) -> Result<(), CodegenError> {
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

    fn validate_sequence_dispatch(
        &self,
        fields: &[SequenceField],
        path: &str,
    ) -> Result<(), CodegenError> {
        for (index, field) in fields.iter().enumerate() {
            if !(field.optional || field.default.is_some()) {
                continue;
            }
            for following in &fields[index + 1..] {
                if self.tag_shape(&following.ty, &mut BTreeSet::new())? == TagShape::Untagged {
                    return Err(CodegenError::new(
                        format!("{path}.{}", following.name),
                        "a CHOICE/open type following an optional/defaulted field must be explicitly tagged",
                    ));
                }
                if !(following.optional || following.default.is_some()) {
                    break;
                }
            }
        }
        let mut suffix = TagDomain::Finite(BTreeSet::new());
        for field in fields.iter().rev() {
            let current = self.tag_domain(&field.ty, &mut BTreeSet::new())?;
            if field.optional || field.default.is_some() {
                if self.tag_shape(&field.ty, &mut BTreeSet::new())? == TagShape::Untagged {
                    return Err(CodegenError::new(
                        format!("{path}.{}", field.name),
                        "an optional/defaulted CHOICE or open type must be explicitly tagged",
                    ));
                }
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

    fn detect_cycle(
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
                    "recursive ASN.1 definitions require a Vest fixpoint combinator: {}",
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

    fn validate_value_assignment(
        &self,
        assignment: &SchemaValueAssignment,
    ) -> Result<(), CodegenError> {
        let (base, _) = self.resolve_base_type(&assignment.ty, &mut BTreeSet::new())?;
        match (base, &assignment.value) {
            (Type::Boolean, SchemaValue::Boolean(_))
            | (Type::ObjectIdentifier, SchemaValue::ObjectIdentifier(_)) => Ok(()),
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

    fn generate(&self) -> Result<String, CodegenError> {
        let mut output = String::new();
        let oid_registry = self.build_oid_registry()?;
        writeln!(
            output,
            "// @generated by vestasn1 from ASN.1 module `{}`.",
            self.module.name
        )
        .unwrap();
        writeln!(output, "// Generated formats parse and serialize DER.").unwrap();
        writeln!(output).unwrap();
        writeln!(output, "use vest_lib2::asn1::*;").unwrap();
        writeln!(
            output,
            "use vest_lib2::combinators::mapped::spec::{{BiMap, SpecMap}};"
        )
        .unwrap();
        writeln!(output, "use vest_lib2::combinators::*;").unwrap();
        writeln!(output, "use vest_lib2::core::exec::fns::{{Map, Pred}};").unwrap();
        writeln!(output, "use vest_lib2::core::spec::*;").unwrap();
        writeln!(output, "use vstd::prelude::*;\n").unwrap();
        writeln!(output, "verus! {{\n").unwrap();

        for definition in &self.definitions {
            self.render_value_declaration(definition, &mut output)?;
        }
        for definition in &self.definitions {
            self.render_mapper_declaration(definition, &mut output)?;
        }
        for definition in &self.definitions {
            self.render_format_declaration(definition, &mut output)?;
        }

        writeln!(output, "proof fn vestasn1_generated_formats_are_valid() {{").unwrap();
        writeln!(output, "    use vest_lib2::core::proof::*;").unwrap();
        writeln!(output, "    use vest_lib2::asn1::modifiers::{{lemma_disjoint_asn1_tags, lemma_disjoint_defaulted}};").unwrap();
        writeln!(
            output,
            "    use vest_lib2::asn1::tag::lemma_tag_wf_implies_tag_consistent;"
        )
        .unwrap();
        writeln!(
            output,
            "    use vest_lib2::combinators::disjoint::disjointness_lemmas;"
        )
        .unwrap();
        writeln!(output, "    broadcast use disjointness_lemmas;").unwrap();
        writeln!(
            output,
            "    broadcast use lemma_tag_wf_implies_tag_consistent;"
        )
        .unwrap();
        writeln!(
            output,
            "    broadcast use {{lemma_disjoint_asn1_tags, lemma_disjoint_defaulted}};"
        )
        .unwrap();
        for definition in &self.definitions {
            let format = format!("{}()", self.names[&definition.name].format_const);
            writeln!(output, "    assert({format}.safe_inv());").unwrap();
            writeln!(output, "    assert({format}.sound_inv());").unwrap();
            match &definition.ty {
                Type::Choice(variants) => {
                    self.render_choice_validity_proof(definition, variants, &mut output)?;
                }
                Type::Sequence(fields) => {
                    self.render_sequence_validity_proof(definition, fields, &mut output)?;
                }
                _ => {}
            }
            writeln!(output, "    assert({format}.unambiguous());").unwrap();
        }
        writeln!(output, "}}\n").unwrap();
        writeln!(output, "}} // verus!\n").unwrap();
        for assignment in &self.schema.values {
            self.render_value_constant(assignment, &oid_registry, &mut output)?;
        }
        Ok(output)
    }

    fn render_choice_validity_proof(
        &self,
        definition: &Definition,
        variants: &[ChoiceVariant],
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let format = format!("{}()", self.names[&definition.name].format_const);
        let branches = (0..variants.len())
            .map(|index| choice_branch_access(&format!("{format}.inner"), index, variants.len()))
            .collect::<Vec<_>>();
        for left in 0..branches.len() {
            for right in left + 1..branches.len() {
                writeln!(
                    output,
                    "    lemma_disjoint_asn1_tags(({}).0, ({}).0);",
                    branches[left], branches[right]
                )
                .unwrap();
                writeln!(
                    output,
                    "    vest_lib2::combinators::disjoint::lemma_disjoint_refs({}, {});",
                    branches[left], branches[right]
                )
                .unwrap();
            }
        }
        writeln!(output, "    assert(({format}.inner).unambiguous());").unwrap();
        Ok(())
    }

    fn render_sequence_validity_proof(
        &self,
        definition: &Definition,
        fields: &[SequenceField],
        output: &mut String,
    ) -> Result<(), CodegenError> {
        if fields.is_empty() {
            return Ok(());
        }
        let format = format!("{}()", self.names[&definition.name].format_const);
        let root = format!("{format}.1.inner");
        let accesses = sequence_field_accesses(&root, fields);

        for (index, field) in fields.iter().enumerate() {
            if !(field.optional || field.default.is_some()) {
                continue;
            }
            let Some(rest) = &accesses[index].1 else {
                continue;
            };
            let current_path = &accesses[index].0;
            let current_is_ref = field.default.is_none();

            for target in index + 1..fields.len() {
                let target_field = &fields[target];
                let target_path = &accesses[target].0;
                let target_is_ref = target_field.default.is_none();
                let current_inner = if current_is_ref {
                    format!("({current_path}).0")
                } else {
                    current_path.clone()
                };
                let target_inner = if target_is_ref {
                    format!("({target_path}).0")
                } else {
                    target_path.clone()
                };
                writeln!(
                    output,
                    "    lemma_disjoint_asn1_tags({current_inner}, {target_inner});"
                )
                .unwrap();
                match (current_is_ref, target_is_ref) {
                    (true, true) => writeln!(
                        output,
                        "    vest_lib2::combinators::disjoint::lemma_disjoint_refs({current_path}, {target_path});"
                    )
                    .unwrap(),
                    (true, false) => writeln!(
                        output,
                        "    vest_lib2::combinators::disjoint::lemma_disjoint_ref_left({current_path}, {target_path});"
                    )
                    .unwrap(),
                    (false, true) => writeln!(
                        output,
                        "    vest_lib2::combinators::disjoint::lemma_disjoint_ref_right({current_path}, {target_path});"
                    )
                    .unwrap(),
                    (false, false) => {}
                }
                if !(target_field.optional || target_field.default.is_some()) {
                    break;
                }
            }
            writeln!(
                output,
                "    assert(disjoint_domains({current_path}, {rest}));"
            )
            .unwrap();
        }
        writeln!(output, "    assert(({root}).unambiguous());").unwrap();
        Ok(())
    }

    fn render_value_declaration(
        &self,
        definition: &Definition,
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        match &definition.ty {
            Type::Sequence(fields) => {
                let lifetime = self.borrows[&definition.name];
                writeln!(output, "/// Value type for ASN.1 `{}`.", definition.name).unwrap();
                writeln!(
                    output,
                    "pub struct {}{} {{",
                    names.value,
                    lifetime_declaration(lifetime)
                )
                .unwrap();
                for field in fields {
                    let mut ty = self.exec_type(&field.ty, "'a")?;
                    if field.optional {
                        ty = format!("Option<{ty}>");
                    }
                    writeln!(output, "    pub {}: {},", rust_field_name(&field.name), ty).unwrap();
                }
                writeln!(output, "}}\n").unwrap();

                writeln!(output, "#[verifier::ext_equal]").unwrap();
                writeln!(output, "pub struct {} {{", names.spec).unwrap();
                for field in fields {
                    let mut ty = self.spec_type(&field.ty)?;
                    if field.optional {
                        ty = format!("Option<{ty}>");
                    }
                    writeln!(output, "    pub {}: {},", rust_field_name(&field.name), ty).unwrap();
                }
                writeln!(output, "}}\n").unwrap();

                writeln!(
                    output,
                    "impl{} DeepView for {}{} {{",
                    impl_lifetime(lifetime),
                    names.value,
                    lifetime_application(lifetime, "'a")
                )
                .unwrap();
                writeln!(output, "    type V = {};", names.spec).unwrap();
                writeln!(output, "    open spec fn deep_view(&self) -> Self::V {{").unwrap();
                writeln!(output, "        {} {{", names.spec).unwrap();
                for field in fields {
                    let rust_name = rust_field_name(&field.name);
                    writeln!(
                        output,
                        "            {rust_name}: self.{rust_name}.deep_view(),"
                    )
                    .unwrap();
                }
                writeln!(output, "        }}").unwrap();
                writeln!(output, "    }}").unwrap();
                writeln!(output, "}}\n").unwrap();
            }
            Type::Choice(variants) => {
                let lifetime = self.borrows[&definition.name];
                writeln!(output, "/// Value type for ASN.1 `{}`.", definition.name).unwrap();
                writeln!(
                    output,
                    "pub enum {}{} {{",
                    names.value,
                    lifetime_declaration(lifetime)
                )
                .unwrap();
                for variant in variants {
                    writeln!(
                        output,
                        "    {}({}),",
                        rust_variant_name(&variant.name),
                        self.exec_type(&variant.ty, "'a")?
                    )
                    .unwrap();
                }
                writeln!(output, "}}\n").unwrap();

                writeln!(output, "#[verifier::ext_equal]").unwrap();
                writeln!(output, "pub enum {} {{", names.spec).unwrap();
                for variant in variants {
                    writeln!(
                        output,
                        "    {}({}),",
                        rust_variant_name(&variant.name),
                        self.spec_type(&variant.ty)?
                    )
                    .unwrap();
                }
                writeln!(output, "}}\n").unwrap();

                writeln!(
                    output,
                    "impl{} DeepView for {}{} {{",
                    impl_lifetime(lifetime),
                    names.value,
                    lifetime_application(lifetime, "'a")
                )
                .unwrap();
                writeln!(output, "    type V = {};", names.spec).unwrap();
                writeln!(output, "    open spec fn deep_view(&self) -> Self::V {{").unwrap();
                writeln!(output, "        match self {{").unwrap();
                for variant in variants {
                    let variant_name = rust_variant_name(&variant.name);
                    writeln!(
                        output,
                        "            {}::{variant_name}(value) => {}::{variant_name}(value.deep_view()),",
                        names.value, names.spec
                    )
                    .unwrap();
                }
                writeln!(output, "        }}").unwrap();
                writeln!(output, "    }}").unwrap();
                writeln!(output, "}}\n").unwrap();
            }
            Type::Enumerated(values) => {
                writeln!(output, "#[repr(i16)]").unwrap();
                writeln!(
                    output,
                    "#[derive(Debug, Clone, Copy, PartialEq, Eq, StructuralEq)]"
                )
                .unwrap();
                writeln!(output, "#[verifier::ext_equal]").unwrap();
                writeln!(output, "pub enum {} {{", names.value).unwrap();
                for value in values {
                    writeln!(
                        output,
                        "    {} = {},",
                        rust_variant_name(&value.name),
                        value.value
                    )
                    .unwrap();
                }
                writeln!(output, "}}\n").unwrap();
                writeln!(output, "pub type {} = {};", names.spec, names.value).unwrap();
                writeln!(output, "impl DeepView for {} {{", names.value).unwrap();
                writeln!(output, "    type V = Self;").unwrap();
                writeln!(
                    output,
                    "    open spec fn deep_view(&self) -> Self::V {{ *self }}"
                )
                .unwrap();
                writeln!(output, "}}").unwrap();
                writeln!(output, "#[cfg(not(verus_keep_ghost))]").unwrap();
                writeln!(output, "unsafe impl Structural for {} {{}}\n", names.value).unwrap();
            }
            ty => {
                let lifetime = self.borrows[&definition.name];
                writeln!(
                    output,
                    "pub type {}{} = {};",
                    names.value,
                    lifetime_declaration(lifetime),
                    self.exec_type(ty, "'a")?
                )
                .unwrap();
                writeln!(
                    output,
                    "pub type {} = {};\n",
                    names.spec,
                    self.spec_type(ty)?
                )
                .unwrap();
            }
        }
        Ok(())
    }

    fn render_mapper_declaration(
        &self,
        definition: &Definition,
        output: &mut String,
    ) -> Result<(), CodegenError> {
        match &definition.ty {
            Type::Sequence(fields) => self.render_sequence_mappers(definition, fields, output),
            Type::Choice(variants) => self.render_choice_mappers(definition, variants, output),
            Type::Enumerated(values) => self.render_enumerated_mappers(definition, values, output),
            _ => Ok(()),
        }
    }

    fn render_sequence_mappers(
        &self,
        definition: &Definition,
        fields: &[SequenceField],
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let lifetime = self.borrows[&definition.name];
        let mut spec_parts = fields
            .iter()
            .map(|field| {
                let ty = self.spec_type(&field.ty)?;
                Ok(if field.optional {
                    format!("Option<{ty}>")
                } else {
                    ty
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let mut parsed_parts = fields
            .iter()
            .map(|field| {
                let ty = self.exec_type(&field.ty, "'a")?;
                Ok(if field.optional {
                    format!("Option<{ty}>")
                } else {
                    ty
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let mut reverse_parts = fields
            .iter()
            .map(|field| {
                let ty = self.exec_type(&field.ty, "'a")?;
                Ok(if field.default.is_some() {
                    ty
                } else if field.optional {
                    format!("Option<&'x {ty}>")
                } else {
                    format!("&'x {ty}")
                })
            })
            .collect::<Result<Vec<_>, CodegenError>>()?;
        let identifiers = fields
            .iter()
            .map(|field| rust_field_name(&field.name))
            .collect::<Vec<_>>();
        let mut tuple_identifiers = identifiers.clone();
        spec_parts.push("()".to_string());
        parsed_parts.push("()".to_string());
        reverse_parts.push("()".to_string());
        tuple_identifiers.push("_end".to_string());

        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};", names.forward).unwrap();
        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};\n", names.reverse).unwrap();
        writeln!(output, "impl SpecMap for {} {{", names.forward).unwrap();
        writeln!(output, "    type Input = {};", nested_type(&spec_parts)).unwrap();
        writeln!(output, "    type Output = {};", names.spec).unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {{"
        )
        .unwrap();
        writeln!(
            output,
            "        let {} = input;",
            nested_pattern(&tuple_identifiers)
        )
        .unwrap();
        writeln!(output, "        {} {{", names.spec).unwrap();
        for identifier in &identifiers {
            writeln!(output, "            {identifier},").unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        writeln!(output, "impl SpecMap for {} {{", names.reverse).unwrap();
        writeln!(output, "    type Input = {};", names.spec).unwrap();
        writeln!(output, "    type Output = {};", nested_type(&spec_parts)).unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {{"
        )
        .unwrap();
        let mut spec_expressions = identifiers
            .iter()
            .map(|identifier| format!("value.{identifier}"))
            .collect::<Vec<_>>();
        spec_expressions.push("()".to_string());
        writeln!(output, "        {}", nested_expression(&spec_expressions)).unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        writeln!(
            output,
            "impl{} Map<{}> for {} {{",
            impl_lifetime(lifetime),
            nested_type(&parsed_parts),
            names.forward
        )
        .unwrap();
        writeln!(
            output,
            "    type O = {}{};",
            names.value,
            lifetime_application(lifetime, "'a")
        )
        .unwrap();
        writeln!(
            output,
            "    fn map(&self, input: {}) -> (value: Self::O) {{",
            nested_type(&parsed_parts)
        )
        .unwrap();
        writeln!(
            output,
            "        let {} = input;",
            nested_pattern(&tuple_identifiers)
        )
        .unwrap();
        writeln!(output, "        {} {{", names.value).unwrap();
        for identifier in &identifiers {
            writeln!(output, "            {identifier},").unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        let reverse_impl = if lifetime { "impl<'a, 'x>" } else { "impl<'x>" };
        writeln!(
            output,
            "{reverse_impl} Map<&'x {}{}> for {} {{",
            names.value,
            lifetime_application(lifetime, "'a"),
            names.reverse
        )
        .unwrap();
        writeln!(output, "    type O = {};", nested_type(&reverse_parts)).unwrap();
        writeln!(
            output,
            "    fn map(&self, value: &'x {}{}) -> (output: Self::O) {{",
            names.value,
            lifetime_application(lifetime, "'a")
        )
        .unwrap();
        let mut reverse_expressions = fields
            .iter()
            .map(|field| {
                let identifier = rust_field_name(&field.name);
                if field.default.is_some() {
                    format!("value.{identifier}")
                } else if field.optional {
                    format!("value.{identifier}.as_ref()")
                } else {
                    format!("&value.{identifier}")
                }
            })
            .collect::<Vec<_>>();
        reverse_expressions.push("()".to_string());
        writeln!(
            output,
            "        {}",
            nested_expression(&reverse_expressions)
        )
        .unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        Ok(())
    }

    fn render_choice_mappers(
        &self,
        definition: &Definition,
        variants: &[ChoiceVariant],
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let lifetime = self.borrows[&definition.name];
        let spec_parts = variants
            .iter()
            .map(|variant| self.spec_type(&variant.ty))
            .collect::<Result<Vec<_>, _>>()?;
        let parsed_parts = variants
            .iter()
            .map(|variant| self.exec_type(&variant.ty, "'a"))
            .collect::<Result<Vec<_>, _>>()?;
        let reverse_parts = parsed_parts
            .iter()
            .map(|ty| format!("&'x {ty}"))
            .collect::<Vec<_>>();

        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};", names.forward).unwrap();
        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};\n", names.reverse).unwrap();
        writeln!(output, "impl SpecMap for {} {{", names.forward).unwrap();
        writeln!(output, "    type Input = {};", nested_sum_type(&spec_parts)).unwrap();
        writeln!(output, "    type Output = {};", names.spec).unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, input: Self::Input) -> Self::Output {{"
        )
        .unwrap();
        writeln!(output, "        match input {{").unwrap();
        for (index, variant) in variants.iter().enumerate() {
            writeln!(
                output,
                "            {} => {}::{}(value),",
                sum_pattern(index, variants.len(), "value"),
                names.spec,
                rust_variant_name(&variant.name)
            )
            .unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        writeln!(output, "impl SpecMap for {} {{", names.reverse).unwrap();
        writeln!(output, "    type Input = {};", names.spec).unwrap();
        writeln!(
            output,
            "    type Output = {};",
            nested_sum_type(&spec_parts)
        )
        .unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, value: Self::Input) -> Self::Output {{"
        )
        .unwrap();
        writeln!(output, "        match value {{").unwrap();
        for (index, variant) in variants.iter().enumerate() {
            let variant_name = rust_variant_name(&variant.name);
            writeln!(
                output,
                "            {}::{variant_name}(value) => {},",
                names.spec,
                sum_expression(index, variants.len(), "value")
            )
            .unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        writeln!(
            output,
            "impl{} Map<{}> for {} {{",
            impl_lifetime(lifetime),
            nested_sum_type(&parsed_parts),
            names.forward
        )
        .unwrap();
        writeln!(
            output,
            "    type O = {}{};",
            names.value,
            lifetime_application(lifetime, "'a")
        )
        .unwrap();
        writeln!(
            output,
            "    fn map(&self, input: {}) -> (value: Self::O) {{",
            nested_sum_type(&parsed_parts)
        )
        .unwrap();
        writeln!(output, "        match input {{").unwrap();
        for (index, variant) in variants.iter().enumerate() {
            writeln!(
                output,
                "            {} => {}::{}(value),",
                sum_pattern(index, variants.len(), "value"),
                names.value,
                rust_variant_name(&variant.name)
            )
            .unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        let reverse_impl = if lifetime { "impl<'a, 'x>" } else { "impl<'x>" };
        writeln!(
            output,
            "{reverse_impl} Map<&'x {}{}> for {} {{",
            names.value,
            lifetime_application(lifetime, "'a"),
            names.reverse
        )
        .unwrap();
        writeln!(output, "    type O = {};", nested_sum_type(&reverse_parts)).unwrap();
        writeln!(
            output,
            "    fn map(&self, value: &'x {}{}) -> (output: Self::O) {{",
            names.value,
            lifetime_application(lifetime, "'a")
        )
        .unwrap();
        writeln!(output, "        match value {{").unwrap();
        for (index, variant) in variants.iter().enumerate() {
            let variant_name = rust_variant_name(&variant.name);
            writeln!(
                output,
                "            {}::{variant_name}(value) => {},",
                names.value,
                sum_expression(index, variants.len(), "value")
            )
            .unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        Ok(())
    }

    fn render_enumerated_mappers(
        &self,
        definition: &Definition,
        values: &[NamedNumber],
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};", names.predicate).unwrap();
        writeln!(output, "impl SpecPred<i16> for {} {{", names.predicate).unwrap();
        writeln!(
            output,
            "    open spec fn apply(&self, value: i16) -> bool {{"
        )
        .unwrap();
        writeln!(
            output,
            "        {}",
            values
                .iter()
                .map(|value| format!("value == {}i16", value.value))
                .collect::<Vec<_>>()
                .join(" || ")
        )
        .unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}").unwrap();
        writeln!(output, "impl Pred<i16> for {} {{", names.predicate).unwrap();
        writeln!(output, "    fn test(&self, value: &i16) -> (ok: bool) {{").unwrap();
        writeln!(
            output,
            "        {}",
            values
                .iter()
                .map(|value| format!("*value == {}i16", value.value))
                .collect::<Vec<_>>()
                .join(" || ")
        )
        .unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();

        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};", names.forward).unwrap();
        writeln!(output, "#[derive(Clone, Copy)]").unwrap();
        writeln!(output, "pub struct {};\n", names.reverse).unwrap();
        writeln!(output, "impl SpecMap for {} {{", names.forward).unwrap();
        writeln!(output, "    type Input = i16;").unwrap();
        writeln!(output, "    type Output = {};", names.value).unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, value: i16) -> Self::Output {{"
        )
        .unwrap();
        render_enum_number_match(values, &names.value, output, 8);
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        writeln!(output, "impl SpecMap for {} {{", names.reverse).unwrap();
        writeln!(output, "    type Input = {};", names.value).unwrap();
        writeln!(output, "    type Output = i16;").unwrap();
        writeln!(
            output,
            "    open spec fn spec_map(&self, value: Self::Input) -> i16 {{"
        )
        .unwrap();
        render_enum_value_match(values, &names.value, output, 8);
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        writeln!(output, "impl Map<i16> for {} {{", names.forward).unwrap();
        writeln!(output, "    type O = {};", names.value).unwrap();
        writeln!(
            output,
            "    fn map(&self, value: i16) -> (output: Self::O) {{"
        )
        .unwrap();
        render_enum_number_match(values, &names.value, output, 8);
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        writeln!(
            output,
            "impl<'a> Map<&'a {}> for {} {{",
            names.value, names.reverse
        )
        .unwrap();
        writeln!(output, "    type O = i16;").unwrap();
        writeln!(
            output,
            "    fn map(&self, value: &'a {}) -> (output: i16) {{",
            names.value
        )
        .unwrap();
        writeln!(output, "        match value {{").unwrap();
        for value in values {
            writeln!(
                output,
                "            {}::{} => {}i16,",
                names.value,
                rust_variant_name(&value.name),
                value.value
            )
            .unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}\n").unwrap();
        Ok(())
    }

    fn render_format_declaration(
        &self,
        definition: &Definition,
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let rendered = match &definition.ty {
            Type::Sequence(fields) => {
                let raw = self.render_sequence_fields(fields, &definition.name)?;
                let mapped = Rendered {
                    ty: format!(
                        "Mapped<{}, BiMap<{}, {}>>",
                        raw.ty, names.forward, names.reverse
                    ),
                    expr: format!(
                        "Mapped {{ inner: {}, mapper: BiMap({}, {}) }}",
                        raw.expr, names.forward, names.reverse
                    ),
                    shape: TagShape::Untagged,
                };
                Rendered {
                    ty: format!("ASN1Fmt<{}, DER>", mapped.ty),
                    expr: format!("ASN1Fmt::<_, DER>(TagFmt::SEQUENCE, {})", mapped.expr),
                    shape: TagShape::Tlv { constructed: true },
                }
            }
            Type::Choice(variants) => {
                let raw = self.render_choice_raw(variants)?;
                Rendered {
                    ty: format!(
                        "Mapped<{}, BiMap<{}, {}>>",
                        raw.ty, names.forward, names.reverse
                    ),
                    expr: format!(
                        "Mapped {{ inner: {}, mapper: BiMap({}, {}) }}",
                        raw.expr, names.forward, names.reverse
                    ),
                    shape: TagShape::Untagged,
                }
            }
            Type::Enumerated(_) => Rendered {
                ty: format!(
                    "ASN1Fmt<Mapped<Refined<Integer16Fmt, {}>, BiMap<{}, {}>>, DER>",
                    names.predicate, names.forward, names.reverse
                ),
                expr: format!(
                    "ASN1Fmt::<_, DER>(TagFmt::ENUMERATED, Mapped {{ inner: Refined(Integer16Fmt, {}), mapper: BiMap({}, {}) }})",
                    names.predicate, names.forward, names.reverse
                ),
                shape: TagShape::Tlv { constructed: false },
            },
            ty => self.render_type(ty)?,
        };
        writeln!(output, "/// DER format for ASN.1 `{}`.", definition.name).unwrap();
        writeln!(output, "pub type {} = {};", names.format, rendered.ty).unwrap();
        writeln!(output, "#[verifier::allow_in_spec]").unwrap();
        writeln!(output, "#[allow(non_snake_case)]").unwrap();
        let returns_expr = pretty_format_expr(&rendered.expr, 12);
        let body_expr = pretty_format_expr(&rendered.expr, 4);
        writeln!(
            output,
            "pub const fn {}() -> {}\n    returns\n        (\n{}\n        ),\n{{\n{}\n}}\n",
            names.format_const, names.format, returns_expr, body_expr
        )
        .unwrap();
        Ok(())
    }

    fn render_type(&self, ty: &Type) -> Result<Rendered, CodegenError> {
        Ok(match ty {
            Type::SequenceOf(inner, constraint) => {
                let inner = self.render_type(inner)?;
                if let Some(constraint) = constraint {
                    let bounds = legacy_size_bounds(constraint, "SEQUENCE OF")?;
                    let (predicate_type, predicate_expr) = render_size_predicate(bounds);
                    Rendered {
                        ty: format!(
                            "ASN1Fmt<Refined<RepeatTillEnd<{}>, {}>, DER>",
                            inner.ty, predicate_type
                        ),
                        expr: format!(
                            "ASN1Fmt::<_, DER>(TagFmt::SEQUENCE, Refined(RepeatTillEnd({}), {}))",
                            inner.expr, predicate_expr
                        ),
                        shape: TagShape::Tlv { constructed: true },
                    }
                } else {
                    Rendered {
                        ty: format!("ASN1Fmt<RepeatTillEnd<{}>, DER>", inner.ty),
                        expr: format!("SEQUENCE_OF({})", inner.expr),
                        shape: TagShape::Tlv { constructed: true },
                    }
                }
            }
            Type::TypeRef(name) => {
                let names = &self.names[name];
                Rendered {
                    ty: names.format.clone(),
                    expr: format!("{}()", names.format_const),
                    shape: self.tag_shape(ty, &mut BTreeSet::new())?,
                }
            }
            Type::Integer(_, _) => primitive("ASN1IntegerFmt<DER>", "INTEGER", false),
            Type::Boolean => primitive("ASN1BoolFmt<DER>", "BOOLEAN", false),
            Type::OctetString(constraint) => match constraint {
                Some(constraint) => {
                    render_sized_octet_string(legacy_size_bounds(constraint, "OCTET STRING")?)
                }
                None => primitive("ASN1OctetStringFmt<DER>", "OCTET_STRING", false),
            },
            Type::BitString(_) => primitive("ASN1BitStringFmt<DER>", "BIT_STRING", false),
            Type::ObjectIdentifier => {
                primitive("ASN1ObjectIdentifierFmt<DER>", "OBJECT_IDENTIFIER", false)
            }
            Type::Real => primitive("ASN1RealFmt<DER>", "REAL", false),
            Type::Null => primitive("ASN1NullFmt<DER>", "NULL", false),
            Type::Utf8String(constraint) => render_optionally_sized_string(
                "Utf8StringFmt", "Utf8StringFmt", "TagFmt::UTF8_STRING", "ASN1Utf8StringFmt<DER>", "UTF8_STRING", constraint.as_ref(),
            )?,
            Type::PrintableString(constraint) => render_optionally_sized_string(
                "PrintableStringFmt", "PrintableStringFmt", "TagFmt::PRINTABLE_STRING", "ASN1PrintableStringFmt<DER>", "PRINTABLE_STRING", constraint.as_ref(),
            )?,
            Type::IA5String(constraint) => render_optionally_sized_string(
                "Ia5StringFmt", "Ia5StringFmt", "TagFmt::IA5_STRING", "ASN1Ia5StringFmt<DER>", "IA5_STRING", constraint.as_ref(),
            )?,
            Type::TeletexString(constraint) => render_optionally_sized_string(
                "TeletexStringFmt", "TeletexStringFmt", "TagFmt::TELETEX_STRING", "ASN1TeletexStringFmt<DER>", "TELETEX_STRING", constraint.as_ref(),
            )?,
            Type::BmpString(constraint) => render_optionally_sized_string(
                "BmpStringFmt", "BmpStringFmt", "TagFmt::BMP_STRING", "ASN1BmpStringFmt<DER>", "BMP_STRING", constraint.as_ref(),
            )?,
            Type::UtcTime => primitive("ASN1UtcTimeFmt<DER>", "UTC_TIME", false),
            Type::GeneralizedTime => {
                primitive("ASN1GeneralizedTimeFmt<DER>", "GENERALIZED_TIME", false)
            }
            Type::Any => Rendered {
                ty: "ASN1AnyFmt<DER>".to_string(),
                expr: "ANY".to_string(),
                shape: TagShape::Untagged,
            },
            Type::Tagged { tag, inner } => self.render_tagged(tag, inner)?,
            Type::Constrained {
                base_type,
                constraint,
            } => match base_type.as_ref() {
                Type::OctetString(None) => render_sized_octet_string(string_size_bounds(constraint, "OCTET STRING")?),
                Type::Utf8String(None) => render_sized_content("Utf8StringFmt", "Utf8StringFmt", "TagFmt::UTF8_STRING", string_size_bounds(constraint, "UTF8String")?),
                Type::PrintableString(None) => render_sized_content("PrintableStringFmt", "PrintableStringFmt", "TagFmt::PRINTABLE_STRING", string_size_bounds(constraint, "PrintableString")?),
                Type::IA5String(None) => render_sized_content("Ia5StringFmt", "Ia5StringFmt", "TagFmt::IA5_STRING", string_size_bounds(constraint, "IA5String")?),
                Type::TeletexString(None) => render_sized_content("TeletexStringFmt", "TeletexStringFmt", "TagFmt::TELETEX_STRING", string_size_bounds(constraint, "TeletexString")?),
                Type::BmpString(None) => render_sized_content("BmpStringFmt", "BmpStringFmt", "TagFmt::BMP_STRING", string_size_bounds(constraint, "BMPString")?),
                Type::Integer(None, _) => {
                    render_constrained_integer(integer_value_bounds(constraint, "INTEGER")?)
                }
                _ => unreachable!("validated constrained type"),
            },
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Enumerated(_)
            | Type::Set(_)
            | Type::SetOf(_, _)
            | Type::RelativeOid
            | Type::UniversalString(_)
            | Type::GeneralString(_)
            | Type::NumericString(_)
            | Type::VisibleString(_)
            | Type::AnyDefinedBy(_)
            | Type::Class(_) => {
                return Err(CodegenError::new(
                    "internal",
                    "unsupported or unlowered inline ASN.1 type reached format rendering",
                ));
            }
        })
    }

    fn render_sequence_fields(
        &self,
        fields: &[SequenceField],
        path: &str,
    ) -> Result<Rendered, CodegenError> {
        let mut result = Rendered {
            ty: "Eof".to_string(),
            expr: "Eof".to_string(),
            shape: TagShape::Untagged,
        };

        for field in fields.iter().rev() {
            let field_rendered = self.render_type(&field.ty)?;
            result = if let Some(default) = &field.default {
                let default =
                    self.render_default(&field.ty, default, &format!("{path}.{}", field.name))?;
                Rendered {
                    ty: format!(
                        "DefaultedFmt<{}, {}, {}, DER>",
                        field_rendered.ty, default.ty, result.ty
                    ),
                    expr: format!(
                        "DEFAULT({}, {}, {})",
                        field_rendered.expr, default.expr, result.expr
                    ),
                    shape: TagShape::Untagged,
                }
            } else {
                let field_rendered = wrap_ref(field_rendered);
                let (ty_constructor, expr_constructor) = if field.optional {
                    ("Optional", "OPTIONAL")
                } else {
                    ("Pair", "REQUIRED")
                };
                Rendered {
                    ty: format!("{ty_constructor}<{}, {}>", field_rendered.ty, result.ty),
                    expr: format!(
                        "{expr_constructor}({}, {})",
                        field_rendered.expr, result.expr
                    ),
                    shape: TagShape::Untagged,
                }
            };
        }
        Ok(result)
    }

    fn render_choice_raw(&self, variants: &[ChoiceVariant]) -> Result<Rendered, CodegenError> {
        let rendered = variants
            .iter()
            .map(|variant| self.render_type(&variant.ty).map(wrap_ref))
            .collect::<Result<Vec<_>, _>>()?;
        let mut result = rendered
            .last()
            .cloned()
            .expect("empty CHOICE rejected during validation");
        for variant in rendered[..rendered.len() - 1].iter().rev() {
            result = Rendered {
                ty: format!("Choice<{}, {}>", variant.ty, result.ty),
                expr: format!("CHOICE({}, {})", variant.expr, result.expr),
                shape: TagShape::Untagged,
            };
        }
        result.shape = TagShape::Untagged;
        Ok(result)
    }

    fn render_tagged(&self, tag: &TagInfo, inner_ty: &Type) -> Result<Rendered, CodegenError> {
        let inner = self.render_type(inner_ty)?;
        match (tag.tagging.clone(), inner.shape) {
            (Tagging::Explicit, TagShape::Untagged) => Ok(Rendered {
                ty: format!("ASN1Fmt<{}, DER>", inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr),
                shape: TagShape::Tlv { constructed: true },
            }),
            (Tagging::Explicit, TagShape::Tlv { .. }) => Ok(Rendered {
                ty: format!("ASN1Fmt<{}, DER>", inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr),
                shape: TagShape::Tlv { constructed: true },
            }),
            (Tagging::Implicit, TagShape::Untagged) => Ok(Rendered {
                ty: format!("ASN1Fmt<{}, DER>", inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr),
                shape: TagShape::Tlv { constructed: true },
            }),
            (Tagging::Implicit, TagShape::Tlv { constructed }) => Ok(Rendered {
                ty: inner.ty,
                expr: render_retag_helper(tag, false, &inner.expr),
                shape: TagShape::Tlv { constructed },
            }),
        }
    }

    fn tag_shape(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<TagShape, CodegenError> {
        match ty {
            Type::Choice(_) | Type::Any => Ok(TagShape::Untagged),
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving tags",
                    ));
                }
                let shape = self.tag_shape(&self.definition(name)?.ty, visiting)?;
                visiting.remove(name);
                Ok(shape)
            }
            Type::Tagged { tag, inner } => match tag.tagging {
                Tagging::Explicit => Ok(TagShape::Tlv { constructed: true }),
                Tagging::Implicit => match self.tag_shape(inner, visiting)? {
                    TagShape::Untagged => Ok(TagShape::Tlv { constructed: true }),
                    shape => Ok(shape),
                },
            },
            Type::Sequence(_) | Type::SequenceOf(_, _) | Type::Set(_) | Type::SetOf(_, _) => {
                Ok(TagShape::Tlv { constructed: true })
            }
            Type::Constrained { base_type, .. } => self.tag_shape(base_type, visiting),
            _ => Ok(TagShape::Tlv { constructed: false }),
        }
    }

    fn tag_domain(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<TagDomain, CodegenError> {
        let singleton = |class, number, constructed| {
            TagDomain::Finite(BTreeSet::from([WireTag {
                class,
                number,
                constructed,
            }]))
        };
        Ok(match ty {
            Type::Boolean => singleton(0, 1, false),
            Type::Integer(_, _) => singleton(0, 2, false),
            Type::BitString(_) => singleton(0, 3, false),
            Type::OctetString(_) => singleton(0, 4, false),
            Type::Null => singleton(0, 5, false),
            Type::ObjectIdentifier => singleton(0, 6, false),
            Type::Real => singleton(0, 9, false),
            Type::Enumerated(_) => singleton(0, 10, false),
            Type::Utf8String(_) => singleton(0, 12, false),
            Type::RelativeOid => singleton(0, 13, false),
            Type::Sequence(_) | Type::SequenceOf(_, _) => singleton(0, 16, true),
            Type::Set(_) | Type::SetOf(_, _) => singleton(0, 17, true),
            Type::NumericString(_) => singleton(0, 18, false),
            Type::PrintableString(_) => singleton(0, 19, false),
            Type::TeletexString(_) => singleton(0, 20, false),
            Type::IA5String(_) => singleton(0, 22, false),
            Type::UtcTime => singleton(0, 23, false),
            Type::GeneralizedTime => singleton(0, 24, false),
            Type::VisibleString(_) => singleton(0, 26, false),
            Type::GeneralString(_) => singleton(0, 27, false),
            Type::UniversalString(_) => singleton(0, 28, false),
            Type::BmpString(_) => singleton(0, 30, false),
            Type::Any | Type::AnyDefinedBy(_) => TagDomain::Open,
            Type::Choice(variants) => {
                let mut domain = TagDomain::Finite(BTreeSet::new());
                for variant in variants {
                    domain = union_domains(domain, self.tag_domain(&variant.ty, visiting)?);
                }
                domain
            }
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving tags",
                    ));
                }
                let domain = self.tag_domain(&self.definition(name)?.ty, visiting)?;
                visiting.remove(name);
                domain
            }
            Type::Tagged { tag, inner } => {
                let constructed = match tag.tagging {
                    Tagging::Explicit => true,
                    Tagging::Implicit => match self.tag_shape(inner, &mut BTreeSet::new())? {
                        TagShape::Tlv { constructed } => constructed,
                        TagShape::Untagged => true,
                    },
                };
                singleton(tag_class_id(&tag.class), tag.number, constructed)
            }
            Type::Constrained { base_type, .. } => self.tag_domain(base_type, visiting)?,
            Type::Class(_) => TagDomain::Open,
        })
    }

    fn exec_type(&self, ty: &Type, lifetime: &str) -> Result<String, CodegenError> {
        Ok(match ty {
            Type::TypeRef(name) => {
                let names = &self.names[name];
                format!(
                    "{}{}",
                    names.value,
                    lifetime_application(self.borrows[name], lifetime)
                )
            }
            Type::Integer(_, _) => format!("vest_lib2::asn1::Integer<{lifetime}>"),
            Type::Boolean => "bool".to_string(),
            Type::OctetString(_) => format!("&{lifetime} [u8]"),
            Type::BitString(_) => format!("vest_lib2::asn1::BitString<{lifetime}, DER>"),
            Type::ObjectIdentifier => {
                format!("vest_lib2::asn1::ObjectIdentifier<{lifetime}>")
            }
            Type::Real => format!("vest_lib2::asn1::Real<{lifetime}>"),
            Type::Null => "()".to_string(),
            Type::Utf8String(_) => format!("&{lifetime} str"),
            Type::PrintableString(_) => {
                format!("vest_lib2::asn1::PrintableString<{lifetime}>")
            }
            Type::IA5String(_) => format!("vest_lib2::asn1::Ia5String<{lifetime}>"),
            Type::TeletexString(_) => {
                format!("vest_lib2::asn1::TeletexString<{lifetime}>")
            }
            Type::BmpString(_) => format!("vest_lib2::asn1::BmpString<{lifetime}>"),
            Type::UtcTime => "vest_lib2::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => {
                format!("vest_lib2::asn1::GeneralizedTime<{lifetime}>")
            }
            Type::Any => format!("vest_lib2::asn1::Any<{lifetime}>"),
            Type::SequenceOf(inner, _) => {
                format!("Vec<{}>", self.exec_type(inner, lifetime)?)
            }
            Type::Tagged { inner, .. } => self.exec_type(inner, lifetime)?,
            Type::Constrained { base_type, .. } => self.exec_type(base_type, lifetime)?,
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Enumerated(_)
            | Type::Set(_)
            | Type::SetOf(_, _)
            | Type::RelativeOid
            | Type::UniversalString(_)
            | Type::GeneralString(_)
            | Type::NumericString(_)
            | Type::VisibleString(_)
            | Type::AnyDefinedBy(_)
            | Type::Class(_) => {
                return Err(CodegenError::new(
                    "internal",
                    "unsupported or unlowered inline type reached value rendering",
                ));
            }
        })
    }

    fn spec_type(&self, ty: &Type) -> Result<String, CodegenError> {
        Ok(match ty {
            Type::TypeRef(name) => self.names[name].spec.clone(),
            Type::Integer(_, _) | Type::Enumerated(_) => "int".to_string(),
            Type::Boolean => "bool".to_string(),
            Type::OctetString(_) => "Seq<u8>".to_string(),
            Type::BitString(_) => "vest_lib2::asn1::BitStringSpec".to_string(),
            Type::ObjectIdentifier => "vest_lib2::asn1::ObjectIdentifierSpec".to_string(),
            Type::Real => "vest_lib2::asn1::RealSpec".to_string(),
            Type::Null => "()".to_string(),
            Type::Utf8String(_) => "Seq<char>".to_string(),
            Type::PrintableString(_) => "vest_lib2::asn1::PrintableStringSpec".to_string(),
            Type::IA5String(_) => "vest_lib2::asn1::Ia5StringSpec".to_string(),
            Type::TeletexString(_) => "vest_lib2::asn1::TeletexStringSpec".to_string(),
            Type::BmpString(_) => "vest_lib2::asn1::BmpStringSpec".to_string(),
            Type::UtcTime => "vest_lib2::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => "vest_lib2::asn1::GeneralizedTimeSpec".to_string(),
            Type::Any => "vest_lib2::asn1::AnySpec".to_string(),
            Type::SequenceOf(inner, _) => format!("Seq<{}>", self.spec_type(inner)?),
            Type::Tagged { inner, .. } => self.spec_type(inner)?,
            Type::Constrained { base_type, .. } => self.spec_type(base_type)?,
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Set(_)
            | Type::SetOf(_, _)
            | Type::RelativeOid
            | Type::UniversalString(_)
            | Type::GeneralString(_)
            | Type::NumericString(_)
            | Type::VisibleString(_)
            | Type::AnyDefinedBy(_)
            | Type::Class(_) => {
                return Err(CodegenError::new(
                    "internal",
                    "unsupported or unlowered inline type reached spec-value rendering",
                ));
            }
        })
    }

    fn render_default(
        &self,
        ty: &Type,
        default: &str,
        path: &str,
    ) -> Result<RenderedDefault, CodegenError> {
        let (base, base_name) = self.resolve_base_type(ty, &mut BTreeSet::new())?;
        match base {
            Type::Boolean => {
                if default.eq_ignore_ascii_case("TRUE") {
                    Ok(RenderedDefault {
                        ty: "bool".to_string(),
                        expr: "true".to_string(),
                    })
                } else if default.eq_ignore_ascii_case("FALSE") {
                    Ok(RenderedDefault {
                        ty: "bool".to_string(),
                        expr: "false".to_string(),
                    })
                } else {
                    Err(CodegenError::new(
                        path,
                        format!("`{default}` is not a BOOLEAN DEFAULT value"),
                    ))
                }
            }
            Type::Enumerated(values) => {
                let value = lookup_named_number(values, default, path)?;
                let enum_name = base_name.ok_or_else(|| {
                    CodegenError::new(path, "anonymous ENUMERATED default was not lowered")
                })?;
                let rust_type = &self.names[enum_name].value;
                Ok(RenderedDefault {
                    ty: rust_type.clone(),
                    expr: format!("{rust_type}::{}", rust_variant_name(&value.name)),
                })
            }
            _ => Err(CodegenError::new(
                path,
                "only BOOLEAN and ENUMERATED DEFAULT values are currently supported",
            )),
        }
    }

    fn resolve_base_type<'b>(
        &'b self,
        ty: &'b Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<(&'b Type, Option<&'b str>), CodegenError> {
        match ty {
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive reference while resolving scalar type",
                    ));
                }
                let definition = self.definition(name)?;
                let (base, nested_name) = self.resolve_base_type(&definition.ty, visiting)?;
                visiting.remove(name);
                Ok((base, nested_name.or(Some(definition.name.as_str()))))
            }
            Type::Tagged { inner, .. } => self.resolve_base_type(inner, visiting),
            Type::Constrained { base_type, .. } => self.resolve_base_type(base_type, visiting),
            _ => Ok((ty, None)),
        }
    }

    fn build_oid_registry(&self) -> Result<BTreeMap<String, Vec<u32>>, CodegenError> {
        let assignments = self
            .schema
            .values
            .iter()
            .filter_map(|assignment| {
                let (base, _) = self
                    .resolve_base_type(&assignment.ty, &mut BTreeSet::new())
                    .ok()?;
                if matches!(base, Type::ObjectIdentifier) {
                    Some((assignment.name.as_str(), assignment))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, _>>();
        let mut registry = BTreeMap::new();
        for name in assignments.keys() {
            resolve_oid_assignment(name, &assignments, &mut registry, &mut BTreeSet::new())?;
        }
        Ok(registry)
    }

    fn render_value_constant(
        &self,
        assignment: &SchemaValueAssignment,
        oid_registry: &BTreeMap<String, Vec<u32>>,
        output: &mut String,
    ) -> Result<(), CodegenError> {
        let constant = value_const_name(&assignment.name);
        let (base, base_name) = self.resolve_base_type(&assignment.ty, &mut BTreeSet::new())?;
        let declared_type = self.exec_type(&assignment.ty, "'static")?;
        match (base, &assignment.value) {
            (Type::Boolean, SchemaValue::Boolean(value)) => {
                writeln!(output, "pub const {constant}: {declared_type} = {value};").unwrap();
            }
            (Type::Integer(_, named), value) => {
                let integer = match value {
                    SchemaValue::Integer(value) => *value,
                    SchemaValue::Identifier(value) => {
                        lookup_named_number(named, value, &assignment.name)?.value
                    }
                    _ => unreachable!("validated integer assignment"),
                };
                writeln!(
                    output,
                    "pub const {constant}: {declared_type} = vest_lib2::asn1::Integer::from_i64({integer}i64);"
                )
                .unwrap();
            }
            (Type::Enumerated(values), value) => {
                let member = match value {
                    SchemaValue::Integer(number) => values
                        .iter()
                        .find(|value| value.value == *number)
                        .expect("validated ENUMERATED number"),
                    SchemaValue::Identifier(name) => {
                        lookup_named_number(values, name, &assignment.name)?
                    }
                    _ => unreachable!("validated ENUMERATED assignment"),
                };
                let enum_definition = base_name.ok_or_else(|| {
                    CodegenError::new(
                        &assignment.name,
                        "ENUMERATED assignment must refer to a named ENUMERATED type",
                    )
                })?;
                let enum_type = &self.names[enum_definition].value;
                writeln!(
                    output,
                    "pub const {constant}: {declared_type} = {enum_type}::{};",
                    rust_variant_name(&member.name)
                )
                .unwrap();
            }
            (Type::ObjectIdentifier, SchemaValue::ObjectIdentifier(_)) => {
                let arcs = &oid_registry[&assignment.name];
                let contents = encode_oid_contents(arcs, &assignment.name)?;
                let bytes = contents
                    .iter()
                    .map(|byte| format!("0x{byte:02x}u8"))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(
                    output,
                    "pub const {constant}: {declared_type} = vest_lib2::asn1::ObjectIdentifier::from_static_der_contents_unchecked(&[{bytes}]);"
                )
                .unwrap();
            }
            _ => unreachable!("value assignment validated before rendering"),
        }
        Ok(())
    }
}

#[derive(Debug)]
struct RenderedDefault {
    ty: String,
    expr: String,
}

fn normalize_definitions(module: &Module) -> Result<Vec<Definition>, CodegenError> {
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

fn lower_root_type(
    ty: &Type,
    parent: &str,
    synthetics: &mut Vec<Definition>,
    used: &mut BTreeSet<String>,
) -> Result<Type, CodegenError> {
    Ok(match ty {
        Type::Sequence(fields) => Type::Sequence(
            fields
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
                .collect::<Result<Vec<_>, CodegenError>>()?,
        ),
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

fn lower_child_type(
    ty: &Type,
    hint: &str,
    synthetics: &mut Vec<Definition>,
    used: &mut BTreeSet<String>,
) -> Result<Type, CodegenError> {
    match ty {
        Type::Sequence(_) | Type::Choice(_) | Type::Enumerated(_) => {
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

fn primitive(ty: &str, expr: &str, constructed: bool) -> Rendered {
    Rendered {
        ty: ty.to_string(),
        expr: expr.to_string(),
        shape: TagShape::Tlv { constructed },
    }
}

fn wrap_ref(rendered: Rendered) -> Rendered {
    Rendered {
        ty: format!("Ref<{}>", rendered.ty),
        expr: format!("Ref({})", rendered.expr),
        shape: rendered.shape,
    }
}

fn render_sized_octet_string(bounds: LengthBounds) -> Rendered {
    render_sized_content("OctetStringFmt", "OctetStringFmt", "TagFmt::OCTET_STRING", bounds)
}

fn render_optionally_sized_string(
    content_type: &str,
    content_expr: &str,
    tag_expr: &str,
    unconstrained_type: &str,
    unconstrained_expr: &str,
    constraint: Option<&SizeConstraint>,
) -> Result<Rendered, CodegenError> {
    match constraint {
        Some(constraint) => Ok(render_sized_content(
            content_type,
            content_expr,
            tag_expr,
            legacy_size_bounds(constraint, unconstrained_expr)?,
        )),
        None => Ok(primitive(unconstrained_type, unconstrained_expr, false)),
    }
}

fn render_sized_content(
    content_type: &str,
    content_expr: &str,
    tag_expr: &str,
    bounds: LengthBounds,
) -> Rendered {
    let (predicate_type, predicate_expr) = render_size_predicate(bounds);
    Rendered {
        ty: format!("ASN1Fmt<Refined<{content_type}, {predicate_type}>, DER>"),
        expr: format!("ASN1Fmt::<_, DER>({tag_expr}, Refined({content_expr}, {predicate_expr}))"),
        shape: TagShape::Tlv { constructed: false },
    }
}

fn render_size_predicate(bounds: LengthBounds) -> (String, String) {
    let has_min = bounds.min.is_some();
    let min = bounds.min.unwrap_or(0);
    let has_max = bounds.max.is_some();
    let max = bounds.max.unwrap_or(0);
    let predicate_type = format!("Size<{has_min}, {min}, {has_max}, {max}>");
    let predicate_expr = format!("Size::<{has_min}, {min}, {has_max}, {max}>");
    (predicate_type, predicate_expr)
}

fn render_constrained_integer(bounds: IntegerBounds) -> Rendered {
    let has_min = bounds.min.is_some();
    let min = bounds.min.unwrap_or(0);
    let has_max = bounds.max.is_some();
    let max = bounds.max.unwrap_or(0);
    let predicate_type = format!("IntegerRange<{has_min}, {min}, {has_max}, {max}>");
    let predicate_expr = format!("IntegerRange::<{has_min}, {min}, {has_max}, {max}>");
    Rendered {
        ty: format!("ASN1Fmt<Refined<IntegerFmt, {predicate_type}>, DER>"),
        expr: format!("ASN1Fmt::<_, DER>(TagFmt::INTEGER, Refined(IntegerFmt, {predicate_expr}))"),
        shape: TagShape::Tlv { constructed: false },
    }
}

fn lifetime_declaration(has_lifetime: bool) -> &'static str {
    if has_lifetime {
        "<'a>"
    } else {
        ""
    }
}

fn lifetime_application(has_lifetime: bool, lifetime: &str) -> String {
    if has_lifetime {
        format!("<{lifetime}>")
    } else {
        String::new()
    }
}

fn impl_lifetime(has_lifetime: bool) -> &'static str {
    if has_lifetime {
        "<'a>"
    } else {
        ""
    }
}

fn nested_type(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_type(rest)),
    }
}

fn nested_pattern(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_pattern(rest)),
    }
}

fn nested_expression(parts: &[String]) -> String {
    match parts {
        [] => "()".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("({}, {})", first, nested_expression(rest)),
    }
}

fn nested_sum_type(parts: &[String]) -> String {
    match parts {
        [] => "Never".to_string(),
        [only] => only.clone(),
        [first, rest @ ..] => format!("Sum<{}, {}>", first, nested_sum_type(rest)),
    }
}

fn sum_pattern(index: usize, len: usize, binding: &str) -> String {
    if len == 1 {
        binding.to_string()
    } else if index == 0 {
        format!("Sum::Inl({binding})")
    } else {
        format!("Sum::Inr({})", sum_pattern(index - 1, len - 1, binding))
    }
}

fn sum_expression(index: usize, len: usize, value: &str) -> String {
    if len == 1 {
        value.to_string()
    } else if index == 0 {
        format!("Sum::Inl({value})")
    } else {
        format!("Sum::Inr({})", sum_expression(index - 1, len - 1, value))
    }
}

fn choice_branch_access(root: &str, index: usize, len: usize) -> String {
    if len == 1 {
        root.to_string()
    } else if index == 0 {
        format!("({root}).0")
    } else {
        choice_branch_access(&format!("({root}).1"), index - 1, len - 1)
    }
}

fn sequence_field_accesses(root: &str, fields: &[SequenceField]) -> Vec<(String, Option<String>)> {
    let mut accesses = Vec::with_capacity(fields.len());
    let mut node = root.to_string();
    for field in fields {
        let rest = if field.default.is_some() {
            format!("({node}).2")
        } else {
            format!("({node}).1")
        };
        accesses.push((format!("({node}).0"), Some(rest.clone())));
        node = rest;
    }
    accesses
}

fn render_enum_number_match(
    values: &[NamedNumber],
    enum_name: &str,
    output: &mut String,
    indent: usize,
) {
    let padding = " ".repeat(indent);
    writeln!(output, "{padding}match value {{").unwrap();
    for value in values {
        writeln!(
            output,
            "{padding}    {}i16 => {enum_name}::{},",
            value.value,
            rust_variant_name(&value.name)
        )
        .unwrap();
    }
    writeln!(
        output,
        "{padding}    _ => {enum_name}::{},",
        rust_variant_name(&values[0].name)
    )
    .unwrap();
    writeln!(output, "{padding}}}").unwrap();
}

fn render_enum_value_match(
    values: &[NamedNumber],
    enum_name: &str,
    output: &mut String,
    indent: usize,
) {
    let padding = " ".repeat(indent);
    writeln!(output, "{padding}match value {{").unwrap();
    for value in values {
        writeln!(
            output,
            "{padding}    {enum_name}::{} => {}i16,",
            rust_variant_name(&value.name),
            value.value
        )
        .unwrap();
    }
    writeln!(output, "{padding}}}").unwrap();
}

fn domains_overlap(left: &TagDomain, right: &TagDomain) -> bool {
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

fn union_domains(left: TagDomain, right: TagDomain) -> TagDomain {
    match (left, right) {
        (TagDomain::Open, _) | (_, TagDomain::Open) => TagDomain::Open,
        (TagDomain::Finite(mut left), TagDomain::Finite(right)) => {
            left.extend(right);
            TagDomain::Finite(left)
        }
    }
}

fn tag_class_id(class: &TagClass) -> u8 {
    match class {
        TagClass::Universal => 0,
        TagClass::Application => 1,
        TagClass::ContextSpecific => 2,
        TagClass::Private => 3,
    }
}

fn lookup_named_number<'a>(
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

fn resolve_oid_assignment(
    name: &str,
    assignments: &BTreeMap<&str, &SchemaValueAssignment>,
    registry: &mut BTreeMap<String, Vec<u32>>,
    visiting: &mut BTreeSet<String>,
) -> Result<Vec<u32>, CodegenError> {
    if let Some(value) = registry.get(name) {
        return Ok(value.clone());
    }
    if !visiting.insert(name.to_string()) {
        return Err(CodegenError::new(
            name,
            "cycle in OBJECT IDENTIFIER value assignments",
        ));
    }
    let assignment = assignments[name];
    let SchemaValue::ObjectIdentifier(components) = &assignment.value else {
        unreachable!();
    };
    let mut arcs = Vec::new();
    for component in components {
        match component {
            OidComponent::Number(number) => arcs.push(*number),
            OidComponent::NamedRef(reference) => {
                if assignments.contains_key(reference.as_str()) {
                    arcs.extend(resolve_oid_assignment(
                        reference,
                        assignments,
                        registry,
                        visiting,
                    )?);
                } else if let Some(root) = builtin_oid_arc(reference) {
                    arcs.push(root);
                } else {
                    return Err(CodegenError::new(
                        name,
                        format!("unknown OBJECT IDENTIFIER reference `{reference}`"),
                    ));
                }
            }
        }
    }
    visiting.remove(name);
    validate_oid_arcs(&arcs, name)?;
    registry.insert(name.to_string(), arcs.clone());
    Ok(arcs)
}

fn builtin_oid_arc(name: &str) -> Option<u32> {
    match name.to_ascii_lowercase().as_str() {
        "itu-t" | "ccitt" => Some(0),
        "iso" => Some(1),
        "joint-iso-itu-t" | "joint-iso-ccitt" => Some(2),
        _ => None,
    }
}

fn validate_oid_arcs(arcs: &[u32], path: &str) -> Result<(), CodegenError> {
    if arcs.len() < 2 {
        return Err(CodegenError::new(
            path,
            "OBJECT IDENTIFIER must contain at least two arcs",
        ));
    }
    if arcs[0] > 2 {
        return Err(CodegenError::new(
            path,
            "OBJECT IDENTIFIER first arc must be 0, 1, or 2",
        ));
    }
    if arcs[0] < 2 && arcs[1] >= 40 {
        return Err(CodegenError::new(
            path,
            "OBJECT IDENTIFIER second arc must be below 40 when the first arc is 0 or 1",
        ));
    }
    Ok(())
}

fn encode_oid_contents(arcs: &[u32], path: &str) -> Result<Vec<u8>, CodegenError> {
    validate_oid_arcs(arcs, path)?;
    let mut output = Vec::new();
    push_base128(
        &mut output,
        if arcs[0] < 2 {
            u64::from(arcs[0]) * 40 + u64::from(arcs[1])
        } else {
            80 + u64::from(arcs[1])
        },
    );
    for arc in &arcs[2..] {
        push_base128(&mut output, u64::from(*arc));
    }
    Ok(output)
}

fn push_base128(output: &mut Vec<u8>, mut value: u64) {
    let mut bytes = [0u8; 10];
    let mut start = bytes.len() - 1;
    bytes[start] = (value & 0x7f) as u8;
    value >>= 7;
    while value != 0 {
        start -= 1;
        bytes[start] = ((value & 0x7f) as u8) | 0x80;
        value >>= 7;
    }
    output.extend_from_slice(&bytes[start..]);
}

fn legacy_size_bounds(
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

fn string_size_bounds(
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

fn integer_value_bounds(
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
        return Err(CodegenError::new(path, "only INTEGER value ranges are supported yet"));
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
                    return Err(CodegenError::new(path, "invalid or unresolved INTEGER lower bound"));
                }
            },
            max: match max {
                ConstraintValue::Max => None,
                ConstraintValue::Integer(value) => Some(*value),
                ConstraintValue::Min | ConstraintValue::NamedValue(_) => {
                    return Err(CodegenError::new(path, "invalid or unresolved INTEGER upper bound"));
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
        return Err(CodegenError::new(path, "INTEGER constraint minimum exceeds maximum"));
    }
    Ok(bounds)
}

fn finite_size_value(
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

fn lower_size_bound(value: &ConstraintValue, path: &str) -> Result<Option<usize>, CodegenError> {
    match value {
        ConstraintValue::Min => Ok(None),
        ConstraintValue::Integer(_) => finite_size_value(value, path, "minimum SIZE").map(Some),
        _ => Err(CodegenError::new(
            path,
            "minimum SIZE must be an integer or MIN",
        )),
    }
}

fn upper_size_bound(value: &ConstraintValue, path: &str) -> Result<Option<usize>, CodegenError> {
    match value {
        ConstraintValue::Max => Ok(None),
        ConstraintValue::Integer(_) => finite_size_value(value, path, "maximum SIZE").map(Some),
        _ => Err(CodegenError::new(
            path,
            "maximum SIZE must be an integer or MAX",
        )),
    }
}

fn validate_length_bounds(bounds: LengthBounds, path: &str) -> Result<LengthBounds, CodegenError> {
    if matches!((bounds.min, bounds.max), (Some(min), Some(max)) if min > max) {
        return Err(CodegenError::new(
            path,
            "minimum SIZE is greater than maximum SIZE",
        ));
    }
    Ok(bounds)
}

fn render_retag_helper(tag: &TagInfo, explicit: bool, inner: &str) -> String {
    let helper = match (&tag.class, explicit) {
        (TagClass::ContextSpecific, false) => "IMPLICIT",
        (TagClass::ContextSpecific, true) => "EXPLICIT",
        (TagClass::Application, false) => "IMPLICIT_APPLICATION",
        (TagClass::Application, true) => "EXPLICIT_APPLICATION",
        (TagClass::Private, false) => "IMPLICIT_PRIVATE",
        (TagClass::Private, true) => "EXPLICIT_PRIVATE",
        (TagClass::Universal, false) => {
            return format!("Implicit(Class::Universal, {}u64, {inner})", tag.number);
        }
        (TagClass::Universal, true) => {
            return format!("Explicit(Class::Universal, {}u64, {inner})", tag.number);
        }
    };
    format!("{helper}({}u64, {inner})", tag.number)
}

fn pretty_format_expr(expr: &str, indent: usize) -> String {
    let expr = expr.trim();
    if is_sequence_chain(expr) {
        return pretty_format_sequence_chain(expr, indent, "");
    }
    let Some((head, opener, inner)) = split_root_group(expr) else {
        return format!("{}{expr}", " ".repeat(indent));
    };

    if opener == '{' {
        let fields = split_top_level(inner);
        let mut output = format!("{}{} {{", " ".repeat(indent), head.trim_end());
        for field in fields {
            let Some((name, value)) = split_struct_field(field) else {
                output.push('\n');
                output.push_str(&pretty_format_expr(field, indent + 4));
                output.push(',');
                continue;
            };
            let pretty_value = pretty_format_expr(value, indent + 4);
            output.push('\n');
            if pretty_value.contains('\n') {
                output.push_str(&format!("{}{}:\n", " ".repeat(indent + 4), name.trim()));
                output.push_str(&pretty_format_expr(value, indent + 8));
            } else {
                output.push_str(&format!(
                    "{}{}: {}",
                    " ".repeat(indent + 4),
                    name.trim(),
                    pretty_value.trim_start()
                ));
            }
            output.push(',');
        }
        output.push('\n');
        output.push_str(&format!("{}}}", " ".repeat(indent)));
        return output;
    }

    let args = split_top_level(inner);
    let pretty_args = args
        .iter()
        .map(|arg| pretty_format_expr(arg, indent + 4))
        .collect::<Vec<_>>();
    let force_multiline = matches!(
        head.trim(),
        "REQUIRED"
            | "OPTIONAL"
            | "DEFAULT"
            | "CHOICE"
            | "ASN1Fmt::<_, DER>"
    );
    let multiline = force_multiline
        || pretty_args.iter().any(|arg| arg.contains('\n'))
        || expr.len() + indent > 92;
    if !multiline {
        return format!(
            "{}{}({})",
            " ".repeat(indent),
            head.trim(),
            pretty_args
                .iter()
                .map(|arg| arg.trim())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }

    let mut output = format!("{}{}(", " ".repeat(indent), head.trim());
    for arg in pretty_args {
        output.push('\n');
        output.push_str(&arg);
        output.push(',');
    }
    output.push('\n');
    output.push_str(&format!("{})", " ".repeat(indent)));
    output
}

fn is_sequence_chain(expr: &str) -> bool {
    if expr.trim() == "Eof" {
        return true;
    }
    split_root_group(expr).is_some_and(|(head, opener, _)| {
        opener == '(' && matches!(head.trim(), "REQUIRED" | "OPTIONAL" | "DEFAULT")
    })
}

fn pretty_format_sequence_chain(expr: &str, indent: usize, closing: &str) -> String {
    let expr = expr.trim();
    if expr == "Eof" {
        return format!("{}Eof{closing}", " ".repeat(indent));
    }
    let Some((head, '(', inner)) = split_root_group(expr) else {
        return format!("{}{}{closing}", " ".repeat(indent), expr);
    };
    let args = split_top_level(inner);
    let continuation_index = match head.trim() {
        "REQUIRED" | "OPTIONAL" if args.len() == 2 => 1,
        "DEFAULT" if args.len() == 3 => 2,
        _ => return format!("{}{}{closing}", " ".repeat(indent), expr),
    };
    let current_args = args[..continuation_index].join(", ");
    let continuation = args[continuation_index];
    format!(
        "{}{}({},\n{}",
        " ".repeat(indent),
        head.trim(),
        current_args,
        pretty_format_sequence_chain(continuation, indent, &format!("){closing}"))
    )
}

fn split_root_group(expr: &str) -> Option<(&str, char, &str)> {
    let bytes = expr.as_bytes();
    let mut stack = Vec::<u8>::new();
    for (index, byte) in bytes.iter().copied().enumerate() {
        match byte {
            b'<' | b'[' => stack.push(byte),
            b'>' => {
                if stack.last() == Some(&b'<') {
                    stack.pop();
                }
            }
            b']' => {
                if stack.last() == Some(&b'[') {
                    stack.pop();
                }
            }
            b'(' | b'{' if stack.is_empty() => {
                let close = if byte == b'(' { b')' } else { b'}' };
                let end = matching_delimiter(bytes, index, byte, close)?;
                if end + 1 == bytes.len() {
                    return Some((&expr[..index], byte as char, &expr[index + 1..end]));
                }
                return None;
            }
            _ => {}
        }
    }
    None
}

fn matching_delimiter(bytes: &[u8], start: usize, open: u8, close: u8) -> Option<usize> {
    let mut depth = 0usize;
    for (index, byte) in bytes.iter().copied().enumerate().skip(start) {
        if byte == open {
            depth += 1;
        } else if byte == close {
            depth -= 1;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

fn split_top_level(input: &str) -> Vec<&str> {
    let bytes = input.as_bytes();
    let mut stack = Vec::<u8>::new();
    let mut start = 0usize;
    let mut parts = Vec::new();
    for (index, byte) in bytes.iter().copied().enumerate() {
        match byte {
            b'(' | b'{' | b'[' | b'<' => stack.push(byte),
            b')' => {
                if stack.last() == Some(&b'(') { stack.pop(); }
            }
            b'}' => {
                if stack.last() == Some(&b'{') { stack.pop(); }
            }
            b']' => {
                if stack.last() == Some(&b'[') { stack.pop(); }
            }
            b'>' => {
                if stack.last() == Some(&b'<') { stack.pop(); }
            }
            b',' if stack.is_empty() => {
                parts.push(input[start..index].trim());
                start = index + 1;
            }
            _ => {}
        }
    }
    if start < input.len() || parts.is_empty() {
        parts.push(input[start..].trim());
    }
    parts.into_iter().filter(|part| !part.is_empty()).collect()
}

fn split_struct_field(field: &str) -> Option<(&str, &str)> {
    let bytes = field.as_bytes();
    let mut stack = Vec::<u8>::new();
    for (index, byte) in bytes.iter().copied().enumerate() {
        match byte {
            b'(' | b'{' | b'[' | b'<' => stack.push(byte),
            b')' | b'}' | b']' | b'>' => { stack.pop(); }
            b':' if stack.is_empty()
                && bytes.get(index.wrapping_sub(1)) != Some(&b':')
                && bytes.get(index + 1) != Some(&b':') =>
            {
                return Some((&field[..index], &field[index + 1..]));
            }
            _ => {}
        }
    }
    None
}

fn collect_type_refs<'a>(ty: &'a Type, output: &mut Vec<&'a str>) {
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
