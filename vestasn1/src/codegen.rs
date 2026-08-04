//! Nominal Rust/Vest backend for the lossless ASN.1 frontend.

use crate::error::CodegenError;
use crate::frontend::{SchemaModule, SchemaValue, SchemaValueAssignment};
use crate::naming::{
    format_type_name, rust_field_name, rust_variant_name, spec_type_name, value_const_name,
    value_type_name,
};
use std::collections::{BTreeMap, BTreeSet};
use synta_codegen::ast::{
    ChoiceVariant, Constraint, ConstraintSpec, ConstraintValue, Definition, Module, NamedNumber,
    SequenceField, SizeConstraint, SubtypeConstraint, TagClass, TagInfo, Tagging, TaggingMode,
    Type,
};

mod analysis;
mod formats;
mod helpers;
mod normalize;
mod values;

use helpers::*;
use normalize::*;

/// ASN.1 encoding rules used by generated formats.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum EncodingRules {
    /// Distinguished Encoding Rules.
    #[default]
    Der,
    /// Basic Encoding Rules, including constructed and indefinite-length forms
    /// supported by `vest_lib2`.
    Ber,
}

impl EncodingRules {
    fn module(self) -> &'static str {
        match self {
            Self::Der => "der",
            Self::Ber => "ber",
        }
    }

    fn display(self) -> &'static str {
        match self {
            Self::Der => "DER",
            Self::Ber => "BER",
        }
    }
}

/// Configuration for one code-generation invocation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CodegenOptions {
    pub encoding_rules: EncodingRules,
}

pub fn generate(schema: &SchemaModule) -> Result<String, CodegenError> {
    generate_with_options(schema, CodegenOptions::default())
}

pub fn generate_with_options(
    schema: &SchemaModule,
    options: CodegenOptions,
) -> Result<String, CodegenError> {
    Generator::new(schema, options, &BTreeMap::new())?.generate()
}

/// Generate one nominal-format module with selected definitions forced to a
/// different encoding rule. Non-overridden references inherit the caller's
/// rule; a shared definition is emitted once per rule when both are needed.
pub fn generate_with_rule_overrides(
    schema: &SchemaModule,
    options: CodegenOptions,
    definition_rules: &BTreeMap<String, EncodingRules>,
) -> Result<String, CodegenError> {
    Generator::new(schema, options, definition_rules)?.generate()
}

struct Generator<'a> {
    module: &'a Module,
    definitions: Vec<Definition>,
    definition_index: BTreeMap<String, usize>,
    names: BTreeMap<String, Names>,
    borrows: BTreeMap<String, bool>,
    rules: BTreeMap<String, EncodingRules>,
    values: Vec<SchemaValueAssignment>,
    mixed_rules: bool,
    options: CodegenOptions,
}

impl<'a> Generator<'a> {
    fn new(
        schema: &'a SchemaModule,
        options: CodegenOptions,
        definition_rules: &BTreeMap<String, EncodingRules>,
    ) -> Result<Self, CodegenError> {
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

        let normalized = normalize_definitions(module)?;
        let (definitions, rules, values) = expand_rule_variants(
            normalized,
            &schema.values,
            options.encoding_rules,
            definition_rules,
        )?;
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
            let inner_format = format!("{format}__");
            for generated in [&value, &spec, &format, &inner_format] {
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
            names.insert(
                definition.name.clone(),
                Names {
                    forward: format!("{value}Forward"),
                    reverse: format!("{value}Reverse"),
                    predicate: format!("{value}Predicate"),
                    value,
                    spec,
                    format,
                    inner_format,
                },
            );
        }

        for assignment in &values {
            let constant = value_const_name(&assignment.name);
            if let Some(previous) = rust_consts.insert(constant.clone(), assignment.name.clone()) {
                return Err(CodegenError::new(
                    &assignment.name,
                    format!("generated Rust constant name `{constant}` collides with `{previous}`"),
                ));
            }
        }

        let mut generator = Self {
            module,
            definitions,
            definition_index,
            names,
            borrows: BTreeMap::new(),
            rules,
            values,
            mixed_rules: !definition_rules.is_empty(),
            options,
        };
        generator.compute_lifetimes()?;
        generator.validate()?;
        Ok(generator)
    }
}

impl<'a> Generator<'a> {
    pub(super) fn generate(&self) -> Result<String, CodegenError> {
        let mut output = CodeWriter::new();
        output.line(format_args!(
            "// @generated by vestasn1 from ASN.1 module `{}`.",
            self.module.name
        ));
        output.line(format_args!(
            "// Generated formats parse and serialize {}.",
            if self.mixed_rules {
                "a schema-selected mixture of BER and DER"
            } else {
                self.options.encoding_rules.display()
            }
        ));
        output.line(format_args!("#![allow(unused_imports)]"));
        output.line(format_args!("#![allow(non_camel_case_types)]"));
        output.line(format_args!("#![allow(non_upper_case_globals)]"));
        output.blank_line();
        output.line(format_args!("use vest_lib2::asn1::*;"));
        output.line(format_args!(
            "use vest_lib2::asn1::der_ord::{{DerOrd, DerState}};"
        ));
        output.line(format_args!("use vest_lib2::asn1::disjoint::HasAsn1Start;"));
        if self.mixed_rules {
            output.line(format_args!(
                "use vest_lib2::asn1::modifiers::{{\
                 implicitly_tagged as Implicit, ImplicitFmt, CHOICE, IMPLICIT, \
                 IMPLICIT_APPLICATION, IMPLICIT_PRIVATE, OPTIONAL, REQUIRED\
                 }};"
            ));
        } else {
            output.line(format_args!("use vest_lib2::asn1::{}::{{\
                 AnyTlvFmt, BitStringTlvFmt, BmpStringTlvFmt, BoolTlvFmt, DefaultFmt, \
                 Enumerated16TlvFmt, EnumeratedTlvFmt, Explicit, ExplicitFmt, GeneralizedTimeTlvFmt, \
                 Ia5StringTlvFmt, Implicit, ImplicitFmt, Integer16TlvFmt, Integer8TlvFmt, \
                 IntegerTlvFmt, NullTlvFmt, ObjectIdentifierTlvFmt, OctetStringTlvFmt, \
                 NumericStringTlvFmt, PrintableStringTlvFmt, RealTlvFmt, SequenceFmt, SequenceOfFmt, \
                 SetOfTlvFmt, TeletexStringTlvFmt, UniversalStringTlvFmt, UtcTimeTlvFmt, \
                 Utf8StringTlvFmt, ANY, BIT_STRING, BMP_STRING, \
                 BOOLEAN, CHOICE, DEFAULT, ENUMERATED, ENUMERATED16, EXPLICIT, \
                 EXPLICIT_APPLICATION, EXPLICIT_PRIVATE, GENERALIZED_TIME, IA5_STRING, IMPLICIT, \
                 IMPLICIT_APPLICATION, IMPLICIT_PRIVATE, INTEGER, INTEGER16, INTEGER8, NULL, \
                 NUMERIC_STRING, OBJECT_IDENTIFIER, OCTET_STRING, OPTIONAL, PRINTABLE_STRING, REAL, \
                 REQUIRED, SEQUENCE, SEQUENCE_OF, SET_OF, TELETEX_STRING, UNIVERSAL_STRING, \
                 UTC_TIME, UTF8_STRING\
                 }};",
                self.options.encoding_rules.module()
            ));
            if self.options.encoding_rules == EncodingRules::Ber {
                output.line(format_args!(
                    "use vest_lib2::asn1::ber::{{BerEndFmt, BER_END}};"
                ));
            } else {
                output.line(format_args!("use vest_lib2::asn1::der::{{SetFmt, SET}};"));
            }
        }
        output.line(format_args!(
            "use vest_lib2::combinators::mapped::spec::{{BiMap, SpecMap}};"
        ));
        output.line(format_args!("use vest_lib2::combinators::*;"));
        output.line(format_args!("use vest_lib2::combinators::Eof;"));
        output.line(format_args!("use Sum::Inl as L;"));
        output.line(format_args!("use Sum::Inr as R;"));
        output.line(format_args!(
            "use vest_lib2::core::exec::fns::{{Map, Pred}};"
        ));
        output.line(format_args!(
            "use vest_lib2::core::exec::output::OutputBuf;"
        ));
        output.line(format_args!(
            "use vest_lib2::core::exec::parser::{{PResult, Parser}};"
        ));
        output.line(format_args!("use vest_lib2::core::exec::serializer::{{ByteLen, PreSerializeError, Prepare, Serializer}};"));
        output.line(format_args!("use vest_lib2::core::proof::*;"));
        output.line(format_args!("use vest_lib2::core::spec::*;"));
        output.line(format_args!(
            "use vstd::prelude::*;
"
        ));
        output.line(format_args!(
            "verus! {{
"
        ));

        for definition in &self.definitions {
            self.render_value_declaration(definition, &mut output)?;
        }
        for definition in &self.definitions {
            self.render_mapper_declaration(definition, &mut output)?;
        }
        for definition in &self.definitions {
            self.render_format_declaration(definition, &mut output)?;
        }

        for assignment in &self.values {
            self.render_value_constant(assignment, &mut output)?;
        }
        output.line(format_args!(
            "
}} // verus!"
        ));
        for definition in &self.definitions {
            self.render_format_impl_invocation(definition, &mut output)?;
        }
        Ok(output.finish())
    }

    fn render_format_impl_invocation(
        &self,
        definition: &Definition,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let rule = self.rules[&definition.name];
        let kind = match self.nominal_kind(definition)? {
            NominalKind::Tagged { constructed } => format!("tagged({constructed})"),
            NominalKind::UntaggedStart => "untagged_start".to_string(),
            NominalKind::Untagged => "untagged".to_string(),
        };
        let ownership = if self.borrows[&definition.name] {
            "borrowed"
        } else {
            "owned"
        };
        let implementation = match rule {
            EncodingRules::Der => "impl_der",
            EncodingRules::Ber => "impl_ber",
        };
        let module = format!("__impl_{}", names.format.to_ascii_lowercase());
        let mapper = match &definition.ty {
            Type::Sequence(_) | Type::Set(_) | Type::Choice(_) | Type::Enumerated(_) => {
                format!(", {}, {}", names.forward, names.reverse)
            }
            _ => String::new(),
        };
        output.blank_line();
        output.line(format_args!("mod {module} {{"));
        output.line(format_args!("    use super::*;"));
        output.blank_line();
        output.line(format_args!(
            "    vest_lib2::{implementation}!({kind}, {ownership}, {}, {}, {}, {}{mapper});",
            names.format, names.inner_format, names.spec, names.value,
        ));
        output.line(format_args!("}}"));
        Ok(())
    }
}
