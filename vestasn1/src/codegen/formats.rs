//! Format combinator lowering and nominal-format emission.

use super::*;

impl<'a> Generator<'a> {
    pub(super) fn render_format_declaration(
        &self,
        definition: &Definition,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let rule = self.rules[&definition.name];
        let rendered = match &definition.ty {
            Type::Sequence(fields) => {
                let sequence = match rule {
                    EncodingRules::Der => {
                        let raw = self.render_sequence_fields(fields, &definition.name, rule)?;
                        Rendered {
                            ty: format!("{}<{}>", self.backend_item(rule, "SequenceFmt"), raw.ty),
                            expr: format!("{}({})", self.backend_item(rule, "SEQUENCE"), raw.expr),
                            shape: TagShape::Tlv { constructed: true },
                        }
                    }
                    EncodingRules::Ber => {
                        let end_ty = self.backend_item(rule, "BerEndFmt");
                        let end_expr = self.backend_item(rule, "BER_END");
                        let raw = self.render_sequence_fields_with_end(
                            fields,
                            &definition.name,
                            &end_ty,
                            &end_expr,
                            rule,
                        )?;
                        Rendered {
                            ty: format!("{}<{}>", self.backend_item(rule, "SequenceFmt"), raw.ty),
                            expr: format!("{}({})", self.backend_item(rule, "SEQUENCE"), raw.expr),
                            shape: TagShape::Tlv { constructed: true },
                        }
                    }
                };
                map_with_bimap(sequence, &names.forward, &names.reverse)
            }
            Type::Set(fields) => {
                debug_assert_eq!(rule, EncodingRules::Der);
                let raw = self.render_sequence_fields(fields, &definition.name, rule)?;
                let set = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SetFmt"), raw.ty),
                    expr: format!("{}({})", self.backend_item(rule, "SET"), raw.expr),
                    shape: TagShape::Tlv { constructed: true },
                };
                map_with_bimap(set, &names.forward, &names.reverse)
            }
            Type::Choice(variants) => {
                let raw = self.render_choice_raw(variants, rule)?;
                map_with_bimap(raw, &names.forward, &names.reverse)
            }
            Type::Enumerated(_) => {
                let wire = Rendered {
                    ty: self.backend_item(rule, "Enumerated16TlvFmt"),
                    expr: self.backend_item(rule, "ENUMERATED16"),
                    shape: TagShape::Tlv { constructed: false },
                };
                let refined = refine(wire, names.predicate.clone(), names.predicate.clone());
                map_with_bimap(refined, &names.forward, &names.reverse)
            }
            ty => self.render_type(ty, rule)?,
        };
        output.line(format_args!(
            "/// {} format for ASN.1 `{}`.",
            rule.display(),
            definition.name
        ));
        output.line(format_args!(
            "type {} = {};",
            names.inner_format, rendered.ty
        ));
        output.line(format_args!("#[derive(Clone, Copy)]"));
        output.line(format_args!("#[verifier::ext_equal]"));
        match self.nominal_kind(definition)? {
            NominalKind::Tagged { constructed } => {
                let (class, number) = self.nominal_tag(definition)?;
                output.line(format_args!(
                    "pub struct {}(pub Class, pub u64);",
                    names.format
                ));
                output.line(format_args!("impl {} {{", names.format));
                output.line(format_args!(
                    "    pub const Fmt: Self = Self({class}, {number}u64);"
                ));
                output.blank_line();
                output.line(format_args!(
                    "    pub open spec fn spec_inner(&self) -> {} {{",
                    names.inner_format
                ));
                output.line(format_args!("        let fmt = {};", rendered.expr));
                output.line(format_args!("        fmt.spec_retagged(Tag {{"));
                output.line(format_args!("            class: self.0,"));
                output.line(format_args!("            constructed: {constructed},"));
                output.line(format_args!(
                    "            number: tag_num_from_uint(self.1),"
                ));
                output.line(format_args!("        }})"));
                output.line(format_args!("    }}"));
                output.blank_line();
                output.line(format_args!(
                    "    pub fn exec_inner(&self) -> (fmt: {})",
                    names.inner_format
                ));
                output.line(format_args!("        ensures fmt == self.spec_inner(),"));
                output.line(format_args!("    {{"));
                output.line(format_args!("        let fmt = {};", rendered.expr));
                output.line(format_args!("        fmt.retagged(Tag {{"));
                output.line(format_args!("            class: self.0,"));
                output.line(format_args!("            constructed: {constructed},"));
                output.line(format_args!(
                    "            number: tag_num_from_uint(self.1),"
                ));
                output.line(format_args!("        }})"));
                output.line(format_args!("    }}"));
                output.line(format_args!(
                    "}}
"
                ));
            }
            NominalKind::UntaggedStart | NominalKind::Untagged => {
                output.line(format_args!("pub struct {};", names.format));
                output.line(format_args!("impl {} {{", names.format));
                output.line(format_args!("    pub const Fmt: Self = Self;"));
                output.blank_line();
                output.line(format_args!(
                    "    pub open spec fn spec_inner(&self) -> {} {{",
                    names.inner_format
                ));
                output.line(format_args!("        let fmt = {};", rendered.expr));
                output.line(format_args!("        fmt"));
                output.line(format_args!("    }}"));
                output.blank_line();
                output.line(format_args!(
                    "    pub fn exec_inner(&self) -> (fmt: {})",
                    names.inner_format
                ));
                output.line(format_args!("        ensures fmt == self.spec_inner(),"));
                output.line(format_args!("    {{"));
                output.line(format_args!("        let fmt = {};", rendered.expr));
                output.line(format_args!("        fmt"));
                output.line(format_args!("    }}"));
                output.line(format_args!(
                    "}}
"
                ));
            }
        }
        Ok(())
    }

    pub(super) fn render_type(
        &self,
        ty: &Type,
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        let backend_primitive = |ty: &str, expr: &str, constructed: bool| {
            primitive(
                &self.backend_item(rule, ty),
                &self.backend_item(rule, expr),
                constructed,
            )
        };
        Ok(match ty {
            Type::SequenceOf(inner, constraint) => {
                let inner = self.render_type(inner, rule)?;
                let sequence_of = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SequenceOfFmt"), inner.ty),
                    expr: format!("{}({})", self.backend_item(rule, "SEQUENCE_OF"), inner.expr),
                    shape: TagShape::Tlv { constructed: true },
                };
                if let Some(constraint) = constraint {
                    let bounds = legacy_size_bounds(constraint, "SEQUENCE OF")?;
                    let (predicate_type, predicate_expr) = render_size_predicate(bounds);
                    refine(sequence_of, predicate_type, predicate_expr)
                } else {
                    sequence_of
                }
            }
            Type::SetOf(inner, constraint) => {
                let inner = self.render_type(inner, rule)?;
                let set_of = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SetOfTlvFmt"), inner.ty),
                    expr: format!("{}({})", self.backend_item(rule, "SET_OF"), inner.expr),
                    shape: TagShape::Tlv { constructed: true },
                };
                if let Some(constraint) = constraint {
                    let bounds = legacy_size_bounds(constraint, "SET OF")?;
                    let (predicate_type, predicate_expr) = render_size_predicate(bounds);
                    refine(set_of, predicate_type, predicate_expr)
                } else {
                    set_of
                }
            }
            Type::TypeRef(name) => {
                let names = &self.names[name];
                Rendered {
                    ty: names.format.clone(),
                    expr: format!("{}::Fmt", names.format),
                    shape: self.tag_shape(ty, &mut BTreeSet::new(), self.rules[name])?,
                }
            }
            Type::Integer(_, _) => backend_primitive("IntegerTlvFmt", "INTEGER", false),
            Type::Boolean => backend_primitive("BoolTlvFmt", "BOOLEAN", false),
            Type::OctetString(constraint) => match constraint {
                Some(constraint) => render_sized_format(
                    &self.backend_item(rule, "OctetStringTlvFmt"),
                    &self.backend_item(rule, "OCTET_STRING"),
                    legacy_size_bounds(constraint, "OCTET STRING")?,
                ),
                None => backend_primitive("OctetStringTlvFmt", "OCTET_STRING", false),
            },
            Type::BitString(_) => backend_primitive("BitStringTlvFmt", "BIT_STRING", false),
            Type::ObjectIdentifier => {
                backend_primitive("ObjectIdentifierTlvFmt", "OBJECT_IDENTIFIER", false)
            }
            Type::Real => backend_primitive("RealTlvFmt", "REAL", false),
            Type::Null => backend_primitive("NullTlvFmt", "NULL", false),
            Type::Utf8String(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "Utf8StringTlvFmt"),
                &self.backend_item(rule, "UTF8_STRING"),
                constraint.as_ref(),
            )?,
            Type::PrintableString(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "PrintableStringTlvFmt"),
                &self.backend_item(rule, "PRINTABLE_STRING"),
                constraint.as_ref(),
            )?,
            Type::IA5String(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "Ia5StringTlvFmt"),
                &self.backend_item(rule, "IA5_STRING"),
                constraint.as_ref(),
            )?,
            Type::TeletexString(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "TeletexStringTlvFmt"),
                &self.backend_item(rule, "TELETEX_STRING"),
                constraint.as_ref(),
            )?,
            Type::BmpString(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "BmpStringTlvFmt"),
                &self.backend_item(rule, "BMP_STRING"),
                constraint.as_ref(),
            )?,
            Type::NumericString(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "NumericStringTlvFmt"),
                &self.backend_item(rule, "NUMERIC_STRING"),
                constraint.as_ref(),
            )?,
            Type::UniversalString(constraint) => render_optionally_sized_string(
                &self.backend_item(rule, "UniversalStringTlvFmt"),
                &self.backend_item(rule, "UNIVERSAL_STRING"),
                constraint.as_ref(),
            )?,
            Type::UtcTime => backend_primitive("UtcTimeTlvFmt", "UTC_TIME", false),
            Type::GeneralizedTime => {
                backend_primitive("GeneralizedTimeTlvFmt", "GENERALIZED_TIME", false)
            }
            Type::Any => Rendered {
                ty: self.backend_item(rule, "AnyTlvFmt"),
                expr: self.backend_item(rule, "ANY"),
                shape: TagShape::Untagged,
            },
            Type::Tagged { tag, inner } => self.render_tagged(tag, inner, rule)?,
            Type::Constrained {
                base_type,
                constraint,
            } => match base_type.as_ref() {
                Type::OctetString(None) => render_sized_format(
                    &self.backend_item(rule, "OctetStringTlvFmt"),
                    &self.backend_item(rule, "OCTET_STRING"),
                    string_size_bounds(constraint, "OCTET STRING")?,
                ),
                Type::Utf8String(None) => render_sized_format(
                    &self.backend_item(rule, "Utf8StringTlvFmt"),
                    &self.backend_item(rule, "UTF8_STRING"),
                    string_size_bounds(constraint, "UTF8String")?,
                ),
                Type::PrintableString(None) => render_sized_format(
                    &self.backend_item(rule, "PrintableStringTlvFmt"),
                    &self.backend_item(rule, "PRINTABLE_STRING"),
                    string_size_bounds(constraint, "PrintableString")?,
                ),
                Type::IA5String(None) => render_sized_format(
                    &self.backend_item(rule, "Ia5StringTlvFmt"),
                    &self.backend_item(rule, "IA5_STRING"),
                    string_size_bounds(constraint, "IA5String")?,
                ),
                Type::TeletexString(None) => render_sized_format(
                    &self.backend_item(rule, "TeletexStringTlvFmt"),
                    &self.backend_item(rule, "TELETEX_STRING"),
                    string_size_bounds(constraint, "TeletexString")?,
                ),
                Type::BmpString(None) => render_sized_format(
                    &self.backend_item(rule, "BmpStringTlvFmt"),
                    &self.backend_item(rule, "BMP_STRING"),
                    string_size_bounds(constraint, "BMPString")?,
                ),
                Type::NumericString(None) => render_sized_format(
                    &self.backend_item(rule, "NumericStringTlvFmt"),
                    &self.backend_item(rule, "NUMERIC_STRING"),
                    string_size_bounds(constraint, "NumericString")?,
                ),
                Type::UniversalString(None) => render_sized_format(
                    &self.backend_item(rule, "UniversalStringTlvFmt"),
                    &self.backend_item(rule, "UNIVERSAL_STRING"),
                    string_size_bounds(constraint, "UniversalString")?,
                ),
                Type::Integer(None, _) => self
                    .render_constrained_integer(integer_value_bounds(constraint, "INTEGER")?, rule),
                _ => unreachable!("validated constrained type"),
            },
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Enumerated(_)
            | Type::Set(_)
            | Type::RelativeOid
            | Type::GeneralString(_)
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

    pub(super) fn render_sequence_fields(
        &self,
        fields: &[SequenceField],
        path: &str,
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        self.render_sequence_fields_with_end(fields, path, "Eof", "Eof", rule)
    }

    pub(super) fn render_sequence_fields_with_end(
        &self,
        fields: &[SequenceField],
        path: &str,
        end_ty: &str,
        end_expr: &str,
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        let mut result = Rendered {
            ty: end_ty.to_string(),
            expr: end_expr.to_string(),
            shape: TagShape::Untagged,
        };

        for field in fields.iter().rev() {
            result = if let Some(default) = &field.default {
                let field_rendered = self.render_type(&field.ty, rule)?;
                let default =
                    self.render_default(&field.ty, default, &format!("{path}.{}", field.name))?;
                Rendered {
                    ty: format!(
                        "{}<{}, {}, {}>",
                        self.backend_item(rule, "DefaultFmt"),
                        field_rendered.ty,
                        default.ty,
                        result.ty
                    ),
                    expr: format!(
                        "{}({}, {}, {})",
                        self.backend_item(rule, "DEFAULT"),
                        field_rendered.expr,
                        default.expr,
                        result.expr
                    ),
                    shape: TagShape::Untagged,
                }
            } else {
                let field_rendered = self.render_type_by_ref(&field.ty, rule)?;
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

    pub(super) fn render_choice_raw(
        &self,
        variants: &[ChoiceVariant],
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        let rendered = variants
            .iter()
            .map(|variant| self.render_type_by_ref(&variant.ty, rule))
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

    pub(super) fn render_tagged(
        &self,
        tag: &TagInfo,
        inner_ty: &Type,
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        let inner = self.render_type(inner_ty, rule)?;
        Ok(self.apply_tag(tag, inner, rule))
    }

    pub(super) fn render_type_by_ref(
        &self,
        ty: &Type,
        rule: EncodingRules,
    ) -> Result<Rendered, CodegenError> {
        match ty {
            Type::Tagged { tag, inner } => {
                let inner = self.render_type_by_ref(inner, rule)?;
                Ok(self.apply_tag(tag, inner, rule))
            }
            _ => self.render_type(ty, rule).map(wrap_ref),
        }
    }

    pub(super) fn apply_tag(
        &self,
        tag: &TagInfo,
        inner: Rendered,
        rule: EncodingRules,
    ) -> Rendered {
        match (tag.tagging.clone(), inner.shape) {
            (Tagging::Explicit, TagShape::Untagged) => Rendered {
                ty: format!("{}<{}>", self.backend_item(rule, "ExplicitFmt"), inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr, self.mixed_rules.then_some(rule)),
                shape: TagShape::Tlv { constructed: true },
            },
            (Tagging::Explicit, TagShape::Tlv { .. }) => Rendered {
                ty: format!("{}<{}>", self.backend_item(rule, "ExplicitFmt"), inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr, self.mixed_rules.then_some(rule)),
                shape: TagShape::Tlv { constructed: true },
            },
            (Tagging::Implicit, TagShape::Untagged) => Rendered {
                ty: format!("{}<{}>", self.backend_item(rule, "ExplicitFmt"), inner.ty),
                expr: render_retag_helper(tag, true, &inner.expr, self.mixed_rules.then_some(rule)),
                shape: TagShape::Tlv { constructed: true },
            },
            (Tagging::Implicit, TagShape::Tlv { constructed }) => Rendered {
                ty: format!("ImplicitFmt<{}>", inner.ty),
                expr: render_retag_helper(tag, false, &inner.expr, None),
                shape: TagShape::Tlv { constructed },
            },
        }
    }

    pub(super) fn tag_shape(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
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
                let shape =
                    self.tag_shape(&self.definition(name)?.ty, visiting, self.rules[name])?;
                visiting.remove(name);
                Ok(shape)
            }
            Type::Tagged { tag, inner } => match tag.tagging {
                Tagging::Explicit => Ok(TagShape::Tlv { constructed: true }),
                Tagging::Implicit => match self.tag_shape(inner, visiting, rule)? {
                    TagShape::Untagged => Ok(TagShape::Tlv { constructed: true }),
                    shape => Ok(shape),
                },
            },
            Type::Sequence(_) | Type::SequenceOf(_, _) | Type::Set(_) | Type::SetOf(_, _) => {
                Ok(TagShape::Tlv { constructed: true })
            }
            Type::Constrained { base_type, .. } => self.tag_shape(base_type, visiting, rule),
            _ => Ok(TagShape::Tlv { constructed: false }),
        }
    }

    pub(super) fn nominal_kind(
        &self,
        definition: &Definition,
    ) -> Result<NominalKind, CodegenError> {
        let rule = self.rules[&definition.name];
        match self.tag_shape(&definition.ty, &mut BTreeSet::new(), rule)? {
            TagShape::Tlv { constructed } => Ok(NominalKind::Tagged { constructed }),
            TagShape::Untagged
                if self.untagged_has_asn1_start(&definition.ty, &mut BTreeSet::new())? =>
            {
                Ok(NominalKind::UntaggedStart)
            }
            TagShape::Untagged => Ok(NominalKind::Untagged),
        }
    }

    pub(super) fn untagged_has_asn1_start(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<bool, CodegenError> {
        Ok(match ty {
            Type::Any => true,
            Type::Constrained { base_type, .. } => {
                self.untagged_has_asn1_start(base_type, visiting)?
            }
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving ASN.1 starts",
                    ));
                }
                let has_start =
                    self.untagged_has_asn1_start(&self.definition(name)?.ty, visiting)?;
                visiting.remove(name);
                has_start
            }
            _ => false,
        })
    }

    pub(super) fn nominal_tag(
        &self,
        definition: &Definition,
    ) -> Result<(&'static str, u32), CodegenError> {
        let rule = self.rules[&definition.name];
        let TagDomain::Finite(tags) =
            self.tag_domain(&definition.ty, &mut BTreeSet::new(), rule)?
        else {
            return Err(CodegenError::new(
                &definition.name,
                "a tagged nominal format must have a finite outer tag domain",
            ));
        };
        let Some(first) = tags.iter().next() else {
            return Err(CodegenError::new(
                &definition.name,
                "a tagged nominal format must accept an outer tag",
            ));
        };
        if tags
            .iter()
            .any(|tag| tag.class != first.class || tag.number != first.number)
        {
            return Err(CodegenError::new(
                &definition.name,
                "a tagged nominal format must have one outer tag identity",
            ));
        }
        let class = match first.class {
            0 => "Class::Universal",
            1 => "Class::Application",
            2 => "Class::ContextSpecific",
            3 => "Class::Private",
            _ => unreachable!("tag classes are normalized by tag_class_id"),
        };
        Ok((class, first.number))
    }

    pub(super) fn tag_domain(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
    ) -> Result<TagDomain, CodegenError> {
        let singleton = |class, number, constructed| {
            TagDomain::Finite(BTreeSet::from([WireTag {
                class,
                number,
                constructed,
            }]))
        };
        let primitive_or_constructed = |class, number| {
            TagDomain::Finite(BTreeSet::from([
                WireTag {
                    class,
                    number,
                    constructed: false,
                },
                WireTag {
                    class,
                    number,
                    constructed: true,
                },
            ]))
        };
        Ok(match ty {
            Type::Boolean => singleton(0, 1, false),
            Type::Integer(_, _) => singleton(0, 2, false),
            Type::BitString(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 3),
            Type::BitString(_) => singleton(0, 3, false),
            Type::OctetString(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 4),
            Type::OctetString(_) => singleton(0, 4, false),
            Type::Null => singleton(0, 5, false),
            Type::ObjectIdentifier => singleton(0, 6, false),
            Type::Real => singleton(0, 9, false),
            Type::Enumerated(_) => singleton(0, 10, false),
            Type::Utf8String(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 12),
            Type::Utf8String(_) => singleton(0, 12, false),
            Type::RelativeOid => singleton(0, 13, false),
            Type::Sequence(_) | Type::SequenceOf(_, _) => singleton(0, 16, true),
            Type::Set(_) | Type::SetOf(_, _) => singleton(0, 17, true),
            Type::NumericString(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 18),
            Type::NumericString(_) => singleton(0, 18, false),
            Type::PrintableString(_) if rule == EncodingRules::Ber => {
                primitive_or_constructed(0, 19)
            }
            Type::PrintableString(_) => singleton(0, 19, false),
            Type::TeletexString(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 20),
            Type::TeletexString(_) => singleton(0, 20, false),
            Type::IA5String(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 22),
            Type::IA5String(_) => singleton(0, 22, false),
            Type::UtcTime => singleton(0, 23, false),
            Type::GeneralizedTime => singleton(0, 24, false),
            Type::VisibleString(_) => singleton(0, 26, false),
            Type::GeneralString(_) => singleton(0, 27, false),
            Type::UniversalString(_) if rule == EncodingRules::Ber => {
                primitive_or_constructed(0, 28)
            }
            Type::UniversalString(_) => singleton(0, 28, false),
            Type::BmpString(_) if rule == EncodingRules::Ber => primitive_or_constructed(0, 30),
            Type::BmpString(_) => singleton(0, 30, false),
            Type::Any | Type::AnyDefinedBy(_) => TagDomain::Open,
            Type::Choice(variants) => {
                let mut domain = TagDomain::Finite(BTreeSet::new());
                for variant in variants {
                    domain = union_domains(domain, self.tag_domain(&variant.ty, visiting, rule)?);
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
                let domain =
                    self.tag_domain(&self.definition(name)?.ty, visiting, self.rules[name])?;
                visiting.remove(name);
                domain
            }
            Type::Tagged { tag, inner } => {
                let constructed = match tag.tagging {
                    Tagging::Explicit => true,
                    Tagging::Implicit => {
                        match self.tag_shape(inner, &mut BTreeSet::new(), rule)? {
                            TagShape::Tlv { constructed } => constructed,
                            TagShape::Untagged => true,
                        }
                    }
                };
                if tag.tagging == Tagging::Implicit
                    && self.accepts_primitive_and_constructed(inner, &mut BTreeSet::new(), rule)?
                {
                    primitive_or_constructed(tag_class_id(&tag.class), tag.number)
                } else {
                    singleton(tag_class_id(&tag.class), tag.number, constructed)
                }
            }
            Type::Constrained { base_type, .. } => self.tag_domain(base_type, visiting, rule)?,
            Type::Class(_) => TagDomain::Open,
        })
    }

    pub(super) fn accepts_primitive_and_constructed(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
    ) -> Result<bool, CodegenError> {
        if rule != EncodingRules::Ber {
            return Ok(false);
        }
        Ok(match ty {
            Type::BitString(_)
            | Type::OctetString(_)
            | Type::Utf8String(_)
            | Type::NumericString(_)
            | Type::PrintableString(_)
            | Type::IA5String(_)
            | Type::TeletexString(_)
            | Type::UniversalString(_)
            | Type::BmpString(_) => true,
            Type::Constrained { base_type, .. } => {
                self.accepts_primitive_and_constructed(base_type, visiting, rule)?
            }
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving BER tag forms",
                    ));
                }
                let accepts = self.accepts_primitive_and_constructed(
                    &self.definition(name)?.ty,
                    visiting,
                    self.rules[name],
                )?;
                visiting.remove(name);
                accepts
            }
            Type::Tagged { tag, inner } => {
                tag.tagging == Tagging::Implicit
                    && self.tag_shape(inner, &mut BTreeSet::new(), rule)? != TagShape::Untagged
                    && self.accepts_primitive_and_constructed(inner, visiting, rule)?
            }
            _ => false,
        })
    }

    pub(super) fn exec_type(
        &self,
        ty: &Type,
        lifetime: &str,
        rule: EncodingRules,
    ) -> Result<String, CodegenError> {
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
            Type::OctetString(_) => match rule {
                EncodingRules::Der => format!("&{lifetime} [u8]"),
                EncodingRules::Ber => "Vec<u8>".to_string(),
            },
            Type::BitString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib2::asn1::BitString<{lifetime}, DER>")
                }
                EncodingRules::Ber => "vest_lib2::asn1::BitStringOwned".to_string(),
            },
            Type::ObjectIdentifier => "vest_lib2::asn1::ObjectIdentifier".to_string(),
            Type::Real => format!("vest_lib2::asn1::Real<{lifetime}, {}>", rule.display()),
            Type::Null => "()".to_string(),
            Type::Utf8String(_) => match rule {
                EncodingRules::Der => format!("&{lifetime} str"),
                EncodingRules::Ber => "String".to_string(),
            },
            Type::PrintableString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib2::asn1::PrintableString<{lifetime}>")
                }
                EncodingRules::Ber => "vest_lib2::asn1::PrintableStringOwned".to_string(),
            },
            Type::IA5String(_) => match rule {
                EncodingRules::Der => format!("vest_lib2::asn1::Ia5String<{lifetime}>"),
                EncodingRules::Ber => "vest_lib2::asn1::Ia5StringOwned".to_string(),
            },
            Type::TeletexString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib2::asn1::TeletexString<{lifetime}>")
                }
                EncodingRules::Ber => "vest_lib2::asn1::TeletexStringOwned".to_string(),
            },
            Type::BmpString(_) => "vest_lib2::asn1::BmpString".to_string(),
            Type::NumericString(_) => match rule {
                EncodingRules::Der => format!("vest_lib2::asn1::NumericString<{lifetime}>"),
                EncodingRules::Ber => "vest_lib2::asn1::NumericStringOwned".to_string(),
            },
            Type::UniversalString(_) => "vest_lib2::asn1::UniversalString".to_string(),
            Type::UtcTime => "vest_lib2::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => {
                format!("vest_lib2::asn1::GeneralizedTime<{lifetime}>")
            }
            Type::Any => match rule {
                EncodingRules::Der => format!("vest_lib2::asn1::Any<{lifetime}>"),
                EncodingRules::Ber => "vest_lib2::asn1::AnyOwned".to_string(),
            },
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
                format!("Vec<{}>", self.exec_type(inner, lifetime, rule)?)
            }
            Type::Tagged { inner, .. } => self.exec_type(inner, lifetime, rule)?,
            Type::Constrained {
                base_type,
                constraint,
            } => {
                if matches!(base_type.as_ref(), Type::Integer(None, _)) {
                    match integer_repr(integer_value_bounds(constraint, "INTEGER")?) {
                        IntegerRepr::I8 => "i8".to_string(),
                        IntegerRepr::I16 => "i16".to_string(),
                        IntegerRepr::General => self.exec_type(base_type, lifetime, rule)?,
                    }
                } else {
                    self.exec_type(base_type, lifetime, rule)?
                }
            }
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Enumerated(_)
            | Type::Set(_)
            | Type::RelativeOid
            | Type::GeneralString(_)
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

    pub(super) fn spec_type(&self, ty: &Type) -> Result<String, CodegenError> {
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
            Type::NumericString(_) => "vest_lib2::asn1::NumericStringSpec".to_string(),
            Type::UniversalString(_) => "vest_lib2::asn1::UniversalStringSpec".to_string(),
            Type::UtcTime => "vest_lib2::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => "vest_lib2::asn1::GeneralizedTimeSpec".to_string(),
            Type::Any => "vest_lib2::asn1::AnySpec".to_string(),
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
                format!("Seq<{}>", self.spec_type(inner)?)
            }
            Type::Tagged { inner, .. } => self.spec_type(inner)?,
            Type::Constrained {
                base_type,
                constraint,
            } => {
                if matches!(base_type.as_ref(), Type::Integer(None, _)) {
                    match integer_repr(integer_value_bounds(constraint, "INTEGER")?) {
                        IntegerRepr::I8 => "i8".to_string(),
                        IntegerRepr::I16 => "i16".to_string(),
                        IntegerRepr::General => self.spec_type(base_type)?,
                    }
                } else {
                    self.spec_type(base_type)?
                }
            }
            Type::Sequence(_)
            | Type::Choice(_)
            | Type::Set(_)
            | Type::RelativeOid
            | Type::GeneralString(_)
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

    pub(super) fn render_default(
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
            Type::Integer(_, named) => {
                let value = match default.parse::<i64>() {
                    Ok(value) => value,
                    Err(_) => lookup_named_number(named, default, path)?.value,
                };
                match self.integer_repr_for_type(ty, &mut BTreeSet::new())? {
                    Some(IntegerRepr::I8) => Ok(RenderedDefault {
                        ty: "i8".to_string(),
                        expr: format!("{value}i8"),
                    }),
                    Some(IntegerRepr::I16) => Ok(RenderedDefault {
                        ty: "i16".to_string(),
                        expr: format!("{value}i16"),
                    }),
                    _ => Err(CodegenError::new(
                        path,
                        "INTEGER DEFAULT requires a finite constraint contained in i8 or i16 so the generated default is Structural + Copy",
                    )),
                }
            }
            _ => Err(CodegenError::new(
                path,
                "only BOOLEAN, ENUMERATED, and compact constrained INTEGER DEFAULT values are currently supported",
            )),
        }
    }

    pub(super) fn integer_repr_for_type(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
    ) -> Result<Option<IntegerRepr>, CodegenError> {
        match ty {
            Type::Integer(_, _) => Ok(Some(IntegerRepr::General)),
            Type::Constrained {
                base_type,
                constraint,
            } if matches!(base_type.as_ref(), Type::Integer(None, _)) => Ok(Some(integer_repr(
                integer_value_bounds(constraint, "INTEGER")?,
            ))),
            Type::Constrained { base_type, .. }
            | Type::Tagged {
                inner: base_type, ..
            } => self.integer_repr_for_type(base_type, visiting),
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive reference while resolving INTEGER representation",
                    ));
                }
                let repr = self.integer_repr_for_type(&self.definition(name)?.ty, visiting)?;
                visiting.remove(name);
                Ok(repr)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn resolve_base_type<'b>(
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
}
