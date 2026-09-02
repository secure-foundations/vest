//! Format combinator lowering and nominal-format emission.

use super::*;

struct UnambiguityEmitter<'a> {
    names: &'a Names,
    lines: Vec<String>,
    next_id: usize,
    bridged_start_domains: BTreeSet<StartCertificate>,
    reveal_exact_uint: bool,
    reveal_any_non_eoc: bool,
    reveal_empty: bool,
    reveal_union: bool,
    reveal_disjoint: bool,
}

struct EmittedUnambiguity {
    code: String,
    reveal_exact_uint: bool,
    reveal_any_non_eoc: bool,
    reveal_empty: bool,
    reveal_union: bool,
    reveal_disjoint: bool,
}

impl<'a> UnambiguityEmitter<'a> {
    fn new(names: &'a Names) -> Self {
        Self {
            names,
            lines: Vec::new(),
            next_id: 0,
            bridged_start_domains: BTreeSet::new(),
            reveal_exact_uint: false,
            reveal_any_non_eoc: false,
            reveal_empty: false,
            reveal_union: false,
            reveal_disjoint: false,
        }
    }

    fn emit_start_equality(
        &mut self,
        format: &str,
        domain: &StartCertificate,
    ) -> Result<(), CodegenError> {
        finite_start_certificate(domain)?;
        let tags = domain
            .tags
            .as_ref()
            .expect("finite certificate checked above");
        let tags = tags.iter().collect::<Vec<_>>();
        let bridged = if !domain.accepts_empty && tags.len() == 1 {
            self.reveal_exact_uint = true;
            let tag = tags[0];
            let class = match tag.class {
                0 => "Class::Universal",
                1 => "Class::Application",
                2 => "Class::ContextSpecific",
                3 => "Class::Private",
                _ => unreachable!("wire tag classes are normalized by the frontend"),
            };
            self.lines.push(format!(
                "assert({format}.asn1_start() == asn1_start_exact_uint({class}, {}, {}u64));",
                tag.constructed, tag.number,
            ));
            if self.bridged_start_domains.insert(domain.clone()) {
                self.lines.push(format!(
                    "assert(asn1_start_exact_uint({class}, {}, {}u64) == {}) by (bit_vector);",
                    tag.constructed,
                    tag.number,
                    render_start_certificate(domain),
                ));
            }
            true
        } else if !domain.accepts_empty && tags.len() == 2 {
            let first = tags[0];
            let second = tags[1];
            if first.class == second.class
                && first.number == second.number
                && first.constructed != second.constructed
            {
                self.reveal_exact_uint = true;
                let class = match first.class {
                    0 => "Class::Universal",
                    1 => "Class::Application",
                    2 => "Class::ContextSpecific",
                    3 => "Class::Private",
                    _ => unreachable!("wire tag classes are normalized by the frontend"),
                };
                if self.bridged_start_domains.insert(domain.clone()) {
                    self.lines.push(format!(
                        "lemma_asn1_start_identity_uint({class}, {}u64);",
                        first.number,
                    ));
                    self.lines.push(format!(
                        "assert(asn1_start_identity_uint({class}, {}u64) == {}) by (bit_vector);",
                        first.number,
                        render_start_certificate(domain),
                    ));
                }
                self.lines.push(format!(
                    "assert({format}.asn1_start() == asn1_start_identity_uint({class}, {}u64));",
                    first.number,
                ));
                true
            } else {
                false
            }
        } else if domain.accepts_empty
            && tags.len() == 1
            && tags[0].class == 0
            && tags[0].number == 0
            && !tags[0].constructed
        {
            if self.bridged_start_domains.insert(domain.clone()) {
                self.lines
                    .push("reveal(asn1_start_ber_boundary);".to_string());
                self.lines.push(format!(
                    "assert(asn1_start_ber_boundary() == {}) by (bit_vector);",
                    render_start_certificate(domain),
                ));
            }
            self.lines.push(format!(
                "assert({format}.asn1_start() == asn1_start_ber_boundary());"
            ));
            true
        } else {
            false
        };
        if !bridged {
            if domain == &StartCertificate::any_non_eoc() {
                self.reveal_any_non_eoc = true;
            } else if domain.accepts_empty && tags.is_empty() {
                self.reveal_empty = true;
            }
            self.lines.push(format!(
                "assert({format}.asn1_start() == {});",
                render_start_certificate(domain),
            ));
        }
        Ok(())
    }

    fn emit(
        mut self,
        plan: &UnambiguityPlan,
        needs_certificate: bool,
    ) -> Result<EmittedUnambiguity, CodegenError> {
        self.emit_plan(plan, needs_certificate)?;
        Ok(EmittedUnambiguity {
            code: self.lines.join("\n"),
            reveal_exact_uint: self.reveal_exact_uint,
            reveal_any_non_eoc: self.reveal_any_non_eoc,
            reveal_empty: self.reveal_empty,
            reveal_union: self.reveal_union,
            reveal_disjoint: self.reveal_disjoint,
        })
    }

    fn emit_plan(
        &mut self,
        plan: &UnambiguityPlan,
        needs_certificate: bool,
    ) -> Result<String, CodegenError> {
        let needs_binding = needs_certificate;
        let name = if needs_binding {
            let name = format!("__asn1_fmt_{}", self.next_id);
            self.next_id += 1;
            self.lines.push(format!(
                "let {name} =\n    {};",
                indent_continuation(&plan.expr, 4)
            ));
            name
        } else {
            plan.expr.clone()
        };

        let mut is_union = false;
        match &plan.kind {
            UnambiguityKind::Leaf => {}
            // Nominal formats expose trivial public proof invariants and a sealed FIRST
            // certificate through their macro-generated trait implementations. Their private
            // schema proof is therefore not an obligation of an enclosing format.
            UnambiguityKind::Nominal => {}
            UnambiguityKind::Transparent(child) | UnambiguityKind::Mapped(child) => {
                self.emit_plan(child, needs_certificate)?;
            }
            UnambiguityKind::Retagged(child) => {
                self.emit_plan(child, false)?;
            }
            UnambiguityKind::Pair(left, right) => {
                self.emit_plan(left, needs_certificate)?;
                self.emit_plan(right, false)?;
            }
            UnambiguityKind::BerSequenceOf(child) => {
                self.reveal_disjoint = true;
                let child_name = self.emit_plan(child, true)?;
                let child_domain = finite_start_certificate(&child.start)?;
                let eoc_domain = StartCertificate {
                    accepts_empty: false,
                    tags: Some(BTreeSet::from([WireTag {
                        class: 0,
                        number: 0,
                        constructed: false,
                    }])),
                };
                let eoc_name = format!("__asn1_fmt_{}", self.next_id);
                self.next_id += 1;
                self.lines.push(format!("let {eoc_name} = EOC;"));
                self.emit_start_equality(&eoc_name, &eoc_domain)?;
                self.lines.push(format!(
                    "assert(asn1_starts_disjoint({}, {})) by (bit_vector);",
                    render_start_certificate(child_domain),
                    render_start_certificate(&eoc_domain),
                ));
                self.lines.push(format!(
                    "assert(asn1_starts_disjoint({child_name}.asn1_start(), {eoc_name}.asn1_start()));"
                ));
                self.lines.push(format!(
                    "lemma_disjoint_asn1_starts({child_name}, {eoc_name});"
                ));
            }
            UnambiguityKind::Choice(left, right)
            | UnambiguityKind::Optional(left, right)
            | UnambiguityKind::Defaulted(left, right) => {
                self.reveal_disjoint = true;
                let left_name = self.emit_plan(left, true)?;
                let right_name = self.emit_plan(right, true)?;
                let left_domain = finite_start_certificate(&left.start)?;
                let right_domain = finite_start_certificate(&right.start)?;
                self.lines.push(format!(
                    "assert(asn1_starts_disjoint({}, {})) by (bit_vector);",
                    render_start_certificate(left_domain),
                    render_start_certificate(right_domain),
                ));
                self.lines.push(format!(
                    "assert(asn1_starts_disjoint({left_name}.asn1_start(), {right_name}.asn1_start()));"
                ));
                self.lines.push(format!(
                    "lemma_disjoint_asn1_starts({left_name}, {right_name});"
                ));
                is_union = true;
            }
        }

        if matches!(plan.kind, UnambiguityKind::Mapped(_)) {
            self.lines.push(format!(
                "assert forall|output: <{} as SpecMap>::Output| #[trigger]\n    {name}.consistent(output) implies {name}.mapper.sound(output) by {{\n    if {name}.consistent(output) {{\n        {}::lemma_from_into(output);\n    }}\n}}",
                self.names.forward, self.names.spec,
            ));
        }
        if is_union {
            let left = match &plan.kind {
                UnambiguityKind::Choice(left, _)
                | UnambiguityKind::Optional(left, _)
                | UnambiguityKind::Defaulted(left, _) => &left.start,
                _ => unreachable!("union children are recorded only for union formats"),
            };
            let right = match &plan.kind {
                UnambiguityKind::Choice(_, right)
                | UnambiguityKind::Optional(_, right)
                | UnambiguityKind::Defaulted(_, right) => &right.start,
                _ => unreachable!("union children are recorded only for union formats"),
            };
            if needs_certificate {
                self.reveal_union = true;
                self.lines.push(format!(
                    "assert(asn1_start_union({}, {}) == {}) by (bit_vector);",
                    render_start_certificate(left),
                    render_start_certificate(right),
                    render_start_certificate(&plan.start),
                ));
                self.lines.push(format!(
                    "assert({name}.asn1_start() == {});",
                    render_start_certificate(&plan.start),
                ));
            }
        } else if needs_certificate && plan.start.tags.is_some() {
            self.emit_start_equality(&name, &plan.start)?;
        }
        Ok(name)
    }
}

fn finite_start_certificate(
    certificate: &StartCertificate,
) -> Result<&StartCertificate, CodegenError> {
    if certificate.tags.is_some() {
        Ok(certificate)
    } else {
        Err(CodegenError::new(
            "internal",
            "an open ASN.1 start domain reached a generated disjointness obligation",
        ))
    }
}

impl<'a> Generator<'a> {
    pub(super) fn render_format_declaration(
        &self,
        definition: &Definition,
        output: &mut CodeWriter,
    ) -> Result<(), CodegenError> {
        let names = &self.names[&definition.name];
        let rule = self.rules[&definition.name];
        let mut rendered = match &definition.ty {
            Type::Sequence(fields) => {
                let sequence = match rule {
                    EncodingRules::Der => {
                        let raw = self.render_sequence_fields(fields, &definition.name, rule)?;
                        let expr =
                            render_list_combinator(&self.backend_item(rule, "SEQUENCE"), &raw.expr);
                        Rendered {
                            ty: format!("{}<{}>", self.backend_item(rule, "SequenceFmt"), raw.ty),
                            proof: UnambiguityPlan {
                                expr: expr.clone(),
                                start: StartCertificate::finite(BTreeSet::from([WireTag {
                                    class: 0,
                                    number: 16,
                                    constructed: true,
                                }])),
                                kind: UnambiguityKind::Transparent(Box::new(raw.proof)),
                            },
                            expr,
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
                        let expr =
                            render_list_combinator(&self.backend_item(rule, "SEQUENCE"), &raw.expr);
                        Rendered {
                            ty: format!("{}<{}>", self.backend_item(rule, "SequenceFmt"), raw.ty),
                            proof: UnambiguityPlan {
                                expr: expr.clone(),
                                start: StartCertificate::finite(BTreeSet::from([WireTag {
                                    class: 0,
                                    number: 16,
                                    constructed: true,
                                }])),
                                kind: UnambiguityKind::Transparent(Box::new(raw.proof)),
                            },
                            expr,
                            shape: TagShape::Tlv { constructed: true },
                        }
                    }
                };
                map_with_bimap(sequence, &names.forward, &names.reverse)
            }
            Type::Set(fields) => {
                debug_assert_eq!(rule, EncodingRules::Der);
                let raw = self.render_sequence_fields(fields, &definition.name, rule)?;
                let expr = render_list_combinator(&self.backend_item(rule, "SET"), &raw.expr);
                let set = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SetFmt"), raw.ty),
                    proof: UnambiguityPlan {
                        expr: expr.clone(),
                        start: StartCertificate::finite(BTreeSet::from([WireTag {
                            class: 0,
                            number: 17,
                            constructed: true,
                        }])),
                        kind: UnambiguityKind::Transparent(Box::new(raw.proof)),
                    },
                    expr,
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
                    proof: UnambiguityPlan::leaf(self.backend_item(rule, "ENUMERATED16")),
                };
                let refined = refine(wire, names.predicate.clone(), names.predicate.clone());
                map_with_bimap(refined, &names.forward, &names.reverse)
            }
            ty => self.render_type(ty, rule)?,
        };
        rendered.proof.start =
            self.start_certificate(&definition.ty, &mut BTreeSet::new(), rule)?;
        let (rendered_expr, local_items) = if self.mixed_rules {
            localize_rule_items(&rendered.expr, rule)
        } else {
            (rendered.expr.clone(), Vec::new())
        };
        let local_import = render_local_rule_import(rule, &local_items);
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
            NominalKind::TaggedExact { .. } | NominalKind::TaggedIdentity { .. } => {
                let (class, number) = self.nominal_tag(definition)?;
                output.line(format_args!(
                    "pub struct {}(pub Class, pub u64);",
                    names.format
                ));
                output.line(format_args!("impl {} {{", names.format));
                output.line(format_args!(
                    "    pub const Fmt: Self = Self({class}, {number}u64);"
                ));
            }
            NominalKind::UntaggedFinite(_) | NominalKind::UntaggedAny | NominalKind::Untagged => {
                output.line(format_args!("pub struct {};", names.format));
                output.line(format_args!("impl {} {{", names.format));
                output.line(format_args!("    pub const Fmt: Self = Self;"));
            }
        }
        output.blank_line();
        output.line(format_args!("    #[verifier::allow_in_spec]"));
        output.line(format_args!(
            "    pub const fn schema() -> {}",
            names.inner_format
        ));
        output.line(format_args!("        returns"));
        if let Some(local_import) = &local_import {
            output.line(format_args!("            ({{"));
            output.line(format_args!("                {local_import}"));
            output.line(format_args!(
                "                {}",
                indent_continuation(&rendered_expr, 16)
            ));
            output.line(format_args!("            }}),"));
        } else {
            output.line(format_args!("            ("));
            output.line(format_args!(
                "                {}",
                indent_continuation(&rendered_expr, 16)
            ));
            output.line(format_args!("            ),"));
        }
        output.line(format_args!("    {{"));
        if let Some(local_import) = &local_import {
            output.line(format_args!("        {local_import}"));
        }
        output.line(format_args!(
            "        {}",
            indent_continuation(&rendered_expr, 8)
        ));
        output.line(format_args!("    }}"));
        let nominal_kind = self.nominal_kind(definition)?;
        let mut proof_plan = rendered.proof.clone();
        proof_plan.expr = "self.spec_inner()".to_string();
        if matches!(
            nominal_kind,
            NominalKind::TaggedExact { .. } | NominalKind::TaggedIdentity { .. }
        ) {
            // `self` is retaggable, so only `Self::Fmt` has the schema's concrete start mask.
            // The arbitrary receiver's start is related to `spec_inner` symbolically below.
            proof_plan.start = StartCertificate::open();
        }
        let certify_root = matches!(
            nominal_kind,
            NominalKind::UntaggedFinite(_) | NominalKind::UntaggedAny
        );
        let proof = UnambiguityEmitter::new(names).emit(&proof_plan, certify_root)?;
        output.blank_line();
        output.line(format_args!("    proof fn lemma_schema_unambiguous(&self)"));
        output.line(format_args!("        ensures"));
        output.line(format_args!("            self.spec_inner().unambiguous(),"));
        let has_start = !matches!(&nominal_kind, NominalKind::Untagged);
        if has_start {
            output.line(format_args!(
                "            self.spec_inner().asn1_start() == self.asn1_start(),"
            ));
            output.line(format_args!(
                "            Self::Fmt.asn1_start() == {},",
                render_start_certificate(&rendered.proof.start)
            ));
        }
        output.line(format_args!("    {{"));
        if proof.reveal_exact_uint
            || matches!(
                &nominal_kind,
                NominalKind::TaggedExact { .. } | NominalKind::TaggedIdentity { .. }
            )
        {
            output.line(format_args!("        reveal(asn1_start_exact_uint);"));
        }
        if proof.reveal_any_non_eoc {
            output.line(format_args!("        reveal(asn1_start_any_non_eoc);"));
        }
        if proof.reveal_empty {
            output.line(format_args!("        reveal(asn1_start_empty);"));
        }
        if proof.reveal_union {
            output.line(format_args!("        reveal(asn1_start_union);"));
        }
        if proof.reveal_disjoint {
            output.line(format_args!("        reveal(asn1_starts_disjoint);"));
        }
        output.line(format_args!(
            "        reveal({}::spec_inner);",
            names.format
        ));
        match nominal_kind {
            NominalKind::TaggedExact { constructed } => {
                output.line(format_args!(
                    "        lemma_asn1_start_exact_uint(self.0, {constructed}, self.1);"
                ));
            }
            NominalKind::TaggedIdentity { .. } => {
                output.line(format_args!(
                    "        lemma_asn1_start_identity_uint(self.0, self.1);"
                ));
            }
            NominalKind::UntaggedFinite(_) | NominalKind::UntaggedAny | NominalKind::Untagged => {}
        }
        if !proof.code.is_empty() {
            output.line(format_args!(
                "        {}",
                indent_continuation(&proof.code, 8)
            ));
        }
        if has_start {
            output.line(format_args!(
                "        assert(self.spec_inner().asn1_start() == self.asn1_start());"
            ));
            output.line(format_args!(
                "        assert(Self::Fmt.asn1_start() == {}) by (bit_vector);",
                render_start_certificate(&rendered.proof.start)
            ));
        }
        output.line(format_args!("    }}"));
        output.line(format_args!(
            "}}
"
        ));
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
        let mut rendered = match ty {
            Type::SequenceOf(inner, constraint) => {
                let inner = self.render_type(inner, rule)?;
                let expr = format!("{}({})", self.backend_item(rule, "SEQUENCE_OF"), inner.expr);
                let proof = if rule == EncodingRules::Ber {
                    UnambiguityPlan {
                        expr: expr.clone(),
                        start: inner.proof.start.clone(),
                        kind: UnambiguityKind::BerSequenceOf(Box::new(inner.proof)),
                    }
                } else {
                    UnambiguityPlan::transparent(expr.clone(), inner.proof)
                };
                let sequence_of = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SequenceOfFmt"), inner.ty),
                    proof,
                    expr,
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
                let expr = format!("{}({})", self.backend_item(rule, "SET_OF"), inner.expr);
                let proof = if rule == EncodingRules::Ber {
                    UnambiguityPlan {
                        expr: expr.clone(),
                        start: inner.proof.start.clone(),
                        kind: UnambiguityKind::BerSequenceOf(Box::new(inner.proof)),
                    }
                } else {
                    UnambiguityPlan::transparent(expr.clone(), inner.proof)
                };
                let set_of = Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "SetOfTlvFmt"), inner.ty),
                    proof,
                    expr,
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
                let expr = format!("{}::Fmt", names.format);
                Rendered {
                    ty: names.format.clone(),
                    expr: expr.clone(),
                    shape: self.tag_shape(ty, &mut BTreeSet::new(), self.rules[name])?,
                    proof: UnambiguityPlan {
                        expr,
                        start: StartCertificate::open(),
                        kind: UnambiguityKind::Nominal,
                    },
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
                proof: UnambiguityPlan::leaf(self.backend_item(rule, "ANY")),
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
        };
        rendered.proof.start = self.start_certificate(ty, &mut BTreeSet::new(), rule)?;
        Ok(rendered)
    }

    fn start_certificate(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
    ) -> Result<StartCertificate, CodegenError> {
        Ok(match ty {
            Type::Any | Type::AnyDefinedBy(_) => StartCertificate::any_non_eoc(),
            Type::Choice(variants) => {
                let mut result = StartCertificate::finite(BTreeSet::new());
                for variant in variants {
                    result = result.union(&self.start_certificate(&variant.ty, visiting, rule)?);
                }
                result
            }
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving ASN.1 start certificate",
                    ));
                }
                let result =
                    self.start_certificate(&self.definition(name)?.ty, visiting, self.rules[name])?;
                visiting.remove(name);
                result
            }
            Type::Constrained { base_type, .. } => {
                self.start_certificate(base_type, visiting, rule)?
            }
            _ => StartCertificate::from_tag_domain(&self.tag_domain(ty, visiting, rule)?),
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
        let end_start = if end_expr.ends_with("BER_END") {
            StartCertificate {
                accepts_empty: true,
                tags: Some(BTreeSet::from([WireTag {
                    class: 0,
                    number: 0,
                    constructed: false,
                }])),
            }
        } else {
            StartCertificate::eof()
        };
        let mut result = Rendered {
            ty: end_ty.to_string(),
            expr: end_expr.to_string(),
            shape: TagShape::Untagged,
            proof: UnambiguityPlan {
                expr: end_expr.to_string(),
                start: end_start,
                kind: UnambiguityKind::Leaf,
            },
        };

        for field in fields.iter().rev() {
            result = if let Some(default) = &field.default {
                let field_rendered = self.render_type(&field.ty, rule)?;
                let default =
                    self.render_default(&field.ty, default, &format!("{path}.{}", field.name))?;
                let expr = format!(
                    "{}({}, {},\n{})",
                    self.backend_item(rule, "DEFAULT"),
                    field_rendered.expr,
                    default.expr,
                    result.expr
                );
                let start = field_rendered.proof.start.union(&result.proof.start);
                Rendered {
                    ty: format!(
                        "{}<{}, {}, {}>",
                        self.backend_item(rule, "DefaultFmt"),
                        field_rendered.ty,
                        default.ty,
                        result.ty
                    ),
                    proof: UnambiguityPlan {
                        expr: expr.clone(),
                        start,
                        kind: UnambiguityKind::Defaulted(
                            Box::new(field_rendered.proof),
                            Box::new(result.proof),
                        ),
                    },
                    expr,
                    shape: TagShape::Untagged,
                }
            } else {
                let field_rendered = self.render_type_by_ref(&field.ty, rule)?;
                let (ty_constructor, expr_constructor) = if field.optional {
                    ("Optional", "OPTIONAL")
                } else {
                    ("Pair", "REQUIRED")
                };
                let expr = format!(
                    "{expr_constructor}({},\n{})",
                    field_rendered.expr, result.expr
                );
                let (start, kind) = if field.optional {
                    (
                        field_rendered.proof.start.union(&result.proof.start),
                        UnambiguityKind::Optional(
                            Box::new(field_rendered.proof),
                            Box::new(result.proof),
                        ),
                    )
                } else {
                    (
                        field_rendered.proof.start.clone(),
                        UnambiguityKind::Pair(
                            Box::new(field_rendered.proof),
                            Box::new(result.proof),
                        ),
                    )
                };
                Rendered {
                    ty: format!("{ty_constructor}<{}, {}>", field_rendered.ty, result.ty),
                    proof: UnambiguityPlan {
                        expr: expr.clone(),
                        start,
                        kind,
                    },
                    expr,
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
        fn combine(rendered: &[Rendered]) -> Rendered {
            match rendered {
                [] => unreachable!("empty CHOICE rejected during validation"),
                [only] => return only.clone(),
                _ => {}
            }
            let middle = choice_split(rendered.len());
            let left = combine(&rendered[..middle]);
            let right = combine(&rendered[middle..]);
            let expr = render_choice_combinator(&left.expr, &right.expr);
            let start = left.proof.start.union(&right.proof.start);
            Rendered {
                ty: format!("Choice<{}, {}>", left.ty, right.ty),
                proof: UnambiguityPlan {
                    expr: expr.clone(),
                    start,
                    kind: UnambiguityKind::Choice(Box::new(left.proof), Box::new(right.proof)),
                },
                expr,
                shape: TagShape::Untagged,
            }
        }

        let rendered = variants
            .iter()
            .map(|variant| self.render_type_by_ref(&variant.ty, rule))
            .collect::<Result<Vec<_>, _>>()?;
        let mut result = combine(&rendered);
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
                let mut rendered = self.apply_tag(tag, inner, rule);
                rendered.proof.start = self.start_certificate(ty, &mut BTreeSet::new(), rule)?;
                Ok(rendered)
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
            (Tagging::Explicit, TagShape::Untagged)
            | (Tagging::Explicit, TagShape::Tlv { .. })
            | (Tagging::Implicit, TagShape::Untagged) => {
                let expr =
                    render_retag_helper(tag, true, &inner.expr, self.mixed_rules.then_some(rule));
                Rendered {
                    ty: format!("{}<{}>", self.backend_item(rule, "ExplicitFmt"), inner.ty),
                    proof: UnambiguityPlan::retagged(expr.clone(), inner.proof),
                    expr,
                    shape: TagShape::Tlv { constructed: true },
                }
            }
            (Tagging::Implicit, TagShape::Tlv { constructed }) => {
                let expr = render_retag_helper(tag, false, &inner.expr, None);
                Rendered {
                    ty: format!("ImplicitFmt<{}>", inner.ty),
                    proof: UnambiguityPlan::retagged(expr.clone(), inner.proof),
                    expr,
                    shape: TagShape::Tlv { constructed },
                }
            }
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
            TagShape::Tlv { constructed }
                if self.accepts_primitive_and_constructed(
                    &definition.ty,
                    &mut BTreeSet::new(),
                    rule,
                )? =>
            {
                Ok(NominalKind::TaggedIdentity { constructed })
            }
            TagShape::Tlv { constructed } => Ok(NominalKind::TaggedExact { constructed }),
            TagShape::Untagged => {
                match self.tag_domain(&definition.ty, &mut BTreeSet::new(), rule)? {
                    TagDomain::Finite(tags) if !tags.is_empty() => Ok(NominalKind::UntaggedFinite(
                        self.start_atoms(&definition.ty, &mut BTreeSet::new(), rule)?,
                    )),
                    TagDomain::Open => Ok(NominalKind::UntaggedAny),
                    TagDomain::Finite(_) => Ok(NominalKind::Untagged),
                }
            }
        }
    }

    pub(super) fn start_atoms(
        &self,
        ty: &Type,
        visiting: &mut BTreeSet<String>,
        rule: EncodingRules,
    ) -> Result<Vec<WireTag>, CodegenError> {
        match ty {
            Type::Choice(variants) => {
                let mut atoms = Vec::new();
                for variant in variants {
                    for atom in self.start_atoms(&variant.ty, visiting, rule)? {
                        if !atoms.contains(&atom) {
                            atoms.push(atom);
                        }
                    }
                }
                Ok(atoms)
            }
            Type::Constrained { base_type, .. } => self.start_atoms(base_type, visiting, rule),
            Type::TypeRef(name) => {
                if !visiting.insert(name.clone()) {
                    return Err(CodegenError::new(
                        name,
                        "recursive type while resolving ASN.1 start atoms",
                    ));
                }
                let definition = self.definition(name)?;
                let referenced_rule = self.rules[name];
                let atoms = self.start_atoms(&definition.ty, visiting, referenced_rule)?;
                visiting.remove(name);
                Ok(atoms)
            }
            _ if self.accepts_primitive_and_constructed(ty, &mut BTreeSet::new(), rule)? => {
                let TagDomain::Finite(tags) = self.tag_domain(ty, &mut BTreeSet::new(), rule)?
                else {
                    return Ok(Vec::new());
                };
                Ok(tags.into_iter().collect())
            }
            _ => match self.tag_domain(ty, visiting, rule)? {
                TagDomain::Finite(tags) => Ok(tags.into_iter().collect()),
                TagDomain::Open => Ok(Vec::new()),
            },
        }
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
            Type::Integer(_, _) => format!("vest_lib::asn1::Integer<{lifetime}>"),
            Type::Boolean => "bool".to_string(),
            Type::OctetString(_) => match rule {
                EncodingRules::Der => format!("&{lifetime} [u8]"),
                EncodingRules::Ber => "Vec<u8>".to_string(),
            },
            Type::BitString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib::asn1::BitString<{lifetime}, DER>")
                }
                EncodingRules::Ber => "vest_lib::asn1::BitStringOwned".to_string(),
            },
            Type::ObjectIdentifier => "vest_lib::asn1::ObjectIdentifier".to_string(),
            Type::Real => format!("vest_lib::asn1::Real<{lifetime}, {}>", rule.display()),
            Type::Null => "()".to_string(),
            Type::Utf8String(_) => match rule {
                EncodingRules::Der => format!("&{lifetime} str"),
                EncodingRules::Ber => "String".to_string(),
            },
            Type::PrintableString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib::asn1::PrintableString<{lifetime}>")
                }
                EncodingRules::Ber => "vest_lib::asn1::PrintableStringOwned".to_string(),
            },
            Type::IA5String(_) => match rule {
                EncodingRules::Der => format!("vest_lib::asn1::Ia5String<{lifetime}>"),
                EncodingRules::Ber => "vest_lib::asn1::Ia5StringOwned".to_string(),
            },
            Type::TeletexString(_) => match rule {
                EncodingRules::Der => {
                    format!("vest_lib::asn1::TeletexString<{lifetime}>")
                }
                EncodingRules::Ber => "vest_lib::asn1::TeletexStringOwned".to_string(),
            },
            Type::BmpString(_) => "vest_lib::asn1::BmpString".to_string(),
            Type::NumericString(_) => match rule {
                EncodingRules::Der => format!("vest_lib::asn1::NumericString<{lifetime}>"),
                EncodingRules::Ber => "vest_lib::asn1::NumericStringOwned".to_string(),
            },
            Type::UniversalString(_) => "vest_lib::asn1::UniversalString".to_string(),
            Type::UtcTime => "vest_lib::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => {
                format!("vest_lib::asn1::GeneralizedTime<{lifetime}>")
            }
            Type::Any => match rule {
                EncodingRules::Der => format!("vest_lib::asn1::Any<{lifetime}>"),
                EncodingRules::Ber => "vest_lib::asn1::AnyOwned".to_string(),
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
            Type::BitString(_) => "vest_lib::asn1::BitStringSpec".to_string(),
            Type::ObjectIdentifier => "vest_lib::asn1::ObjectIdentifierSpec".to_string(),
            Type::Real => "vest_lib::asn1::RealSpec".to_string(),
            Type::Null => "()".to_string(),
            Type::Utf8String(_) => "Seq<char>".to_string(),
            Type::PrintableString(_) => "vest_lib::asn1::PrintableStringSpec".to_string(),
            Type::IA5String(_) => "vest_lib::asn1::Ia5StringSpec".to_string(),
            Type::TeletexString(_) => "vest_lib::asn1::TeletexStringSpec".to_string(),
            Type::BmpString(_) => "vest_lib::asn1::BmpStringSpec".to_string(),
            Type::NumericString(_) => "vest_lib::asn1::NumericStringSpec".to_string(),
            Type::UniversalString(_) => "vest_lib::asn1::UniversalStringSpec".to_string(),
            Type::UtcTime => "vest_lib::asn1::UtcTime".to_string(),
            Type::GeneralizedTime => "vest_lib::asn1::GeneralizedTimeSpec".to_string(),
            Type::Any => "vest_lib::asn1::AnySpec".to_string(),
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
