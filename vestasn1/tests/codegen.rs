use std::collections::BTreeMap;
use vestasn1::{
    compile, compile_with_options, compile_with_rule_overrides, CodegenOptions, EncodingRules,
    Error,
};

fn compile_ber(source: &str) -> Result<String, Error> {
    compile_with_options(
        source,
        CodegenOptions {
            encoding_rules: EncodingRules::Ber,
        },
    )
}

fn assert_uses_broadcast_disjointness_only(generated: &str) {
    assert!(!generated.contains("assert(disjoint_domains"));
    assert!(!generated.contains("lemma_disjoint_"));
    assert!(!generated
        .lines()
        .any(|line| line.contains(".inner") && line.contains(".unambiguous()")));
    assert!(generated.contains("vest_lib2::impl_"));
    assert!(!generated.contains("format_spec_invariants"));
}

const BASIC_SCHEMA: &str = r#"
Example DEFINITIONS EXPLICIT TAGS ::= BEGIN
    Flag ::= BOOLEAN
    Count ::= INTEGER
    Payload ::= OCTET STRING
    Message ::= SEQUENCE {
        flag Flag,
        count Count,
        payload Payload OPTIONAL
    }
    Messages ::= SEQUENCE OF Message
    Selection ::= CHOICE {
        flag [0] IMPLICIT Flag,
        payload [1] EXPLICIT Payload
    }
END
"#;

#[test]
fn generates_vest_der_formats() {
    let generated = compile(BASIC_SCHEMA).unwrap();
    assert!(generated.contains("pub struct Message<'a>"));
    assert!(generated.contains("type MESSAGE__ = Mapped<SequenceFmt<Pair<"));
    assert!(generated.contains("Optional<Ref<PAYLOAD>, Eof>"));
    assert!(generated.contains("pub struct MESSAGES(pub Class, pub u64);"));
    assert!(generated.contains("type MESSAGES__ = SequenceOfFmt<MESSAGE>;"));
    assert!(generated.contains("Choice<ImplicitFmt<Ref<FLAG>>, ExplicitFmt<Ref<PAYLOAD>>>"));
    assert!(generated.contains("IMPLICIT(0u64, Ref(FLAG::Fmt))"));
    assert_uses_broadcast_disjointness_only(&generated);
}

#[test]
fn relies_on_broadcast_disjointness_for_multiway_choice() {
    let generated = compile(
        r#"
Choices DEFINITIONS ::= BEGIN
    Value ::= CHOICE {
        flag [0] IMPLICIT BOOLEAN,
        count [1] IMPLICIT INTEGER,
        payload [2] EXPLICIT OCTET STRING,
        nothing [3] IMPLICIT NULL,
        text [4] EXPLICIT UTF8String,
        identifier [5] EXPLICIT OBJECT IDENTIFIER
    }
END
"#,
    )
    .unwrap();

    assert_uses_broadcast_disjointness_only(&generated);
    assert!(generated.contains("impl_der!(untagged, borrowed, VALUE"));
    assert!(generated.contains("use Sum::Inl as L;"));
    assert!(generated.contains("use Sum::Inr as R;"));
    assert!(generated.contains("R(R(L(value)))"));
    assert!(!generated.contains("Sum::Inl("));
    assert!(!generated.contains("Sum::Inr("));
}

#[test]
fn generates_verified_octet_string_size_constraint() {
    let generated =
        compile("Example DEFINITIONS ::= BEGIN Payload ::= OCTET STRING (SIZE (1..32)) END")
            .unwrap();
    assert!(generated.contains("Refined<OctetStringTlvFmt, Size<true, 1, true, 32>>"));
    assert!(generated.contains("Refined(OCTET_STRING, Size::<true, 1, true, 32>)"));
}

#[test]
fn generates_verified_integer_range_constraint() {
    let generated =
        compile("Example DEFINITIONS ::= BEGIN Version ::= INTEGER (0..2) END").unwrap();
    assert!(generated.contains("pub type Version = i8;"));
    assert!(generated.contains("Refined<Integer8TlvFmt, IntegerRange<true, 0, true, 2>>"));
    assert!(generated.contains("Refined(INTEGER8, IntegerRange::<true, 0, true, 2>)"));
}

#[test]
fn generates_verified_string_size_constraint() {
    let generated =
        compile("Example DEFINITIONS ::= BEGIN Label ::= UTF8String (SIZE (1..32)) END").unwrap();
    assert!(generated.contains("Refined<Utf8StringTlvFmt, Size<true, 1, true, 32>>"));
    assert!(generated.contains("Refined(UTF8_STRING, Size::<true, 1, true, 32>)"));
}

#[test]
fn bmp_string_values_are_owned_and_do_not_force_lifetimes() {
    let generated = compile(
        r#"
BmpValues DEFINITIONS ::= BEGIN
    Name ::= BMPString
    Container ::= SEQUENCE { name Name }
END
"#,
    )
    .unwrap();

    assert!(generated.contains("pub type Name = vest_lib2::asn1::BmpString;"));
    assert!(generated.contains("pub struct Container {"));
    assert!(!generated.contains("pub struct Container<'a>"));
}

#[test]
fn rejects_unknown_references() {
    let error = compile("Example DEFINITIONS ::= BEGIN Item ::= Missing END").unwrap_err();
    assert!(error
        .to_string()
        .contains("unknown ASN.1 type reference `Missing`"));
}

#[test]
fn rejects_recursive_aliases_until_fixpoints_are_generated() {
    let error = compile(
        "Example DEFINITIONS ::= BEGIN Node ::= SEQUENCE { children SEQUENCE OF Node } END",
    )
    .unwrap_err();
    assert!(error.to_string().contains("Vest fixpoint combinator"));
}

#[test]
fn reports_synta_parse_errors() {
    let error = compile("not an ASN.1 module").unwrap_err();
    assert!(matches!(error, Error::Parse(_)));
}

#[test]
fn generates_boolean_default_with_vests_der_defaulted_combinator() {
    let generated = compile(
        r#"
Defaults DEFINITIONS ::= BEGIN
    Enabled ::= BOOLEAN
    Flags ::= SEQUENCE {
        enabled [0] IMPLICIT Enabled DEFAULT TRUE,
        disabled [1] IMPLICIT BOOLEAN DEFAULT FALSE
    }
END
"#,
    )
    .unwrap();
    assert!(generated.contains("pub struct Flags"));
    assert!(generated.contains("DefaultFmt<ImplicitFmt<ENABLED>, bool,"));
    let left_aligned = generated
        .lines()
        .map(str::trim_start)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(left_aligned.contains("SEQUENCE(\nDEFAULT("));
    assert!(generated.contains("IMPLICIT(0u64, ENABLED::Fmt)"));
    assert!(generated.contains("IMPLICIT(1u64, BOOLEAN)"));
    assert!(left_aligned.contains("Eof))"));
    assert!(generated.contains("pub struct FLAGS(pub Class, pub u64);"));
    assert!(generated.contains("pub const fn schema()"));
}

#[test]
fn rejects_defaults_whose_exec_value_is_not_supported() {
    let error = compile(
        "Defaults DEFINITIONS ::= BEGIN Config ::= SEQUENCE { port INTEGER DEFAULT 80 } END",
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("INTEGER DEFAULT requires a finite constraint"));
}

#[test]
fn promotes_implicit_choice_tags_to_explicit() {
    let generated = compile(
        r#"
TaggedChoice DEFINITIONS IMPLICIT TAGS ::= BEGIN
    Value ::= CHOICE { number INTEGER, flag BOOLEAN }
    Container ::= SEQUENCE { value [0] Value OPTIONAL }
END
"#,
    )
    .unwrap();
    assert!(generated.contains("Optional<ExplicitFmt<Ref<VALUE>>, Eof>"));
    assert!(generated.contains("EXPLICIT(0u64, Ref(VALUE::Fmt))"));
}

#[test]
fn uses_class_specific_tagging_helpers() {
    let generated = compile(
        r#"
Tagged DEFINITIONS ::= BEGIN
    Value ::= SEQUENCE {
        application [APPLICATION 3] IMPLICIT INTEGER,
        private [PRIVATE 7] EXPLICIT BOOLEAN
    }
END
"#,
    )
    .unwrap();
    assert!(generated.contains("IMPLICIT_APPLICATION(3u64, Ref(INTEGER))"));
    assert!(generated.contains("EXPLICIT_PRIVATE(7u64, Ref(BOOLEAN))"));
}

#[test]
fn composes_implicit_tagging_through_tagged_aliases() {
    let generated = compile(
        r#"
TaggedAliases DEFINITIONS ::= BEGIN
    Base ::= [0] IMPLICIT INTEGER
    Retagged ::= [1] IMPLICIT Base
END
"#,
    )
    .unwrap();
    assert!(generated.contains("type BASE__ = ImplicitFmt<IntegerTlvFmt>;"));
    assert!(generated.contains("type RETAGGED__ = ImplicitFmt<BASE>;"));
    assert!(generated.contains("IMPLICIT(1u64, BASE::Fmt)"));
}

#[test]
fn format_value_names_do_not_collide_with_vest_der_symbols() {
    let generated = compile("Names DEFINITIONS ::= BEGIN DER ::= BOOLEAN END").unwrap();
    assert!(generated.contains("type DER__ = BoolTlvFmt;"));
    assert!(generated.contains("pub struct DER(pub Class, pub u64);"));
}

#[test]
fn emits_closed_enumerated_and_typed_scalar_constants() {
    let generated = compile(
        r#"
Values DEFINITIONS ::= BEGIN
    Color ::= ENUMERATED { red(0), green(1) }
    Count ::= INTEGER
    Enabled ::= BOOLEAN

    selected Color ::= green
    answer Count ::= 42
    enabled Enabled ::= TRUE
END
"#,
    )
    .unwrap();
    assert!(generated.contains("pub enum Color"));
    assert!(generated.contains("pub const SELECTED: Color = Color::Green;"));
    assert!(generated.contains("pub const ANSWER: Count<'static>"));
    assert!(generated.contains("Integer::Small { v: 42i64 }"));
    assert!(generated.contains("pub const ENABLED: Enabled = true;"));
    assert!(generated.find("pub const SELECTED").unwrap() < generated.find("} // verus!").unwrap());
}

#[test]
fn vendored_frontend_retains_forward_typed_value_assignments() {
    let generated = compile(
        r#"
Values DEFINITIONS ::= BEGIN
    selected Color ::= green
    Color ::= ENUMERATED { red(0), green(1) }
END
"#,
    )
    .unwrap();
    assert!(generated.contains("pub const SELECTED: Color = Color::Green;"));
}

#[test]
fn rejects_object_identifier_value_assignments_for_now() {
    let error = compile(
        r#"
Values DEFINITIONS ::= BEGIN
    Identifier ::= OBJECT IDENTIFIER
    base Identifier ::= { 1 2 840 113549 }
END
"#,
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("OBJECT IDENTIFIER value assignments are not supported yet"));
}

#[test]
fn emits_oid_real_any_and_inline_nominal_helpers() {
    let generated = compile(
        r#"
Backends DEFINITIONS ::= BEGIN
    Identifier ::= OBJECT IDENTIFIER
    Measurement ::= REAL
    OpenValue ::= ANY
    Container ::= SEQUENCE {
        nested SEQUENCE { id Identifier },
        selected CHOICE {
            measurement [0] EXPLICIT Measurement,
            open [1] EXPLICIT OpenValue
        }
    }
END
"#,
    )
    .unwrap();
    assert!(generated.contains("type IDENTIFIER__ = ObjectIdentifierTlvFmt;"));
    assert!(generated.contains("type MEASUREMENT__ = RealTlvFmt;"));
    assert!(generated.contains("type OPEN_VALUE__ = AnyTlvFmt;"));
    assert!(generated.contains("pub struct ContainerNested"));
    assert!(generated.contains("pub enum ContainerSelected<'a>"));
}

#[test]
fn emits_set_of_for_der_and_ber() {
    let schema = "Sets DEFINITIONS ::= BEGIN Values ::= SET OF INTEGER END";
    let der = compile(schema).unwrap();
    assert!(der.contains("type VALUES__ = SetOfTlvFmt<IntegerTlvFmt>;"));
    assert!(der.contains("SET_OF(INTEGER)"));

    let ber = compile_with_options(
        schema,
        CodegenOptions {
            encoding_rules: EncodingRules::Ber,
        },
    )
    .unwrap();
    assert!(ber.contains("type VALUES__ = SetOfTlvFmt<IntegerTlvFmt>;"));
    assert!(ber.contains("SET_OF(INTEGER)"));
}

#[test]
fn rejects_open_type_choice_ambiguity() {
    let error = compile(
        "OpenChoice DEFINITIONS ::= BEGIN Value ::= CHOICE { known BOOLEAN, unknown ANY } END",
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("untagged CHOICE/open-type alternative"));
}

#[test]
fn rejects_ambiguous_default_dispatch_early() {
    let error = compile(
        "Defaults DEFINITIONS ::= BEGIN Flags ::= SEQUENCE { a BOOLEAN DEFAULT TRUE, b BOOLEAN DEFAULT FALSE } END",
    )
    .unwrap_err();
    assert!(error.to_string().contains("overlaps the first-tag domain"));
}

#[test]
fn accepts_terminal_optional_open_type_but_rejects_one_before_a_field() {
    let accepted = compile(
        "OpenTail DEFINITIONS ::= BEGIN Value ::= SEQUENCE { kind OBJECT IDENTIFIER, value ANY OPTIONAL } END",
    )
    .unwrap();
    assert!(accepted.contains("OPTIONAL(Ref(ANY),"));

    let error = compile(
        "OpenMiddle DEFINITIONS ::= BEGIN Value ::= SEQUENCE { value ANY OPTIONAL, flag BOOLEAN } END",
    )
    .unwrap_err();
    assert!(error.to_string().contains("overlaps the first-tag domain"));
}

#[test]
fn emits_only_statically_ordered_heterogeneous_der_sets() {
    let generated = compile(
        "Sets DEFINITIONS ::= BEGIN Value ::= SET { a [0] IMPLICIT BOOLEAN, b [1] IMPLICIT INTEGER OPTIONAL } END",
    )
    .unwrap();
    assert!(generated.contains("type VALUE__ = Mapped<SetFmt<"));
    assert!(generated.contains("SET("));

    let unordered = compile(
        "Sets DEFINITIONS ::= BEGIN Value ::= SET { b [1] IMPLICIT BOOLEAN, a [0] IMPLICIT INTEGER } END",
    )
    .unwrap_err();
    assert!(unordered
        .to_string()
        .contains("not in strict canonical order"));

    let ber = compile_ber(
        "Sets DEFINITIONS ::= BEGIN Value ::= SET { a [0] IMPLICIT BOOLEAN, b [1] IMPLICIT INTEGER } END",
    )
    .unwrap_err();
    assert!(ber
        .to_string()
        .contains("heterogeneous SET is supported only for DER"));
}

#[test]
fn emits_numeric_and_universal_strings_for_der_and_ber() {
    let schema = "Strings DEFINITIONS ::= BEGIN Digits ::= NumericString (SIZE (1..8)) Wide ::= UniversalString (SIZE (1..8)) END";
    let der = compile(schema).unwrap();
    assert!(der.contains("Refined<NumericStringTlvFmt, Size<true, 1, true, 8>>"));
    assert!(der.contains("Refined<UniversalStringTlvFmt, Size<true, 1, true, 8>>"));
    assert!(der.contains("pub type Digits<'a> = vest_lib2::asn1::NumericString<'a>;"));
    assert!(der.contains("pub type Wide = vest_lib2::asn1::UniversalString;"));

    let ber = compile_ber(schema).unwrap();
    assert!(ber.contains("pub type Digits = vest_lib2::asn1::NumericStringOwned;"));
    assert!(ber.contains("pub type Wide = vest_lib2::asn1::UniversalString;"));
    assert!(ber.contains("Refined(NUMERIC_STRING, Size::<true, 1, true, 8>)"));
    assert!(ber.contains("Refined(UNIVERSAL_STRING, Size::<true, 1, true, 8>)"));
}

#[test]
fn mixed_rules_propagate_and_duplicate_shared_definitions() {
    let mut overrides = BTreeMap::new();
    overrides.insert("Canonical".to_string(), EncodingRules::Der);
    overrides.insert("Ordered".to_string(), EncodingRules::Der);
    let generated = compile_with_rule_overrides(
        include_str!("../test/fixture_mixed.asn1"),
        CodegenOptions {
            encoding_rules: EncodingRules::Ber,
        },
        &overrides,
    )
    .unwrap();

    assert!(generated.contains("pub struct Shared {"));
    assert!(generated.contains("pub struct SharedDer<'a> {"));
    assert!(generated.contains("type CANONICAL__ = vest_lib2::asn1::der::SetOfTlvFmt<SHARED_DER>;"));
    assert!(
        generated.contains("use vest_lib2::asn1::ber::{BER_END, DEFAULT, OCTET_STRING, SEQUENCE};")
    );
    assert!(generated.contains("use vest_lib2::asn1::der::SET_OF;"));
    assert!(generated.contains("SET_OF(SHARED_DER::Fmt)"));
    assert!(!generated.contains("vest_lib2::asn1::ber::SEQUENCE("));
    assert!(!generated.contains("vest_lib2::asn1::der::SET_OF("));
    assert!(generated.contains("type ORDERED__ = Mapped<vest_lib2::asn1::der::SetFmt<"));
    assert!(generated.contains("pub type Version = i8;"));
    assert!(generated.contains("pub type VersionDer = i8;"));
}

#[test]
fn vendored_frontend_rejects_unrepresented_extension_markers() {
    let error =
        compile("Extensible DEFINITIONS ::= BEGIN Value ::= SEQUENCE { flag BOOLEAN, ... } END")
            .unwrap_err();
    assert!(error
        .to_string()
        .contains("extension markers are not represented in the Synta AST"));
}

#[test]
fn preserves_and_generates_collection_size_constraints() {
    let generated =
        compile("Sized DEFINITIONS ::= BEGIN Values ::= SEQUENCE SIZE (1..MAX) OF BOOLEAN END")
            .unwrap();
    assert!(generated.contains("Refined<SequenceOfFmt<BoolTlvFmt>, Size<true, 1, false, 0>>"));
    assert!(generated.contains("Refined(SEQUENCE_OF(BOOLEAN), Size::<true, 1, false, 0>)"));
}

#[test]
fn vendored_frontend_rejects_unrepresented_with_components() {
    let error = compile(
        "Components DEFINITIONS ::= BEGIN Value ::= SEQUENCE { flag BOOLEAN } (WITH COMPONENTS { flag PRESENT }) END",
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("trailing type constraints such as WITH COMPONENTS are not represented"));
}

#[test]
fn emits_explicit_notation_for_untagged_choice_and_any() {
    let generated = compile(include_str!("../test/fixture.asn1")).unwrap();
    assert!(generated.contains("EXPLICIT(3u64, Ref(SELECTION::Fmt))"));
    assert!(generated.contains("EXPLICIT(1u64, Ref(OPEN_VALUE::Fmt))"));
    assert!(!generated.contains("Tag { class: Class::ContextSpecific"));
}

#[test]
fn pretty_prints_sequence_fields_as_a_left_aligned_chain() {
    let generated = compile(include_str!("../test/fixture.asn1")).unwrap();
    let left_aligned = generated
        .lines()
        .map(str::trim_start)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(left_aligned.contains(concat!(
        "SEQUENCE(\n",
        "DEFAULT(IMPLICIT(0u64, COLOR::Fmt), Color::Green,\n",
        "REQUIRED(Ref(IDENTIFIER::Fmt),\n",
        "REQUIRED(Ref(MEASUREMENT::Fmt),\n",
        "REQUIRED(EXPLICIT(1u64, Ref(OPEN_VALUE::Fmt)),\n",
        "Eof)))),\n",
        ")",
    )));

    assert!(left_aligned.contains(concat!(
        "CHOICE(\n",
        "IMPLICIT(10u64, Ref(BOOLEAN)), CHOICE(\n",
        "IMPLICIT(11u64, Ref(INTEGER)), CHOICE(\n",
        "IMPLICIT(12u64, Ref(OCTET_STRING)), CHOICE(\n",
        "IMPLICIT(13u64, Ref(NULL)), CHOICE(\n",
        "EXPLICIT(14u64, Ref(UTF8_STRING)),\n",
        "EXPLICIT(15u64, Ref(OBJECT_IDENTIFIER))))))",
    )));
}

#[test]
fn checked_in_verified_fixture_is_fresh() {
    let generated = compile(include_str!("../test/fixture.asn1")).unwrap();
    if std::env::var("UPDATE_GOLDEN").is_ok() {
        std::fs::write("test/src/generated.rs", &generated).unwrap();
    }
    assert_eq!(generated, include_str!("../test/src/generated.rs"));
}

#[test]
fn generates_ber_formats_with_owned_flattened_values() {
    let generated = compile_ber(include_str!("../test/fixture_ber.asn1")).unwrap();
    assert!(generated.contains("// Generated formats parse and serialize BER."));
    assert!(generated.contains("use vest_lib2::asn1::ber::{"));
    assert!(generated.contains("pub type Payload = Vec<u8>;"));
    assert!(generated.contains("pub type Bits = vest_lib2::asn1::BitStringOwned;"));
    assert!(generated.contains("pub type Label = String;"));
    assert!(generated.contains("pub type OpenValue = vest_lib2::asn1::AnyOwned;"));
    assert!(!generated.contains("impl_der!(tagged(true), owned, ITEM"));
    assert!(generated.contains("impl_ber!(tagged(true), owned, ITEM"));
    assert!(generated.contains("BerEndFmt"));
    assert!(generated.contains("BER_END"));
    assert_uses_broadcast_disjointness_only(&generated);
}

#[test]
fn generates_ber_real_with_the_rule_specific_zero_copy_value() {
    let generated = compile_ber("Values DEFINITIONS ::= BEGIN Measurement ::= REAL END").unwrap();
    assert!(generated.contains("pub type Measurement<'a> = vest_lib2::asn1::Real<'a, BER>;"));
    assert!(generated.contains("type MEASUREMENT__ = RealTlvFmt;"));
    assert!(generated.contains("impl_ber!(tagged(false), borrowed, MEASUREMENT"));
}

#[test]
fn checked_in_verified_ber_fixture_is_fresh() {
    let generated = compile_ber(include_str!("../test/fixture_ber.asn1")).unwrap();
    if std::env::var("UPDATE_GOLDEN").is_ok() {
        std::fs::write("test/src/generated_ber.rs", &generated).unwrap();
    }
    assert_eq!(generated, include_str!("../test/src/generated_ber.rs"));
}

#[test]
fn checked_in_verified_mixed_fixture_is_fresh() {
    let mut overrides = BTreeMap::new();
    overrides.insert("Canonical".to_string(), EncodingRules::Der);
    overrides.insert("Ordered".to_string(), EncodingRules::Der);
    let generated = compile_with_rule_overrides(
        include_str!("../test/fixture_mixed.asn1"),
        CodegenOptions {
            encoding_rules: EncodingRules::Ber,
        },
        &overrides,
    )
    .unwrap();
    if std::env::var("UPDATE_GOLDEN").is_ok() {
        std::fs::write("test/src/generated_mixed.rs", &generated).unwrap();
    }
    assert_eq!(generated, include_str!("../test/src/generated_mixed.rs"));
}

#[test]
fn generates_the_curated_cms_module_with_ber_and_canonical_der_substructures() {
    let overrides = [
        "SignedAttributes",
        "AuthAttributes",
        "Certificate",
        "CertificateList",
        "AttributeCertificate",
        "AttributeCertificateV1",
        "Name",
        // PersonalName is a standalone X.400 SET in the curated module and is
        // not structurally reachable through Name because AttributeValue is open.
        "PersonalName",
    ]
    .into_iter()
    .map(|name| (name.to_string(), EncodingRules::Der))
    .collect::<BTreeMap<_, _>>();
    let generated = compile_with_rule_overrides(
        include_str!("../rfcs/CMS-RFC5652-Curated.asn1"),
        CodegenOptions {
            encoding_rules: EncodingRules::Ber,
        },
        &overrides,
    )
    .unwrap();

    assert!(
        generated.contains("type SIGNED_ATTRIBUTES__ = Refined<vest_lib2::asn1::der::SetOfTlvFmt<")
    );
    assert!(generated.contains("type CERTIFICATE__ = Mapped<vest_lib2::asn1::der::"));
    assert!(generated.contains("type CONTENT_INFO__ = Mapped<vest_lib2::asn1::ber::"));
    assert!(generated.contains("type ALGORITHM_IDENTIFIER_DER__"));
    assert!(generated.contains("impl_der!(tagged(true), borrowed, SIGNED_ATTRIBUTES"));
    assert!(generated.contains("impl_ber!(tagged(true), owned, CONTENT_INFO"));
}

#[test]
fn parses_the_standalone_curated_cms_rfc5652_module() {
    use vestasn1::ast::{TagClass, Tagging, TaggingMode};

    fn contains_only_lowered_wire_types(ty: &vestasn1::Type) -> bool {
        use vestasn1::Type;

        match ty {
            Type::Sequence(fields) | Type::Set(fields) => fields
                .iter()
                .all(|field| contains_only_lowered_wire_types(&field.ty)),
            Type::SequenceOf(inner, _) | Type::SetOf(inner, _) => {
                contains_only_lowered_wire_types(inner)
            }
            Type::Choice(variants) => variants
                .iter()
                .all(|variant| contains_only_lowered_wire_types(&variant.ty)),
            Type::Tagged { inner, .. }
            | Type::Constrained {
                base_type: inner, ..
            } => contains_only_lowered_wire_types(inner),
            Type::AnyDefinedBy(_) | Type::Class(_) => false,
            _ => true,
        }
    }

    fn definition<'a>(module: &'a vestasn1::SchemaModule, name: &str) -> &'a vestasn1::Type {
        &module
            .definitions
            .iter()
            .find(|definition| definition.name == name)
            .unwrap_or_else(|| panic!("curated CMS module is missing {name}"))
            .ty
    }

    fn field<'a>(ty: &'a vestasn1::Type, name: &str) -> &'a vestasn1::Type {
        let vestasn1::Type::Sequence(fields) = ty else {
            panic!("expected SEQUENCE containing {name}");
        };
        &fields
            .iter()
            .find(|field| field.name == name)
            .unwrap_or_else(|| panic!("SEQUENCE is missing {name}"))
            .ty
    }

    let module = vestasn1::parse(include_str!("../rfcs/CMS-RFC5652-Curated.asn1")).unwrap();

    assert_eq!(module.name, "VestCmsRfc5652Curated");
    assert_eq!(module.tagging_mode, Some(TaggingMode::Explicit));
    assert!(module.imports.is_empty());
    assert!(module.exports.is_empty());
    assert!(module.values.is_empty());
    assert!(module
        .definitions
        .iter()
        .all(|definition| contains_only_lowered_wire_types(&definition.ty)));

    for required in [
        "ContentInfo",
        "SignedData",
        "EnvelopedData",
        "DigestedData",
        "EncryptedData",
        "AuthenticatedData",
        "Certificate",
        "CertificateList",
        "AttributeCertificate",
        "AttributeCertificateV1",
        "GeneralName",
        "ORAddress",
    ] {
        assert!(
            module
                .definitions
                .iter()
                .any(|definition| definition.name == required),
            "curated CMS module is missing {required}",
        );
    }

    let vestasn1::Type::Tagged { tag, inner } =
        field(definition(&module, "ContentInfo"), "content")
    else {
        panic!("ContentInfo.content must remain tagged");
    };
    assert_eq!(tag.class, TagClass::ContextSpecific);
    assert_eq!(tag.number, 0);
    assert_eq!(tag.tagging, Tagging::Explicit);
    assert!(matches!(inner.as_ref(), vestasn1::Type::Any));

    let vestasn1::Type::Tagged { tag, .. } =
        field(definition(&module, "SignedData"), "certificates")
    else {
        panic!("SignedData.certificates must remain tagged");
    };
    assert_eq!(tag.class, TagClass::ContextSpecific);
    assert_eq!(tag.number, 0);
    assert_eq!(tag.tagging, Tagging::Implicit);

    let vestasn1::Type::Choice(general_names) = definition(&module, "GeneralName") else {
        panic!("GeneralName must remain a CHOICE");
    };
    let directory_name = &general_names
        .iter()
        .find(|variant| variant.name == "directoryName")
        .expect("GeneralName.directoryName is missing")
        .ty;
    let vestasn1::Type::Tagged { tag, .. } = directory_name else {
        panic!("GeneralName.directoryName must remain tagged");
    };
    assert_eq!(tag.class, TagClass::ContextSpecific);
    assert_eq!(tag.number, 4);
    assert_eq!(tag.tagging, Tagging::Explicit);
}
