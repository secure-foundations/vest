use vestasn1::{compile, Error};

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
    assert!(generated.contains("pub type MessageFmt = Mapped<SequenceFmt<Pair<"));
    assert!(generated.contains("Optional<Ref<PayloadFmt>, Eof>"));
    assert!(generated.contains("pub const fn MESSAGES_FMT() -> MessagesFmt"));
    assert!(generated.contains("pub type MessagesFmt = SequenceOfFmt<MessageFmt>;"));
    assert!(generated.contains(
        "Choice<ImplicitFmt<Ref<FlagFmt>>, ExplicitFmt<Ref<PayloadFmt>>>"
    ));
    assert!(generated.contains("IMPLICIT(0u64, Ref(FLAG_FMT()))"));
    assert!(!generated.contains("assert(disjoint_domains"));
}

#[test]
fn generates_verified_octet_string_size_constraint() {
    let generated =
        compile("Example DEFINITIONS ::= BEGIN Payload ::= OCTET STRING (SIZE (1..32)) END")
            .unwrap();
    assert!(generated.contains(
        "Refined<OctetStringTlvFmt, Size<true, 1, true, 32>>"
    ));
    assert!(generated.contains("Refined(OCTET_STRING, Size::<true, 1, true, 32>)"));
}

#[test]
fn generates_verified_integer_range_constraint() {
    let generated =
        compile("Example DEFINITIONS ::= BEGIN Version ::= INTEGER (0..2) END").unwrap();
    assert!(generated.contains(
        "Refined<IntegerTlvFmt, IntegerRange<true, 0, true, 2>>"
    ));
    assert!(generated.contains("Refined(INTEGER, IntegerRange::<true, 0, true, 2>)"));
}

#[test]
fn generates_verified_string_size_constraint() {
    let generated = compile(
        "Example DEFINITIONS ::= BEGIN Label ::= UTF8String (SIZE (1..32)) END",
    )
    .unwrap();
    assert!(generated.contains(
        "Refined<Utf8StringTlvFmt, Size<true, 1, true, 32>>"
    ));
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
    assert!(generated.contains("DefaultFmt<ImplicitFmt<EnabledFmt>, bool,"));
    let left_aligned = generated.lines().map(str::trim_start).collect::<Vec<_>>().join("\n");
    assert!(left_aligned.contains("inner:\nSEQUENCE(\nDEFAULT("));
    assert!(generated.contains("IMPLICIT(0u64, ENABLED_FMT())"));
    assert!(generated.contains("IMPLICIT(1u64, BOOLEAN)"));
    assert!(left_aligned.contains("Eof))"));
    assert!(generated.contains("pub const fn FLAGS_FMT()"));
    assert!(generated.contains("{\n    Mapped {"));
}

#[test]
fn rejects_defaults_whose_exec_value_is_not_supported() {
    let error = compile(
        "Defaults DEFINITIONS ::= BEGIN Config ::= SEQUENCE { port INTEGER DEFAULT 80 } END",
    )
    .unwrap_err();
    assert!(error
        .to_string()
        .contains("only BOOLEAN and ENUMERATED DEFAULT"));
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
    assert!(generated.contains("Optional<ExplicitFmt<Ref<ValueFmt>>, Eof>"));
    assert!(generated.contains("EXPLICIT(0u64, Ref(VALUE_FMT()))"));
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
    assert!(generated.contains("pub type BaseFmt = ImplicitFmt<IntegerTlvFmt>;"));
    assert!(generated.contains("pub type RetaggedFmt = ImplicitFmt<BaseFmt>;"));
    assert!(generated.contains("IMPLICIT(1u64, BASE_FMT())"));
}

#[test]
fn format_value_names_do_not_collide_with_vest_der_symbols() {
    let generated = compile("Names DEFINITIONS ::= BEGIN DER ::= BOOLEAN END").unwrap();
    assert!(generated.contains("pub type DerFmt = BoolTlvFmt;"));
    assert!(generated.contains("pub const fn DER_FMT() -> DerFmt"));
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
    assert!(error.to_string().contains(
        "OBJECT IDENTIFIER value assignments are not supported yet"
    ));
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
    assert!(generated.contains("pub type IdentifierFmt = ObjectIdentifierTlvFmt;"));
    assert!(generated.contains("pub type MeasurementFmt = RealTlvFmt;"));
    assert!(generated.contains("pub type OpenValueFmt = AnyTlvFmt;"));
    assert!(generated.contains("pub struct ContainerNested"));
    assert!(generated.contains("pub enum ContainerSelected<'a>"));
}

#[test]
fn rejects_set_of_until_allocation_free_der_ordering_is_generic() {
    let error = compile("Sets DEFINITIONS ::= BEGIN Values ::= SET OF INTEGER END").unwrap_err();
    assert!(error.to_string().contains("SET OF generation is disabled"));
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
    assert!(generated.contains(
        "Refined<SequenceOfFmt<BoolTlvFmt>, Size<true, 1, false, 0>>"
    ));
    assert!(generated.contains(
        "Refined(SEQUENCE_OF(BOOLEAN), Size::<true, 1, false, 0>)"
    ));
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
    assert!(generated.contains("EXPLICIT(3u64, Ref(SELECTION_FMT()))"));
    assert!(generated.contains("EXPLICIT(1u64, Ref(OPEN_VALUE_FMT()))"));
    assert!(!generated.contains("Tag { class: Class::ContextSpecific"));
}

#[test]
fn pretty_prints_sequence_fields_as_a_left_aligned_chain() {
    let generated = compile(include_str!("../test/fixture.asn1")).unwrap();
    let left_aligned = generated.lines().map(str::trim_start).collect::<Vec<_>>().join("\n");
    assert!(left_aligned.contains(concat!(
        "DEFAULT(IMPLICIT(0u64, COLOR_FMT()), Color::Green,\n",
        "REQUIRED(Ref(IDENTIFIER_FMT()),\n",
        "REQUIRED(Ref(MEASUREMENT_FMT()),\n",
        "REQUIRED(EXPLICIT(1u64, Ref(OPEN_VALUE_FMT())),\n",
        "Eof))))",
    )));
}

#[test]
fn checked_in_verified_fixture_is_fresh() {
    let generated = compile(include_str!("../test/fixture.asn1")).unwrap();
    assert_eq!(generated, include_str!("../test/src/generated.rs"));
}
