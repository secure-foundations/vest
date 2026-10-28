use std::collections::BTreeMap;
use vest_asn1::{compile_with_rule_overrides, CodegenOptions, EncodingRules};

#[test]
fn generated_modules_are_current() {
    let cases = [
        (
            include_str!("../../vest_asn1/tests/fixtures/fixture.asn1"),
            include_str!("../src/generated.rs"),
            EncodingRules::Der,
            &[][..],
        ),
        (
            include_str!("../../vest_asn1/tests/fixtures/fixture_ber.asn1"),
            include_str!("../src/generated_ber.rs"),
            EncodingRules::Ber,
            &[][..],
        ),
        (
            include_str!("../../vest_asn1/tests/fixtures/fixture_mixed.asn1"),
            include_str!("../src/generated_mixed.rs"),
            EncodingRules::Ber,
            &["Shared", "Canonical", "Ordered"][..],
        ),
        (
            include_str!("../../vest_asn1/rfcs/CMS-RFC5652-Curated.asn1"),
            include_str!("../src/generated_cms.rs"),
            EncodingRules::Ber,
            &[
                "SignedAttributes",
                "AuthAttributes",
                "Certificate",
                "CertificateList",
                "AttributeCertificate",
                "AttributeCertificateV1",
            ][..],
        ),
    ];
    for (source, expected, encoding_rules, der_definitions) in cases {
        let overrides = der_definitions
            .iter()
            .map(|name| (name.to_string(), EncodingRules::Der))
            .collect::<BTreeMap<_, _>>();
        let generated = compile_with_rule_overrides(
            source,
            CodegenOptions { encoding_rules },
            &overrides,
        )
        .unwrap();
        assert_eq!(generated, expected, "Run make -C vest_asn1_tests generate");
    }
}
