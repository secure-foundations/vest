//! BER constructed-value formats and notation-style aliases.
use crate::asn1::{
    ASN1Fmt, BmpStringFmt, BoolFmt, Class, EnumeratedFmt, Ia5StringFmt, IntegerFmt, NullFmt,
    ObjectIdentifierFmt, PrintableStringFmt, RealFmt, TagFmt, TeletexStringFmt, Utf8StringFmt, BER,
};
use crate::core::spec::SpecByteLen;
use vstd::prelude::*;

use super::modifiers::{defaulted, explicit_tag};
pub use super::modifiers::{
    implicitly_tagged as Implicit, ImplicitFmt, CHOICE, IMPLICIT, IMPLICIT_APPLICATION,
    IMPLICIT_PRIVATE, OPTIONAL, REQUIRED,
};
use super::{GeneralizedTimeFmt, Integer16Fmt, Integer8Fmt, UtcTimeFmt};

pub mod any;
pub mod bit_string;
pub mod char_string;
pub mod octet_string;
pub mod sequence;
pub mod sequence_of;

pub use any::*;
pub use bit_string::*;
pub use char_string::*;
pub use octet_string::*;
pub use sequence::*;
pub use sequence_of::*;

verus! {

/// Control the maximum recursion depth for BER OCTET STRING and restricted character string parsing.
pub const MAX_RECURSION_DEPTH: usize = 30;

/// Uniform notation aliases used by schema generators.
pub type BoolTlvFmt = ASN1Fmt<BoolFmt<BER>, BER>;

pub type AnyTlvFmt = BerAnyFmt<MAX_RECURSION_DEPTH>;

pub type IntegerTlvFmt = ASN1Fmt<IntegerFmt, BER>;

pub type Integer8TlvFmt = ASN1Fmt<Integer8Fmt, BER>;

pub type Integer16TlvFmt = ASN1Fmt<Integer16Fmt, BER>;

pub type EnumeratedTlvFmt = ASN1Fmt<EnumeratedFmt, BER>;

pub type Enumerated16TlvFmt = ASN1Fmt<Integer16Fmt, BER>;

pub type ObjectIdentifierTlvFmt = ASN1Fmt<ObjectIdentifierFmt, BER>;

pub type RealTlvFmt = ASN1Fmt<RealFmt, BER>;

pub type BitStringTlvFmt = BerBitStringFmt<MAX_RECURSION_DEPTH>;

pub type OctetStringTlvFmt = BerOctetStringFmt<MAX_RECURSION_DEPTH>;

pub type NullTlvFmt = ASN1Fmt<NullFmt, BER>;

pub type Utf8StringTlvFmt = BerUtf8StringFmt<MAX_RECURSION_DEPTH>;

pub type PrintableStringTlvFmt = BerPrintableStringFmt<MAX_RECURSION_DEPTH>;

pub type TeletexStringTlvFmt = BerTeletexStringFmt<MAX_RECURSION_DEPTH>;

pub type Ia5StringTlvFmt = BerIa5StringFmt<MAX_RECURSION_DEPTH>;

pub type UtcTimeTlvFmt = ASN1Fmt<UtcTimeFmt<BER>, BER>;

pub type GeneralizedTimeTlvFmt = ASN1Fmt<GeneralizedTimeFmt<BER>, BER>;

pub type BmpStringTlvFmt = BerBmpStringFmt<MAX_RECURSION_DEPTH>;

pub type SequenceFmt<C> = BerSequenceFmt<C>;

pub type SequenceOfFmt<C> = BerSequenceOfFmt<C>;

pub type SetOfTlvFmt<C> = BerSequenceOfFmt<C>;

pub type ExplicitFmt<C> = BerSequenceFmt<C>;

pub type DefaultFmt<Field, Default, Rest> = super::DefaultedFmt<Field, Default, Rest, BER>;

pub const BOOLEAN: BoolTlvFmt = ASN1Fmt(TagFmt::BOOLEAN, BoolFmt::<BER>);

pub const ANY: AnyTlvFmt = BerAnyFmt;

pub const INTEGER: IntegerTlvFmt = ASN1Fmt(TagFmt::INTEGER, IntegerFmt);

pub const INTEGER8: Integer8TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer8Fmt);

pub const INTEGER16: Integer16TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer16Fmt);

pub const ENUMERATED: EnumeratedTlvFmt = ASN1Fmt(TagFmt::ENUMERATED, EnumeratedFmt);

pub const ENUMERATED16: Enumerated16TlvFmt = ASN1Fmt(TagFmt::ENUMERATED, Integer16Fmt);

pub const OBJECT_IDENTIFIER: ObjectIdentifierTlvFmt = ASN1Fmt(
    TagFmt::OBJECT_IDENTIFIER,
    ObjectIdentifierFmt,
);

pub const REAL: RealTlvFmt = ASN1Fmt(TagFmt::REAL, RealFmt);

pub const BIT_STRING: BitStringTlvFmt = BerBitStringFmt(TagFmt::BIT_STRING);

pub const NULL: NullTlvFmt = ASN1Fmt(TagFmt::NULL, NullFmt);

pub const UTC_TIME: UtcTimeTlvFmt = ASN1Fmt(TagFmt::UTC_TIME, UtcTimeFmt::<BER>);

pub const GENERALIZED_TIME: GeneralizedTimeTlvFmt = ASN1Fmt(
    TagFmt::GENERALIZED_TIME,
    GeneralizedTimeFmt::<BER>,
);

pub const OCTET_STRING: OctetStringTlvFmt = BerOctetStringFmt(TagFmt::OCTET_STRING);

pub const UTF8_STRING: Utf8StringTlvFmt = BerCharStringFmt(TagFmt::UTF8_STRING, Utf8StringFmt);

pub const PRINTABLE_STRING: PrintableStringTlvFmt = BerCharStringFmt(
    TagFmt::PRINTABLE_STRING,
    PrintableStringFmt,
);

pub const IA5_STRING: Ia5StringTlvFmt = BerCharStringFmt(TagFmt::IA5_STRING, Ia5StringFmt);

pub const TELETEX_STRING: TeletexStringTlvFmt = BerCharStringFmt(
    TagFmt::TELETEX_STRING,
    TeletexStringFmt,
);

pub const BMP_STRING: BmpStringTlvFmt = BerCharStringFmt(TagFmt::BMP_STRING, BmpStringFmt);

/// Construct a BER `SEQUENCE`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE<C: Copy>(content: C) -> SequenceFmt<C>
    returns
        BerSequenceFmt(TagFmt::SEQUENCE, content),
{
    BerSequenceFmt::universal(content)
}

/// Construct a BER `SEQUENCE OF`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE_OF<C: Copy>(content: C) -> SequenceOfFmt<C>
    returns
        BerSequenceOfFmt(TagFmt::SEQUENCE, content),
{
    BerSequenceOfFmt::universal(content)
}

/// Construct a BER `SET OF`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SET_OF<C: Copy>(content: C) -> SetOfTlvFmt<C>
    returns
        BerSequenceOfFmt(TagFmt::SET, content),
{
    BerSequenceOfFmt(TagFmt::SET, content)
}

/// Apply an ASN.1 EXPLICIT tag with an arbitrary tag class.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn Explicit<C: Copy>(class: Class, number: u64, inner: C) -> ExplicitFmt<C>
    returns
        BerSequenceFmt(explicit_tag(class, number), inner),
{
    BerSequenceFmt(explicit_tag(class, number), inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_APPLICATION<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Application, number, inner),
{
    Explicit(Class::Application, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_PRIVATE<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Private, number, inner),
{
    Explicit(Class::Private, number, inner)
}

#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn DEFAULT<Field, Rest>(field: Field, default: Field::T, cont: Rest) -> DefaultFmt<
    Field,
    Field::T,
    Rest,
> where Field: SpecByteLen
    returns
        defaulted::<Field, Rest, BER>(field, default, cont),
{
    defaulted::<Field, Rest, BER>(field, default, cont)
}

} // verus!
#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use crate::asn1::{BmpString, Integer8Fmt};
    use crate::combinators::Pair;
    use crate::core::exec::{ParseErrorKind, Parser, Prepare, SerializerExt};

    type Octets = BerOctetStringFmt<8>;

    fn parse_universal(input: &[u8]) -> (usize, Vec<u8>) {
        Octets::universal().parse(&input).unwrap()
    }

    fn integer_sequence() -> BerSequenceOfFmt<ASN1Fmt<Integer8Fmt, BER>> {
        SEQUENCE_OF(ASN1Fmt(TagFmt::INTEGER, Integer8Fmt))
    }

    fn integer_fields_sequence(
    ) -> BerSequenceFmt<Pair<ASN1Fmt<Integer8Fmt, BER>, ASN1Fmt<Integer8Fmt, BER>>> {
        let integer = ASN1Fmt::<_, BER>(TagFmt::INTEGER, Integer8Fmt);
        SEQUENCE(Pair(integer, integer))
    }

    #[test]
    fn ber_sequence_parses_definite_and_indefinite_schema_bodies() {
        let format = integer_fields_sequence();
        let definite = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), (1i8, 2i8)),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), (1i8, 2i8)),
        );

        let missing_eoc = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        assert!(format.parse(&&missing_eoc[..]).is_err());

        let extra_component = [
            0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x02, 0x01, 0x03, 0x00, 0x00,
        ];
        assert!(format.parse(&&extra_component[..]).is_err());
    }

    #[test]
    fn ber_sequence_supports_implicit_tags_and_definite_normalization() {
        let content = integer_fields_sequence().1;
        let format = BerSequenceFmt::implicit(Class::ContextSpecific, 0, content);
        let indefinite = [0xa0, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];
        let (_, value) = format.parse(&&indefinite[..]).unwrap();
        assert_eq!(value, (1i8, 2i8));

        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0xa0, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02]);

        let universal = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        assert!(format.parse(&&universal[..]).is_err());
    }

    #[test]
    fn ber_sequence_of_parses_definite_and_indefinite_forms() {
        let format = integer_sequence();
        let definite = [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02];
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), vec![1i8, 2i8]),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), vec![1i8, 2i8]),
        );

        let empty_definite = [0x30, 0x00];
        let empty_indefinite = [0x30, 0x80, 0x00, 0x00];
        assert_eq!(
            format.parse(&&empty_definite[..]).unwrap(),
            (empty_definite.len(), Vec::<i8>::new()),
        );
        assert_eq!(
            format.parse(&&empty_indefinite[..]).unwrap(),
            (empty_indefinite.len(), Vec::<i8>::new()),
        );
    }

    #[test]
    fn ber_sequence_of_supports_implicit_outer_tags() {
        let element = ASN1Fmt::<_, BER>(TagFmt::INTEGER, Integer8Fmt);
        let format = BerSequenceOfFmt::implicit(Class::ContextSpecific, 0, element);
        let definite = [0xa0, 0x03, 0x02, 0x01, 0x01];
        let indefinite = [0xa0, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00];

        assert_eq!(
            format.parse(&&definite[..]).unwrap(),
            (definite.len(), vec![1i8]),
        );
        assert_eq!(
            format.parse(&&indefinite[..]).unwrap(),
            (indefinite.len(), vec![1i8]),
        );

        let universal = [0x30, 0x03, 0x02, 0x01, 0x01];
        assert!(format.parse(&&universal[..]).is_err());

        let value = vec![1i8];
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, definite);
    }

    #[test]
    fn ber_sequence_of_serialization_normalizes_to_definite_form() {
        let format = integer_sequence();
        let indefinite = [0x30, 0x80, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02, 0x00, 0x00];
        let (_, value) = format.parse(&&indefinite[..]).unwrap();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());

        assert_eq!(output, [0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02]);
    }

    #[test]
    fn nested_ber_sequence_of_delegates_indefinite_values_to_the_element_codec() {
        let inner = integer_sequence();
        let outer = SEQUENCE_OF(inner);
        let input = [
            0x30, 0x80, // outer indefinite SEQUENCE OF
            0x30, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00, // inner indefinite value
            0x30, 0x03, 0x02, 0x01, 0x02, // inner definite value
            0x00, 0x00, // outer EOC
        ];

        assert_eq!(
            outer.parse(&&input[..]).unwrap(),
            (input.len(), vec![vec![1i8], vec![2i8]]),
        );
    }

    #[test]
    fn ber_sequence_of_rejects_missing_eoc_and_non_elements() {
        let format = integer_sequence();
        let missing_eoc = [0x30, 0x80, 0x02, 0x01, 0x01];
        assert!(format.parse(&&missing_eoc[..]).is_err());

        let boolean_element = [0x30, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00];
        assert!(format.parse(&&boolean_element[..]).is_err());
    }

    #[test]
    fn parses_primitive_and_definite_constructed_octet_strings() {
        let primitive = [0x04, 0x03, b'a', b'b', b'c'];
        assert_eq!(
            parse_universal(&primitive),
            (primitive.len(), b"abc".to_vec())
        );

        let constructed = [0x24, 0x07, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c'];
        assert_eq!(
            parse_universal(&constructed),
            (constructed.len(), b"abc".to_vec()),
        );
    }

    #[test]
    fn parses_indefinite_and_nested_constructed_octet_strings() {
        let indefinite = [
            0x24, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        assert_eq!(
            parse_universal(&indefinite),
            (indefinite.len(), b"abc".to_vec()),
        );

        let nested = [
            0x24, 0x80, 0x24, 0x80, 0x04, 0x01, b'a', 0x00, 0x00, 0x04, 0x01, b'b', 0x00, 0x00,
        ];
        assert_eq!(parse_universal(&nested), (nested.len(), b"ab".to_vec()));
    }

    #[test]
    fn implicit_tagging_replaces_only_the_outer_tag() {
        let format = Octets::implicit(Class::ContextSpecific, 0);

        let primitive = [0x80, 0x03, b'a', b'b', b'c'];
        assert_eq!(
            format.parse(&&primitive[..]).unwrap(),
            (primitive.len(), b"abc".to_vec()),
        );

        let constructed = [
            0xa0, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        assert_eq!(
            format.parse(&&constructed[..]).unwrap(),
            (constructed.len(), b"abc".to_vec()),
        );

        // Recursive components retain the universal OCTET STRING tag.
        let retagged_child = [0xa0, 0x80, 0x80, 0x01, b'a', 0x00, 0x00];
        assert_eq!(
            format.parse(&&retagged_child[..]).unwrap_err().kind,
            ParseErrorKind::InvalidTag,
        );
    }

    #[test]
    fn rejects_malformed_framing_and_enforces_the_recursion_limit() {
        let missing_eoc = [0x24, 0x80, 0x04, 0x01, b'a'];
        assert!(Octets::universal().parse(&&missing_eoc[..]).is_err());

        let short_definite_body = [0x24, 0x04, 0x04, 0x01, b'a'];
        assert!(Octets::universal()
            .parse(&&short_definite_body[..])
            .is_err());

        let nested_2 = [
            0x24, 0x80, 0x24, 0x80, 0x04, 0x01, b'a', 0x00, 0x00, 0x04, 0x01, b'b', 0x00, 0x00,
        ];
        assert!(BerOctetStringFmt::<1>::universal()
            .parse(&&nested_2[..])
            .is_err());
    }

    #[test]
    fn serialization_normalizes_to_primitive_definite_form() {
        let constructed = [
            0x24, 0x80, 0x04, 0x02, b'a', b'b', 0x04, 0x01, b'c', 0x00, 0x00,
        ];
        let (_, value) = parse_universal(&constructed);
        let format = Octets::universal();
        let mut output = vec![0; format.prepare(value.as_slice()).unwrap()];
        format.serialize(value.as_slice(), output.as_mut_slice());
        assert_eq!(output, [0x04, 0x03, b'a', b'b', b'c']);

        let implicit = Octets::implicit(Class::ContextSpecific, 0);
        let mut output = vec![0; implicit.prepare(value.as_slice()).unwrap()];
        implicit.serialize(value.as_slice(), output.as_mut_slice());
        assert_eq!(output, [0x80, 0x03, b'a', b'b', b'c']);
    }

    #[test]
    fn ber_utf8_string_validates_after_flattening_segments() {
        type Format = BerUtf8StringFmt<8>;

        // U+20AC is split in the middle of its three-octet UTF-8 encoding. Validating each
        // primitive segment separately would reject this standards-permitted encoding.
        let split_scalar = [
            0x2c, 0x80, 0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00,
        ];
        let (n, value) = Format::universal().parse(&&split_scalar[..]).unwrap();
        assert_eq!(n, split_scalar.len());
        assert_eq!(value.as_str(), "€");

        let primitive = [0x0c, 0x03, 0xe2, 0x82, 0xac];
        assert_eq!(
            Format::universal()
                .parse(&&primitive[..])
                .unwrap()
                .1
                .as_str(),
            "€"
        );

        let nested = [
            0x2c, 0x80, // constructed UTF8String
            0x24, 0x80, // nested universal constructed OCTET STRING
            0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00, // nested EOC
            0x00, 0x00, // outer EOC
        ];
        assert_eq!(
            Format::universal().parse(&&nested[..]).unwrap().1.as_str(),
            "€"
        );

        let format = Format::universal();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x0c, 0x03, 0xe2, 0x82, 0xac]);
    }

    #[test]
    fn ber_restricted_strings_support_implicit_outer_tags() {
        type Format = BerUtf8StringFmt<8>;
        let format = Format::implicit(Class::ContextSpecific, 0);
        let input = [
            0xa0, 0x80, 0x04, 0x01, 0xe2, 0x04, 0x02, 0x82, 0xac, 0x00, 0x00,
        ];
        let (_, value) = format.parse(&&input[..]).unwrap();
        assert_eq!(value.as_str(), "€");

        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x80, 0x03, 0xe2, 0x82, 0xac]);
    }

    #[test]
    fn ber_printable_and_ia5_validate_flattened_contents() {
        let printable = [
            0x33, 0x80, 0x04, 0x02, b'A', b'B', 0x04, 0x02, b'1', b'?', 0x00, 0x00,
        ];
        let (_, value) = BerPrintableStringFmt::<8>::universal()
            .parse(&&printable[..])
            .unwrap();
        assert_eq!(value.inner(), "AB1?");

        let invalid_ia5 = [0x36, 0x80, 0x04, 0x01, 0x80, 0x00, 0x00];
        assert!(BerIa5StringFmt::<8>::universal()
            .parse(&&invalid_ia5[..])
            .is_err());
    }

    #[test]
    fn ber_bmp_string_allows_code_units_to_cross_segments() {
        type Format = BerBmpStringFmt<8>;

        // BMPString "A" is 00 41. The code unit is deliberately split between children.
        let split_code_unit = [0x3e, 0x80, 0x04, 0x01, 0x00, 0x04, 0x01, 0x41, 0x00, 0x00];
        let (_, value) = Format::universal().parse(&&split_code_unit[..]).unwrap();
        assert_eq!(value.inner(), "A");

        let malformed = [0x1e, 0x01, 0x00];
        assert!(Format::universal().parse(&&malformed[..]).is_err());
        let surrogate = [0x1e, 0x02, 0xd8, 0x00];
        assert!(Format::universal().parse(&&surrogate[..]).is_err());

        let value = BmpString::new(String::from("A"));
        let format = Format::universal();
        let mut output = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x1e, 0x02, 0x00, 0x41]);
    }
}
