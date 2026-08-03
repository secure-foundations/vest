#![allow(dead_code)]

pub mod generated;
pub mod generated_ber;
// #[path = "/tmp/vestasn1_generated_cms.rs"]
// pub mod generated_cms;
pub mod generated_mixed;

use vest_lib2::core::exec::parser::{PResult, Parser};
use vstd::prelude::*;

verus! {

pub fn parse_envelope<'a>(input: &'a [u8]) -> PResult<
    <generated::ENVELOPE as Parser<&'a [u8]>>::PT,
> {
    generated::ENVELOPE::Fmt.parse(&input)
}

pub fn parse_selection<'a>(input: &'a [u8]) -> PResult<
    <generated::SELECTION as Parser<&'a [u8]>>::PT,
> {
    generated::SELECTION::Fmt.parse(&input)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::generated::*;
    use vest_lib2::asn1::{DerOrd, TagFmt};
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::{Prepare, SerializerExt};
    use vstd::prelude::DeepView;

    fn assert_der_ord<F, T: DeepView + ?Sized>()
    where
        F: DerOrd<T>,
    {
    }

    #[test]
    fn generated_der_formats_compose_all_ordering_wrappers() {
        assert_der_ord::<PAYLOAD, &'static [u8]>();
        assert_der_ord::<SELECTION, Selection<'static>>();
        assert_der_ord::<AUTOMATION_SEQUENCE, AutomationSequence<'static>>();
        assert_der_ord::<ENVELOPES, Vec<Envelope<'static>>>();
    }

    #[test]
    fn primitive_round_trip_uses_generated_format() {
        let encoded = [0x01, 0x01, 0xff];
        let input = encoded.as_slice();
        let (consumed, value) = FLAG::Fmt.parse(&input).unwrap();
        assert_eq!(consumed, encoded.len());
        assert!(value);

        let len = FLAG::Fmt.prepare(&value).unwrap();
        let mut output = vec![0; len];
        FLAG::Fmt.serialize(&value, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn octet_string_size_constraint_checks_parse_and_prepare() {
        let encoded = [0x04, 0x01, 0xaa];
        let input = encoded.as_slice();
        assert!(PAYLOAD::Fmt.parse(&input).is_err());

        let short = &[0xaa][..];
        assert!(PAYLOAD::Fmt.prepare(&short).is_err());
    }

    #[test]
    fn parses_generated_sequence_and_optional_tag() {
        let encoded = [
            0x30, 0x0c, // Envelope SEQUENCE
            0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x05, // Header
            0x80, 0x02, 0xaa, 0xbb, // [0] IMPLICIT OCTET STRING
        ];
        let input = encoded.as_slice();
        let (consumed, envelope) = ENVELOPE::Fmt.parse(&input).unwrap();
        assert_eq!(consumed, encoded.len());
        assert!(envelope.header.flag);
        assert_eq!(envelope.payload, Some(&[0xaa, 0xbb][..]));

        let mut output = vec![0; ENVELOPE::Fmt.prepare(&envelope).unwrap()];
        ENVELOPE::Fmt.serialize(&envelope, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn parses_generated_choice() {
        let encoded = [0x81, 0x01, 0xff];
        let input = encoded.as_slice();
        let (_, selection) = SELECTION::Fmt.parse(&input).unwrap();
        assert!(matches!(selection, Selection::Flag(true)));

        let mut output = vec![0; SELECTION::Fmt.prepare(&selection).unwrap()];
        SELECTION::Fmt.serialize(&selection, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn boolean_defaults_are_inserted_and_omitted_canonically() {
        let encoded = [0x30, 0x00];
        let input = encoded.as_slice();
        let (_, features) = FEATURES::Fmt.parse(&input).unwrap();
        assert!(features.enabled);
        assert!(!features.visible);

        let value = Features {
            enabled: true,
            visible: false,
        };
        let len = FEATURES::Fmt.prepare(&value).unwrap();
        let mut output = vec![0; len];
        FEATURES::Fmt.serialize(&value, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn implicit_tag_on_choice_is_encoded_explicitly() {
        let encoded = [
            0x30, 0x05, // ChoiceEnvelope SEQUENCE
            0xa3, 0x03, // [3] promoted to EXPLICIT
            0x81, 0x01, 0xff, // Selection.flag
        ];
        let input = encoded.as_slice();
        let (_, envelope) = CHOICE_ENVELOPE::Fmt.parse(&input).unwrap();
        assert!(matches!(envelope.selection, Some(Selection::Flag(true))));
    }

    #[test]
    fn enumerated_is_closed_and_round_trips_nominally() {
        let encoded = [0x0a, 0x01, 0x01];
        let (_, color) = COLOR::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(color, Color::Green);

        let mut output = vec![0; COLOR::Fmt.prepare(&color).unwrap()];
        COLOR::Fmt.serialize(&color, output.as_mut_slice());
        assert_eq!(output, encoded);

        let unknown = [0x0a, 0x01, 0x05];
        assert!(COLOR::Fmt.parse(&unknown.as_slice()).is_err());
    }

    #[test]
    fn der_set_of_orders_complete_generated_tlvs_and_allows_duplicates() {
        let first = Header {
            flag: false,
            count: vest_lib2::asn1::Integer::from_i64(2),
        };
        let second = Header {
            flag: true,
            count: vest_lib2::asn1::Integer::from_i64(1),
        };
        let values = vec![first, second];
        let expected = [
            0x31, 0x10, // SET OF, 16 content octets
            0x30, 0x06, 0x01, 0x01, 0x00, 0x02, 0x01, 0x02, 0x30, 0x06, 0x01, 0x01, 0xff, 0x02,
            0x01, 0x01,
        ];

        let len = HEADERS::Fmt.prepare(&values).unwrap();
        let mut encoded = vec![0; len];
        HEADERS::Fmt.serialize(&values, encoded.as_mut_slice());
        assert_eq!(encoded, expected);

        let unordered = vec![
            Header {
                flag: true,
                count: vest_lib2::asn1::Integer::from_i64(1),
            },
            Header {
                flag: false,
                count: vest_lib2::asn1::Integer::from_i64(2),
            },
        ];
        assert!(HEADERS::Fmt.prepare(&unordered).is_err());

        let duplicate = vec![
            Header {
                flag: false,
                count: vest_lib2::asn1::Integer::from_i64(2),
            },
            Header {
                flag: false,
                count: vest_lib2::asn1::Integer::from_i64(2),
            },
        ];
        assert!(HEADERS::Fmt.prepare(&duplicate).is_ok());
    }

    #[test]
    fn generated_scalar_constants_keep_their_declared_types() {
        assert!(FEATURE_ENABLED);
        assert_eq!(ANSWER.as_i64(), Some(42));
        assert_eq!(DEFAULT_COLOR, Color::Green);
    }

    #[test]
    fn object_identifier_parses_owned_arcs_and_round_trips() {
        let encoded = [0x06, 0x03, 0x88, 0x37, 0x03];
        let (_, identifier) = IDENTIFIER::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(identifier.first(), 2);
        assert_eq!(identifier.second(), 999);
        assert_eq!(identifier.rest(), &[3]);

        let mut output = vec![0; IDENTIFIER::Fmt.prepare(&identifier).unwrap()];
        IDENTIFIER::Fmt.serialize(&identifier, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn real_and_any_backends_are_emitted() {
        let real_zero = [0x09, 0x00];
        let (_, real) = MEASUREMENT::Fmt.parse(&real_zero.as_slice()).unwrap();
        assert!(real.contents().is_empty());

        let any_boolean = [0x01, 0x01, 0xff];
        let (_, value) = OPEN_VALUE::Fmt.parse(&any_boolean.as_slice()).unwrap();
        assert_eq!(value.tag(), TagFmt::BOOLEAN);
        assert_eq!(value.content(), &[0xff]);
    }

    #[test]
    fn bmp_string_codegen_uses_owned_values_and_ucs2_octets() {
        let encoded = [0x30, 0x04, 0x1e, 0x02, 0x00, 0x41];
        let (_, value) = BMP_CONTAINER::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(value.name.inner(), "A");
        assert_eq!(BMP_NAME::Fmt.prepare(&value.name).unwrap(), 4);

        let mut output = vec![0; BMP_NAME::Fmt.prepare(&value.name).unwrap()];
        BMP_NAME::Fmt.serialize(&value.name, output.as_mut_slice());
        assert_eq!(output, encoded[2..]);
    }

    #[test]
    fn inline_composites_receive_nominal_helper_types() {
        let encoded = [
            0x30, 0x08, // InlineRecord
            0x30, 0x03, 0x04, 0x01, 0xaa, // nested SEQUENCE
            0x82, 0x01, 0xff, // selected.flag
        ];
        let (_, record) = INLINE_RECORD::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(record.nested.payload, &[0xaa]);
        assert!(matches!(record.selected, InlineRecordSelected::Flag(true)));

        let mut output = vec![0; INLINE_RECORD::Fmt.prepare(&record).unwrap()];
        INLINE_RECORD::Fmt.serialize(&record, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn ber_generated_sequence_flattens_constructed_values_and_normalizes_output() {
        use super::generated_ber as ber;

        #[rustfmt::skip]
        let encoded = [
            0x30, 0x80, // indefinite Item SEQUENCE
            0x24, 0x80, // constructed indefinite OCTET STRING
            0x04, 0x02, 0xaa, 0xbb, 0x04, 0x01, 0xcc, 0x00, 0x00,
            0xa0, 0x80, // [0] IMPLICIT constructed BIT STRING
            0x03, 0x02, 0x00, 0xf0, 0x03, 0x02, 0x04, 0xa0, 0x00, 0x00,
            0xa1, 0x80, // [1] IMPLICIT constructed UTF8String
            0x04, 0x02, b'h', b'i', 0x04, 0x01, b'!', 0x00, 0x00,
            0x00, 0x00, // Item EOC
        ];
        let (consumed, item) = ber::ITEM::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(consumed, encoded.len());
        assert_eq!(item.payload, [0xaa, 0xbb, 0xcc]);
        assert_eq!(item.bits.unused(), 4);
        assert_eq!(item.bits.bits(), &[0xf0, 0xa0]);
        assert_eq!(item.label, "hi!");
        assert!(item.printable.is_none());
        assert!(item.open.is_none());

        let mut payload = vec![0; ber::PAYLOAD::Fmt.prepare(&item.payload).unwrap()];
        ber::PAYLOAD::Fmt.serialize(&item.payload, payload.as_mut_slice());
        assert_eq!(payload, [0x04, 0x03, 0xaa, 0xbb, 0xcc]);

        let mut bits = vec![0; ber::BITS::Fmt.prepare(&item.bits).unwrap()];
        ber::BITS::Fmt.serialize(&item.bits, bits.as_mut_slice());
        assert_eq!(bits, [0x03, 0x03, 0x04, 0xf0, 0xa0]);

        let mut label = vec![0; ber::LABEL::Fmt.prepare(&item.label).unwrap()];
        ber::LABEL::Fmt.serialize(&item.label, label.as_mut_slice());
        assert_eq!(label, [0x0c, 0x03, b'h', b'i', b'!']);

        let mut item_output = vec![0; ber::ITEM::Fmt.prepare(&item).unwrap()];
        ber::ITEM::Fmt.serialize(&item, item_output.as_mut_slice());
        assert_eq!(
            item_output,
            [
                0x30, 0x0f, 0x04, 0x03, 0xaa, 0xbb, 0xcc, 0x80, 0x03, 0x04, 0xf0, 0xa0, 0x81, 0x03,
                b'h', b'i', b'!'
            ]
        );
    }

    #[test]
    fn ber_generated_sequence_of_accepts_indefinite_length() {
        use super::generated_ber as ber;

        let encoded = [0x30, 0x80, 0x01, 0x01, 0xff, 0x01, 0x01, 0x00, 0x00, 0x00];
        let (_, flags) = ber::FLAGS::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(flags, [true, false]);

        let mut output = vec![0; ber::FLAGS::Fmt.prepare(&flags).unwrap()];
        ber::FLAGS::Fmt.serialize(&flags, output.as_mut_slice());
        assert_eq!(output, [0x30, 0x06, 0x01, 0x01, 0xff, 0x01, 0x01, 0x00]);
    }

    #[test]
    fn ber_generated_set_of_preserves_schema_order_without_der_sorting() {
        use super::generated_ber as ber;

        // DER would require FALSE before TRUE, but BER SET OF imposes no canonical octet order.
        let values = vec![true, false];
        let mut output = vec![0; ber::FLAG_SET::Fmt.prepare(&values).unwrap()];
        ber::FLAG_SET::Fmt.serialize(&values, output.as_mut_slice());
        assert_eq!(output, [0x31, 0x06, 0x01, 0x01, 0xff, 0x01, 0x01, 0x00]);

        let (_, parsed) = ber::FLAG_SET::Fmt.parse(&output.as_slice()).unwrap();
        assert_eq!(parsed, values);
    }

    #[test]
    fn ber_generated_any_preserves_indefinite_contents_then_serializes_definite() {
        use super::generated_ber as ber;

        let encoded = [0x30, 0x80, 0x01, 0x01, 0xff, 0x04, 0x01, 0xaa, 0x00, 0x00];
        let (_, value) = ber::OPEN_VALUE::Fmt.parse(&encoded.as_slice()).unwrap();
        assert_eq!(value.tag(), TagFmt::SEQUENCE);
        assert_eq!(value.content(), &[0x01, 0x01, 0xff, 0x04, 0x01, 0xaa]);

        let mut output = vec![0; ber::OPEN_VALUE::Fmt.prepare(&value).unwrap()];
        ber::OPEN_VALUE::Fmt.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x30, 0x06, 0x01, 0x01, 0xff, 0x04, 0x01, 0xaa]);

        let nested = [
            0x30, 0x80, // outer SEQUENCE
            0x31, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00, // inner SET, including EOC
            0x00, 0x00,
        ];
        let (_, value) = ber::OPEN_VALUE::Fmt.parse(&nested.as_slice()).unwrap();
        assert_eq!(value.content(), &[0x31, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00]);

        let primitive_indefinite = [0x04, 0x80, 0x04, 0x01, 0xaa, 0x00, 0x00];
        assert!(ber::OPEN_VALUE::Fmt
            .parse(&primitive_indefinite.as_slice())
            .is_err());
    }
}
