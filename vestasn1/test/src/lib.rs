#![allow(dead_code)]

pub mod generated;
pub mod generated_ber;

use vest_lib2::core::exec::parser::{PResult, Parser};
use vstd::prelude::*;

verus! {

pub fn parse_envelope<'a>(input: &'a [u8]) -> PResult<
    <generated::EnvelopeFmt as Parser<&'a [u8]>>::PT,
> {
    generated::ENVELOPE_FMT().parse(&input)
}

pub fn parse_selection<'a>(input: &'a [u8]) -> PResult<
    <generated::SelectionFmt as Parser<&'a [u8]>>::PT,
> {
    generated::SELECTION_FMT().parse(&input)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::generated::*;
    use vest_lib2::asn1::TagFmt;
    use vest_lib2::core::exec::parser::Parser;
    use vest_lib2::core::exec::serializer::{Prepare, SerializerExt};

    #[test]
    fn primitive_round_trip_uses_generated_format() {
        let encoded = [0x01, 0x01, 0xff];
        let input = encoded.as_slice();
        let (consumed, value) = FLAG_FMT().parse(&input).unwrap();
        assert_eq!(consumed, encoded.len());
        assert!(value);

        let len = FLAG_FMT().prepare(&value).unwrap();
        let mut output = vec![0; len];
        FLAG_FMT().serialize(&value, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn octet_string_size_constraint_checks_parse_and_prepare() {
        let encoded = [0x04, 0x01, 0xaa];
        let input = encoded.as_slice();
        assert!(PAYLOAD_FMT().parse(&input).is_err());

        let short = &[0xaa][..];
        assert!(PAYLOAD_FMT().prepare(&short).is_err());
    }

    #[test]
    fn parses_generated_sequence_and_optional_tag() {
        let encoded = [
            0x30, 0x0c, // Envelope SEQUENCE
            0x30, 0x06, 0x01, 0x01, 0xff, 0x02, 0x01, 0x05, // Header
            0x80, 0x02, 0xaa, 0xbb, // [0] IMPLICIT OCTET STRING
        ];
        let input = encoded.as_slice();
        let (consumed, envelope) = ENVELOPE_FMT().parse(&input).unwrap();
        assert_eq!(consumed, encoded.len());
        assert!(envelope.header.flag);
        assert_eq!(envelope.payload, Some(&[0xaa, 0xbb][..]));

        let mut output = vec![0; ENVELOPE_FMT().prepare(&envelope).unwrap()];
        ENVELOPE_FMT().serialize(&envelope, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn parses_generated_choice() {
        let encoded = [0x81, 0x01, 0xff];
        let input = encoded.as_slice();
        let (_, selection) = SELECTION_FMT().parse(&input).unwrap();
        assert!(matches!(selection, Selection::Flag(true)));

        let mut output = vec![0; SELECTION_FMT().prepare(&selection).unwrap()];
        SELECTION_FMT().serialize(&selection, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn boolean_defaults_are_inserted_and_omitted_canonically() {
        let encoded = [0x30, 0x00];
        let input = encoded.as_slice();
        let (_, features) = FEATURES_FMT().parse(&input).unwrap();
        assert!(features.enabled);
        assert!(!features.visible);

        let value = Features {
            enabled: true,
            visible: false,
        };
        let len = FEATURES_FMT().prepare(&value).unwrap();
        let mut output = vec![0; len];
        FEATURES_FMT().serialize(&value, output.as_mut_slice());
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
        let (_, envelope) = CHOICE_ENVELOPE_FMT().parse(&input).unwrap();
        assert!(matches!(envelope.selection, Some(Selection::Flag(true))));
    }

    #[test]
    fn enumerated_is_closed_and_round_trips_nominally() {
        let encoded = [0x0a, 0x01, 0x01];
        let (_, color) = COLOR_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(color, Color::Green);

        let mut output = vec![0; COLOR_FMT().prepare(&color).unwrap()];
        COLOR_FMT().serialize(&color, output.as_mut_slice());
        assert_eq!(output, encoded);

        let unknown = [0x0a, 0x01, 0x05];
        assert!(COLOR_FMT().parse(&unknown.as_slice()).is_err());
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
        let (_, identifier) = IDENTIFIER_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(identifier.first(), 2);
        assert_eq!(identifier.second(), 999);
        assert_eq!(identifier.rest(), &[3]);

        let mut output = vec![0; IDENTIFIER_FMT().prepare(&identifier).unwrap()];
        IDENTIFIER_FMT().serialize(&identifier, output.as_mut_slice());
        assert_eq!(output, encoded);
    }

    #[test]
    fn real_and_any_backends_are_emitted() {
        let real_zero = [0x09, 0x00];
        let (_, real) = MEASUREMENT_FMT().parse(&real_zero.as_slice()).unwrap();
        assert!(real.contents().is_empty());

        let any_boolean = [0x01, 0x01, 0xff];
        let (_, value) = OPEN_VALUE_FMT().parse(&any_boolean.as_slice()).unwrap();
        assert_eq!(value.tag(), TagFmt::BOOLEAN);
        assert_eq!(value.content(), &[0xff]);
    }

    #[test]
    fn bmp_string_codegen_uses_owned_values_and_ucs2_octets() {
        let encoded = [0x30, 0x04, 0x1e, 0x02, 0x00, 0x41];
        let (_, value) = BMP_CONTAINER_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(value.name.inner(), "A");
        assert_eq!(BMP_NAME_FMT().prepare(&value.name).unwrap(), 4);

        let mut output = vec![0; BMP_NAME_FMT().prepare(&value.name).unwrap()];
        BMP_NAME_FMT().serialize(&value.name, output.as_mut_slice());
        assert_eq!(output, encoded[2..]);
    }

    #[test]
    fn inline_composites_receive_nominal_helper_types() {
        let encoded = [
            0x30, 0x08, // InlineRecord
            0x30, 0x03, 0x04, 0x01, 0xaa, // nested SEQUENCE
            0x82, 0x01, 0xff, // selected.flag
        ];
        let (_, record) = INLINE_RECORD_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(record.nested.payload, &[0xaa]);
        assert!(matches!(record.selected, InlineRecordSelected::Flag(true)));

        let mut output = vec![0; INLINE_RECORD_FMT().prepare(&record).unwrap()];
        INLINE_RECORD_FMT().serialize(&record, output.as_mut_slice());
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
        let (consumed, item) = ber::ITEM_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(consumed, encoded.len());
        assert_eq!(item.payload, [0xaa, 0xbb, 0xcc]);
        assert_eq!(item.bits.unused(), 4);
        assert_eq!(item.bits.bits(), &[0xf0, 0xa0]);
        assert_eq!(item.label, "hi!");
        assert!(item.printable.is_none());
        assert!(item.open.is_none());

        let mut payload = vec![0; ber::PAYLOAD_FMT().prepare(&item.payload).unwrap()];
        ber::PAYLOAD_FMT().serialize(&item.payload, payload.as_mut_slice());
        assert_eq!(payload, [0x04, 0x03, 0xaa, 0xbb, 0xcc]);

        let mut bits = vec![0; ber::BITS_FMT().prepare(&item.bits).unwrap()];
        ber::BITS_FMT().serialize(&item.bits, bits.as_mut_slice());
        assert_eq!(bits, [0x03, 0x03, 0x04, 0xf0, 0xa0]);

        let mut label = vec![0; ber::LABEL_FMT().prepare(&item.label).unwrap()];
        ber::LABEL_FMT().serialize(&item.label, label.as_mut_slice());
        assert_eq!(label, [0x0c, 0x03, b'h', b'i', b'!']);

        let mut item_output = vec![0; ber::ITEM_FMT().prepare(&item).unwrap()];
        ber::ITEM_FMT().serialize(&item, item_output.as_mut_slice());
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
        let (_, flags) = ber::FLAGS_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(flags, [true, false]);

        let mut output = vec![0; ber::FLAGS_FMT().prepare(&flags).unwrap()];
        ber::FLAGS_FMT().serialize(&flags, output.as_mut_slice());
        assert_eq!(output, [0x30, 0x06, 0x01, 0x01, 0xff, 0x01, 0x01, 0x00]);
    }

    #[test]
    fn ber_generated_any_preserves_indefinite_contents_then_serializes_definite() {
        use super::generated_ber as ber;

        let encoded = [0x30, 0x80, 0x01, 0x01, 0xff, 0x04, 0x01, 0xaa, 0x00, 0x00];
        let (_, value) = ber::OPEN_VALUE_FMT().parse(&encoded.as_slice()).unwrap();
        assert_eq!(value.tag(), TagFmt::SEQUENCE);
        assert_eq!(value.content(), &[0x01, 0x01, 0xff, 0x04, 0x01, 0xaa]);

        let mut output = vec![0; ber::OPEN_VALUE_FMT().prepare(&value).unwrap()];
        ber::OPEN_VALUE_FMT().serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x30, 0x06, 0x01, 0x01, 0xff, 0x04, 0x01, 0xaa]);

        let nested = [
            0x30, 0x80, // outer SEQUENCE
            0x31, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00, // inner SET, including EOC
            0x00, 0x00,
        ];
        let (_, value) = ber::OPEN_VALUE_FMT().parse(&nested.as_slice()).unwrap();
        assert_eq!(value.content(), &[0x31, 0x80, 0x01, 0x01, 0xff, 0x00, 0x00]);

        let primitive_indefinite = [0x04, 0x80, 0x04, 0x01, 0xaa, 0x00, 0x00];
        assert!(ber::OPEN_VALUE_FMT()
            .parse(&primitive_indefinite.as_slice())
            .is_err());
    }
}
