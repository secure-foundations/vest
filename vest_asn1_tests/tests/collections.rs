#![cfg(feature = "fixtures")]

use vest_asn1_tests::{
    generated_sized_sequence_of_ber as seq_ber, generated_sized_sequence_of_der as seq_der,
    generated_sized_set_of_ber as set_ber, generated_sized_set_of_der as set_der,
};
use vest_lib::asn1::Integer;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

#[test]
fn der_sized_sequence_of_roundtrips_and_checks_size() {
    let encoded = [0x30, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01];
    let (consumed, mut value) = seq_der::CONTAINER::Fmt.parse(&encoded.as_slice()).unwrap();
    assert_eq!(consumed, encoded.len());
    assert!(value.marker.is_none());
    assert_eq!(value.items.len(), 1);
    assert_eq!(value.items[0].as_i64(), Some(1));

    let mut output = vec![0; seq_der::CONTAINER::Fmt.prepare(&value).unwrap()];
    seq_der::CONTAINER::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, encoded);

    value.items.push(Integer::Small { v: 2 });
    assert!(seq_der::CONTAINER::Fmt.prepare(&value).is_err());
    value.items.clear();
    assert!(seq_der::CONTAINER::Fmt.prepare(&value).is_err());
    let empty = [0x30, 0x02, 0x30, 0x00];
    assert!(seq_der::CONTAINER::Fmt.parse(&empty.as_slice()).is_err());
    // INTEGER is the element's tag, not a substitute for the SEQUENCE OF tag.
    let wrong_tag = [0x30, 0x03, 0x02, 0x01, 0x01];
    assert!(seq_der::CONTAINER::Fmt
        .parse(&wrong_tag.as_slice())
        .is_err());
}

#[test]
fn der_sized_set_of_roundtrips_and_checks_its_own_tag() {
    let encoded = [0x30, 0x07, 0x31, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01];
    let (consumed, mut value) = set_der::CONTAINER::Fmt.parse(&encoded.as_slice()).unwrap();
    assert_eq!(consumed, encoded.len());
    assert!(value.marker.is_none());
    assert_eq!(value.items.len(), 1);
    assert_eq!(value.items[0].value.as_i64(), Some(1));

    let mut output = vec![0; set_der::CONTAINER::Fmt.prepare(&value).unwrap()];
    set_der::CONTAINER::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, encoded);

    // These elements are in DER order, but the SIZE (1) constraint rejects them.
    value.items.push(set_der::Element {
        value: Integer::Small { v: 2 },
    });
    assert!(set_der::CONTAINER::Fmt.prepare(&value).is_err());
    value.items.clear();
    assert!(set_der::CONTAINER::Fmt.prepare(&value).is_err());

    // The element's SEQUENCE tag cannot replace the SET OF tag.
    let wrong_tag = [0x30, 0x07, 0x30, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01];
    assert!(set_der::CONTAINER::Fmt
        .parse(&wrong_tag.as_slice())
        .is_err());
}

#[test]
fn ber_sized_sequence_of_accepts_indefinite_and_normalizes_to_definite() {
    let encoded = [
        0x30, 0x80, // Container
        0x30, 0x80, // SEQUENCE OF
        0x02, 0x01, 0x01, // INTEGER 1
        0x00, 0x00, // SEQUENCE OF EOC
        0x00, 0x00, // Container EOC
    ];
    let (consumed, value) = seq_ber::CONTAINER::Fmt.parse(&encoded.as_slice()).unwrap();
    assert_eq!(consumed, encoded.len());
    assert!(value.marker.is_none());
    assert_eq!(value.items.len(), 1);
    assert_eq!(value.items[0].as_i64(), Some(1));

    let mut output = vec![0; seq_ber::CONTAINER::Fmt.prepare(&value).unwrap()];
    seq_ber::CONTAINER::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, [0x30, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01]);

    let empty = [0x30, 0x80, 0x30, 0x80, 0x00, 0x00, 0x00, 0x00];
    assert!(seq_ber::CONTAINER::Fmt.parse(&empty.as_slice()).is_err());
}

#[test]
fn ber_sized_set_of_accepts_nested_indefinite_containers() {
    let encoded = [
        0x30, 0x80, // Container
        0x31, 0x80, // SET OF
        0x30, 0x80, // Element
        0x02, 0x01, 0x01, // INTEGER 1
        0x00, 0x00, // Element EOC
        0x00, 0x00, // SET OF EOC
        0x00, 0x00, // Container EOC
    ];
    let (consumed, value) = set_ber::CONTAINER::Fmt.parse(&encoded.as_slice()).unwrap();
    assert_eq!(consumed, encoded.len());
    assert_eq!(value.items.len(), 1);
    assert_eq!(value.items[0].value.as_i64(), Some(1));

    let mut output = vec![0; set_ber::CONTAINER::Fmt.prepare(&value).unwrap()];
    set_ber::CONTAINER::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(
        output,
        [0x30, 0x07, 0x31, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01]
    );
}

#[test]
fn nested_sized_collections_keep_both_envelopes() {
    let encoded = [0x30, 0x07, 0x30, 0x05, 0x31, 0x03, 0x02, 0x01, 0x01];
    let (consumed, value) = set_der::NESTED_COLLECTIONS::Fmt
        .parse(&encoded.as_slice())
        .unwrap();
    assert_eq!(consumed, encoded.len());
    assert_eq!(value.items.len(), 1);
    assert_eq!(value.items[0].len(), 1);
    assert_eq!(value.items[0][0].as_i64(), Some(1));
    let mut output = vec![0; set_der::NESTED_COLLECTIONS::Fmt.prepare(&value).unwrap()];
    set_der::NESTED_COLLECTIONS::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, encoded);

    let (consumed, value) = set_ber::NESTED_COLLECTIONS::Fmt
        .parse(&encoded.as_slice())
        .unwrap();
    assert_eq!(consumed, encoded.len());
    assert_eq!(value.items[0][0].as_i64(), Some(1));
}

#[test]
fn optional_and_choice_collections_use_collection_start_domains() {
    let empty = [0x30, 0x00];
    let (_, value) = seq_der::OPTIONAL_COLLECTION::Fmt
        .parse(&empty.as_slice())
        .unwrap();
    assert!(value.items.is_none());
    let (_, value) = seq_ber::OPTIONAL_COLLECTION::Fmt
        .parse(&empty.as_slice())
        .unwrap();
    assert!(value.items.is_none());

    let selected = [0x30, 0x03, 0x02, 0x01, 0x01];
    let (consumed, value) = seq_der::COLLECTION_CHOICE::Fmt
        .parse(&selected.as_slice())
        .unwrap();
    assert_eq!(consumed, selected.len());
    assert!(matches!(value, seq_der::CollectionChoice::Items(_)));
    let (consumed, value) = seq_ber::COLLECTION_CHOICE::Fmt
        .parse(&selected.as_slice())
        .unwrap();
    assert_eq!(consumed, selected.len());
    assert!(matches!(value, seq_ber::CollectionChoice::Items(_)));
}

#[test]
fn zero_sized_collection_still_has_a_tlv_envelope() {
    let encoded = [0x30, 0x02, 0x30, 0x00];
    let (_, value) = seq_der::EMPTY_COLLECTION::Fmt
        .parse(&encoded.as_slice())
        .unwrap();
    assert!(value.items.is_empty());
    let mut output = vec![0; seq_der::EMPTY_COLLECTION::Fmt.prepare(&value).unwrap()];
    seq_der::EMPTY_COLLECTION::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, encoded);

    let (_, value) = seq_ber::EMPTY_COLLECTION::Fmt
        .parse(&encoded.as_slice())
        .unwrap();
    assert!(value.items.is_empty());
    let mut output = vec![0; seq_ber::EMPTY_COLLECTION::Fmt.prepare(&value).unwrap()];
    seq_ber::EMPTY_COLLECTION::Fmt.serialize(&value, output.as_mut_slice());
    assert_eq!(output, encoded);
}

#[test]
fn collection_certificates_do_not_prevent_implicit_retagging() {
    let der = vest_lib::asn1::der::IMPLICIT(3, seq_der::CONTAINER::Fmt);
    let canonical = [0xa3, 0x05, 0x30, 0x03, 0x02, 0x01, 0x01];
    let (consumed, value) = der.parse(&canonical.as_slice()).unwrap();
    assert_eq!(consumed, canonical.len());
    assert_eq!(value.items[0].as_i64(), Some(1));
    let mut output = vec![0; der.prepare(&value).unwrap()];
    der.serialize(&value, output.as_mut_slice());
    assert_eq!(output, canonical);

    let ber = vest_lib::asn1::ber::IMPLICIT(3, seq_ber::CONTAINER::Fmt);
    let indefinite = [
        0xa3, 0x80, 0x30, 0x80, 0x02, 0x01, 0x01, 0x00, 0x00, 0x00, 0x00,
    ];
    let (consumed, value) = ber.parse(&indefinite.as_slice()).unwrap();
    assert_eq!(consumed, indefinite.len());
    assert_eq!(value.items[0].as_i64(), Some(1));
    let mut output = vec![0; ber.prepare(&value).unwrap()];
    ber.serialize(&value, output.as_mut_slice());
    assert_eq!(output, canonical);
}
