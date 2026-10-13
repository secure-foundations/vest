use ciborium::value::Value;
use vest_bench::real::cbor::*;
use vest_lib::core::exec::Parser;
#[test]
fn cbor_checks_reject_trailing_input() {
    for decode in [ciborium_exact, cbor4ii_exact, minicbor_exact] {
        assert_eq!(decode(&[0x01]), Value::Integer(1.into()));
        assert!(std::panic::catch_unwind(|| decode(&[0x01, 0x02])).is_err());
    }
}

#[test]
fn cbor4ii_fragmented_strings_do_not_qualify_as_complete_parses() {
    // A complete, empty indefinite byte string. The current baseline leaves
    // its break unread, so this workload must not receive a cbor4ii timing.
    assert!(std::panic::catch_unwind(|| cbor4ii_exact(&[0x5f, 0xff])).is_err());
}

#[test]
fn cbor_projection_checks_values_not_just_consumption() {
    let bytes = &[0x5f, 0x42, 1, 2, 0x41, 3, 0xff][..];
    let (n, value) = vest_lib::cbor::CborFmt::<false>.parse(&bytes).unwrap();
    assert_eq!(n, bytes.len());
    assert_eq!(semantic_value(&value), Value::Bytes(vec![1, 2, 3]));
    assert_ne!(semantic_value(&value), Value::Bytes(vec![1, 2, 4]));
}

#[test]
fn native_cbor4ii_preserves_tags_and_rejects_trailing_input() {
    let bytes = [0xd2, 0x82, 0x01, 0x42, 0xab, 0xcd];
    let value = cbor4ii_parse(&bytes);
    assert_eq!(cbor4ii_semantic_value(&value), ciborium_exact(&bytes));
    assert_eq!(cbor4ii_encode(&value), bytes);
    assert_eq!(cbor4ii_value(&ciborium_exact(&bytes)), value);
    assert!(std::panic::catch_unwind(|| cbor4ii_exact(&[0xd2, 0x01, 0x02])).is_err());
}
