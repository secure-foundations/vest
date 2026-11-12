use ciborium::value::Value;
use std::borrow::Cow;
use vest_bench::real::cbor::*;
use vest_lib::core::exec::Parser;

#[test]
fn cbor_checks_reject_trailing_input() {
    assert_eq!(ciborium_exact(&[0x01]), Value::Integer(1.into()));
    assert!(std::panic::catch_unwind(|| ciborium_exact(&[0x01, 0x02])).is_err());
    assert_eq!(cbor4ii::parse(&[0x01]).unwrap(), BorrowedValue::Integer(1));
    assert_eq!(minicbor::parse(&[0x01]).unwrap(), BorrowedValue::Integer(1));
    assert!(cbor4ii::parse(&[0x01, 0x02]).is_err());
    assert!(minicbor::parse(&[0x01, 0x02]).is_err());
}

#[test]
fn cbor4ii_consumes_fragment_breaks_without_losing_siblings_or_map_values() {
    // Regressions from upstream issue 60, including a top-level empty string.
    let inputs: &[&[u8]] = &[
        &[0x5f, 0xff],
        &[0x9f, 0x7f, 0xff, 0x61, 0x61, 0xff],
        &[0x82, 0x7f, 0xff, 0x61, 0x61],
        &[0xa1, 0x7f, 0x61, 0x6b, 0xff, 0x01],
        &[0x9f, 0x5f, 0x41, 0x01, 0xff, 0x41, 0x02, 0xff],
    ];
    for bytes in inputs {
        let value = cbor4ii::parse(bytes).unwrap();
        assert_eq!(value.semantic_value(), ciborium_exact(bytes));
        assert_eq!(value, minicbor::parse(bytes).unwrap());
    }
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
fn vest_counted_collections_preserve_validation_and_consumption() {
    let format = vest_lib::cbor::CborFmt::<false>;
    let expected = [
        Value::Array(vec![Value::Integer(1.into()), Value::Integer(2.into())]),
        Value::Map(vec![(Value::Integer(1.into()), Value::Integer(2.into()))]),
    ];
    for (input, expected) in [vec![0x82, 1, 2, 0x63], vec![0xa1, 1, 2, 0x63]]
        .iter()
        .zip(expected)
    {
        let (consumed, value) = format.parse(&input.as_slice()).unwrap();
        assert_eq!(consumed, 3);
        assert_eq!(semantic_value(&value), expected);
    }
    for input in [&[0x81][..], &[0x82, 1][..], &[0xa1, 1][..], &[0x81, 0xff][..]] {
        assert!(format.parse(&input).is_err());
        assert!(vest_lib::cbor::CborFmt::<true>.parse(&input).is_err());
    }
}

#[test]
fn native_adapters_preserve_tags_and_reject_trailing_input() {
    let bytes = [0xd2, 0x82, 0x01, 0x42, 0xab, 0xcd];
    for value in [
        cbor4ii::parse(&bytes).unwrap(),
        minicbor::parse(&bytes).unwrap(),
    ] {
        assert_eq!(value.semantic_value(), ciborium_exact(&bytes));
        assert_eq!(cbor4ii::encode(&value), bytes);
        assert_eq!(minicbor::encode(&value), bytes);
    }
    assert!(cbor4ii::parse(&[0xd2, 0x01, 0x02]).is_err());
    assert!(minicbor::parse(&[0xd2, 0x01, 0x02]).is_err());
}

#[test]
fn definite_strings_and_map_keys_borrow_the_input() {
    // ["abc", {"k": h'78797a'}]
    let bytes = vec![
        0x82, 0x63, b'a', b'b', b'c', 0xa1, 0x61, b'k', 0x43, b'x', b'y', b'z',
    ];
    for value in [
        cbor4ii::parse(&bytes).unwrap(),
        minicbor::parse(&bytes).unwrap(),
    ] {
        let BorrowedValue::Array(values) = value else {
            panic!("not an array")
        };
        let BorrowedValue::Text(Cow::Borrowed(text)) = &values[0] else {
            panic!("text copied")
        };
        assert_eq!(text.as_ptr(), bytes[2..].as_ptr());
        let BorrowedValue::Map(entries) = &values[1] else {
            panic!("not a map")
        };
        let BorrowedValue::Text(Cow::Borrowed(key)) = &entries[0].0 else {
            panic!("key copied")
        };
        let BorrowedValue::Bytes(Cow::Borrowed(payload)) = &entries[0].1 else {
            panic!("bytes copied")
        };
        assert_eq!(key.as_ptr(), bytes[7..].as_ptr());
        assert_eq!(payload.as_ptr(), bytes[9..].as_ptr());
    }
}

#[test]
fn minicbor_flattens_fragmented_strings_and_normalizes_framing() {
    // [_ (_ "a", "b"), (_ h'78', h'79')]
    let bytes = [
        0x9f, 0x7f, 0x61, b'a', 0x61, b'b', 0xff, 0x5f, 0x41, b'x', 0x41, b'y', 0xff, 0xff,
    ];
    let value = minicbor::parse(&bytes).unwrap();
    assert_eq!(
        value,
        BorrowedValue::Array(vec![
            BorrowedValue::Text(Cow::Owned("ab".to_owned())),
            BorrowedValue::Bytes(Cow::Owned(b"xy".to_vec())),
        ])
    );
    let normalized = [0x82, 0x62, b'a', b'b', 0x42, b'x', b'y'];
    assert_eq!(minicbor::encode(&value), normalized);
    assert_eq!(cbor4ii::encode(&value), normalized);
}

#[test]
fn native_adapters_preserve_map_order_and_duplicate_entries() {
    let bytes = [0xa3, 0x02, 0x03, 0x01, 0x04, 0x02, 0x05];
    let expected = BorrowedValue::Map(vec![
        (BorrowedValue::Integer(2), BorrowedValue::Integer(3)),
        (BorrowedValue::Integer(1), BorrowedValue::Integer(4)),
        (BorrowedValue::Integer(2), BorrowedValue::Integer(5)),
    ]);
    for value in [
        cbor4ii::parse(&bytes).unwrap(),
        minicbor::parse(&bytes).unwrap(),
    ] {
        assert_eq!(value, expected);
        assert_eq!(cbor4ii::encode(&value), bytes);
        assert_eq!(minicbor::encode(&value), bytes);
    }
}

#[test]
fn native_ast_decoders_do_not_substitute_raw_capture_or_tokenization() {
    let malformed: &[&[u8]] = &[
        &[],
        &[0xff],                   // standalone break
        &[0x61, 0xff],             // invalid UTF-8
        &[0x5f, 0x01, 0xff],       // wrong byte-string chunk type
        &[0x7f, 0x41, 0x61, 0xff], // wrong text-string chunk type
        &[0x82, 0x01],             // incomplete array
        &[0xbf, 0x01, 0xff],       // map key without a value
        &[0xa1, 0x01],             // incomplete definite map
        &[0xc1],                   // missing tagged value
        &[0xf8, 0x00],             // two-byte simple values must be >= 32
        &[0xf8, 0x14],             // not an alternate encoding of false
        &[0xf8, 0x1f],             // reserved simple value
    ];
    for bytes in malformed {
        assert!(
            cbor4ii::parse(bytes).is_err(),
            "cbor4ii accepted {bytes:02x?}"
        );
        assert!(
            minicbor::parse(bytes).is_err(),
            "minicbor accepted {bytes:02x?}"
        );
    }
    let mut too_deep = vec![0x81; 300];
    too_deep.push(0x00);
    assert!(cbor4ii::parse(&too_deep).is_err());
    assert!(minicbor::parse(&too_deep).is_err());
}

#[test]
fn native_ast_decoders_cover_integer_extremes_and_scalar_types() {
    let inputs: &[&[u8]] = &[
        &[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
        &[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
        &[0xf4],
        &[0xf5],
        &[0xf6],
        &[0xf7],
        &[0xe0],
        &[0xf8, 0x20],
        &[0xf9, 0x3c, 0x00],                   // binary16 1.0
        &[0xfa, 0x3f, 0x80, 0x00, 0x00],       // binary32 1.0
        &[0xfb, 0x3f, 0xf0, 0, 0, 0, 0, 0, 0], // binary64 1.0
    ];
    for bytes in inputs {
        let first = cbor4ii::parse(bytes).unwrap();
        let second = minicbor::parse(bytes).unwrap();
        assert_eq!(first, second);
        assert_eq!(cbor4ii::encode(&first), minicbor::encode(&second));
    }
}

#[test]
fn native_ast_adapters_validate_every_benchmark_input_and_output() {
    let values = synthetic_values();
    let inputs = values.iter().map(malleable).collect::<Vec<_>>();
    validated_values(&values, &inputs);

    let inputs = cose_inputs();
    let values = inputs
        .iter()
        .map(|bytes| ciborium_exact(bytes))
        .collect::<Vec<_>>();
    validated_values(&values, &inputs);
}
