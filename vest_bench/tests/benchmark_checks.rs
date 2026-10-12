//! Regression tests for untimed benchmark validation and input ownership.

#[path = "../benches/shared/cbor.rs"]
mod cbor;
#[path = "../benches/shared/cms.rs"]
#[allow(dead_code)]
mod cms;
#[path = "../benches/shared/timing.rs"]
#[allow(dead_code)]
mod harness;
#[path = "../benches/shared/tls.rs"]
mod tls;

use ciborium::value::Value;
use der::{Decode, Encode};
use rustls::internal::msgs::{base::Payload, codec::Codec};
use vest_lib::core::exec::Parser;
use vest_lib::core::exec::{Prepare, SerializerExt};

#[test]
fn tls_parse_retains_the_original_input_allocation() {
    for input in vest_bench::corpora::tls_handshakes() {
        let mut payload = Payload::new(input.bytes.clone());
        let pointer = payload.0.as_ptr();
        for _ in 0..2 {
            let parsed = tls::parse(&mut payload);
            assert_eq!(payload.0.as_ptr(), pointer);
            assert_eq!(payload.0, input.bytes);
            let mut encoded = Vec::new();
            parsed.encode(&mut encoded);
            assert_eq!(encoded, input.bytes);
        }
    }
}

#[test]
fn cbor_checks_reject_trailing_input() {
    for decode in [
        cbor::ciborium_exact,
        cbor::cbor4ii_exact,
        cbor::minicbor_exact,
    ] {
        assert_eq!(decode(&[0x01]), Value::Integer(1.into()));
        assert!(std::panic::catch_unwind(|| decode(&[0x01, 0x02])).is_err());
    }
}

#[test]
fn cbor4ii_fragmented_strings_do_not_qualify_as_complete_parses() {
    // A complete, empty indefinite byte string. The current baseline leaves
    // its break unread, so this workload must not receive a cbor4ii timing.
    assert!(std::panic::catch_unwind(|| cbor::cbor4ii_exact(&[0x5f, 0xff])).is_err());
}

#[test]
fn cbor_projection_checks_values_not_just_consumption() {
    let bytes = &[0x5f, 0x42, 1, 2, 0x41, 3, 0xff][..];
    let (n, value) = vest_lib::cbor::CborFmt::<false>.parse(&bytes).unwrap();
    assert_eq!(n, bytes.len());
    assert_eq!(cbor::semantic_value(&value), Value::Bytes(vec![1, 2, 3]));
    assert_ne!(cbor::semantic_value(&value), Value::Bytes(vec![1, 2, 4]));
}

#[test]
fn retained_results_survive_the_whole_timed_pass() {
    use std::cell::Cell;
    struct Dropped<'a>(&'a Cell<usize>);
    impl Drop for Dropped<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Cell::new(0);
    let mut outputs = Vec::with_capacity(3);
    harness::fill(&mut outputs, 3, &mut |_| {
        assert_eq!(drops.get(), 0, "a previous result dropped inside the pass");
        Dropped(&drops)
    });
    assert_eq!(drops.get(), 0);
    drop(outputs);
    assert_eq!(drops.get(), 3);
}

#[test]
fn native_cbor4ii_preserves_tags_and_rejects_trailing_input() {
    let bytes = [0xd2, 0x82, 0x01, 0x42, 0xab, 0xcd];
    let value = cbor::cbor4ii_parse(&bytes);
    assert_eq!(
        cbor::cbor4ii_semantic_value(&value),
        cbor::ciborium_exact(&bytes)
    );
    assert_eq!(cbor::cbor4ii_encode(&value), bytes);
    assert_eq!(cbor::cbor4ii_value(&cbor::ciborium_exact(&bytes)), value);
    assert!(std::panic::catch_unwind(|| cbor::cbor4ii_exact(&[0xd2, 0x01, 0x02])).is_err());
}

#[test]
fn cms_normalization_is_shared_and_idempotent() {
    for name in [
        "pkits/041270873da77b43.cms", // GeneralizedTime -> UTCTime
        "pkits/86e59bbb660905d7.cms",
        "dss/91b3289e675755c4.cms", // fragmented OCTET STRING
        "dss/aa310d5544f6af4e.cms",
        "dss/b580f27686e54201.cms",
    ] {
        let file =
            std::fs::read(vest_bench::corpora::corpora_dir().join("cms").join(name)).unwrap();
        let envelope = rustcrypto_cms::content_info::ContentInfo::from_ber(&file).unwrap();
        let original = envelope.content.to_der().unwrap();
        let common = cms::normalized_signed_data(&original);
        assert_eq!(cms::normalized_signed_data(&common), common);
        let format = vest_asn1_tests::generated_cms::SIGNED_DATA::Fmt;
        let (n, value) = format.parse(&common.as_slice()).unwrap();
        assert_eq!(n, common.len());
        let mut encoded = vec![0; format.prepare(&value).unwrap()];
        format.serialize(&value, &mut encoded);
        assert_eq!(encoded, common);
    }
}

#[test]
fn cms_repetitions_do_not_reserve_one_large_value_per_input_byte() {
    let format = vest_asn1_tests::generated_cms::SIGNED_DATA::Fmt;
    assert!(<_ as Parser<&[u8]>>::min_byte_len(&format) > 0);
    for name in ["pkits/86e59bbb660905d7.cms", "dss/91b3289e675755c4.cms"] {
        let file =
            std::fs::read(vest_bench::corpora::corpora_dir().join("cms").join(name)).unwrap();
        let input = cms::signed_data(&file).unwrap();
        let (n, value) = format.parse(&input).unwrap();
        assert_eq!(n, input.len());
        let certificates = value.certificates.as_ref().unwrap();
        assert!(
            certificates.capacity() <= 32,
            "{}: capacity {}",
            name,
            certificates.capacity()
        );
        assert!(value.signer_infos.capacity() <= 64);
    }
}

#[test]
fn bcder_content_info_keeps_the_explicit_wrapper() {
    use bcder::{decode::Constructed, encode::Values, Mode};
    let input = [
        0x30, 0x0f, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x01, 0xa0, 0x02,
        0x04, 0x00,
    ];
    let value = Constructed::decode(&input[..], Mode::Der, |c| {
        c.take_sequence(cryptographic_message_syntax::asn1::rfc5652::ContentInfo::from_sequence)
    })
    .unwrap();
    assert_eq!(
        cms::bcder_content_info(&value)
            .to_captured(Mode::Der)
            .as_slice(),
        &input
    );
}
