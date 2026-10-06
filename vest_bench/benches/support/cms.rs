//! Untimed normalization and full-consumption checks for CMS comparisons.

use bcder::encode::PrimitiveContent;
use der::{Decode, Encode};

/// The crate's ContentInfo encoder omits the [0] EXPLICIT wrapper. Build the
/// specified envelope with bcder's public combinators instead; the added work
/// is included in serialization timing, not hidden in setup.
pub fn bcder_content_info(
    value: &cryptographic_message_syntax::asn1::rfc5652::ContentInfo,
) -> impl bcder::encode::Values + '_ {
    bcder::encode::sequence((
        value.content_type.encode_ref(),
        bcder::encode::sequence_as(bcder::Tag::CTX_0, &value.content),
    ))
}

pub fn rasn_exact<T: rasn::Decode>(input: &[u8]) -> T {
    let (value, remaining) = rasn::ber::decode_with_remainder(input).unwrap();
    assert!(remaining.is_empty(), "rasn left trailing CMS input");
    value
}

/// A common encoding for serializer inputs, not a signature-validity oracle.
///
/// rasn flattens eContent and sorts SET OF; RustCrypto additionally chooses
/// UTCTime for applicable certificate dates. Both transformations are outside
/// timing. Opaque ANY contents are not claimed to be recursively canonical DER.
/// Original BER messages remain the inputs to the parsing benchmark.
pub fn normalized_signed_data(input: &[u8]) -> Vec<u8> {
    let value: rasn_cms::SignedData = rasn_exact(input);
    let sorted = rasn::der::encode(&value).unwrap();
    let value = rustcrypto_cms::signed_data::SignedData::from_ber(&sorted).unwrap();
    let common = value.to_der().unwrap();
    // Do not silently select a subset or accept a library-dependent encoding.
    let value: rasn_cms::SignedData = rasn_exact(&common);
    assert_eq!(rasn::der::encode(&value).unwrap(), common);
    common
}
