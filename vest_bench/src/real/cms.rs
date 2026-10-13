//! Shared CMS inputs, baseline adapters, and untimed correctness checks.

use bcder::{
    decode::Constructed,
    encode::{PrimitiveContent, Values},
    Mode,
};
use der::{Decode, Encode};
use std::fs;
use vest_asn1_tests::generated_cms;
use vest_lib::core::exec::{Prepare, SerializerExt};

pub const CONTENT_INFO: generated_cms::CONTENT_INFO = generated_cms::CONTENT_INFO::Fmt;
pub const SIGNED_DATA: generated_cms::SIGNED_DATA = generated_cms::SIGNED_DATA::Fmt;

fn der_len(len: usize) -> Vec<u8> {
    if len < 128 {
        vec![len as u8]
    } else {
        let bytes = len.to_be_bytes();
        let first = bytes.iter().position(|byte| *byte != 0).unwrap();
        let mut out = vec![0x80 | (bytes.len() - first) as u8];
        out.extend_from_slice(&bytes[first..]);
        out
    }
}

fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    out.extend_from_slice(&der_len(body.len()));
    out.extend_from_slice(body);
    out
}

pub fn synthetic_content_info() -> Vec<Vec<u8>> {
    (0..1024usize)
        .map(|seed| {
            let payload: Vec<_> = (0..seed % 512)
                .map(|i| (seed.wrapping_mul(29) ^ i.wrapping_mul(17)) as u8)
                .collect();
            let mut body = vec![
                0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x07, 0x01,
            ];
            body.extend_from_slice(&tlv(0xa0, &tlv(0x04, &payload)));
            tlv(0x30, &body)
        })
        .collect()
}

#[inline]
pub fn parse_bcder(input: &[u8]) -> cryptographic_message_syntax::asn1::rfc5652::ContentInfo {
    Constructed::decode(input, Mode::Der, |cons| {
        cons.take_sequence(cryptographic_message_syntax::asn1::rfc5652::ContentInfo::from_sequence)
    })
    .unwrap()
}

fn header(input: &[u8], offset: usize) -> Option<(usize, Option<usize>)> {
    let mut pos = offset + 1;
    if input.get(offset)? & 31 == 31 {
        while input.get(pos)? & 0x80 != 0 {
            pos += 1;
        }
        pos += 1;
    }
    let first = *input.get(pos)?;
    pos += 1;
    if first == 0x80 {
        return Some((pos, None));
    }
    if first & 0x80 == 0 {
        return Some((pos, Some(first as usize)));
    }
    let count = (first & 0x7f) as usize;
    let mut len = 0usize;
    for byte in input.get(pos..pos + count)? {
        len = (len << 8) | *byte as usize;
    }
    Some((pos + count, Some(len)))
}

fn tlv_end(input: &[u8], offset: usize) -> Option<usize> {
    let (start, len) = header(input, offset)?;
    if let Some(len) = len {
        return start.checked_add(len).filter(|end| *end <= input.len());
    }
    let mut pos = start;
    loop {
        if input.get(pos..pos + 2)? == [0, 0] {
            return Some(pos + 2);
        }
        pos = tlv_end(input, pos)?;
    }
}

pub fn signed_data(input: &[u8]) -> Option<&[u8]> {
    let (outer, _) = header(input, 0)?;
    let explicit = tlv_end(input, outer)?;
    let (inner, _) = header(input, explicit)?;
    let end = tlv_end(input, inner)?;
    input.get(inner..end)
}

/// Raw eContent value bytes, including chunk TLVs for constructed strings.
/// RustCrypto's ANY preserves these bytes rather than decoding OCTET STRING.
pub fn econtent_body(input: &[u8]) -> Option<&[u8]> {
    let (version, _) = header(input, 0)?;
    let algorithms = tlv_end(input, version)?;
    let encap = tlv_end(input, algorithms)?;
    let (oid, len) = header(input, encap)?;
    let explicit = tlv_end(input, oid)?;
    if len.is_some_and(|len| explicit == oid + len) || input.get(explicit..explicit + 2)? == [0, 0]
    {
        return None;
    }
    assert_eq!(input[explicit], 0xa0);
    let (octets, _) = header(input, explicit)?;
    assert!(matches!(input[octets], 0x04 | 0x24));
    let (body, len) = header(input, octets)?;
    let end = len.map_or_else(
        || tlv_end(input, octets).map(|end| end - 2),
        |len| Some(body + len),
    )?;
    input.get(body..end)
}

fn visit_cms(dir: &std::path::Path, inputs: &mut Vec<Vec<u8>>) {
    for path in super::files(dir, "cms") {
        let file = fs::read(&path).unwrap();
        let end = tlv_end(&file, 0).expect("complete CMS envelope");
        // Some DSS files have zero padding after the envelope. This
        // benchmark measures its SignedData, not the enclosing file.
        assert!(
            file[end..].iter().all(|byte| *byte == 0),
            "{}: non-padding bytes after CMS envelope",
            path.display()
        );
        let envelope = rustcrypto_cms::content_info::ContentInfo::from_ber(&file[..end])
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert_eq!(envelope.content_type.to_string(), "1.2.840.113549.1.7.2");
        let value = signed_data(&file[..end]).expect("extract SignedData from CMS envelope");
        rustcrypto_cms::signed_data::SignedData::from_ber(value).unwrap();
        inputs.push(value.to_vec());
    }
}

pub fn real_signed_data() -> Vec<Vec<u8>> {
    let root = super::corpora_dir().join("cms");
    let mut inputs = Vec::new();
    visit_cms(&root.join("pkits"), &mut inputs);
    visit_cms(&root.join("dss"), &mut inputs);
    visit_cms(&root.join("rfc4134"), &mut inputs);
    inputs
}

/// The crate's ContentInfo encoder omits the [0] EXPLICIT wrapper. Build the
/// specified envelope with bcder's public combinators instead; the added work
/// is included in serialization timing, not hidden in setup.
#[inline]
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

pub struct ContentInfoValues {
    pub vest: Vec<generated_cms::ContentInfo>,
    pub rasn: Vec<rasn_cms::ContentInfo>,
    pub rustcrypto: Vec<rustcrypto_cms::content_info::ContentInfo>,
    pub bcder: Vec<cryptographic_message_syntax::asn1::rfc5652::ContentInfo>,
}

/// Decode once and check the encoders used by the synthetic benchmark.
pub fn content_info_values(inputs: &[Vec<u8>]) -> ContentInfoValues {
    let mut values = ContentInfoValues {
        vest: Vec::new(),
        rasn: Vec::new(),
        rustcrypto: Vec::new(),
        bcder: Vec::new(),
    };
    for input in inputs {
        values
            .vest
            .push(crate::harness::roundtrip(&CONTENT_INFO, input).unwrap());
        let rasn: rasn_cms::ContentInfo = rasn_exact(input);
        let rustcrypto = rustcrypto_cms::content_info::ContentInfo::from_ber(input).unwrap();
        let bcder = parse_bcder(input);
        assert_eq!(rasn::der::encode(&rasn).unwrap(), *input);
        let mut output = vec![0; input.len()];
        assert_eq!(rustcrypto.encode_to_slice(&mut output).unwrap(), &input[..]);
        assert_eq!(
            bcder_content_info(&bcder).to_captured(Mode::Der).as_slice(),
            &input[..]
        );
        values.rasn.push(rasn);
        values.rustcrypto.push(rustcrypto);
        values.bcder.push(bcder);
    }
    values
}

/// Validate original BER messages and return common serializer encodings.
pub fn validated_signed_data(inputs: &[Vec<u8>]) -> Vec<Vec<u8>> {
    assert!(!inputs.is_empty());
    inputs
        .iter()
        .map(|input| {
            let value = crate::harness::parse_complete(&SIGNED_DATA, input).unwrap();
            let expected = normalized_signed_data(input);
            // Original BER can be malleable: compare after normalization, not byte-for-byte.
            let mut output = vec![0; SIGNED_DATA.prepare(&value).unwrap()];
            SIGNED_DATA.serialize(&value, &mut output);
            assert_eq!(normalized_signed_data(&output), expected);
            let mut rustcrypto = rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap();
            assert!(
                rustcrypto
                    .encap_content_info
                    .econtent
                    .as_ref()
                    .map(|value| value.value())
                    == econtent_body(input),
                "RustCrypto changed raw eContent bytes"
            );
            // ANY loses the constructed bit. Check raw preservation before replacing
            // eContent with rasn's independently flattened OCTET STRING.
            let rasn: rasn_cms::SignedData = rasn_exact(input);
            rustcrypto.encap_content_info.econtent = rasn
                .encap_content_info
                .content
                .map(|bytes| der::asn1::Any::new(der::Tag::OctetString, bytes.to_vec()).unwrap());
            assert_eq!(
                normalized_signed_data(&rustcrypto.to_der().unwrap()),
                expected
            );
            expected
        })
        .collect()
}

pub struct SignedDataValues<'i> {
    pub vest: Vec<generated_cms::SignedData<'i>>,
    pub rasn: Vec<rasn_cms::SignedData>,
    pub rustcrypto: Vec<rustcrypto_cms::signed_data::SignedData>,
}

/// Normalized inputs must serialize byte-identically with all three codecs.
pub fn signed_data_values(inputs: &[Vec<u8>]) -> SignedDataValues<'_> {
    let mut values = SignedDataValues {
        vest: Vec::new(),
        rasn: Vec::new(),
        rustcrypto: Vec::new(),
    };
    for input in inputs {
        values
            .vest
            .push(crate::harness::roundtrip(&SIGNED_DATA, input).unwrap());
        let rasn: rasn_cms::SignedData = rasn_exact(input);
        let rustcrypto = rustcrypto_cms::signed_data::SignedData::from_ber(input).unwrap();
        assert_eq!(rasn::der::encode(&rasn).unwrap(), *input);
        let mut output = vec![0; input.len()];
        assert_eq!(rustcrypto.encode_to_slice(&mut output).unwrap(), &input[..]);
        values.rasn.push(rasn);
        values.rustcrypto.push(rustcrypto);
    }
    values
}
