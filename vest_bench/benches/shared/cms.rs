//! Shared CMS inputs, baseline adapters, and untimed correctness checks.

use std::fs;
use std::path::{Path, PathBuf};

use bcder::{decode::Constructed, encode::PrimitiveContent, Mode};
use der::{Decode, Encode};

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

fn visit_cms(dir: &Path, inputs: &mut Vec<Vec<u8>>) {
    let mut paths: Vec<_> = fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            visit_cms(&path, inputs);
        } else if path.extension().is_some_and(|extension| extension == "cms") {
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
}

pub fn real_signed_data() -> Vec<Vec<u8>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("corpora/cms");
    let mut inputs = Vec::new();
    visit_cms(&root.join("pkits"), &mut inputs);
    visit_cms(&root.join("dss"), &mut inputs);
    visit_cms(&root.join("rfc4134"), &mut inputs);
    inputs
}

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
