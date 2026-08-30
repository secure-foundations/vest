//! Concise Binary Object Representation (CBOR) formats.
//!
//! This module implements the basic generic data model from RFC 8949.
//! It is allocation-gated because recursive generic values necessarily contain
//! `Box`es and `Vec`s.
//! Definite byte and text strings borrow directly from the input;
//! allocation is needed only for fragmented strings and recursive items.
//!
//! [`CborFmt<false>`] accepts the well-formed representation variants described
//! by RFC 8949. [`CborFmt<true>`] additionally requires preferred integer,
//! length, and tag arguments and rejects indefinite-length items (RFC 8949
//! section 4.2.1).
//!
//! ## Limitations
//!
//! - Map-key ordering is not yet enforced in [`CborFmt<true>`].
//! - Floating-point widths are retained in [`CborFloat`], so shortest-width
//! floating-point normalization is likewise not yet imposed.
//!
//! See the [CBOR guide](https://secure-foundations.github.io/vest/guide/cbor.html)
//! for the runtime workflow, ownership model, and deterministic-profile scope.
mod chunk;
pub mod format;
mod head;
mod value;

pub use format::CborFmt;
pub use head::{
    BreakFmt, CborHead, CborHeadFmt, CborHeadValue, CborInitial, CborInitialFmt, MajorType, BREAK,
};
pub use value::{CborArray, CborBytes, CborFloat, CborMap, CborText, CborValue, CborValueSpec};

/// Default maximum nesting depth for generic CBOR values.
pub const MAX_RECURSION_DEPTH: usize = 30;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::exec::{ByteLen, Parser, Prepare, SerializerExt};
    use alloc::borrow::ToOwned;

    const GENERAL: bool = false;
    const DETERMINISTIC: bool = true;

    #[test]
    fn rfc8949_major_types_conformance() {
        let format = CborFmt::<GENERAL>;

        // Major 0: Unsigned integers
        assert_eq!(format.parse(&&[0x00][..]), Ok((1, CborValue::Integer(0))));
        assert_eq!(format.parse(&&[0x17][..]), Ok((1, CborValue::Integer(23))));
        assert_eq!(format.parse(&&[0x18, 0x18][..]), Ok((2, CborValue::Integer(24))));
        assert_eq!(format.parse(&&[0x19, 0x01, 0x00][..]), Ok((3, CborValue::Integer(256))));
        assert_eq!(
            format.parse(&&[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..]),
            Ok((9, CborValue::Integer(u64::MAX as i128)))
        );

        // Major 1: Negative integers (-1 - n)
        assert_eq!(format.parse(&&[0x20][..]), Ok((1, CborValue::Integer(-1))));
        assert_eq!(format.parse(&&[0x37][..]), Ok((1, CborValue::Integer(-24))));
        assert_eq!(format.parse(&&[0x38, 0x18][..]), Ok((2, CborValue::Integer(-25))));
        assert_eq!(format.parse(&&[0x39, 0x03, 0xe7][..]), Ok((3, CborValue::Integer(-1000))));
        assert_eq!(
            format.parse(&&[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff][..]),
            Ok((9, CborValue::Integer(-1i128 - u64::MAX as i128)))
        );

        // Major 2: Byte strings (definite, zero-copy borrow)
        let raw_bytes = [0x44, 0x01, 0x02, 0x03, 0x04];
        let (consumed, parsed) = format.parse(&&raw_bytes[..]).unwrap();
        assert_eq!(consumed, 5);
        match parsed {
            CborValue::Bytes(CborBytes::Definite(slice)) => {
                assert_eq!(slice, &[1, 2, 3, 4]);
                assert_eq!(slice.as_ptr(), raw_bytes[1..].as_ptr());
            }
            _ => panic!("expected definite byte string"),
        }

        // Major 3: Text strings (definite, zero-copy UTF-8 borrow)
        let raw_text = [0x63, 0xe6, 0xb0, 0xb4]; // UTF-8 for '水'
        let (consumed, parsed) = format.parse(&&raw_text[..]).unwrap();
        assert_eq!(consumed, 4);
        match parsed {
            CborValue::Text(CborText::Definite(s)) => {
                assert_eq!(s, "水");
                assert_eq!(s.as_ptr(), raw_text[1..].as_ptr());
            }
            _ => panic!("expected definite text string"),
        }

        // Major 4: Arrays
        assert_eq!(format.parse(&&[0x80][..]), Ok((1, CborValue::Array(vec![]))));
        assert_eq!(
            format.parse(&&[0x82, 0x01, 0x02][..]),
            Ok((3, CborValue::Array(vec![CborValue::Integer(1), CborValue::Integer(2)])))
        );

        // Major 5: Maps
        assert_eq!(format.parse(&&[0xa0][..]), Ok((1, CborValue::Map(vec![]))));
        assert_eq!(
            format.parse(&&[0xa1, 0x61, b'a', 0x01][..]),
            Ok((
                4,
                CborValue::Map(vec![(
                    CborValue::Text(CborText::Definite("a")),
                    CborValue::Integer(1)
                )])
            ))
        );

        // Major 6: Tags
        assert_eq!(
            format.parse(&&[0xc0, 0x60][..]),
            Ok((2, CborValue::Tag(0, alloc::boxed::Box::new(CborValue::Text(CborText::Definite(""))))))
        );

        // Major 7: Simple values and Floats
        assert_eq!(format.parse(&&[0xf4][..]), Ok((1, CborValue::Bool(false))));
        assert_eq!(format.parse(&&[0xf5][..]), Ok((1, CborValue::Bool(true))));
        assert_eq!(format.parse(&&[0xf6][..]), Ok((1, CborValue::Null)));
        assert_eq!(format.parse(&&[0xf7][..]), Ok((1, CborValue::Undefined)));
        assert_eq!(format.parse(&&[0xf0][..]), Ok((1, CborValue::Simple(16))));
        assert_eq!(format.parse(&&[0xf8, 0x20][..]), Ok((2, CborValue::Simple(32))));
        assert_eq!(format.parse(&&[0xf9, 0x3c, 0x00][..]), Ok((3, CborValue::Float(CborFloat::F16(0x3c00)))));
        assert_eq!(format.parse(&&[0xfa, 0x47, 0xc3, 0x50, 0x00][..]), Ok((5, CborValue::Float(CborFloat::F32(0x47c35000)))));
        assert_eq!(format.parse(&&[0xfb, 0x3f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00][..]), Ok((9, CborValue::Float(CborFloat::F64(0x3ff8000000000000)))));
    }

    #[test]
    fn indefinite_streaming_and_chunk_security() {
        let format = CborFmt::<GENERAL>;

        // Valid indefinite byte string and text string (flattening)
        let byte_chunks = [0x5f, 0x42, 0x01, 0x02, 0x41, 0x03, 0xff];
        assert_eq!(
            format.parse(&&byte_chunks[..]),
            Ok((byte_chunks.len(), CborValue::Bytes(CborBytes::Indefinite(vec![1, 2, 3]))))
        );

        let text_chunks = [0x7f, 0x62, b'h', b'i', 0x61, b'!', 0xff];
        assert_eq!(
            format.parse(&&text_chunks[..]),
            Ok((text_chunks.len(), CborValue::Text(CborText::Indefinite("hi!".to_owned()))))
        );

        // Valid indefinite array and map
        let array = [0x9f, 0x01, 0x02, 0xff];
        assert_eq!(
            format.parse(&&array[..]),
            Ok((array.len(), CborValue::Array(vec![CborValue::Integer(1), CborValue::Integer(2)])))
        );

        let map = [0xbf, 0x61, b'k', 0x01, 0xff];
        assert_eq!(
            format.parse(&&map[..]),
            Ok((
                map.len(),
                CborValue::Map(vec![(
                    CborValue::Text(CborText::Definite("k")),
                    CborValue::Integer(1)
                )])
            ))
        );

        // RFC 8949 §3.2.3 Chunk Security Violations (Must be rejected)
        // 1. Nested indefinite string chunks are forbidden
        assert!(format.parse(&&[0x5f, 0x5f, 0x41, 0x01, 0xff, 0xff][..]).is_err());

        // 2. Major type mismatch inside indefinite chunk
        assert!(format.parse(&&[0x5f, 0x61, b'x', 0xff][..]).is_err());
        assert!(format.parse(&&[0x7f, 0x41, 0x01, 0xff][..]).is_err());
        assert!(format.parse(&&[0x5f, 0x01, 0xff][..]).is_err());

        // 3. UTF-8 code point split across chunks (each text chunk must be valid UTF-8)
        let split_utf8 = [0x7f, 0x61, 0xc2, 0x61, 0xa2, 0xff];
        assert!(format.parse(&&split_utf8[..]).is_err());

        // 4. Odd number of items in indefinite map (break cannot substitute map value)
        assert!(format.parse(&&[0xbf, 0x01, 0xff][..]).is_err());

        // 5. Standalone or misplaced break byte
        assert!(format.parse(&&[0xff][..]).is_err());
        assert!(format.parse(&&[0x81, 0xff][..]).is_err());
    }

    #[test]
    fn deterministic_dcbor_vs_general_cbor() {
        let det = CborFmt::<DETERMINISTIC>;
        let gen = CborFmt::<GENERAL>;

        // Non-minimal unsigned integers (e.g. 23 encoded in 2 bytes)
        let non_minimal_uint = [0x18, 0x17];
        assert!(det.parse(&&non_minimal_uint[..]).is_err());
        assert_eq!(gen.parse(&&non_minimal_uint[..]), Ok((2, CborValue::Integer(23))));

        // Non-minimal negative integers (e.g. -24 encoded in 2 bytes)
        let non_minimal_neg = [0x38, 0x17];
        assert!(det.parse(&&non_minimal_neg[..]).is_err());
        assert_eq!(gen.parse(&&non_minimal_neg[..]), Ok((2, CborValue::Integer(-24))));

        // Non-minimal length header
        let non_minimal_bstr_len = [0x58, 0x01, 0xaa];
        assert!(det.parse(&&non_minimal_bstr_len[..]).is_err());
        assert!(gen.parse(&&non_minimal_bstr_len[..]).is_ok());

        // Non-minimal tag header
        let non_minimal_tag = [0xd8, 0x01, 0x00];
        assert!(det.parse(&&non_minimal_tag[..]).is_err());
        assert!(gen.parse(&&non_minimal_tag[..]).is_ok());

        // Indefinite-length framing is strictly rejected in deterministic mode
        assert!(det.parse(&&[0x5f, 0x41, 0x01, 0xff][..]).is_err());
        assert!(det.parse(&&[0x7f, 0x61, b'a', 0xff][..]).is_err());
        assert!(det.parse(&&[0x9f, 0x01, 0xff][..]).is_err());
        assert!(det.parse(&&[0xbf, 0x01, 0x02, 0xff][..]).is_err());
    }

    #[test]
    fn truncation_and_malformed_input_robustness() {
        let format = CborFmt::<GENERAL>;

        // Truncated header arguments
        assert!(format.parse(&&[0x18][..]).is_err());
        assert!(format.parse(&&[0x19, 0x01][..]).is_err());
        assert!(format.parse(&&[0x1a, 0x00, 0x01][..]).is_err());
        assert!(format.parse(&&[0x1b, 0x00, 0x00, 0x00, 0x01][..]).is_err());

        // Truncated string payloads
        assert!(format.parse(&&[0x45, 0x01, 0x02, 0x03][..]).is_err()); // claims 5 bytes, provides 3
        assert!(format.parse(&&[0x65, b'a', b'b'][..]).is_err()); // claims 5 bytes, provides 2

        // Truncated containers
        assert!(format.parse(&&[0x83, 0x01, 0x02][..]).is_err()); // claims 3 items, provides 2
        assert!(format.parse(&&[0xa1, 0x01][..]).is_err()); // key without value

        // Unclosed indefinite containers
        assert!(format.parse(&&[0x9f, 0x01, 0x02][..]).is_err());
        assert!(format.parse(&&[0x5f, 0x41, 0x01][..]).is_err());

        // Reserved additional information values (28..30)
        assert!(format.parse(&&[0x1c][..]).is_err());
        assert!(format.parse(&&[0x1d][..]).is_err());
        assert!(format.parse(&&[0x1e][..]).is_err());
    }

    #[test]
    fn recursion_depth_limit_defense() {
        // 4-level nested array: [[[[1]]]] -> [0x81, 0x81, 0x81, 0x81, 0x01]
        let deeply_nested = [0x81, 0x81, 0x81, 0x81, 0x01];

        // Allowed when nesting budget is sufficient
        let format_deep = CborFmt::<GENERAL, 6>;
        assert!(format_deep.parse(&&deeply_nested[..]).is_ok());

        // Rejected when depth limit is exceeded (prevents stack overflow)
        let format_shallow = CborFmt::<GENERAL, 3>;
        assert!(format_shallow.parse(&&deeply_nested[..]).is_err());
    }

    #[test]
    fn serialization_and_roundtrip_invariants() {
        let format = CborFmt::<DETERMINISTIC, 8>;

        let value = CborValue::Map(vec![
            (
                CborValue::Integer(1),
                CborValue::Array(vec![CborValue::Bool(true), CborValue::Null]),
            ),
            (
                CborValue::Text(CborText::Definite("tag")),
                CborValue::Tag(42, alloc::boxed::Box::new(CborValue::Integer(100))),
            ),
        ]);

        // Pre-serialization size bound agreement
        let len = format.prepare(&value).unwrap();
        assert_eq!(format.length(&value), len);

        // In-place serialization
        let mut buffer = vec![0u8; len];
        format.serialize(&value, buffer.as_mut_slice());

        // Round-trip invertibility: parse(serialize(v)) == v
        assert_eq!(format.parse(&&buffer[..]), Ok((len, value)));

        // Serialization normalizes indefinite-length strings to definite encoding
        let gen_format = CborFmt::<GENERAL, 8>;
        let indefinite_bytes = CborValue::Bytes(CborBytes::Indefinite(vec![1, 2, 3]));
        let len = gen_format.prepare(&indefinite_bytes).unwrap();
        let mut buffer = vec![0u8; len];
        gen_format.serialize(&indefinite_bytes, buffer.as_mut_slice());
        assert_eq!(buffer, [0x43, 0x01, 0x02, 0x03]);
    }
}
