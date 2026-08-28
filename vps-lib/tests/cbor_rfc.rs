//! RFC 8949 conformance tests for [`vps_lib::cbor`], assisted by Claude Opus 5.
//!
//! Vectors are taken verbatim from RFC 8949 Appendix A (encoded data item
//! examples), Appendix F.1 (data items that are *not* well-formed), and the
//! normative requirements of sections 3.x, 4.2.1, 5.3.1, and 10.
//!
//! Tests whose names begin with `documented_gap_` assert *current* behavior that
//! deliberately deviates from the RFC; see the `Limitations` section of the
//! `cbor` module documentation. They exist so the deviations cannot change
//! silently.
#![cfg(feature = "alloc")]

use vps_lib::cbor::{CborBytes, CborFloat, CborFmt, CborText, CborValue, MAX_RECURSION_DEPTH};
use vps_lib::core::exec::{ByteLen, Parser, Prepare, SerializerExt};

const GENERAL: bool = false;
const DET: bool = true;

fn parse_general(bytes: &[u8]) -> Option<(usize, CborValue<'_>)> {
    CborFmt::<GENERAL>.parse(&bytes).ok()
}

fn parse_det(bytes: &[u8]) -> Option<(usize, CborValue<'_>)> {
    CborFmt::<DET>.parse(&bytes).ok()
}

/// A well-formed encoded data item spans exactly one item (RFC 8949 section 3),
/// so consuming only a prefix does not count as accepting the input.
fn accepts_whole(bytes: &[u8], det: bool) -> bool {
    let parsed = if det { parse_det(bytes) } else { parse_general(bytes) };
    matches!(parsed, Some((consumed, _)) if consumed == bytes.len())
}

/// True for Appendix A diagnostic notations that use the `_` encoding
/// indicator, i.e. items that contain an indefinite-length item at any depth.
fn uses_indefinite_encoding(diagnostic: &str) -> bool {
    diagnostic.contains("_ ")
}

// ===========================================================================
// Appendix F.1: data items that are NOT well-formed.
// ===========================================================================

/// Every byte sequence RFC 8949 Appendix F.1 lists as not well-formed, as
/// `(label, bytes)` pairs.
const NOT_WELL_FORMED: &[(&str, &[u8])] = &[
    // --- error kind 2: end of input in a head ---
    ("head: 18", &[0x18]),
    ("head: 19", &[0x19]),
    ("head: 1a", &[0x1a]),
    ("head: 1b", &[0x1b]),
    ("head: 19 01", &[0x19, 0x01]),
    ("head: 1a 01 02", &[0x1a, 0x01, 0x02]),
    (
        "head: 1b 01 02 03 04 05 06 07",
        &[0x1b, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07],
    ),
    ("head: 38", &[0x38]),
    ("head: 58", &[0x58]),
    ("head: 78", &[0x78]),
    ("head: 98", &[0x98]),
    ("head: 9a 01 ff 00", &[0x9a, 0x01, 0xff, 0x00]),
    ("head: b8", &[0xb8]),
    ("head: d8", &[0xd8]),
    ("head: f8", &[0xf8]),
    ("head: f9 00", &[0xf9, 0x00]),
    ("head: fa 00 00", &[0xfa, 0x00, 0x00]),
    ("head: fb 00 00 00", &[0xfb, 0x00, 0x00, 0x00]),
    // --- definite-length strings with short data ---
    ("short string: 41", &[0x41]),
    ("short string: 61", &[0x61]),
    ("short string: 5a ffffffff 00", &[0x5a, 0xff, 0xff, 0xff, 0xff, 0x00]),
    (
        "short string: 5b ffffffffffffffff 010203",
        &[0x5b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x02, 0x03],
    ),
    ("short string: 7a ffffffff 00", &[0x7a, 0xff, 0xff, 0xff, 0xff, 0x00]),
    (
        "short string: 7b 7fffffffffffffff 010203",
        &[0x7b, 0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01, 0x02, 0x03],
    ),
    // --- definite-length maps and arrays not closed with enough items ---
    ("short array: 81", &[0x81]),
    (
        "short array: 81*9",
        &[0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81, 0x81],
    ),
    ("short array: 82 00", &[0x82, 0x00]),
    ("short map: a1", &[0xa1]),
    ("short map: a2 01 02", &[0xa2, 0x01, 0x02]),
    ("short map: a1 00", &[0xa1, 0x00]),
    ("short map: a2 00 00 00", &[0xa2, 0x00, 0x00, 0x00]),
    // --- tag number not followed by tag content ---
    ("bare tag: c0", &[0xc0]),
    // --- indefinite-length strings not closed by a break stop code ---
    ("unterminated string: 5f 41 00", &[0x5f, 0x41, 0x00]),
    ("unterminated string: 7f 61 00", &[0x7f, 0x61, 0x00]),
    // --- indefinite-length maps and arrays not closed by a break stop code ---
    ("unterminated: 9f", &[0x9f]),
    ("unterminated: 9f 01 02", &[0x9f, 0x01, 0x02]),
    ("unterminated: bf", &[0xbf]),
    ("unterminated: bf 01 02 01 02", &[0xbf, 0x01, 0x02, 0x01, 0x02]),
    ("unterminated: 81 9f", &[0x81, 0x9f]),
    ("unterminated: 9f 80 00", &[0x9f, 0x80, 0x00]),
    (
        "unterminated: 9f 9f 9f 9f 9f ff ff ff ff",
        &[0x9f, 0x9f, 0x9f, 0x9f, 0x9f, 0xff, 0xff, 0xff, 0xff],
    ),
    (
        "unterminated: 9f 81 9f 81 9f 9f ff ff ff",
        &[0x9f, 0x81, 0x9f, 0x81, 0x9f, 0x9f, 0xff, 0xff, 0xff],
    ),
    // --- syntax subkind 1: reserved additional information 28, 29, 30 ---
    ("reserved ai: 1c", &[0x1c]),
    ("reserved ai: 1d", &[0x1d]),
    ("reserved ai: 1e", &[0x1e]),
    ("reserved ai: 3c", &[0x3c]),
    ("reserved ai: 3d", &[0x3d]),
    ("reserved ai: 3e", &[0x3e]),
    ("reserved ai: 5c", &[0x5c]),
    ("reserved ai: 5d", &[0x5d]),
    ("reserved ai: 5e", &[0x5e]),
    ("reserved ai: 7c", &[0x7c]),
    ("reserved ai: 7d", &[0x7d]),
    ("reserved ai: 7e", &[0x7e]),
    ("reserved ai: 9c", &[0x9c]),
    ("reserved ai: 9d", &[0x9d]),
    ("reserved ai: 9e", &[0x9e]),
    ("reserved ai: bc", &[0xbc]),
    ("reserved ai: bd", &[0xbd]),
    ("reserved ai: be", &[0xbe]),
    ("reserved ai: dc", &[0xdc]),
    ("reserved ai: dd", &[0xdd]),
    ("reserved ai: de", &[0xde]),
    ("reserved ai: fc", &[0xfc]),
    ("reserved ai: fd", &[0xfd]),
    ("reserved ai: fe", &[0xfe]),
    // --- syntax subkind 2: reserved two-byte encodings of simple values ---
    ("bad simple: f8 00", &[0xf8, 0x00]),
    ("bad simple: f8 01", &[0xf8, 0x01]),
    ("bad simple: f8 18", &[0xf8, 0x18]),
    ("bad simple: f8 1f", &[0xf8, 0x1f]),
    // --- syntax subkind 3: bad indefinite-length string chunks ---
    ("bad chunk: 5f 00 ff", &[0x5f, 0x00, 0xff]),
    ("bad chunk: 5f 21 ff", &[0x5f, 0x21, 0xff]),
    ("bad chunk: 5f 61 00 ff", &[0x5f, 0x61, 0x00, 0xff]),
    ("bad chunk: 5f 80 ff", &[0x5f, 0x80, 0xff]),
    ("bad chunk: 5f a0 ff", &[0x5f, 0xa0, 0xff]),
    ("bad chunk: 5f c0 00 ff", &[0x5f, 0xc0, 0x00, 0xff]),
    ("bad chunk: 5f e0 ff", &[0x5f, 0xe0, 0xff]),
    ("bad chunk: 7f 41 00 ff", &[0x7f, 0x41, 0x00, 0xff]),
    ("nested chunk: 5f 5f 41 00 ff ff", &[0x5f, 0x5f, 0x41, 0x00, 0xff, 0xff]),
    ("nested chunk: 7f 7f 61 00 ff ff", &[0x7f, 0x7f, 0x61, 0x00, 0xff, 0xff]),
    // --- syntax subkind 4: misplaced break stop code ---
    ("lone break: ff", &[0xff]),
    ("break in array: 81 ff", &[0x81, 0xff]),
    ("break in array: 82 00 ff", &[0x82, 0x00, 0xff]),
    ("break in map: a1 ff", &[0xa1, 0xff]),
    ("break in map: a1 ff 00", &[0xa1, 0xff, 0x00]),
    ("break in map: a1 00 ff", &[0xa1, 0x00, 0xff]),
    ("break in map: a2 00 00 ff", &[0xa2, 0x00, 0x00, 0xff]),
    ("break in array: 9f 81 ff", &[0x9f, 0x81, 0xff]),
    (
        "break in array: 9f 82 9f 81 9f 9f ff ff ff ff",
        &[0x9f, 0x82, 0x9f, 0x81, 0x9f, 0x9f, 0xff, 0xff, 0xff, 0xff],
    ),
    ("odd indefinite map: bf 00 ff", &[0xbf, 0x00, 0xff]),
    ("odd indefinite map: bf 00 00 00 ff", &[0xbf, 0x00, 0x00, 0x00, 0xff]),
    // --- syntax subkind 5: additional information 31 on major type 0, 1, 6 ---
    ("ai 31 on mt 0: 1f", &[0x1f]),
    ("ai 31 on mt 1: 3f", &[0x3f]),
    ("ai 31 on mt 6: df", &[0xdf]),
];

#[test]
fn appendix_f_items_that_are_not_well_formed_are_rejected() {
    for det in [GENERAL, DET] {
        let accepted = NOT_WELL_FORMED
            .iter()
            .filter(|(_, bytes)| accepts_whole(bytes, det))
            .map(|(label, _)| *label)
            .collect::<Vec<_>>();
        assert!(
            accepted.is_empty(),
            "DET={det} accepted input that is not well-formed: {accepted:#?}"
        );
    }
}

// ===========================================================================
// Appendix A: encoded data item examples.
// ===========================================================================

/// Every encoded data item from RFC 8949 Appendix A, as `(diagnostic, bytes)`.
const APPENDIX_A: &[(&str, &[u8])] = &[
    ("0", &[0x00]),
    ("1", &[0x01]),
    ("10", &[0x0a]),
    ("23", &[0x17]),
    ("24", &[0x18, 0x18]),
    ("25", &[0x18, 0x19]),
    ("100", &[0x18, 0x64]),
    ("1000", &[0x19, 0x03, 0xe8]),
    ("1000000", &[0x1a, 0x00, 0x0f, 0x42, 0x40]),
    ("1000000000000", &[0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00]),
    (
        "18446744073709551615",
        &[0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
    ),
    (
        "18446744073709551616 (bignum)",
        &[0xc2, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ),
    (
        "-18446744073709551616",
        &[0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
    ),
    (
        "-18446744073709551617 (bignum)",
        &[0xc3, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ),
    ("-1", &[0x20]),
    ("-10", &[0x29]),
    ("-100", &[0x38, 0x63]),
    ("-1000", &[0x39, 0x03, 0xe7]),
    ("0.0", &[0xf9, 0x00, 0x00]),
    ("-0.0", &[0xf9, 0x80, 0x00]),
    ("1.0", &[0xf9, 0x3c, 0x00]),
    ("1.1", &[0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a]),
    ("1.5", &[0xf9, 0x3e, 0x00]),
    ("65504.0", &[0xf9, 0x7b, 0xff]),
    ("100000.0", &[0xfa, 0x47, 0xc3, 0x50, 0x00]),
    ("3.4028234663852886e+38", &[0xfa, 0x7f, 0x7f, 0xff, 0xff]),
    ("1.0e+300", &[0xfb, 0x7e, 0x37, 0xe4, 0x3c, 0x88, 0x00, 0x75, 0x9c]),
    ("5.960464477539063e-8", &[0xf9, 0x00, 0x01]),
    ("0.00006103515625", &[0xf9, 0x04, 0x00]),
    ("-4.0", &[0xf9, 0xc4, 0x00]),
    ("-4.1", &[0xfb, 0xc0, 0x10, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66]),
    ("Infinity (binary16)", &[0xf9, 0x7c, 0x00]),
    ("NaN (binary16)", &[0xf9, 0x7e, 0x00]),
    ("-Infinity (binary16)", &[0xf9, 0xfc, 0x00]),
    ("Infinity (binary32)", &[0xfa, 0x7f, 0x80, 0x00, 0x00]),
    ("NaN (binary32)", &[0xfa, 0x7f, 0xc0, 0x00, 0x00]),
    ("-Infinity (binary32)", &[0xfa, 0xff, 0x80, 0x00, 0x00]),
    (
        "Infinity (binary64)",
        &[0xfb, 0x7f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ),
    ("NaN (binary64)", &[0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
    (
        "-Infinity (binary64)",
        &[0xfb, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
    ),
    ("false", &[0xf4]),
    ("true", &[0xf5]),
    ("null", &[0xf6]),
    ("undefined", &[0xf7]),
    ("simple(16)", &[0xf0]),
    ("simple(255)", &[0xf8, 0xff]),
    (
        "0(\"2013-03-21T20:04:00Z\")",
        &[
            0xc0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32,
            0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a,
        ],
    ),
    ("1(1363896240)", &[0xc1, 0x1a, 0x51, 0x4b, 0x67, 0xb0]),
    (
        "1(1363896240.5)",
        &[0xc1, 0xfb, 0x41, 0xd4, 0x52, 0xd9, 0xec, 0x20, 0x00, 0x00],
    ),
    ("23(h'01020304')", &[0xd7, 0x44, 0x01, 0x02, 0x03, 0x04]),
    ("24(h'6449455446')", &[0xd8, 0x18, 0x45, 0x64, 0x49, 0x45, 0x54, 0x46]),
    (
        "32(\"http://www.example.com\")",
        &[
            0xd8, 0x20, 0x76, 0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e,
            0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d,
        ],
    ),
    ("h''", &[0x40]),
    ("h'01020304'", &[0x44, 0x01, 0x02, 0x03, 0x04]),
    ("\"\"", &[0x60]),
    ("\"a\"", &[0x61, 0x61]),
    ("\"IETF\"", &[0x64, 0x49, 0x45, 0x54, 0x46]),
    ("\"\\\"\\\\\"", &[0x62, 0x22, 0x5c]),
    ("\"\\u00fc\"", &[0x62, 0xc3, 0xbc]),
    ("\"\\u6c34\"", &[0x63, 0xe6, 0xb0, 0xb4]),
    ("\"\\ud800\\udd51\"", &[0x64, 0xf0, 0x90, 0x85, 0x91]),
    ("[]", &[0x80]),
    ("[1, 2, 3]", &[0x83, 0x01, 0x02, 0x03]),
    (
        "[1, [2, 3], [4, 5]]",
        &[0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05],
    ),
    (
        "[1, 2, ... 25]",
        &[
            0x98, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
            0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18,
            0x19,
        ],
    ),
    ("{}", &[0xa0]),
    ("{1: 2, 3: 4}", &[0xa2, 0x01, 0x02, 0x03, 0x04]),
    (
        "{\"a\": 1, \"b\": [2, 3]}",
        &[0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03],
    ),
    (
        "[\"a\", {\"b\": \"c\"}]",
        &[0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63],
    ),
    (
        "{\"a\": \"A\", ... \"e\": \"E\"}",
        &[
            0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43, 0x61,
            0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45,
        ],
    ),
    (
        "(_ h'0102', h'030405')",
        &[0x5f, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xff],
    ),
    (
        "(_ \"strea\", \"ming\")",
        &[0x7f, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6d, 0x69, 0x6e, 0x67, 0xff],
    ),
    ("[_ ]", &[0x9f, 0xff]),
    (
        "[_ 1, [2, 3], [_ 4, 5]]",
        &[0x9f, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff, 0xff],
    ),
    (
        "[_ 1, [2, 3], [4, 5]]",
        &[0x9f, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05, 0xff],
    ),
    (
        "[1, [2, 3], [_ 4, 5]]",
        &[0x83, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff],
    ),
    (
        "[1, [_ 2, 3], [4, 5]]",
        &[0x83, 0x01, 0x9f, 0x02, 0x03, 0xff, 0x82, 0x04, 0x05],
    ),
    (
        "[_ 1, 2, ... 25]",
        &[
            0x9f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19,
            0xff,
        ],
    ),
    (
        "{_ \"a\": 1, \"b\": [_ 2, 3]}",
        &[0xbf, 0x61, 0x61, 0x01, 0x61, 0x62, 0x9f, 0x02, 0x03, 0xff, 0xff],
    ),
    (
        "[\"a\", {_ \"b\": \"c\"}]",
        &[0x82, 0x61, 0x61, 0xbf, 0x61, 0x62, 0x61, 0x63, 0xff],
    ),
    (
        "{_ \"Fun\": true, \"Amt\": -2}",
        &[0xbf, 0x63, 0x46, 0x75, 0x6e, 0xf5, 0x63, 0x41, 0x6d, 0x74, 0x21, 0xff],
    ),
];

#[test]
fn appendix_a_well_formed_items_are_accepted_in_full() {
    let rejected = APPENDIX_A
        .iter()
        .filter(|(_, bytes)| !accepts_whole(bytes, GENERAL))
        .map(|(label, bytes)| format!("{label}: consumed {:?}", parse_general(bytes).map(|(n, _)| n)))
        .collect::<Vec<_>>();
    assert!(
        rejected.is_empty(),
        "well-formed Appendix A items were not accepted: {rejected:#?}"
    );
}

#[test]
fn deterministic_mode_rejects_exactly_the_indefinite_length_appendix_a_items() {
    // Section 4.2.1: "Indefinite-length items MUST NOT appear." Every other
    // Appendix A item already uses preferred serialization for its arguments,
    // so nothing else may be filtered out. Note that an indefinite-length item
    // nested inside a definite-length one must also be rejected.
    let mut rejected = 0;
    for (label, bytes) in APPENDIX_A {
        let expected = !uses_indefinite_encoding(label);
        assert_eq!(
            accepts_whole(bytes, DET),
            expected,
            "DET acceptance of {label} should be {expected}"
        );
        rejected += usize::from(!expected);
    }
    assert_eq!(rejected, 11, "expected 11 indefinite-length Appendix A items");
}

#[test]
fn deterministic_mode_reproduces_the_input_bytes_it_accepts() {
    // Parse-then-serialize must be the identity on the deterministic profile,
    // which is the byte-level statement of non-malleability.
    let format = CborFmt::<DET, 8>;
    let mut mismatches = Vec::new();
    for (label, bytes) in APPENDIX_A {
        if !accepts_whole(bytes, DET) {
            continue;
        }
        let (_, value) = parse_det(bytes).unwrap();
        let Ok(len) = format.prepare(&value) else {
            mismatches.push(format!("{label}: prepare rejected a parsed value"));
            continue;
        };
        assert_eq!(format.length(&value), len, "{label}: length and prepare disagree");
        let mut out = vec![0u8; len];
        format.serialize(&value, out.as_mut_slice());
        if out.as_slice() != *bytes {
            mismatches.push(format!("{label}: {bytes:02x?} -> {out:02x?}"));
        }
    }
    assert!(
        mismatches.is_empty(),
        "DET parse->serialize did not reproduce the input: {mismatches:#?}"
    );
}

// ===========================================================================
// Section 3: heads, arguments, and the generic data model.
// ===========================================================================

/// Builds an item for `major` whose argument holds `value` in `width` bytes
/// (widths 1, 2, 4, 8 correspond to additional information 24, 25, 26, 27),
/// followed by whatever content that head requires.
fn item_with_argument_width(major: u8, width: usize, value: u64) -> Vec<u8> {
    let additional = match width {
        1 => 24u8,
        2 => 25,
        4 => 26,
        8 => 27,
        _ => panic!("argument width must be 1, 2, 4, or 8"),
    };
    let mut bytes = vec![(major << 5) | additional];
    bytes.extend_from_slice(&value.to_be_bytes()[8 - width..]);
    let content_items = match major {
        2 | 3 => value as usize, // string bytes
        4 => value as usize,     // array elements
        5 => 2 * value as usize, // map key/value items
        6 => 1,                  // tag content
        _ => 0,
    };
    let filler = if major == 3 { 0x61 } else { 0x00 };
    bytes.extend(std::iter::repeat(filler).take(content_items));
    bytes
}

#[test]
fn full_integer_range_of_the_generic_data_model_is_representable() {
    // Section 2: integers span -2^64 .. 2^64-1.
    let max = [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    assert_eq!(
        parse_general(&max).map(|(_, v)| v),
        Some(CborValue::Integer(u64::MAX as i128))
    );
    let min = [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
    assert_eq!(
        parse_general(&min).map(|(_, v)| v),
        Some(CborValue::Integer(-1 - u64::MAX as i128))
    );

    // Values outside the model must be refused before serialization.
    assert!(CborFmt::<GENERAL>
        .prepare(&CborValue::Integer(u64::MAX as i128 + 1))
        .is_err());
    assert!(CborFmt::<GENERAL>
        .prepare(&CborValue::Integer(-2 - u64::MAX as i128))
        .is_err());
}

#[test]
fn unassigned_simple_values_are_passed_through_and_reserved_ones_are_refused() {
    // Section 3.3, Table 4: 0..19 and 32..255 are unassigned but well-formed.
    assert_eq!(parse_general(&[0xe0]).map(|(_, v)| v), Some(CborValue::Simple(0)));
    assert_eq!(parse_general(&[0xf0]).map(|(_, v)| v), Some(CborValue::Simple(16)));
    assert_eq!(
        parse_general(&[0xf8, 0x20]).map(|(_, v)| v),
        Some(CborValue::Simple(32))
    );
    assert_eq!(
        parse_general(&[0xf8, 0xff]).map(|(_, v)| v),
        Some(CborValue::Simple(255))
    );

    // 20..23 have dedicated variants and 24..31 are reserved, so the generic
    // `Simple` variant must not be able to encode any of them.
    for reserved in 20u8..32 {
        assert!(
            CborFmt::<GENERAL>.prepare(&CborValue::Simple(reserved)).is_err(),
            "prepare accepted reserved simple({reserved})"
        );
    }
}

#[test]
fn deterministic_mode_requires_preferred_argument_encodings() {
    // Section 4.2.1: arguments for integers, string/array/map lengths, and tag
    // numbers must be as short as possible. Value 1 always fits in the initial
    // byte, so any explicit argument carrying it is non-preferred.
    for major in [0u8, 1, 2, 3, 4, 5, 6] {
        for width in [1usize, 2, 4, 8] {
            let bytes = item_with_argument_width(major, width, 1);
            assert!(
                accepts_whole(&bytes, GENERAL),
                "GENERAL should tolerate a non-preferred argument: mt={major} width={width}"
            );
            assert!(
                !accepts_whole(&bytes, DET),
                "DET accepted a non-minimal argument: mt={major} width={width} {bytes:02x?}"
            );
        }
    }

    // Width boundaries: a value needing exactly N bytes is preferred at width N
    // and non-preferred at every wider width.
    for (value, minimal_width) in [(24u64, 1usize), (256, 2), (65536, 4), (4294967296, 8)] {
        let preferred = item_with_argument_width(0, minimal_width, value);
        assert!(
            accepts_whole(&preferred, DET),
            "DET rejected the preferred encoding of {value}: {preferred:02x?}"
        );
        for wider in [1usize, 2, 4, 8].into_iter().filter(|w| *w > minimal_width) {
            let bytes = item_with_argument_width(0, wider, value);
            assert!(
                !accepts_whole(&bytes, DET),
                "DET accepted {value} widened to {wider} bytes: {bytes:02x?}"
            );
        }
    }

    // Major type 7: the two-byte simple form is minimal for values >= 32, since
    // those do not fit the 5-bit field, and is not well-formed below 32.
    assert!(accepts_whole(&[0xf8, 0x20], DET));
    assert!(!accepts_whole(&[0xf8, 0x1f], DET));
}

#[test]
fn indefinite_length_strings_follow_section_3_2_3() {
    // Zero chunks yields the empty string of the indicated type.
    assert_eq!(
        parse_general(&[0x5f, 0xff]).map(|(_, v)| v),
        Some(CborValue::Bytes(CborBytes::Indefinite(Vec::new())))
    );
    assert_eq!(
        parse_general(&[0x7f, 0xff]).map(|(_, v)| v),
        Some(CborValue::Text(CborText::Indefinite(String::new())))
    );

    // Zero-length chunks are permitted, if not useful.
    assert!(accepts_whole(&[0x5f, 0x40, 0x40, 0xff], GENERAL));

    // The item is the concatenation of its chunks.
    assert_eq!(
        parse_general(&[0x5f, 0x42, 0xaa, 0xbb, 0x43, 0xcc, 0xdd, 0xee, 0xff]).map(|(_, v)| v),
        Some(CborValue::Bytes(CborBytes::Indefinite(vec![
            0xaa, 0xbb, 0xcc, 0xdd, 0xee
        ])))
    );

    // A code point may not be split across chunks.
    assert!(!accepts_whole(&[0x7f, 0x61, 0xc2, 0x61, 0xa2, 0xff], GENERAL));
}

#[test]
fn trailing_data_is_reported_through_the_consumed_length() {
    // Section 3 leaves it to the caller to decide whether leftover bytes are an
    // error, so `parse` reports one item and how much of the input it used.
    let two_items = [0x00, 0x00];
    let (consumed, value) = CborFmt::<GENERAL>.parse(&&two_items[..]).unwrap();
    assert_eq!(consumed, 1);
    assert_eq!(value, CborValue::Integer(0));
}

// ===========================================================================
// Section 10: robustness against hostile input.
// ===========================================================================

#[test]
fn oversized_declared_lengths_are_refused() {
    let huge = u64::MAX.to_be_bytes();
    for initial in [0x5bu8, 0x7b, 0x9b, 0xbb] {
        let mut bytes = vec![initial];
        bytes.extend_from_slice(&huge);
        // A handful of content bytes: nowhere near the 2^64-1 claimed.
        bytes.extend_from_slice(&[if initial == 0x7b { 0x61 } else { 0x00 }; 8]);
        assert!(
            !accepts_whole(&bytes, GENERAL),
            "accepted an item claiming 2^64-1 units of content: initial byte {initial:#04x}"
        );
    }
}

#[test]
fn deeply_nested_input_is_bounded_by_the_recursion_limit() {
    // Nesting far beyond the budget must fail as data, not exhaust the stack.
    for initial in [0x9fu8, 0x81, 0xc0] {
        let deep = vec![initial; 100_000];
        assert!(!accepts_whole(&deep, GENERAL));
    }
}

#[test]
fn nesting_is_accepted_up_to_the_configured_recursion_depth() {
    fn nested_arrays(depth: usize) -> Vec<u8> {
        let mut bytes = vec![0x81u8; depth];
        bytes.push(0x00);
        bytes
    }

    assert!(accepts_whole(&nested_arrays(MAX_RECURSION_DEPTH), GENERAL));
    assert!(!accepts_whole(&nested_arrays(MAX_RECURSION_DEPTH + 1), GENERAL));
}

// ===========================================================================
// Documented deviations from RFC 8949. See the `cbor` module `Limitations`.
// ===========================================================================

#[test]
fn documented_gap_map_key_order_is_not_enforced_under_det() {
    // Section 4.2.1 requires map keys sorted in bytewise lexicographic order of
    // their deterministic encodings. {"b": 1, "a": 2} violates that.
    let unsorted = [0xa2, 0x61, 0x62, 0x01, 0x61, 0x61, 0x02];
    assert!(accepts_whole(&unsorted, DET));
}

#[test]
fn documented_gap_duplicate_map_keys_are_not_rejected() {
    // Section 5.3.1: a map with duplicate keys is well-formed but invalid. This
    // codec preserves wire order and duplicates; callers must check validity.
    let duplicate = [0xa2, 0x01, 0x01, 0x01, 0x02];
    assert!(accepts_whole(&duplicate, GENERAL));
    assert!(accepts_whole(&duplicate, DET));
    match parse_det(&duplicate).unwrap().1 {
        CborValue::Map(entries) => assert_eq!(entries.len(), 2),
        other => panic!("expected a map, got {other:?}"),
    }
}

#[test]
fn documented_gap_floating_point_width_is_not_normalized_under_det() {
    // Section 4.2.1 also requires the shortest floating-point form that
    // preserves the value. Width is part of `CborFloat`, so wider encodings of
    // representable values are accepted and re-emitted at their original width.
    assert!(accepts_whole(&[0xfa, 0x7f, 0x80, 0x00, 0x00], DET)); // Infinity as binary32
    assert!(accepts_whole(
        &[0xfb, 0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        DET
    )); // 1.0 as binary64

    let format = CborFmt::<DET, 8>;
    let one_as_binary64 = CborValue::Float(CborFloat::F64(0x3ff0_0000_0000_0000));
    let len = format.prepare(&one_as_binary64).unwrap();
    let mut out = vec![0u8; len];
    format.serialize(&one_as_binary64, out.as_mut_slice());
    assert_eq!(
        out.as_slice(),
        &[0xfb, 0x3f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        "shortest-width float normalization is not implemented"
    );
}

#[test]
fn documented_gap_invalid_utf8_is_rejected_rather_than_reported_as_invalid() {
    // Section 3.1 classifies a text string with invalid UTF-8 as well-formed but
    // invalid, and section 5.3.1 leaves the check optional. This codec is
    // stricter and refuses to decode such an item at all.
    assert!(!accepts_whole(&[0x62, 0xc0, 0xae], GENERAL)); // overlong encoding
    assert!(!accepts_whole(&[0x62, 0xed, 0xa0], GENERAL)); // surrogate lead
    assert!(!accepts_whole(&[0x61, 0x80], GENERAL)); // bare continuation byte
}
