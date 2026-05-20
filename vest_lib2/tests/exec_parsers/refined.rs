use vest_lib::combinators::{Const, Fixed, WithPrefixTag, U8};
use vest_lib::core::exec::{parser::Parser, ParseErrorKind};

use crate::common::assert_err_kind;

#[test]
fn const_accepts_expected_value() {
    let parser = Const(U8, 0xAAu8);
    let input = b"\xAA".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 1);
    assert_eq!(out, 0xAA);
}

#[test]
fn const_rejects_wrong_value() {
    let parser = Const(U8, 0xAAu8);
    let input = b"\xAB".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::InvalidTag);
}

#[test]
fn fixed_const_accepts_matching_array_value() {
    let parser = Const(Fixed::<2>, [0xAAu8, 0xBBu8]);
    let input = b"\xAA\xBB!".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out, [0xAAu8, 0xBBu8]);
}

#[test]
fn fixed_const_rejects_non_matching_array_value() {
    let parser = Const(Fixed::<2>, [0xAAu8, 0xBBu8]);
    let input = b"\xAA\xBC".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::InvalidTag);
}

#[test]
fn tagged_parses_body_after_matching_tag() {
    let parser = WithPrefixTag(U8, 0xA1u8, Fixed::<2>);
    let input = b"\xA1xy".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 3);
    assert_eq!(out, b"xy");
}

#[test]
fn tagged_rejects_wrong_prefix_tag() {
    let parser = WithPrefixTag(U8, 0xA1u8, Fixed::<2>);
    let input = b"\xA2xy".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::InvalidTag);
}
