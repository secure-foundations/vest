use vest_lib::combinators::{
    bytes::{AndThen, ExactLen},
    Fixed, Tail, Varied,
};
use vest_lib::core::exec::{parser::Parser, ParseErrorKind};

use crate::common::assert_err_kind;

#[test]
fn fixed_parses_exact_prefix() {
    let parser = Fixed::<2>;
    let input = b"abc".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out, b"ab");
}

#[test]
fn fixed_reports_unexpected_eof() {
    let parser = Fixed::<3>;
    let input = b"ab".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::UnexpectedEof);
}

#[test]
fn varied_uses_runtime_length() {
    let parser = Varied(3u8);
    let input = b"abcd".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 3);
    assert_eq!(out, b"abc");
}

#[test]
fn and_then_reparses_consumed_chunk() {
    let parser = AndThen(Fixed::<2>, Tail);
    let input = b"abcd".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out, b"ab");
}

#[test]
fn and_then_reports_length_mismatch() {
    let parser = AndThen(Fixed::<2>, Fixed::<1>);
    let input = b"ab".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::LengthMismatch);
}

#[test]
fn exact_len_succeeds_when_inner_consumes_full_chunk() {
    let parser = ExactLen(2u8, Tail);
    let input = b"abc".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out, b"ab");
}

#[test]
fn exact_len_propagates_length_mismatch() {
    let parser = ExactLen(2u8, Fixed::<1>);
    let input = b"ab".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::LengthMismatch);
}
