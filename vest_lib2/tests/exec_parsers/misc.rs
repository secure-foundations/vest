use vest_lib::combinators::{Empty, Eof, Named, Tail};
use vest_lib::core::exec::{parser::Parser, ParseErrorKind};

use crate::common::assert_err_kind;

#[test]
fn tail_consumes_remaining_input() {
    let parser = Tail;
    let input = b"hello".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 5);
    assert_eq!(out, b"hello");
}

#[test]
fn eof_accepts_empty_input() {
    let parser = Eof;
    let input = b"".as_slice();

    let (n, ()) = parser.parse(&input).unwrap();

    assert_eq!(n, 0);
}

#[test]
fn eof_rejects_trailing_bytes() {
    let parser = Eof;
    let input = b"x".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::ExpectingEof);
}

#[test]
fn named_attaches_format_name() {
    let parser = Named(Eof, "Packet");
    let input = b"x".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_eq!(err.failed_format, Some("Packet"));
    assert_eq!(err.format_trace(), &["Packet"]);
    assert_eq!(err.kind, ParseErrorKind::ExpectingEof);
}

#[test]
fn nested_named_accumulates_format_stack() {
    let parser = Named(Named(Eof, "Payload"), "Packet");
    let input = b"x".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_eq!(err.failed_format, Some("Payload"));
    assert_eq!(err.format_trace(), &["Payload", "Packet"]);
    assert_eq!(err.kind, ParseErrorKind::ExpectingEof);
}

#[test]
fn empty_does_not_consume_anything() {
    let parser = Empty;
    let input = b"xyz".as_slice();

    let (n, ()) = parser.parse(&input).unwrap();

    assert_eq!(n, 0);
}
