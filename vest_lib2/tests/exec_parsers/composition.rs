use vest_lib::combinators::{Empty, Fixed, Opt, Optional, Pair, Preceded};
use vest_lib::core::exec::{parser::Parser, ParseErrorKind};

use crate::common::assert_err_kind;

#[test]
fn pair_parses_sequentially() {
    let parser = Pair(Fixed::<1>, Fixed::<2>);
    let input = b"abc".as_slice();

    let (n, (head, tail)) = parser.parse(&input).unwrap();

    assert_eq!(n, 3);
    assert_eq!(head, b"a");
    assert_eq!(tail, b"bc");
}

#[test]
fn pair_propagates_second_parser_error() {
    let parser = Pair(Fixed::<1>, Fixed::<2>);
    let input = b"ab".as_slice();

    let err = parser.parse(&input).unwrap_err();

    assert_err_kind(err, ParseErrorKind::UnexpectedEof);
}

#[test]
fn opt_returns_some_on_success() {
    let parser = Opt(Fixed::<2>);
    let input = b"abc".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out.unwrap(), b"ab");
}

#[test]
fn opt_returns_none_without_consuming_input() {
    let parser = Opt(Fixed::<3>);
    let input = b"ab".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 0);
    assert_eq!(out, None);
}

#[test]
fn optional_can_take_present_prefix() {
    let parser = Optional(Fixed::<1>, Fixed::<2>);
    let input = b"abc".as_slice();

    let (n, (opt, tail)) = parser.parse(&input).unwrap();

    assert_eq!(n, 3);
    assert_eq!(opt.unwrap(), b"a");
    assert_eq!(tail, b"bc");
}

#[test]
fn preceded_discards_prefix_value() {
    let parser = Preceded::<_, _, _, false> {
        a: Fixed::<1>,
        b: Fixed::<2>,
        a_val: b"a".as_slice(),
    };
    let input = b"abc".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 3);
    assert_eq!(out, b"bc");
}

#[test]
fn empty_succeeds_without_consuming() {
    let parser = Empty;
    let input = b"abc".as_slice();

    let (n, ()) = parser.parse(&input).unwrap();

    assert_eq!(n, 0);
}
