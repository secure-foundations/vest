use vest_lib::combinators::{Alt, Choice, Fixed, Sum};
use vest_lib::core::exec::{parser::Parser, ParseErrorKind};

use crate::common::assert_err_kind;

#[test]
fn choice_returns_left_branch_when_it_succeeds() {
    let parser = Choice(Fixed::<1>, Fixed::<2>);
    let input = b"abc".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 1);
    match out {
        Sum::Inl(bytes) => assert_eq!(bytes, b"a"),
        Sum::Inr(_) => panic!("expected left branch"),
    }
}

#[test]
fn choice_falls_back_to_right_branch() {
    let parser = Choice(Fixed::<3>, Fixed::<2>);
    let input = b"ab".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    match out {
        Sum::Inl(_) => panic!("expected right branch"),
        Sum::Inr(bytes) => assert_eq!(bytes, b"ab"),
    }
}

#[test]
fn choice_reports_error_when_both_branches_fail() {
    let parser = Choice(Fixed::<3>, Fixed::<2>);
    let input = b"a".as_slice();

    let err = match parser.parse(&input) {
        Ok(_) => panic!("expected parse error"),
        Err(err) => err,
    };

    assert_err_kind(err, ParseErrorKind::UnexpectedEof);
}

#[test]
fn alt_returns_first_successful_branch() {
    let parser = Alt(Fixed::<1>, Fixed::<2>);
    let input = b"ab".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 1);
    assert_eq!(out, b"a");
}

#[test]
fn alt_uses_second_branch_when_first_fails() {
    let parser = Alt(Fixed::<3>, Fixed::<2>);
    let input = b"ab".as_slice();

    let (n, out) = parser.parse(&input).unwrap();

    assert_eq!(n, 2);
    assert_eq!(out, b"ab");
}
