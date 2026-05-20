use vest_lib::core::exec::{ParseError, ParseErrorKind};

pub fn assert_err_kind(err: ParseError, expected: ParseErrorKind) {
    assert_eq!(err.kind, expected);
}
