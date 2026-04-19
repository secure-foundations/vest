//! Runtime parse errors.
use core::fmt;

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use vstd::prelude::*;

verus! {

/// A minimal runtime parser failure.
///
/// Vest parsers work on progressively sliced inputs, so a globally meaningful byte offset is not
/// available unless the caller explicitly threads that information through the parser stack.
/// Instead, this error carries a coarse-grained failure kind plus the names of the DSL-defined
/// formats on the failing path, when that information is available.
#[derive(Debug, PartialEq, Eq)]
pub struct ParseError {
    /// The kind of failure that occurred.
    pub kind: ParseErrorKind,
    /// The innermost named format known to have failed.
    pub failed_format: Option<&'static str>,
    /// The named-format call stack that led to the failure, stored innermost-first.
    #[cfg(feature = "alloc")]
    pub format_stack: Vec<&'static str>,
}

impl Clone for ParseError {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind.clone(),
            failed_format: self.failed_format,
            #[cfg(feature = "alloc")]
            format_stack: self.format_stack.clone(),
        }
    }
}

impl ParseError {
    /// Creates a new parse error.
    pub fn new(kind: ParseErrorKind) -> Self {
        Self {
            kind,
            failed_format: None,
            #[cfg(feature = "alloc")]
            format_stack: Vec::new(),
        }
    }

    /// Pushes one named format onto the failing format stack.
    ///
    /// The first pushed format becomes `current_format`, so `current_format` continues to refer to
    /// the innermost failing named format even as outer formats append themselves during
    /// propagation.
    pub fn push_format(self, current_format: &'static str) -> Self {
        let mut err = self;
        if err.failed_format.is_none() {
            err.failed_format = Some(current_format);
        }
        #[cfg(feature = "alloc")]
        {
            err.format_stack.push(current_format);
        }
        err
    }

    /// Returns the recorded format stack as an innermost-first slice.
    pub fn format_trace(&self) -> &[&'static str] {
        #[cfg(feature = "alloc")]
        { self.format_stack.as_slice() }
        #[cfg(not(feature = "alloc"))]
        { &[] }
    }
}

impl ParseError {
    /// Creates an unexpected end-of-input error.
    pub fn unexpected_eof() -> Self {
        Self::new(ParseErrorKind::UnexpectedEof)
    }

    /// Creates an invalid-tag error.
    pub fn invalid_tag() -> Self {
        Self::new(ParseErrorKind::InvalidTag)
    }

    /// Creates an invalid-length error.
    pub fn invalid_length() -> Self {
        Self::new(ParseErrorKind::InvalidLength)
    }

    /// Creates a length-mismatch error.
    pub fn length_mismatch() -> Self {
        Self::new(ParseErrorKind::LengthMismatch)
    }

    /// Creates a predicate-failed error.
    pub fn predicate_failed() -> Self {
        Self::new(ParseErrorKind::PredicateFailed)
    }

    /// Creates a branch-rejected error.
    pub fn branch_rejected() -> Self {
        Self::new(ParseErrorKind::BranchRejected)
    }

    /// Creates a non-canonical-encoding error.
    pub fn non_canonical() -> Self {
        Self::new(ParseErrorKind::NonCanonical)
    }

    /// Creates an overflow error.
    pub fn overflow() -> Self {
        Self::new(ParseErrorKind::Overflow)
    }

    /// Creates a recursion-limit-exceeded error.
    pub fn recursion_limit_exceeded() -> Self {
        Self::new(ParseErrorKind::RecursionLimitExceeded)
    }
}

} // verus!
impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let format_trace = self.format_trace();
        if !format_trace.is_empty() {
            write!(f, "{} while parsing format stack ", self.kind)?;
            for (i, format_name) in format_trace.iter().rev().enumerate() {
                if i > 0 {
                    f.write_str(" -> ")?;
                }
                write!(f, "`{}`", format_name)?;
            }
            Ok(())
        } else {
            match self.failed_format {
                Some(current_format) => {
                    write!(f, "{} while parsing format `{}`", self.kind, current_format)
                }
                None => write!(f, "{}", self.kind),
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {}

verus! {

/// The coarse-grained kind of parse failure.
#[derive(Debug, Copy, PartialEq, Eq)]
pub enum ParseErrorKind {
    /// The parser needed more input bytes.
    UnexpectedEof,
    /// A tag or discriminant byte sequence was invalid.
    InvalidTag,
    /// A parsed length field was invalid.
    InvalidLength,
    /// A computed length disagreed with the enclosing format.
    LengthMismatch,
    /// A refinement predicate or semantic check failed.
    PredicateFailed,
    /// A branch was rejected after partial inspection.
    BranchRejected,
    /// A non-canonical representation was observed.
    NonCanonical,
    /// An integer or size computation overflowed.
    Overflow,
    /// Recursion limit exceeded.
    RecursionLimitExceeded,
}

impl Clone for ParseErrorKind {
    fn clone(&self) -> Self {
        *self
    }
}

} // verus!
impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorKind::UnexpectedEof => f.write_str("unexpected end of input"),
            ParseErrorKind::InvalidTag => f.write_str("invalid tag"),
            ParseErrorKind::InvalidLength => f.write_str("invalid length"),
            ParseErrorKind::LengthMismatch => f.write_str("length mismatch"),
            ParseErrorKind::PredicateFailed => f.write_str("predicate failed"),
            ParseErrorKind::BranchRejected => f.write_str("branch rejected"),
            ParseErrorKind::NonCanonical => f.write_str("non-canonical encoding"),
            ParseErrorKind::Overflow => f.write_str("overflow"),
            ParseErrorKind::RecursionLimitExceeded => f.write_str("recursion limit exceeded"),
        }
    }
}
