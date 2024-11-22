// pub use crate::utils::*;
use vstd::prelude::*;
use vstd::*;

verus! {

/// Parser errors
#[derive(Debug)]
pub enum ParseError {
    /// The second combinator of AndThen did not consume all bytes
    AndThenUnusedBytes,
    BuilderError,
    UnexpectedEndOfInput,
    OrdChoiceNoMatch,
    CondFailed,
    SizeOverflow,
    TryMapFailed,
    RefinedPredicateFailed,
    RepeatEmptyElement,
    Other(String),
}

/// Serializer errors
#[derive(Debug)]
pub enum SerializeError {
    InsufficientBuffer,
    AndThenUnusedBytes,
    CondFailed,
    SizeOverflow,
    TryMapFailed,
    RefinedPredicateFailed,
    RepeatEmptyElement,
    Other(String),
}

/// Sum of both parse and serialize errors
#[derive(Debug)]
pub enum Error {
    /// Parser error
    Parse(ParseError),
    /// Serializer error
    Serialize(SerializeError),
}

impl std::convert::From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

impl std::convert::From<SerializeError> for Error {
    fn from(e: SerializeError) -> Self {
        Error::Serialize(e)
    }
}

} // verus!
impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ParseError::AndThenUnusedBytes => {
                write!(f, "`AndThen` combinator did not consume all bytes")
            }
            ParseError::BuilderError => write!(f, "Builder combinator failed"),
            ParseError::UnexpectedEndOfInput => write!(f, "Unexpected end of input"),
            ParseError::OrdChoiceNoMatch => {
                write!(f, "`OrdChoice` combinator did not match any of its options")
            }
            ParseError::CondFailed => write!(f, "`Cond` combinator failed"),
            ParseError::SizeOverflow => write!(f, "Arithmetic overflow"),
            ParseError::TryMapFailed => write!(f, "`TryMap` combinator failed"),
            ParseError::RefinedPredicateFailed => {
                write!(f, "`Refined` combinator predicate failed")
            }
            ParseError::RepeatEmptyElement => write!(f, "`Repeat` combinator could not terminate"),
            ParseError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl std::fmt::Display for SerializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SerializeError::InsufficientBuffer => write!(f, "Insufficient buffer"),
            SerializeError::AndThenUnusedBytes => write!(
                f,
                "`AndThen` combinator did not serialize expected number of bytes"
            ),
            SerializeError::CondFailed => write!(f, "`Cond` combinator failed"),
            SerializeError::SizeOverflow => write!(f, "Arithmetic overflow"),
            SerializeError::TryMapFailed => write!(f, "`TryMap` combinator failed"),
            SerializeError::RefinedPredicateFailed => {
                write!(f, "`Refined` combinator predicate failed")
            }
            SerializeError::RepeatEmptyElement => {
                write!(f, "`Repeat` combinator could not terminate")
            }
            SerializeError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl std::error::Error for ParseError {}

impl std::error::Error for SerializeError {}
