// pub use crate::utils::*;
use vstd::prelude::*;
use vstd::*;

verus! {

/// Parser errors
#[derive(Debug)]
pub enum ParseError {
    /// The second combinator of AndThen did not consume all bytes
    AndThenUnusedBytes,
    UnexpectedEndOfInput,
    OrdChoiceNoMatch,
    CondFailed,
    TryMapFailed,
    RefinedPredicateFailed,
    Other(String),
}

/// Serializer errors
#[derive(Debug)]
pub enum SerializeError {
    InsufficientBuffer,
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

impl vstd::std_specs::convert::FromSpecImpl<ParseError> for Error {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

impl vstd::std_specs::convert::FromSpecImpl<SerializeError> for Error {
    open spec fn obeys_from_spec() -> bool {
        true
    }

    open spec fn from_spec(e: SerializeError) -> Self {
        Error::Serialize(e)
    }
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
            ParseError::UnexpectedEndOfInput => write!(f, "Unexpected end of input"),
            ParseError::OrdChoiceNoMatch => {
                write!(f, "`OrdChoice` combinator did not match any of its options")
            }
            ParseError::CondFailed => write!(f, "`Cond` combinator failed"),
            ParseError::TryMapFailed => write!(f, "`TryMap` combinator failed"),
            ParseError::RefinedPredicateFailed => {
                write!(f, "`Refined` combinator predicate failed")
            }
            ParseError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl std::fmt::Display for SerializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SerializeError::InsufficientBuffer => write!(f, "Insufficient buffer"),
            SerializeError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl std::error::Error for ParseError {}

impl std::error::Error for SerializeError {}
