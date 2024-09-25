pub use crate::utils::*;
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
