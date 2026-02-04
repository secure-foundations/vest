// pub use crate::utils::*;
use alloc::string::String;

/// Parser errors
#[derive(Debug)]
pub enum ParseError {
    /// The second combinator of AndThen did not consume all bytes
    AndThenUnusedBytes,
    UnexpectedEndOfInput,
    FixedLenViolation,
    OrdChoiceNoMatch,
    CondFailed,
    TryMapFailed,
    RefinedPredicateFailed,
    NotEof,
    TagMismatch,
    Other(String),
}

/// Serializer errors
#[derive(Debug)]
pub enum SerializeError {
    InsufficientBuffer,
    Other(String),
}

/// Generator errors
#[derive(Debug)]
pub enum GenerateError {
    TooManyRetries,
    CondFailed,
    Other(String),
}

/// Sum of both parse and serialize errors
#[derive(Debug)]
pub enum Error {
    /// Parser error
    Parse(ParseError),
    /// Serializer error
    Serialize(SerializeError),
    /// Generator error
    Generate(GenerateError),
}

impl core::convert::From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

impl core::convert::From<SerializeError> for Error {
    fn from(e: SerializeError) -> Self {
        Error::Serialize(e)
    }
}

impl core::convert::From<GenerateError> for Error {
    fn from(e: GenerateError) -> Self {
        Error::Generate(e)
    }
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            ParseError::AndThenUnusedBytes => {
                write!(f, "`AndThen` combinator did not consume all bytes")
            }
            ParseError::FixedLenViolation => {
                write!(f, "`FixedLen` combinator failed")
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
            ParseError::NotEof => write!(f, "Expected end of input"),
            ParseError::TagMismatch => write!(f, "Tag mismatch"),
            ParseError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl core::fmt::Display for SerializeError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            SerializeError::InsufficientBuffer => write!(f, "Insufficient buffer"),
            SerializeError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl core::fmt::Display for GenerateError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            GenerateError::TooManyRetries => write!(f, "Too many retries during generation"),
            GenerateError::CondFailed => write!(f, "`Cond` combinator failed"),
            GenerateError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl core::error::Error for ParseError {}

impl core::error::Error for SerializeError {}

impl core::error::Error for GenerateError {}
