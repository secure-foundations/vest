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
    DependFstNotPrefixSecure,
    PairFstNotPrefixSecure,
    PrecededFstNotPrefixSecure,
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
    DependFstNotPrefixSecure,
    PairFstNotPrefixSecure,
    PrecededFstNotPrefixSecure,
    SizeOverflow,
    TryMapFailed,
    RefinedPredicateFailed,
    RepeatEmptyElement,
    Other(String),
}

}
