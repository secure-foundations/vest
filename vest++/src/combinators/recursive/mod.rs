//! Bounded fixpoint combinator for recursive formats.
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

pub use spec::{
    EquivSerializersGeneralRecBody, GoodSerializerRecBody, NoLookAheadRecBody, NonMalleableRecBody,
    NonTailFmtRecBody, SPRoundTripDpsRecBody, SoundParserRecBody, SpecRecBody,
};

verus! {

/// Bounded fixpoint combinator: recursive format up to `LIMIT` levels of nesting.
///
/// Parsing semantics: parses with `Body`, which may recursively refer to `Fix` (up to `LIMIT` times).
pub struct Fix<const LIMIT: usize, Body>(pub Body);

} // verus!
