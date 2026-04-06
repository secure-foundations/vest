//! Bounded fixpoint combinator for recursive formats.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

pub use proof::{
    EquivSerializersGeneralRecBody, NoLookAheadRecBody, NonMalleableRecBody, SPRoundTripDpsRecBody,
    StrictRecBody,
};
pub use spec::{
    BundledSpecs, GoodSerializerRecBody, NonTailFmtRecBody, SafeParserRecBody, SoundParserRecBody,
    SpecRecBody,
};

verus! {

/// Bounded fixpoint combinator: recursive format up to `LIMIT` levels of nesting.
///
/// Parsing semantics: parses with `Body`, which may recursively refer to `Fix` (up to `LIMIT` times).
pub struct Fix<const LIMIT: usize, Body>(pub Body);

} // verus!
