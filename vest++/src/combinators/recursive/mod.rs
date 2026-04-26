//! Bounded fixpoint combinator for recursive formats.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::proof::LeafNonMalleable;
use crate::core::proof::StrictCombinator;
use vstd::prelude::*;

pub use exec::{ParserRecBody, SerializerRecBody};
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

impl<const N: usize, Body: StrictRecBody> LeafNonMalleable for Fix<N, Body> where
    Body::Body: StrictCombinator,
 {
    proof fn nonmal_leaf_inv(&self) {
    }
}

} // verus!
