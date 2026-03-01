//! Sequential composition for pairs.
//! N-ary formats are built by nesting: `Pair(A, Pair(B, C))`.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Sequential composition of formats `A` and `B`.
pub struct Pair<A, B>(pub A, pub B);

} // verus!
