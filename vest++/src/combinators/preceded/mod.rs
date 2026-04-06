//! Sequential composition discarding the prefix.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Parsing semantics: like `(A, B)`, but discards the value parsed by `A` and returns only the value parsed by `B`.
///
/// Serialization semantics: chooses an arbitrary value `a` consistent with `A`, and delegates to `(A, B)`'s serialization.
///
/// ## Consistency
///
/// `B.consistent(v)` and a consistent value for `A` exists.
///
/// ## Malleability
///
/// This combinator introduces malleability by default: the parser loses information about `A`'s value.
/// `A` must implement [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal) to recover non-malleability.
pub struct Preceded<A, B>(pub A, pub B);

} // verus!
