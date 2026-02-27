//! Sequential composition discarding the suffix.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Parsing semantics: like `(A, B)`, but discards the value parsed by `B` and returns only the value parsed by `A`.
///
/// Serialization semantics: chooses an arbitrary value `b` consistent with `B`, and delegates to `(A, B)`'s serialization.
///
/// ## Consistency
///
/// `A.consistent(v)` and a consistent value for `B` exists.
///
/// ## Malleability
///
/// This combinator introduces malleability by default: the parser loses information about `B`'s value.
/// `B` must implement [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal) to recover non-malleability.
pub struct Terminated<A, B>(pub A, pub B);

} // verus!
