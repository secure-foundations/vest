//! Sequential composition discarding the prefix.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::combinators::{Mapped, Pair};
use crate::core::spec::Consistency;
use core::marker::PhantomData;
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

pub struct PrecededMapper<A, VA, VB>(pub A, pub PhantomData<(VA, VB)>);

pub open spec fn preceded_fmt<A, B, VA, VB>(
    prefix: A,
    body: B,
) -> Mapped<Pair<A, B>, PrecededMapper<A, VA, VB>>
{
    Mapped { inner: Pair(prefix, body), mapper: PrecededMapper(prefix, PhantomData) }
}

} // verus!
