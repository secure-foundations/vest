//! Sequential composition discarding the suffix.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::combinators::{Mapped, Pair};
use crate::core::spec::Consistency;
use core::marker::PhantomData;
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

pub struct TerminatedMapper<B, VA, VB>(pub B, pub PhantomData<(VA, VB)>);

pub open spec fn terminated_fmt<A, B, VA, VB>(
    head: A,
    tail: B,
) -> Mapped<Pair<A, B>, TerminatedMapper<B, VA, VB>>
{
    Mapped { inner: Pair(head, tail), mapper: TerminatedMapper(tail, PhantomData) }
}

} // verus!
