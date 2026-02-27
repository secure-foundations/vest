//! Isomorphic type transformation combinator.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Isomorphic format transformation combinator.
///
/// `Mapped { inner, mapper }` applies a bijective mapping to transform the inner
/// combinator's value type. The binary format is identical to `inner`'s.
///
/// Consistency, byte length, unambiguity, and non-malleability are all inherited
/// from `inner` (through the bijection).
pub struct Mapped<Inner, M> {
    /// The inner combinator whose values are being transformed.
    pub inner: Inner,
    /// The bijective mapping between the inner and outer value types.
    pub mapper: M,
}

} // verus!
