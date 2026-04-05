//! Type transformation combinator.
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// `Mapped { inner, mapper }` transforms the inner combinator's value type.
///
/// Lossless mappers preserve all format properties including parser soundness and non-malleability, while lossy mappers may introduce malleability.
pub struct Mapped<Inner, M> {
    /// The inner combinator whose values are being transformed.
    pub inner: Inner,
    /// The mapping between the inner and outer value types.
    pub mapper: M,
}

} // verus!
