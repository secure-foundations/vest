//! Semantic type transformations over structural combinator values.
//!
//! [`Mapped`] supports lossy and lossless mappings with separate proof conditions.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// `Mapped { inner, mapper }` transforms the inner combinator's value type.
///
/// Lossless mappers preserve all format properties including parser soundness and non-malleability, while lossy mappers may introduce malleability.
#[derive(Copy)]
pub struct Mapped<Inner, M> {
    /// The inner combinator whose values are being transformed.
    pub inner: Inner,
    /// The mapping between the inner and outer value types.
    pub mapper: M,
}

impl<Inner: Clone, M: Clone> Clone for Mapped<Inner, M> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.inner,), cloned.inner),
            call_ensures(M::clone, (&self.mapper,), cloned.mapper),
    {
        Mapped { inner: self.inner.clone(), mapper: self.mapper.clone() }
    }
}

} // verus!
