//! Semantic type transformations over structural combinator values.
//!
//! [`Mapped`] carries full round trips when its mapper is lossless and sound;
//! [`TryMap`] also admits a fallible executable conversion.
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

/// `TryMap { inner, mapper }` is the derived combinator
/// `Mapped { inner: Refined(inner, |v| mapper.wf_in(v)), mapper }`.
///
/// Parsing fails when the parsed inner value does not satisfy `mapper.wf_in`.
/// Serialization maps values back with `mapper.spec_map_rev`, and consistency
/// requires both `mapper.wf_out(v)` and that the reverse-mapped inner value is
/// consistent and satisfies `mapper.wf_in`.
#[derive(Copy)]
pub struct TryMap<Inner, M> {
    /// The inner combinator whose values are being transformed.
    pub inner: Inner,
    /// The mapping between the inner and outer value types.
    pub mapper: M,
}

impl<Inner: Clone, M: Clone> Clone for TryMap<Inner, M> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Inner::clone, (&self.inner,), cloned.inner),
            call_ensures(M::clone, (&self.mapper,), cloned.mapper),
    {
        TryMap { inner: self.inner.clone(), mapper: self.mapper.clone() }
    }
}

} // verus!
