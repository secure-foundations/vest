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

/// `TryMap { inner, mapper }` is the derived combinator
/// `Mapped { inner: Refined { inner, pred: M::wf_in }, mapper }`.
///
/// Parsing fails when the parsed inner value does not satisfy `M::wf_in`.
/// Serialization maps values back with `M::spec_map_rev`, and consistency
/// requires both `M::wf_out(v)` and that the reverse-mapped inner value is
/// consistent and satisfies `M::wf_in`.
pub struct TryMap<Inner, M> {
    /// The inner combinator whose values are being transformed.
    pub inner: Inner,
    /// The mapping between the inner and outer value types.
    pub mapper: M,
}

} // verus!
