//! Value refinement and constant-tag combinators.

/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use crate::core::spec::SpecByteLen;
use vstd::prelude::*;

verus! {

/// Value refinement combinator: filters values through a predicate.
///
/// ## Consistency
///
/// `inner.consistent(v) && pred.apply(v)`.
pub struct Refined<Inner, Pred> {
    /// The inner combinator whose values are being refined.
    pub inner: Inner,
    /// The predicate that parsed values must satisfy.
    pub pred: Pred,
}

/// Constant-tag combinator: matches a specific constant value.
///
/// Parsing semantics: parses with `inner` and succeeds only if the result equals `tag`.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
pub struct Tag<Inner, Tag> {
    /// The inner combinator used to parse/serialize the tag value.
    pub inner: Inner,
    /// The expected constant value.
    pub tag: Tag,
}

/// Sugar for `Preceded(Tag { inner, tag }, body)`.
pub struct Tagged<Tag: SpecByteLen, Of>(pub Tag, pub Tag::T, pub Of);

} // verus!
