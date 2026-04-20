//! Ordered choice combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

pub use spec::Sum;

verus! {

/// Ordered choice combinator consuming/producing a sum type.
///
/// Parsing semantics: tries `A` first, wrapping success in [`Sum::Inl`]; on failure, tries `B`,
/// wrapping success in [`Sum::Inr`].
///
/// ## Consistency
///
/// If a value `a` is consistent with `A`, then `Sum::Inl(a)` is consistent with `Choice(A, B)`.
/// If a value `b` is consistent with `B`, then `Sum::Inr(b)` is consistent with `Choice(A, B)`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
pub struct Choice<A, B>(pub A, pub B);

/// Ordered alternative combinator.
///
/// Parsing semantics: like [`Choice`], but both branches consume/produce the same type.
/// The result is returned directly without a [`Sum`] wrapper.
///
/// Serialization semantics: if only one branch is consistent with a value, that
/// branch is used. If both branches are consistent, serialization is
/// intentionally underspecified and may use either branch.
///
/// ## Consistency
///
/// A value `v` is consistent with `Alt(A, B)` iff it is consistent with `A` OR `B`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
///
/// ## Malleability
///
/// This combinator introduces malleability by default.
/// Non-malleability can be recovered if `A` is [`DisjointFrom`](crate::core::spec::DisjointFrom) `B`.
pub struct Alt<A, B>(pub A, pub B);

/// Dispatch combinator that selects one of `N` branches based on a "tag" value.
pub struct Dispatch<T, C, const N: usize>(pub T, pub [(T, C); N]);

} // verus!
