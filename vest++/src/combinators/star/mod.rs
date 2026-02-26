//! Zero-or-more repetition combinators.

/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Kleene star combinator: greedy zero-or-more repetition, consuming/producing `Seq<A::PVal>`.
///
/// Parsing semantics: always succeeds (may return an empty sequence). Stops when `A` fails or
/// consumes zero bytes.
///
/// ## Consistency
///
/// A sequence `s` is consistent with `Star<A>` iff every element of `s` is consistent with `A`.
///
/// ## Note
///
/// This combinator is mostly used *internally* to specify [`Repeat<A, B>`], which is
/// able to disambiguate `A` and `B` and hence more compositional.
pub struct Star<A> {
    /// The inner combinator to repeat.
    pub inner: A,
}

/// Zero-or-more `A` followed by terminator `B`: sugar for `(Star<A>, B)`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
pub struct Repeat<A, B>(pub A, pub B);

/// Exactly `N` repetitions of combinator `C` (`N` is a runtime value).
pub struct RepeatN<C, N = u8>(pub N, pub C);

/// Exactly `N` repetitions of combinator `C` (`N` is a compile-time constant).
pub struct Array<const N: usize, C>(pub C);

} // verus!
