//! Zero-or-more repetition combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
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
#[derive(Copy)]
pub struct Star<A>(pub A);

impl<A: Clone> Clone for Star<A> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
    {
        Star(self.0.clone())
    }
}

/// Zero-or-more `A` followed by terminator `B`: sugar for `Pair(Star<A>, B)`.
///
/// ## Unambiguity
///
/// Requires `disjoint_domains(A, B)`.
#[derive(Copy)]
pub struct Repeat<A, B>(pub A, pub B);

impl<A: Clone, B: Clone> Clone for Repeat<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
    {
        Repeat(self.0.clone(), self.1.clone())
    }
}

/// Exactly `N` repetitions of combinator `C` (`N` is a runtime value).
#[derive(Copy)]
pub struct RepeatN<C, N = u8>(pub N, pub C);

impl<C: Clone, N: Clone> Clone for RepeatN<C, N> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(N::clone, (&self.0,), cloned.0),
            call_ensures(C::clone, (&self.1,), cloned.1),
    {
        RepeatN(self.0.clone(), self.1.clone())
    }
}

/// Exactly `N` repetitions of combinator `C` (`N` is a compile-time constant).
#[derive(Copy)]
pub struct Array<const N: usize, C>(pub C);

impl<const N: usize, C: Clone> Clone for Array<N, C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(C::clone, (&self.0,), cloned.0),
    {
        Array(self.0.clone())
    }
}

} // verus!
