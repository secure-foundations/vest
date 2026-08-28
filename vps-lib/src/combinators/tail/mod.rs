//! Tail-position combinators.
/// Executable trait implementations for this combinator.
pub mod exec;
/// Correctness proofs for this combinator.
pub mod proof;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

verus! {

/// Tail combinator: denotes the "tail" of the format, useful for under-specification.
///
/// Parsing semantics: consumes and return all remaining bytes (even if the input is empty).
///
/// ## Note
///
/// The DPS serialization replaces (not prepends to) the output buffer,
/// so `Tail` should only appear at the end of a format (and the trait system enforces this).
#[derive(Clone, Copy)]
pub struct Tail;

/// End-of-file combinator: denotes the "EOF".
///
/// Parsing semantics: succeeds only if the input is empty, producing `()`.
///
/// Implements [`AdmitsUniqueVal`](crate::core::spec::AdmitsUniqueVal).
///
/// ## Note
///
/// The DPS serialization always replaces the output buffer with the empty sequence, so `Eof`
/// should only appear at the end of a format (and the trait system enforces this).
#[derive(Clone, Copy)]
pub struct Eof;

/// Sequential composition of formats `A` and `B`, where the direction of parsing is reversed compared to [`super::Pair`].
///
/// Parsing semantics: parses `B` from the back, consumes the tail part of the input, then parses `A`.
#[derive(Copy)]
pub struct PairRev<A, B>(pub B, pub A);

impl<A: Clone, B: Clone> Clone for PairRev<A, B> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(B::clone, (&self.0,), cloned.0),
            call_ensures(A::clone, (&self.1,), cloned.1),
    {
        PairRev(self.0.clone(), self.1.clone())
    }
}

/// Sugar for `Optional(C, Eof)`.
#[derive(Copy)]
pub struct OptionalEnd<C>(pub C);

impl<C: Clone> Clone for OptionalEnd<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(C::clone, (&self.0,), cloned.0),
    {
        OptionalEnd(self.0.clone())
    }
}

/// Sugar for `Repeat(C, Eof)`.
#[derive(Copy)]
pub struct RepeatTillEnd<C>(pub C);

impl<C: Clone> Clone for RepeatTillEnd<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(C::clone, (&self.0,), cloned.0),
    {
        RepeatTillEnd(self.0.clone())
    }
}

} // verus!
