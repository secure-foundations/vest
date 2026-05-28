//! Combinators for parsing permutations of sub-parsers.
/// Executable serializer-preparation implementations for this combinator.
pub mod exec;
/// Specification trait implementations for this combinator.
pub mod spec;

use vstd::prelude::*;

use crate::combinators::choice::Alt;
use crate::combinators::Mapped;

verus! {

pub open spec fn swap2<A, B>(i: (B, A)) -> (A, B) {
    (i.1, i.0)
}

pub open spec fn unswap2<A, B>(o: (A, B)) -> (B, A) {
    (o.1, o.0)
}

pub open spec fn swap3_1<A, B, C>(i: (B, (A, C))) -> (A, (B, C)) {
    (i.1.0, (i.0, i.1.1))
}

pub open spec fn unswap3_1<A, B, C>(o: (A, (B, C))) -> (B, (A, C)) {
    (o.1.0, (o.0, o.1.1))
}

pub open spec fn swap3_2<A, B, C>(i: (C, (A, B))) -> (A, (B, C)) {
    (i.1.0, (i.1.1, i.0))
}

pub open spec fn unswap3_2<A, B, C>(o: (A, (B, C))) -> (C, (A, B)) {
    (o.1.1, (o.0, o.1.0))
}

pub open spec fn swap4_1<A, B, C, D>(i: (B, (A, (C, D)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.0, i.1.1))
}

pub open spec fn unswap4_1<A, B, C, D>(o: (A, (B, (C, D)))) -> (B, (A, (C, D))) {
    (o.1.0, (o.0, o.1.1))
}

pub open spec fn swap4_2<A, B, C, D>(i: (C, (A, (B, D)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.1.1.0, (i.0, i.1.1.1)))
}

pub open spec fn unswap4_2<A, B, C, D>(o: (A, (B, (C, D)))) -> (C, (A, (B, D))) {
    (o.1.1.0, (o.0, (o.1.0, o.1.1.1)))
}

pub open spec fn swap4_3<A, B, C, D>(i: (D, (A, (B, C)))) -> (A, (B, (C, D))) {
    (i.1.0, (i.1.1.0, (i.1.1.1, i.0)))
}

pub open spec fn unswap4_3<A, B, C, D>(o: (A, (B, (C, D)))) -> (D, (A, (B, C))) {
    (o.1.1.1, (o.0, (o.1.0, o.1.1.0)))
}

/// `Permute2<P1, P2>` parses either `(P1, P2)` or `(P2, P1)` and produces `(P1::PVal, P2::PVal)`
///
/// `Permute2 ::= Alt((P1, P2), Mapped((P2, P1), swap))`
#[derive(Copy)]
pub struct Permute2<P1, P2>(pub P1, pub P2);

impl<P1: Clone, P2: Clone> Clone for Permute2<P1, P2> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(P1::clone, (&self.0,), cloned.0),
            call_ensures(P2::clone, (&self.1,), cloned.1),
    {
        Permute2(self.0.clone(), self.1.clone())
    }
}

/// `Permute3<A, B, C>` parses any permutation of A, B, C and produces `(A::PVal, (B::PVal, C::PVal))`
///
/// ```text
/// Permute3(A, B, C) ::= Alt(
///     (A, Permute2(B, C)),
///     Alt(
///         Mapped((B, Permute2(A, C)), swap2),
///         Mapped((C, Permute2(A, B)), swap3),
///     )
/// )
/// ```
#[derive(Copy)]
pub struct Permute3<A, B, C>(pub A, pub B, pub C);

impl<A: Clone, B: Clone, C: Clone> Clone for Permute3<A, B, C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
            call_ensures(C::clone, (&self.2,), cloned.2),
    {
        Permute3(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

/// `Permute4<A, B, C, D>` parses any permutation and produces `(A::PVal, (B::PVal, (C::PVal, D::PVal)))`
///
/// ```text
/// Permute4(A, B, C, D) ::= Alt(
///     (A, Permute3(B, C, D)),
///     Alt(
///         Mapped((B, Permute3(A, C, D)), swap4_1),
///         Alt(
///             Mapped((C, Permute3(A, B, D)), swap4_2),
///             Mapped((D, Permute3(A, B, C)), swap4_3),
///         )
///     )
/// )
/// ```
#[derive(Copy)]
pub struct Permute4<A, B, C, D>(pub A, pub B, pub C, pub D);

impl<A: Clone, B: Clone, C: Clone, D: Clone> Clone for Permute4<A, B, C, D> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(A::clone, (&self.0,), cloned.0),
            call_ensures(B::clone, (&self.1,), cloned.1),
            call_ensures(C::clone, (&self.2,), cloned.2),
            call_ensures(D::clone, (&self.3,), cloned.3),
    {
        Permute4(self.0.clone(), self.1.clone(), self.2.clone(), self.3.clone())
    }
}

} // verus!
