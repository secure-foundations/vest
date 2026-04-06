//! Combinators for parsing permutations of sub-parsers.
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
pub struct Permute2<P1, P2>(pub P1, pub P2);

/// `Permute3<A, B, C>` parses any permutation of A, B, C and produces `(A::PVal, (B::PVal, C::PVal))`
///
/// ```
/// Permute3(A, B, C) ::= Alt(
///     (A, Permute2(B, C)),
///     Alt(
///         Mapped((B, Permute2(A, C)), swap2),
///         Mapped((C, Permute2(A, B)), swap3),
///     )
/// )
/// ```
pub struct Permute3<A, B, C>(pub A, pub B, pub C);

/// `Permute4<A, B, C, D>` parses any permutation and produces `(A::PVal, (B::PVal, (C::PVal, D::PVal)))`
///
/// ```
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
pub struct Permute4<A, B, C, D>(pub A, pub B, pub C, pub D);

} // verus!
