use super::fail::Fail;
use super::modifier::{Cond, Mapped, Refined, SpecIso, SpecPartialIsoFn, SpecPred, TryMap};
use super::sequence::{Preceded, SpecPair};
use super::tag::Tag;
use super::variant::Choice;
use crate::properties::*;
use crate::regular::end::End;
use vstd::prelude::*;

verus! {

/// A helper trait for [`Choice`] combinator.
pub trait DisjointFrom<Other> where Self: SpecCombinator, Other: SpecCombinator {
    /// pre-condition that must be held for [`Self`] and [`Other`] to be disjoint
    spec fn disjoint_from(&self, other: &Other) -> bool;

    /// The combinator [`Self`] is disjoint from the combinator [`Other`] if the bytes `buf` can be
    /// parsed by [`Self`] but not by [`Other`]
    proof fn parse_disjoint_on(&self, other: &Other, buf: Seq<u8>)
        requires
            self.disjoint_from(
                other,
            ),
    // just one direction is enough for the proofs of `Choice`

        ensures
            self.spec_parse(buf) is Some ==> other.spec_parse(buf) is None,
    ;
}

// two `Tag(T, value)`s are disjoint if their inner `Refined` combinators are disjoint
impl<Inner, T> DisjointFrom<Tag<Inner, T>> for Tag<Inner, T> where Inner: SpecCombinator<Type = T> {
    open spec fn disjoint_from(&self, other: &Tag<Inner, T>) -> bool {
        self.0.disjoint_from(&other.0)
    }

    proof fn parse_disjoint_on(&self, other: &Tag<Inner, T>, buf: Seq<u8>) {
    }
}

// if `U1` and `U2` are disjoint, then `(U1, V1)` and `(U2, V2)` are disjoint
impl<U1, U2, V1, V2> DisjointFrom<(U2, V2)> for (U1, V1) where
    U1: DisjointFrom<U2>,
    U1: SecureSpecCombinator,
    U2: SecureSpecCombinator,
    V1: SpecCombinator,
    V2: SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &(U2, V2)) -> bool {
        self.0.disjoint_from(&other.0)
    }

    proof fn parse_disjoint_on(&self, other: &(U2, V2), buf: Seq<u8>) {
        self.0.parse_disjoint_on(&other.0, buf)
    }
}

// if `U1` and `U2` are disjoint, then `preceded(U1, V1)` and `preceded(U2, V2)` are disjoint
impl<U1, U2, V1, V2> DisjointFrom<Preceded<U2, V2>> for Preceded<U1, V1> where
    U1: DisjointFrom<U2>,
    U1: SecureSpecCombinator<Type = ()>,
    U2: SecureSpecCombinator<Type = ()>,
    V1: SpecCombinator,
    V2: SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &Preceded<U2, V2>) -> bool {
        self.0.disjoint_from(&other.0)
    }

    proof fn parse_disjoint_on(&self, other: &Preceded<U2, V2>, buf: Seq<u8>) {
        self.0.parse_disjoint_on(&other.0, buf)
    }
}

impl<U1, U2, V1, V2> DisjointFrom<SpecPair<U2, V2>> for SpecPair<U1, V1> where
    U1: DisjointFrom<U2>,
    U1: SecureSpecCombinator,
    U2: SecureSpecCombinator,
    V1: SpecCombinator,
    V2: SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &SpecPair<U2, V2>) -> bool {
        self.fst.disjoint_from(&other.fst)
    }

    proof fn parse_disjoint_on(&self, other: &SpecPair<U2, V2>, buf: Seq<u8>) {
        self.fst.parse_disjoint_on(&other.fst, buf)
    }
}

// if `S1` and `S2` are both disjoint from `S3`, and `S2` is disjoint from `S1`,
// then `Choice<S1, S2>` is disjoint from `S3`,
//
// this allows composition of the form `Choice(..., Choice(..., OrcChoice(...)))`
impl<S1, S2, S3> DisjointFrom<S3> for Choice<S1, S2> where
    S1: SpecCombinator + DisjointFrom<S3>,
    S2: SpecCombinator + DisjointFrom<S1> + DisjointFrom<S3>,
    S3: SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &S3) -> bool {
        self.0.disjoint_from(other) && self.1.disjoint_from(other)
    }

    proof fn parse_disjoint_on(&self, other: &S3, buf: Seq<u8>) {
        self.0.parse_disjoint_on(other, buf);
        self.1.parse_disjoint_on(other, buf);
    }
}

impl<U1, U2, M1, M2> DisjointFrom<Mapped<U2, M2>> for Mapped<U1, M1> where
    U1: DisjointFrom<U2>,
    U2: SpecCombinator,
    M1: SpecIso<Src = U1::Type>,
    M2: SpecIso<Src = U2::Type>,
    U1::Type: SpecFrom<M1::Dst>,
    U2::Type: SpecFrom<M2::Dst>,
    M1::Dst: SpecFrom<U1::Type>,
    M2::Dst: SpecFrom<U2::Type>,
 {
    open spec fn disjoint_from(&self, other: &Mapped<U2, M2>) -> bool {
        self.inner.disjoint_from(&other.inner)
    }

    proof fn parse_disjoint_on(&self, other: &Mapped<U2, M2>, buf: Seq<u8>) {
        self.inner.parse_disjoint_on(&other.inner, buf)
    }
}

// if `U` succeeds on `M1` implies `U` fails on `M2`, then `TryMap<U, M1>` is disjoint from
// `TryMap<U, M2>`
impl<U, M1, M2> DisjointFrom<TryMap<U, M2>> for TryMap<U, M1> where
    U: SpecCombinator,
    M1: SpecPartialIsoFn<Src = U::Type>,
    M2: SpecPartialIsoFn<Src = U::Type>,
    U::Type: SpecTryFrom<M1::Dst>,
    U::Type: SpecTryFrom<M2::Dst>,
    M1::Dst: SpecTryFrom<U::Type>,
    M2::Dst: SpecTryFrom<U::Type>,
 {
    open spec fn disjoint_from(&self, other: &TryMap<U, M2>) -> bool {
        self.inner == other.inner && forall|t|
            {
                <M1 as SpecPartialIsoFn>::spec_apply(t) is Ok
                    ==> <M2 as SpecPartialIsoFn>::spec_apply(t) is Err
            }
    }

    proof fn parse_disjoint_on(&self, other: &TryMap<U, M2>, buf: Seq<u8>) {
    }
}

// if `self.cond` implies `!other.cond`, then `self` is disjoint from `other`
impl<Inner1, Inner2> DisjointFrom<Cond<Inner2>> for Cond<Inner1> where
    Inner1: SpecCombinator,
    Inner2: SpecCombinator,
 {
    open spec fn disjoint_from(&self, other: &Cond<Inner2>) -> bool {
        self.cond ==> !other.cond
    }

    proof fn parse_disjoint_on(&self, other: &Cond<Inner2>, buf: Seq<u8>) {
    }
}

// if the inner combinator is the same, and whenever `self.predicate` succeeds, `other.predicate`
// fails, then `self` is disjoint from `other`
impl<Inner, P1, P2> DisjointFrom<Refined<Inner, P2>> for Refined<Inner, P1> where
    Inner: SpecCombinator,
    P1: SpecPred<Inner::Type>,
    P2: SpecPred<Inner::Type>,
 {
    open spec fn disjoint_from(&self, other: &Refined<Inner, P2>) -> bool {
        self.inner == other.inner && forall|i|
            { self.predicate.spec_apply(&i) ==> !other.predicate.spec_apply(&i) }
    }

    proof fn parse_disjoint_on(&self, other: &Refined<Inner, P2>, buf: Seq<u8>) {
    }
}

impl<'a, 'b, T1, T2> DisjointFrom<&'a T1> for &'b T2 where
    T1: SpecCombinator,
    T2: SpecCombinator + DisjointFrom<T1>,
 {
    open spec fn disjoint_from(&self, other: &&T1) -> bool {
        (*self).disjoint_from(*other)
    }

    proof fn parse_disjoint_on(&self, other: &&T1, buf: Seq<u8>) {
        (*self).parse_disjoint_on(*other, buf)
    }
}

// `[Fail]` is disjoint from any other combinator
impl<T> DisjointFrom<T> for Fail where T: SpecCombinator {
    open spec fn disjoint_from(&self, c: &T) -> bool {
        true
    }

    proof fn parse_disjoint_on(&self, c: &T, buf: Seq<u8>) {
    }
}

impl<T> DisjointFrom<T> for End where T: SecureSpecCombinator {
    open spec fn disjoint_from(&self, c: &T) -> bool {
        c.requires() && c.is_productive()
    }

    proof fn parse_disjoint_on(&self, c: &T, buf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(buf) {
            assert(n == 0);
            c.lemma_parse_productive(buf);
            c.lemma_parse_length(buf);
        }
    }
}

} // verus!
