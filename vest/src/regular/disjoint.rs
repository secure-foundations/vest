use super::bytes::Bytes;
use super::bytes_n::BytesN;
use super::choice::OrdChoice;
use super::cond::Cond;
use super::depend::SpecDepend;
use super::fail::Fail;
use super::map::{Mapped, SpecIso};
use super::preceded::Preceded;
use super::refined::Refined;
use super::tag::{Tag, TagPred};
use super::uints::*;
use crate::properties::*;
use vstd::prelude::*;

verus! {

/// A helper trait for [`OrdChoice`] combinator.
pub trait DisjointFrom<'a, Other> where Self: SpecCombinator<'a>, Other: SpecCombinator<'a> {
    /// pre-condition that must be held for [`Self`] and [`Other`] to be disjoint
    spec fn disjoint_from(&self, other: &Other) -> bool;

    /// The combinator [`Self`] is disjoint from the combinator [`Other`] if the bytes `buf` can be
    /// parsed by [`Self`] but not by [`Other`]
    proof fn parse_disjoint_on(&self, other: &Other, buf: Seq<u8>)
        requires
            self.disjoint_from(
                other,
            ),
    // just one direction is enough for the proofs of `OrdChoice`

        ensures
            self.spec_parse(buf).is_ok() ==> other.spec_parse(buf).is_err(),
    ;
}

macro_rules! impl_disjoint_for_int_tag {
    ($combinator:ty) => {
        ::builtin_macros::verus! {
            impl DisjointFrom<'_, $combinator> for $combinator {
                // two `Tag(T, value)`s are disjoint if their bytes `value`s are different
                open spec fn disjoint_from(&self, other: &$combinator) -> bool {
                    self.0.predicate.0 != other.0.predicate.0
                }

                proof fn parse_disjoint_on(&self, other: &$combinator, buf: Seq<u8>) {
                }
            }
        }
    };
}

macro_rules! impl_disjoint_for_refined_int {
    ($combinator:ty) => {
        ::builtin_macros::verus! {
            impl DisjointFrom<'_, $combinator> for $combinator {
                // two `Tag(T, value)`s are disjoint if their bytes `value`s are different
                open spec fn disjoint_from(&self, other: &$combinator) -> bool {
                    self.predicate.0 != other.predicate.0
                }

                proof fn parse_disjoint_on(&self, other: &$combinator, buf: Seq<u8>) {
                }
            }
        }
    };
}

impl_disjoint_for_int_tag!(Tag<U8, u8>);

impl_disjoint_for_int_tag!(Tag<U16Le, u16>);

impl_disjoint_for_int_tag!(Tag<U24Le, u24>);

impl_disjoint_for_int_tag!(Tag<U32Le, u32>);

impl_disjoint_for_int_tag!(Tag<U64Le, u64>);

impl_disjoint_for_int_tag!(Tag<U16Be, u16>);

impl_disjoint_for_int_tag!(Tag<U24Be, u24>);

impl_disjoint_for_int_tag!(Tag<U32Be, u32>);

impl_disjoint_for_int_tag!(Tag<U64Be, u64>);

impl_disjoint_for_refined_int!(Refined<U8, TagPred<u8>>);

impl_disjoint_for_refined_int!(Refined<U16Le, TagPred<u16>>);

impl_disjoint_for_refined_int!(Refined<U24Le, TagPred<u24>>);

impl_disjoint_for_refined_int!(Refined<U32Le, TagPred<u32>>);

impl_disjoint_for_refined_int!(Refined<U64Le, TagPred<u64>>);

impl_disjoint_for_refined_int!(Refined<U16Be, TagPred<u16>>);

impl_disjoint_for_refined_int!(Refined<U24Be, TagPred<u24>>);

impl_disjoint_for_refined_int!(Refined<U32Be, TagPred<u32>>);

impl_disjoint_for_refined_int!(Refined<U64Be, TagPred<u64>>);

// two `Tag(T, value)`s are disjoint if their bytes `value`s are different
impl<const N: usize> DisjointFrom<'_, Tag<BytesN<N>, Seq<u8>>> for Tag<BytesN<N>, Seq<u8>> {
    open spec fn disjoint_from(&self, other: &Tag<BytesN<N>, Seq<u8>>) -> bool {
        self.0.predicate.0 != other.0.predicate.0
    }

    proof fn parse_disjoint_on(&self, other: &Tag<BytesN<N>, Seq<u8>>, buf: Seq<u8>) {
    }
}

// two `Tag(T, value)`s are disjoint if their bytes `value`s are different
impl DisjointFrom<'_, Tag<Bytes, Seq<u8>>> for Tag<Bytes, Seq<u8>> {
    open spec fn disjoint_from(&self, other: &Tag<Bytes, Seq<u8>>) -> bool {
        // must also say that two `Bytes` combinators are of the same length
        self.0.predicate.0 != other.0.predicate.0 && self.0.inner.0 == other.0.inner.0
    }

    proof fn parse_disjoint_on(&self, other: &Tag<Bytes, Seq<u8>>, buf: Seq<u8>) {
    }
}

impl<const N: usize> DisjointFrom<'_, Refined<BytesN<N>, TagPred<Seq<u8>>>> for Refined<
    BytesN<N>,
    TagPred<Seq<u8>>,
> {
    open spec fn disjoint_from(&self, other: &Refined<BytesN<N>, TagPred<Seq<u8>>>) -> bool {
        self.predicate.0 != other.predicate.0
    }

    proof fn parse_disjoint_on(&self, other: &Refined<BytesN<N>, TagPred<Seq<u8>>>, buf: Seq<u8>) {
    }
}

impl DisjointFrom<'_, Refined<Bytes, TagPred<Seq<u8>>>> for Refined<Bytes, TagPred<Seq<u8>>> {
    open spec fn disjoint_from(&self, other: &Refined<Bytes, TagPred<Seq<u8>>>) -> bool {
        self.predicate.0 != other.predicate.0 && self.inner.0 == other.inner.0
    }

    proof fn parse_disjoint_on(&self, other: &Refined<Bytes, TagPred<Seq<u8>>>, buf: Seq<u8>) {
    }
}

// if `U1` and `U2` are disjoint, then `(U1, V1)` and `(U2, V2)` are disjoint
impl<'a, U1, U2, V1, V2> DisjointFrom<'a, (U2, V2)> for (U1, V1) where
    U1: DisjointFrom<'a, U2>,
    U1: SecureSpecCombinator<'a>,
    U2: SecureSpecCombinator<'a>,
    V1: SpecCombinator<'a>,
    V2: SpecCombinator<'a>,
 {
    open spec fn disjoint_from(&self, other: &(U2, V2)) -> bool {
        self.0.disjoint_from(&other.0)
    }

    proof fn parse_disjoint_on(&self, other: &(U2, V2), buf: Seq<u8>) {
        self.0.parse_disjoint_on(&other.0, buf)
    }
}

// if `U1` and `U2` are disjoint, then `preceded(U1, V1)` and `preceded(U2, V2)` are disjoint
impl<'a, U1, U2, V1, V2> DisjointFrom<'a, Preceded<U2, V2>> for Preceded<U1, V1> where
    U1: DisjointFrom<'a, U2>,
    U1: SecureSpecCombinator<'a, SpecResult = ()>,
    U2: SecureSpecCombinator<'a, SpecResult = ()>,
    V1: SpecCombinator<'a>,
    V2: SpecCombinator<'a>,
 {
    open spec fn disjoint_from(&self, other: &Preceded<U2, V2>) -> bool {
        self.0.disjoint_from(&other.0)
    }

    proof fn parse_disjoint_on(&self, other: &Preceded<U2, V2>, buf: Seq<u8>) {
        self.0.parse_disjoint_on(&other.0, buf)
    }
}

impl<'a, U1, U2, V1, V2> DisjointFrom<'a, SpecDepend<U2, V2, U2::SpecResult>> for SpecDepend<
    U1,
    V1,
    U1::SpecResult,
> where
    U1: DisjointFrom<'a, U2>,
    U1: SecureSpecCombinator<'a>,
    U2: SecureSpecCombinator<'a>,
    V1: SpecCombinator<'a>,
    V2: SpecCombinator<'a>,
 {
    open spec fn disjoint_from(&self, other: &SpecDepend<U2, V2, U2::SpecResult>) -> bool {
        self.fst.disjoint_from(&other.fst)
    }

    proof fn parse_disjoint_on(&self, other: &SpecDepend<U2, V2, U2::SpecResult>, buf: Seq<u8>) {
        self.fst.parse_disjoint_on(&other.fst, buf)
    }
}

// if `S1` and `S2` are both disjoint from `S3`, and `S2` is disjoint from `S1`,
// then `OrdChoice<S1, S2>` is disjoint from `S3`,
//
// this allows composition of the form `OrdChoice(..., OrdChoice(..., OrcChoice(...)))`
impl<'a, S1, S2, S3> DisjointFrom<'a, S3> for OrdChoice<S1, S2> where
    S1: SpecCombinator<'a> + DisjointFrom<'a, S3>,
    S2: SpecCombinator<'a> + DisjointFrom<'a, S1> + DisjointFrom<'a, S3>,
    S3: SpecCombinator<'a>,
 {
    open spec fn disjoint_from(&self, other: &S3) -> bool {
        self.0.disjoint_from(other) && self.1.disjoint_from(other)
    }

    proof fn parse_disjoint_on(&self, other: &S3, buf: Seq<u8>) {
        self.0.parse_disjoint_on(other, buf);
        self.1.parse_disjoint_on(other, buf);
    }
}

impl<'a, U1, U2, M1, M2> DisjointFrom<'a, Mapped<U2, M2>> for Mapped<U1, M1> where
    U1: DisjointFrom<'a, U2>,
    U2: SpecCombinator<'a>,
    M1: SpecIso<'a, Src = U1::SpecResult>,
    M2: SpecIso<'a, Src = U2::SpecResult>,
    U1::SpecResult: SpecFrom<M1::Dst>,
    U2::SpecResult: SpecFrom<M2::Dst>,
    M1::Dst: SpecFrom<U1::SpecResult>,
    M2::Dst: SpecFrom<U2::SpecResult>,
 {
    open spec fn disjoint_from(&self, other: &Mapped<U2, M2>) -> bool {
        self.inner.disjoint_from(&other.inner)
    }

    proof fn parse_disjoint_on(&self, other: &Mapped<U2, M2>, buf: Seq<u8>) {
        self.inner.parse_disjoint_on(&other.inner, buf)
    }
}

// if `self.cond` implies `!other.cond`, then `self` is disjoint from `other`
impl<'a, Inner1, Inner2> DisjointFrom<'a, Cond<Inner2>> for Cond<Inner1> where
    Inner1: SpecCombinator<'a>,
    Inner2: SpecCombinator<'a>,
 {
    open spec fn disjoint_from(&self, other: &Cond<Inner2>) -> bool {
        self.cond ==> !other.cond
    }

    proof fn parse_disjoint_on(&self, other: &Cond<Inner2>, buf: Seq<u8>) {
    }
}

impl<'spec, 'a, 'b, T1, T2> DisjointFrom<'spec, &'a T1> for &'b T2 where
    T1: SpecCombinator<'spec>,
    T2: SpecCombinator<'spec> + DisjointFrom<'spec, T1>,
 {
    open spec fn disjoint_from(&self, other: &&T1) -> bool {
        (*self).disjoint_from(*other)
    }

    proof fn parse_disjoint_on(&self, other: &&T1, buf: Seq<u8>) {
        (*self).parse_disjoint_on(*other, buf)
    }
}

// `[Fail]` is disjoint from any other combinator
impl<'a, T> DisjointFrom<'a, T> for Fail where T: SpecCombinator<'a> {
    open spec fn disjoint_from(&self, c: &T) -> bool {
        true
    }

    proof fn parse_disjoint_on(&self, c: &T, buf: Seq<u8>) {
    }
}

} // verus!
