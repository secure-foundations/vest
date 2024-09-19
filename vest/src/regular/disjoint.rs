use super::bytes::Bytes;
use super::bytes_n::BytesN;
use super::choice::OrdChoice;
use super::cond::Cond;
use super::map::{Iso, Mapped, SpecIso};
use super::preceded::Preceded;
use super::tag::Tag;
use super::uints::{U16, U32, U64, U8};
use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Spec version of [`DisjointFrom`].
pub trait SpecDisjointFrom<Other> where Self: SpecCombinator, Other: SpecCombinator {
    /// pre-condition that must be held for [`Self`] and [`Other`] to be disjoint
    spec fn spec_disjoint_from(&self, other: &Other) -> bool;

    /// The combinator [`Self`] is disjoint from the combinator [`Other`] if the bytes `buf` can be
    /// parsed by [`Self`] but not by [`Other`]
    proof fn spec_parse_disjoint_on(&self, other: &Other, buf: Seq<u8>)
        requires
            self.spec_disjoint_from(
                other,
            ),
    // just one direction is enough for the proofs of `OrdChoice`

        ensures
            self.spec_parse(buf).is_ok() ==> other.spec_parse(buf).is_err(),
    ;
}

macro_rules! impl_spec_disjoint_for_int_type {
    ($combinator:ty) => {
        ::builtin_macros::verus! {
            impl SpecDisjointFrom<$combinator> for $combinator {
                /// two `Tag(T, value)`s are disjoint if their bytes `value`s are different
                open spec fn spec_disjoint_from(&self, other: &$combinator) -> bool {
                    self.0.predicate.0 != other.0.predicate.0
                }

                proof fn spec_parse_disjoint_on(&self, other: &$combinator, buf: Seq<u8>) {
                }
            }
        }
    };
}
impl_spec_disjoint_for_int_type!(Tag<U8, u8>);
impl_spec_disjoint_for_int_type!(Tag<U16, u16>);
impl_spec_disjoint_for_int_type!(Tag<U32, u32>);
impl_spec_disjoint_for_int_type!(Tag<U64, u64>);

// impl<T: FromToBytes> SpecDisjointFrom<Tag<Int<T>, T>> for Tag<Int<T>, T> where
// {
//     open spec fn spec_disjoint_from(&self, other: &Tag<Int<T>, T>) -> bool {
//         self.0.predicate.0 != other.0.predicate.0
//     }
//
//     proof fn spec_parse_disjoint_on(&self, other: &Tag<Int<T>, T>, buf: Seq<u8>) {
//     }
// }

/// two `Tag(T, value)`s are disjoint if their bytes `value`s are different
impl<const N: usize> SpecDisjointFrom<Tag<BytesN<N>, Seq<u8>>> for Tag<BytesN<N>, Seq<u8>> {
    open spec fn spec_disjoint_from(&self, other: &Tag<BytesN<N>, Seq<u8>>) -> bool {
        self.0.predicate.0 != other.0.predicate.0
    }

    proof fn spec_parse_disjoint_on(&self, other: &Tag<BytesN<N>, Seq<u8>>, buf: Seq<u8>) {
    }
}

/// two `Tag(T, value)`s are disjoint if their bytes `value`s are different
impl SpecDisjointFrom<Tag<Bytes, Seq<u8>>> for Tag<Bytes, Seq<u8>>
{
    open spec fn spec_disjoint_from(&self, other: &Tag<Bytes, Seq<u8>>) -> bool {
        // must also say that two `Bytes` combinators are of the same length
        self.0.predicate.0 != other.0.predicate.0 && self.0.inner.0 == other.0.inner.0
    }

    proof fn spec_parse_disjoint_on(&self, other: &Tag<Bytes, Seq<u8>>, buf: Seq<u8>) {
    }
}

// if `U1` and `U2` are disjoint, then `(U1, V1)` and `(U2, V2)` are disjoint
impl<U1, U2, V1, V2> SpecDisjointFrom<(U2, V2)> for (U1, V1) where
    U1: SpecDisjointFrom<U2>,
    U1: SecureSpecCombinator,
    U2: SecureSpecCombinator,
    V1: SpecCombinator,
    V2: SpecCombinator,
 {
    open spec fn spec_disjoint_from(&self, other: &(U2, V2)) -> bool {
        self.0.spec_disjoint_from(&other.0)
    }

    proof fn spec_parse_disjoint_on(&self, other: &(U2, V2), buf: Seq<u8>) {
        self.0.spec_parse_disjoint_on(&other.0, buf)
    }
}

// if `U1` and `U2` are disjoint, then `preceded(U1, V1)` and `preceded(U2, V2)` are disjoint
impl<U1, U2, V1, V2> SpecDisjointFrom<Preceded<U2, V2>> for Preceded<U1, V1> where
    U1: SpecDisjointFrom<U2>,
    U1: SecureSpecCombinator<SpecResult = ()>,
    U2: SecureSpecCombinator<SpecResult = ()>,
    V1: SpecCombinator,
    V2: SpecCombinator,
 {
    open spec fn spec_disjoint_from(&self, other: &Preceded<U2, V2>) -> bool {
        self.0.spec_disjoint_from(&other.0)
    }

    proof fn spec_parse_disjoint_on(&self, other: &Preceded<U2, V2>, buf: Seq<u8>) {
        self.0.spec_parse_disjoint_on(&other.0, buf)
    }
}

/// if `S3` is disjoint from both `S1` and `S2`, then `S3` is disjoint from `OrdChoice<T1, T2, S1, S2>`,
/// where `S2` is disjoint from `S1`
///
/// this allows composition of the form `OrdChoice(OrdChoice(OrcChoice(...), ...), ...)`
impl<U1, U2, U3> SpecDisjointFrom<OrdChoice<U1, U2>> for U3 where
    U2: SpecDisjointFrom<U1>,
    U3: SpecDisjointFrom<U1> + SpecDisjointFrom<U2>,
    U1: SpecCombinator,
 {
    open spec fn spec_disjoint_from(&self, other: &OrdChoice<U1, U2>) -> bool {
        self.spec_disjoint_from(&other.0) && self.spec_disjoint_from(&other.1)
    }

    proof fn spec_parse_disjoint_on(&self, other: &OrdChoice<U1, U2>, buf: Seq<u8>) {
        self.spec_parse_disjoint_on(&other.0, buf);
        self.spec_parse_disjoint_on(&other.1, buf);
    }
}

/*
    the following impl is very similar to the previous one, but it states things a bit differently:
    if `S1` and `S2` are both disjoint from `S3`, then `OrdChoice<T1, T2, S1, S2>` is disjoint from `S3`
    this allows composition of the form `OrdChoice(..., OrdChoice(..., OrdChoice(..., ...)))`
    unfortunately, this creates conflicting implementations with the previous one
    */

// impl<T1, T2, T3, S1, S2, S3> DisjointFrom<Either<T1, T2>, T3, S3> for OrdChoice<T1, T2, S1, S2>
// where
//     T1: View,
//     T2: View,
//     T3: View,
//     S1: SpecCombinator<T1> + DisjointFrom<T1, T3, S3>,
//     S2: SpecCombinator<T2> + DisjointFrom<T2, T1, S1> + DisjointFrom<T2, T3, S3>,
//     S3: SpecCombinator<T3>,
// {
//     fn disjoint_from(&self, other : &S3) -> bool {
//         self.0.disjoint_from(other) && self.1.disjoint_from(other)
//     }
//     open spec fn spec_disjoint_from(&self, other : &S3) -> bool {
//         self.0.spec_disjoint_from(other) && self.1.spec_disjoint_from(other)
//     }
//     proof fn spec_parse_disjoint_on(&self, other : &S3, buf : Seq<u8>) {
//         self.0.spec_parse_disjoint_on(other, buf);
//         self.1.spec_parse_disjoint_on(other, buf);
//     }
// }
impl<U1, U2, M1, M2> SpecDisjointFrom<Mapped<U2, M2>> for Mapped<U1, M1> where
    U1: SpecDisjointFrom<U2>,
    U2: SpecCombinator,
    M1: SpecIso<Src = U1::SpecResult>,
    M2: SpecIso<Src = U2::SpecResult>,
    U1::SpecResult: SpecFrom<M1::Dst>,
    U2::SpecResult: SpecFrom<M2::Dst>,
    M1::Dst: SpecFrom<U1::SpecResult>,
    M2::Dst: SpecFrom<U2::SpecResult>,
 {
    open spec fn spec_disjoint_from(&self, other: &Mapped<U2, M2>) -> bool {
        self.inner.spec_disjoint_from(&other.inner)
    }

    proof fn spec_parse_disjoint_on(&self, other: &Mapped<U2, M2>, buf: Seq<u8>) {
        self.inner.spec_parse_disjoint_on(&other.inner, buf)
    }
}

/// two `Cond` combinators are disjoint if one and *only one* of their operands are equal
impl<T, Inner1, Inner2> SpecDisjointFrom<Cond<T, T, Inner2>> for Cond<T, T, Inner1> where
    Inner1: SpecCombinator,
    Inner2: SpecCombinator,
 {
    open spec fn spec_disjoint_from(&self, other: &Cond<T, T, Inner2>) -> bool {
        ||| (self.lhs == other.lhs) && (self.rhs != other.rhs)
        ||| (self.lhs != other.lhs) && (self.rhs == other.rhs)
    }

    proof fn spec_parse_disjoint_on(&self, other: &Cond<T, T, Inner2>, buf: Seq<u8>) {
    }
}

/// A helper trait for [`OrdChoice`] combinator.
pub trait DisjointFrom<Other> where
    Self::V: SpecDisjointFrom<Other::V>,
    Self: Combinator,
    Other: Combinator,
    Self::V: SecureSpecCombinator<SpecResult = <Self::Owned as View>::V>,
    Other::V: SecureSpecCombinator<SpecResult = <Other::Owned as View>::V>,
 {
    /// pre-condition that must be held for `Self` and `Other` to be disjoint
    fn disjoint_from(&self, other: &Other) -> (res: bool)
        ensures
            res == self@.spec_disjoint_from(&other@),
    ;
}

macro_rules! impl_disjoint_for_int_type {
    ($combinator:ty) => {
        ::builtin_macros::verus! {
            impl DisjointFrom<$combinator> for $combinator {
                fn disjoint_from(&self, other: &$combinator) -> bool {
                    self.0.predicate.0 != other.0.predicate.0
                }
            }
        }
    };
}
impl_disjoint_for_int_type!(Tag<U8, u8>);
impl_disjoint_for_int_type!(Tag<U16, u16>);
impl_disjoint_for_int_type!(Tag<U32, u32>);
impl_disjoint_for_int_type!(Tag<U64, u64>);

// impl<T: FromToBytes> DisjointFrom<Tag<Int<T>, T>> for Tag<Int<T>, T> {
//     fn disjoint_from(&self, other: &Tag<Int<T>, T>) -> bool {
//         !self.0.predicate.0.eq(&other.0.predicate.0)
//     }
// }

impl<const N: usize> DisjointFrom<Tag<BytesN<N>, [u8; N]>> for Tag<BytesN<N>, [u8; N]> {
    fn disjoint_from(&self, other: &Tag<BytesN<N>, [u8; N]>) -> bool {
        !compare_slice(self.0.predicate.0.as_slice(), other.0.predicate.0.as_slice())
    }
}

impl<'a, 'b> DisjointFrom<Tag<Bytes, &'b [u8]>> for Tag<Bytes, &'a [u8]> {
    fn disjoint_from(&self, other: &Tag<Bytes, &[u8]>) -> bool {
        !compare_slice(self.0.predicate.0, other.0.predicate.0) && self.0.inner.0 == other.0.inner.0
    }
}

impl<U1, U2, V1, V2> DisjointFrom<(U2, V2)> for (U1, V1) where
    U1: DisjointFrom<U2>,
    U1::V: SpecDisjointFrom<U2::V>,
    U1: Combinator,
    U2: Combinator,
    V1: Combinator,
    V2: Combinator,
    U1::V: SecureSpecCombinator<SpecResult = <U1::Owned as View>::V>,
    U2::V: SecureSpecCombinator<SpecResult = <U2::Owned as View>::V>,
    V1::V: SecureSpecCombinator<SpecResult = <V1::Owned as View>::V>,
    V2::V: SecureSpecCombinator<SpecResult = <V2::Owned as View>::V>,
 {
    fn disjoint_from(&self, other: &(U2, V2)) -> bool {
        self.0.disjoint_from(&other.0)
    }
}

impl<U1, U2, V1, V2> DisjointFrom<Preceded<U2, V2>> for Preceded<U1, V1> where
    U1: DisjointFrom<U2>,
    U1::V: SpecDisjointFrom<U2::V>,
    U1: for <'a>Combinator<Result<'a> = (), Owned = ()>,
    U2: for <'a>Combinator<Result<'a> = (), Owned = ()>,
    V1: Combinator,
    V2: Combinator,
    U1::V: SecureSpecCombinator<SpecResult = ()>,
    U2::V: SecureSpecCombinator<SpecResult = ()>,
    V1::V: SecureSpecCombinator<SpecResult = <V1::Owned as View>::V>,
    V2::V: SecureSpecCombinator<SpecResult = <V2::Owned as View>::V>,
 {
    fn disjoint_from(&self, other: &Preceded<U2, V2>) -> bool {
        self.0.disjoint_from(&other.0)
    }
}

impl<U1, U2, U3> DisjointFrom<OrdChoice<U1, U2>> for U3 where
    U2: DisjointFrom<U1>,
    U3: DisjointFrom<U1> + DisjointFrom<U2>,
    U2::V: SpecDisjointFrom<U1::V>,
    U3::V: SpecDisjointFrom<U1::V> + SpecDisjointFrom<U2::V>,
    U1: Combinator,
    U2: Combinator,
    U3: Combinator,
    U1::V: SecureSpecCombinator<SpecResult = <U1::Owned as View>::V>,
    U2::V: SecureSpecCombinator<SpecResult = <U2::Owned as View>::V>,
    U3::V: SecureSpecCombinator<SpecResult = <U3::Owned as View>::V>,
 {
    fn disjoint_from(&self, other: &OrdChoice<U1, U2>) -> bool {
        self.disjoint_from(&other.0) && self.disjoint_from(&other.1)
    }
}

impl<U1, U2, M1, M2> DisjointFrom<Mapped<U2, M2>> for Mapped<U1, M1> where
    U1: DisjointFrom<U2>,
    U1::V: SpecDisjointFrom<U2::V>,
    U1: Combinator,
    U2: Combinator,
    U1::V: SecureSpecCombinator<SpecResult = <U1::Owned as View>::V>,
    U2::V: SecureSpecCombinator<SpecResult = <U2::Owned as View>::V>,
    for <'a>M1: Iso<Src<'a> = U1::Result<'a>, SrcOwned = U1::Owned> + View,
    for <'a>M2: Iso<Src<'a> = U2::Result<'a>, SrcOwned = U2::Owned> + View,
    for <'a>U1::Result<'a>: View + From<M1::Dst<'a>>,
    for <'a>U2::Result<'a>: View + From<M2::Dst<'a>>,
    for <'a>M1::Dst<'a>: View + From<U1::Result<'a>>,
    for <'a>M2::Dst<'a>: View + From<U2::Result<'a>>,
    M1::V: SpecIso<Src = <U1::Owned as View>::V, Dst = <M1::DstOwned as View>::V>,
    M2::V: SpecIso<Src = <U2::Owned as View>::V, Dst = <M2::DstOwned as View>::V>,
    <U1::Owned as View>::V: SpecFrom<<M1::DstOwned as View>::V>,
    <U2::Owned as View>::V: SpecFrom<<M2::DstOwned as View>::V>,
    <M1::DstOwned as View>::V: SpecFrom<<U1::Owned as View>::V>,
    <M2::DstOwned as View>::V: SpecFrom<<U2::Owned as View>::V>,
 {
    fn disjoint_from(&self, other: &Mapped<U2, M2>) -> bool {
        self.inner.disjoint_from(&other.inner)
    }
}

impl<Lhs, Rhs, Inner1, Inner2> DisjointFrom<Cond<Lhs, Rhs, Inner2>> for Cond<Lhs, Rhs, Inner1> where
    Lhs: Compare<Rhs> + Compare<Lhs> + View,
    Rhs: Compare<Rhs> + View<V = Lhs::V>,
    Inner1: Combinator,
    Inner2: Combinator,
    Inner1::V: SecureSpecCombinator<SpecResult = <Inner1::Owned as View>::V>,
    Inner2::V: SecureSpecCombinator<SpecResult = <Inner2::Owned as View>::V>,
{
    fn disjoint_from(&self, other: &Cond<Lhs, Rhs, Inner2>) -> bool {
        (self.lhs.compare(&other.lhs) && !self.rhs.compare(&other.rhs))
        || (!self.lhs.compare(&other.lhs) && self.rhs.compare(&other.rhs))
    }
}

impl<'a, T1, T2> DisjointFrom<&'a T1> for &'a T2 where
    T1: Combinator,
    T2: Combinator + DisjointFrom<T1>,
    T1::V: SecureSpecCombinator<SpecResult = <T1::Owned as View>::V>,
    T2::V: SecureSpecCombinator<SpecResult = <T2::Owned as View>::V>,
    T2::V: SpecDisjointFrom<T1::V>,
{
    fn disjoint_from(&self, other: &&T1) -> bool {
        (*self).disjoint_from(*other)
    }
}

} // verus!
