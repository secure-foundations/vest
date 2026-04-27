use crate::combinators::{Fixed, Preceded, Terminated};
use crate::core::exec::cmp_byte_slices;
use crate::core::exec::input::InputBuf;
use crate::core::exec::{DeepEq, SelfView};
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseError,
    },
    spec::{SafeParser, SoundParser, SpecByteLen, SpecParser, SpecPred},
};
use vstd::prelude::*;

verus! {

impl<I, A, PredFn> Parser<I> for super::Refined<A, PredFn> where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    PredFn: Pred<A::PT>,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, v) = self.inner.parse(ibuf)?;
        if self.pred.test(&v) {
            Ok((n, v))
        } else {
            Err(ParseError::predicate_failed())
        }
    }
}

pub broadcast proof fn lemma_refined_exec_inv<I, A, PredFn>(fmt: &super::Refined<A, PredFn>) where
    I: View<V = Seq<u8>>,
    A: Parser<I>,
    PredFn: Pred<A::PT>,

    requires
        fmt.inner.exec_inv(),
    ensures
        #[trigger] fmt.exec_inv(),
{
}

impl<A, PredFn, ST> Serializer<ST> for super::Refined<A, PredFn> where
    ST: DeepView<V = A::SVal>,
    A: Serializer<ST>,
    PredFn: SpecPred<A::SVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.inner.ex_serialize(v, obuf);
    }
}

impl<I, Inner> Parser<I> for super::Tag<Inner, Inner::PVal> where
    I: InputBuf,
    Inner: Parser<I, PT = <Inner as SpecParser>::PVal>,
    Inner::PVal: SelfView,
 {
    type PT = Inner::PVal;

    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, v) = self.inner.parse(ibuf)?;
        if SelfView::eq(&v, &self.tag) {
            Ok((n, v))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

impl<Inner, ST> Serializer<ST> for super::Tag<Inner, ST> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST, SVal = ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.inner.ex_serialize(v, obuf);
    }
}

impl<const N: usize> Serializer<[u8; N]> for super::Tag<Fixed<N>, [u8; N]> {
    fn ex_serialize(&self, v: [u8; N], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(&v);
    }
}

// pub assume_specification<const N: usize>[ <[u8; N] as PartialEq<&[u8]>>::eq ](
//     x: &[u8; N],
//     y: &&[u8],
// ) -> (is_eq: bool)
//     ensures
//         is_eq == (x@ == y@),
// ;
// pub assume_specification<'a, T, U, const N: usize>[ <[T; N] as core::cmp::PartialEq<&[U]>>::eq ](
//     a: &[T; N],
//     b: &&[U],
// ) -> (r: bool) where T: core::cmp::PartialEq<U>
// // , T: DeepView, U: DeepView<V = T::V>,
//     // ensures
//     //     // r == (a@ == b@),
//     //     r == (a.deep_view() == b.deep_view()),
// ;
impl<const N: usize> Parser<&[u8]> for super::Tag<Fixed<N>, [u8; N]> {
    type PT = [u8; N];

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, v) = self.inner.parse(ibuf)?;
        let tag = self.tag.as_slice();
        proof {
            self.inner.lemma_parse_sound_consumption(ibuf@);
            assert(v.len() == N);
            assert(tag.len() == N);
            v.deep_view_eq_view();
            tag.deep_view_eq_view();
        }
        if cmp_byte_slices(tag, v) {
            Ok((n, self.tag))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

impl<I, Tg, Of> Parser<I> for super::WithPrefixTag<Tg, Of> where
    I: InputBuf,
    Tg: SpecByteLen + Parser<I, PT = Tg::T, PVal = Tg::T> + SafeParser,
    Tg::T: SelfView + Copy,
    Of: Parser<I> + SafeParser,
 {
    type PT = Of::PT;

    open spec fn exec_inv(&self) -> bool {
        Preceded::<_, _, _, false> {
            a: super::Tag { inner: &self.0, tag: self.1 },
            b: &self.2,
            a_val: self.1,
        }.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Tag { inner: &self.0, tag: self.1 },
            b: &self.2,
            a_val: self.1,
        };
        fmt.parse(ibuf)
    }
}

impl<Tg, Of, ST> Serializer<ST> for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + Serializer<Tg::T, SVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T> + Copy,
    ST: DeepView<V = Of::SVal>,
    Of: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        Preceded::<_, _, _, false> {
            a: super::Tag { inner: &self.0, tag: self.1 },
            b: &self.2,
            a_val: self.1,
        }.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Tag { inner: &self.0, tag: self.1 },
            b: &self.2,
            a_val: self.1,
        };
        fmt.ex_serialize(v, obuf);
    }
}

impl<I, Tg, Of> Parser<I> for super::WithSuffixTag<Tg, Of> where
    I: InputBuf,
    Tg: SpecByteLen + Parser<I, PT = Tg::T, PVal = Tg::T> + SafeParser,
    Tg::T: SelfView + Copy,
    Of: Parser<I> + SafeParser,
 {
    type PT = Of::PT;

    open spec fn exec_inv(&self) -> bool {
        Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Tag { inner: &self.0, tag: self.1 },
            b_val: self.1,
        }.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Tag { inner: &self.0, tag: self.1 },
            b_val: self.1,
        };
        fmt.parse(ibuf)
    }
}

impl<Tg, Of, ST> Serializer<ST> for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + Serializer<Tg::T, SVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T> + Copy,
    ST: DeepView<V = Of::SVal>,
    Of: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Tag { inner: &self.0, tag: self.1 },
            b_val: self.1,
        }.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Tag { inner: &self.0, tag: self.1 },
            b_val: self.1,
        };
        fmt.ex_serialize(v, obuf);
    }
}

} // verus!
