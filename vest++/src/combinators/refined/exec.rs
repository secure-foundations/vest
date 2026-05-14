use crate::combinators::{Fixed, Preceded, Terminated};
use crate::core::exec::cmp_byte_slices;
use crate::core::exec::input::InputBuf;
use crate::core::exec::{DeepEq, SelfView};
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::{ByteLen, Compliance, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    spec::{Consistency, SafeParser, SoundParser, SpecByteLen, SpecParser, SpecPred},
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
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, v) = self.0.parse(ibuf)?;
        if self.1.test(&v) {
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
        fmt.0.exec_inv(),
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
        self.0.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.0.ex_serialize(v, obuf);
    }
}

impl<A, PredFn, ST> Compliance<ST> for super::Refined<A, PredFn> where
    ST: DeepView + Copy,
    A: Compliance<ST>,
    PredFn: Pred<ST>,
 {
    fn check_compliance(&self, v: ST) -> (yes: bool) {
        self.0.check_compliance(v) && self.1.test(&v)
    }
}

impl<A, PredFn, ST> ByteLen<ST> for super::Refined<A, PredFn> where
    ST: DeepView,
    A: ByteLen<ST>,
    PredFn: Pred<ST>,
 {
    fn length(&self, v: ST) -> (len: usize) {
        self.0.length(v)
    }
}

impl<A, PredFn, ST> Prepare<ST> for super::Refined<A, PredFn> where
    ST: DeepView,
    A: Prepare<ST>,
    PredFn: Pred<ST>,
 {
    fn prepare(&self, v: ST) -> (checked: Result<usize, PreSerializeError>) {
        if self.1.test(&v) {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::NotCompliant("Refined"))
        }
    }
}

impl<I, Inner> Parser<I> for super::Const<Inner, Inner::PVal> where
    I: InputBuf,
    Inner: Parser<I, PT = <Inner as SpecParser>::PVal>,
    Inner::PVal: SelfView,
 {
    type PT = Inner::PVal;

    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, v) = self.0.parse(ibuf)?;
        if SelfView::eq(&v, &self.1) {
            Ok((n, v))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

impl<Inner, ST> Serializer<ST> for super::Const<Inner, ST> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST, SVal = ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        self.0.ex_serialize(v, obuf);
    }
}

impl<Inner, ST> Compliance<ST> for super::Const<Inner, ST> where
    ST: SelfView + Copy,
    Inner: Compliance<ST>,
 {
    fn check_compliance(&self, v: ST) -> (yes: bool) {
        proof {
            self.1.self_view();
        }
        self.0.check_compliance(v) && SelfView::eq(&v, &self.1)
    }
}

impl<Inner, V, ST> ByteLen<ST> for super::Const<Inner, V> where
    ST: DeepView<V = V>,
    Inner: SpecByteLen<T = V> + ByteLen<ST>,
 {
    fn length(&self, v: ST) -> (len: usize) {
        self.0.length(v)
    }
}

impl<Inner, ST> Prepare<ST> for super::Const<Inner, ST> where ST: SelfView, Inner: Prepare<ST> {
    fn prepare(&self, v: ST) -> (checked: Result<usize, PreSerializeError>) {
        if SelfView::eq(&v, &self.1) {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::NotCompliant("Const"))
        }
    }
}

impl<const N: usize> Serializer<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn ex_serialize(&self, v: [u8; N], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(&v);
    }
}

impl<const N: usize> Compliance<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn check_compliance(&self, v: [u8; N]) -> (yes: bool) {
        let v_slice = v.as_slice();
        let tag_slice = self.1.as_slice();
        let eq = cmp_byte_slices(v_slice, tag_slice);
        proof {
            assert(v_slice.deep_view() == v.deep_view());
            assert(tag_slice.deep_view() == self.1@);
            assert(eq == (v.deep_view() == self.1@));
        }
        eq
    }
}

impl<const N: usize> ByteLen<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn length(&self, _v: [u8; N]) -> (len: usize) {
        N
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
impl<const N: usize> Parser<&[u8]> for super::Const<Fixed<N>, [u8; N]> {
    type PT = [u8; N];

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, v) = self.0.parse(ibuf)?;
        let tag = self.1.as_slice();
        proof {
            self.0.lemma_parse_sound_consumption(ibuf@);
            assert(v.len() == N);
            assert(tag.len() == N);
            v.deep_view_eq_view();
            tag.deep_view_eq_view();
        }
        if cmp_byte_slices(tag, v) {
            Ok((n, self.1))
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
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        }.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.parse(ibuf)
    }
}

impl<Tg, Of, ST> Serializer<ST> for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + Serializer<Tg::T, SVal = Tg::T>,
    Tg::T: SelfView + Copy,
    ST: DeepView<V = Of::SVal>,
    Of: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        }.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.ex_serialize(v, obuf);
    }
}

impl<Tg, TagVal, Of, ST> Compliance<ST> for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Compliance<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: Compliance<ST>,
 {
    fn check_compliance(&self, v: ST) -> (yes: bool) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.check_compliance(v)
    }
}

impl<Tg, TagVal, Of, ST> ByteLen<ST> for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: ByteLen<ST>,
 {
    fn length(&self, v: ST) -> (len: usize) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.length(v)
    }
}

impl<Tg, TagVal, Of, ST> Prepare<ST> for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: Prepare<ST>,
 {
    fn prepare(&self, v: ST) -> (checked: Result<usize, PreSerializeError>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.prepare(v)
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
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        }.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        };
        fmt.parse(ibuf)
    }
}

impl<Tg, Of, ST> Serializer<ST> for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + Serializer<Tg::T, SVal = Tg::T>,
    Tg::T: SelfView + Copy,
    ST: DeepView<V = Of::SVal>,
    Of: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        }.exec_inv()
    }

    fn ex_serialize(&self, v: ST, obuf: &mut Vec<u8>) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        };
        fmt.ex_serialize(v, obuf);
    }
}

impl<Tg, TagVal, Of, ST> Compliance<ST> for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Compliance<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: Compliance<ST>,
 {
    fn check_compliance(&self, v: ST) -> (yes: bool) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        };
        fmt.check_compliance(v)
    }
}

impl<Tg, TagVal, Of, ST> ByteLen<ST> for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: ByteLen<ST>,
 {
    fn length(&self, v: ST) -> (len: usize) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        };
        fmt.length(v)
    }
}

impl<Tg, TagVal, Of, ST> Prepare<ST> for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: SelfView + Copy,
    ST: DeepView,
    Of: Prepare<ST>,
 {
    fn prepare(&self, v: ST) -> (checked: Result<usize, PreSerializeError>) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.2,
            b: super::Const(&self.0, self.1),
            b_val: self.1,
        };
        fmt.prepare(v)
    }
}

} // verus!
