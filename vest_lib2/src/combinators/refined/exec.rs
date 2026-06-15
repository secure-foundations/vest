use crate::combinators::{Fixed, Preceded, Terminated};
use crate::core::exec::cmp_byte_slices;
use crate::core::exec::input::InputBuf;
use crate::core::exec::{DeepEq, SelfView};
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::{
            ByteLen, Compliance, ComplianceErrorKind, PreSerializeError, Prepare, Serializer,
        },
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

impl<A, PredFn, T> Serializer<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: Serializer<T>,
    PredFn: SpecPred<T::V>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        self.0.serialize(v, obuf);
    }
}

impl<A, PredFn, T> Compliance<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: Compliance<T>,
    PredFn: Pred<T>,
 {
    fn check_compliance(&self, v: &T) -> (yes: bool) {
        self.0.check_compliance(v) && self.1.test(v)
    }
}

impl<A, PredFn, T> ByteLen<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: ByteLen<T>,
    PredFn: Pred<T>,
 {
    fn length(&self, v: &T) -> (len: usize) {
        self.0.length(v)
    }
}

impl<A, PredFn, T> Prepare<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: Prepare<T>,
    PredFn: Pred<T>,
 {
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        if self.1.test(v) {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
        }
    }
}

impl<I, Inner> Parser<I> for super::Const<Inner, Inner::PVal> where
    I: InputBuf,
    Inner: Parser<I, PT = <Inner as SpecParser>::PVal>,
    Inner::PVal: SelfView,
// Inner::PVal: DeepView<V = Inner::PVal> + PartialEq + Structural,
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

impl<Inner, T> Serializer<T> for super::Const<Inner, T> where
    T: DeepView<V = T>,
    Inner: Serializer<T>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        self.0.serialize(v, obuf);
    }
}

impl<Inner, T> Compliance<T> for super::Const<Inner, T> where T: SelfView, Inner: Compliance<T> {
    fn check_compliance(&self, v: &T) -> (yes: bool) {
        proof {
            self.1.self_view();
        }
        self.0.check_compliance(v) && SelfView::eq(v, &self.1)
    }
}

impl<Inner, V, T> ByteLen<T> for super::Const<Inner, V> where
    T: DeepView<V = V>,
    Inner: SpecByteLen<T = V> + ByteLen<T>,
 {
    fn length(&self, v: &T) -> (len: usize) {
        self.0.length(v)
    }
}

impl<Inner, T> Prepare<T> for super::Const<Inner, T> where T: SelfView, Inner: Prepare<T> {
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        if SelfView::eq(v, &self.1) {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag))
        }
    }
}

impl<const N: usize> Serializer<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn serialize(&self, v: &[u8; N], obuf: &mut Vec<u8>) {
        obuf.extend_from_slice(v);
    }
}

impl<const N: usize> Compliance<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn check_compliance(&self, v: &[u8; N]) -> (yes: bool) {
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
    fn length(&self, _v: &[u8; N]) -> (len: usize) {
        N
    }
}

impl<const N: usize> Prepare<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn prepare(&self, v: &[u8; N]) -> (checked: Result<usize, PreSerializeError>) {
        let v_slice = v.as_slice();
        let tag_slice = self.1.as_slice();
        let eq = cmp_byte_slices(v_slice, tag_slice);
        proof {
            assert(v_slice.deep_view() == v.deep_view());
            assert(tag_slice.deep_view() == self.1@);
            assert(eq == (v.deep_view() == self.1@));
        }
        if eq {
            Ok(N)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag))
        }
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

impl<I, Tg, Of> Parser<I> for super::PrefixTagged<Tg, Of> where
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

impl<Tg, Of, T> Serializer<T> for super::PrefixTagged<Tg, Of> where
    Tg: SpecByteLen + Serializer<Tg::T>,
    Tg::T: SelfView + Copy,
    T: DeepView,
    Of: Serializer<T>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.serialize(v, obuf);
    }
}

impl<Tg, TagVal, Of, T> Compliance<T> for super::PrefixTagged<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Compliance<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: Compliance<T>,
 {
    fn check_compliance(&self, v: &T) -> (yes: bool) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.check_compliance(v)
    }
}

impl<Tg, TagVal, Of, T> ByteLen<T> for super::PrefixTagged<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: ByteLen<T>,
 {
    fn length(&self, v: &T) -> (len: usize) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.length(v)
    }
}

impl<Tg, TagVal, Of, T> Prepare<T> for super::PrefixTagged<Tg, Of> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: Prepare<T>,
 {
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.prepare(v)
    }
}

impl<I, Of, Tg> Parser<I> for super::SuffixTagged<Of, Tg> where
    I: InputBuf,
    Tg: SpecByteLen + Parser<I, PT = Tg::T, PVal = Tg::T> + SafeParser,
    Tg::T: SelfView + Copy,
    Of: Parser<I> + SafeParser,
 {
    type PT = Of::PT;

    open spec fn exec_inv(&self) -> bool {
        Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        }.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.parse(ibuf)
    }
}

impl<Of, Tg, T> Serializer<T> for super::SuffixTagged<Of, Tg> where
    Tg: SpecByteLen + Serializer<Tg::T>,
    Tg::T: SelfView + Copy,
    T: DeepView,
    Of: Serializer<T>,
 {
    fn serialize(&self, v: &T, obuf: &mut Vec<u8>) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.serialize(v, obuf);
    }
}

impl<Of, TagVal, Tg, T> Compliance<T> for super::SuffixTagged<Of, Tg> where
    Tg: SpecByteLen<T = TagVal> + Compliance<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: Compliance<T>,
 {
    fn check_compliance(&self, v: &T) -> (yes: bool) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.check_compliance(v)
    }
}

impl<Of, TagVal, Tg, T> ByteLen<T> for super::SuffixTagged<Of, Tg> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: ByteLen<T>,
 {
    fn length(&self, v: &T) -> (len: usize) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.length(v)
    }
}

impl<Of, TagVal, Tg, T> Prepare<T> for super::SuffixTagged<Of, Tg> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: SelfView + Copy,
    T: DeepView,
    Of: Prepare<T>,
 {
    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.prepare(v)
    }
}

} // verus!
