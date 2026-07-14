use crate::combinators::{Fixed, Preceded, Terminated};
use crate::core::exec::bytes_eq;
use crate::core::exec::input::InputBuf;
use crate::core::exec::output::*;
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::{ByteLen, ComplianceErrorKind, PreSerializeError, Prepare, Serializer},
        ParseError,
    },
    spec::{Consistency, SafeParser, SoundParser, SpecByteLen, SpecParser, SpecPred},
};
use vstd::prelude::*;
use OutputBuf;

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

impl<Output: OutputBuf + ?Sized, A, PredFn, T> Serializer<Output, T> for super::Refined<
    A,
    PredFn,
> where T: DeepView, A: Serializer<Output, T>, PredFn: SpecPred<T::V> {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        self.0.serialize_into(v, obuf);
    }
}

impl<A, PredFn, T> ByteLen<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: ByteLen<T>,
    PredFn: Pred<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &T) -> (len: usize) {
        self.0.length(v)
    }
}

impl<A, PredFn, T> Prepare<T> for super::Refined<A, PredFn> where
    T: DeepView,
    A: Prepare<T>,
    PredFn: Pred<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        if self.1.test(v) {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::PredicateFailed))
        }
    }
}

impl<I, Inner, T> Parser<I> for super::Const<Inner, T> where
    I: InputBuf,
    Inner: Parser<I, PT = T, PVal = T>,
    T: DeepView<V = T> + PartialEq + Structural,
 {
    type PT = Inner::PVal;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& forall|v: Inner::PVal| v.deep_view() == v
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, v) = self.0.parse(ibuf)?;
        if v == self.1 {
            Ok((n, v))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

impl<Output: OutputBuf + ?Sized, Inner, T> Serializer<Output, T> for super::Const<Inner, T> where
    T: DeepView<V = T>,
    Inner: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        self.0.serialize_into(v, obuf);
    }
}

impl<Inner, V, T> ByteLen<T> for super::Const<Inner, V> where
    T: DeepView<V = V>,
    Inner: SpecByteLen<T = V> + ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.0.exec_inv()
    }

    fn length(&self, v: &T) -> (len: usize) {
        self.0.length(v)
    }
}

impl<Inner, T> Prepare<T> for super::Const<Inner, T> where
    T: DeepView<V = T> + PartialEq + Structural,
    Inner: Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& forall|v: T| v.deep_view() == v
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        if v == &self.1 {
            self.0.prepare(v)
        } else {
            Err(PreSerializeError::not_compliant(ComplianceErrorKind::InvalidTag))
        }
    }
}

pub proof fn lemma_const_exec_inv<Inner, T, I>(fmt: &super::Const<Inner, T>) where
    I: InputBuf,
    Inner: Parser<I, PT = T, PVal = T> + Prepare<T>,
    T: DeepView<V = T> + PartialEq + Structural,

    requires
        <_ as Prepare<T>>::exec_inv(&fmt.0),
        <_ as Parser<I>>::exec_inv(&fmt.0),
        forall|v: T| v.deep_view() == v,
    ensures
        #[trigger] <_ as Prepare<T>>::exec_inv(fmt),
        #[trigger] <_ as Parser<I>>::exec_inv(fmt),
{
}

impl<const N: usize> ByteLen<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn length(&self, _v: &[u8; N]) -> (len: usize) {
        N
    }
}

impl<const N: usize> Prepare<[u8; N]> for super::Const<Fixed<N>, [u8; N]> {
    fn prepare(&self, v: &[u8; N]) -> (checked: Result<usize, PreSerializeError>) {
        let v_slice = v.as_slice();
        let tag_slice = self.1.as_slice();
        let eq = bytes_eq(v_slice, tag_slice);
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
        if bytes_eq(tag, v) {
            Ok((n, self.1))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

impl<I, Tg, TagVal, Of> Parser<I> for super::PrefixTagged<Tg, TagVal, Of> where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
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

impl<Output: OutputBuf + ?Sized, Tg, TagVal, Of, T> Serializer<Output, T> for super::PrefixTagged<
    Tg,
    TagVal,
    Of,
> where
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: Tg::T| v.deep_view() == v
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.serialize_into(v, obuf);
    }
}

impl<Tg, TagVal, Of, T> ByteLen<T> for super::PrefixTagged<Tg, TagVal, Of> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: TagVal| v.deep_view() == v
    }

    fn length(&self, v: &T) -> (len: usize) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.length(v)
    }
}

impl<Tg, TagVal, Of, T> Prepare<T> for super::PrefixTagged<Tg, TagVal, Of> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: TagVal| v.deep_view() == v
    }

    fn prepare(&self, v: &T) -> (checked: Result<usize, PreSerializeError>) {
        let fmt = Preceded::<_, _, _, false> {
            a: super::Const(&self.0, self.1),
            b: &self.2,
            a_val: self.1,
        };
        fmt.prepare(v)
    }
}

impl<I, Of, Tg, TagVal> Parser<I> for super::SuffixTagged<Of, Tg, TagVal> where
    I: InputBuf,
    Tg: SpecByteLen<T = TagVal> + Parser<I, PT = TagVal, PVal = TagVal> + SafeParser,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
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

impl<Output: OutputBuf + ?Sized, Of, Tg, TagVal, T> Serializer<Output, T> for super::SuffixTagged<
    Of,
    Tg,
    TagVal,
> where
    Tg: SpecByteLen<T = TagVal> + Serializer<Output, TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& forall|v: TagVal| v.deep_view() == v
    }

    fn serialize_into(&self, v: &T, obuf: &mut Output) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.serialize_into(v, obuf);
    }
}

impl<Of, TagVal, Tg, T> ByteLen<T> for super::SuffixTagged<Of, Tg, TagVal> where
    Tg: SpecByteLen<T = TagVal> + ByteLen<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& forall|v: TagVal| v.deep_view() == v
    }

    fn length(&self, v: &T) -> (len: usize) {
        let fmt = Terminated::<_, _, _, false> {
            a: &self.0,
            b: super::Const(&self.1, self.2),
            b_val: self.2,
        };
        fmt.length(v)
    }
}

impl<Of, TagVal, Tg, T> Prepare<T> for super::SuffixTagged<Of, Tg, TagVal> where
    Tg: SpecByteLen<T = TagVal> + Prepare<TagVal>,
    TagVal: DeepView<V = TagVal> + PartialEq + Structural + Copy,
    T: DeepView,
    Of: Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.1.exec_inv()
        &&& forall|v: TagVal| v.deep_view() == v
    }

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
