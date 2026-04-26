use crate::combinators::{Fixed, U8};
use crate::core::spec::SoundParser;
use crate::core::{
    exec::{
        fns::Pred,
        input::InputSlice,
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseError,
    },
    spec::{SpecParser, SpecPred},
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

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        self.inner.ex_serialize(v, obuf);
    }
}

impl<Inner, ST> Serializer<ST> for super::Tag<Inner, Inner::SVal> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.inner.exec_inv()
    }

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        self.inner.ex_serialize(v, obuf);
    }
}

impl Parser<&[u8]> for super::Tag<U8, u8> {
    type PT = u8;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, v) = self.inner.parse(ibuf)?;
        if v == self.tag {
            Ok((n, v))
        } else {
            Err(ParseError::predicate_failed())
        }
    }
}

impl<const N: usize> Serializer<[u8; N]> for super::Tag<Fixed<N>, [u8; N]> {
    fn ex_serialize(&self, v: &[u8; N], obuf: &mut Vec<u8>) {
        let _slice = v.as_slice();
        obuf.extend_from_slice(v);
        assert(_slice@ == v@);
        assert(final(obuf)@ == old(obuf)@ + v.deep_view());
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
#[verifier::external_body]
#[inline(always)]
fn cmp_byte_slices(a: &[u8], b: &[u8]) -> (r: bool)
    requires
        a.len() == b.len(),
    ensures
        r == (a@ == b@),
        r == (a.deep_view() == b.deep_view()),
{
    a == b
}

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
            proof {
                assert(self.tag.deep_view() == v.deep_view());
            }
            Ok((n, self.tag))
        } else {
            Err(ParseError::invalid_tag())
        }
    }
}

} // verus!
