use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::*;
use crate::core::proof::*;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

pub enum NestedBracesT {
    Brace(Box<NestedBracesT>),
    Eps,
}

pub open spec fn height(n: NestedBracesT) -> nat
    decreases n,
{
    match n {
        NestedBracesT::Brace(inner) => 1 + height(*inner),
        NestedBracesT::Eps => 0,
    }
}

pub struct NestedBracesMapper;

impl SpecMapper for NestedBracesMapper {
    type In = Sum<NestedBracesT, u8>;

    type Out = NestedBracesT;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        match i {
            Sum::Inl(_) => true,
            Sum::Inr(tag) => tag == 0x00u8,
        }
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(inner) => NestedBracesT::Brace(Box::new(inner)),
            Sum::Inr(_) => NestedBracesT::Eps,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            NestedBracesT::Brace(inner) => Sum::Inl(*inner),
            NestedBracesT::Eps => Sum::Inr(0x00u8),
        }
    }
}

impl LossyMapper for NestedBracesMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for NestedBracesMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        match i {
            Sum::Inl(_) => {},
            Sum::Inr(tag) => {
                assert(tag == 0x00u8);
            },
        }
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

pub struct NestedBracesCombinator;

impl SpecParser for NestedBracesCombinator {
    type PVal = NestedBracesT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        p_nested_braces(ibuf)
    }
}

impl Consistency for NestedBracesCombinator {
    type Val = NestedBracesT;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        wf_nested_braces(v)
    }
}

pub open spec fn byte_len_nested_braces(v: NestedBracesT) -> nat
    decreases height(v),
{
    match v {
        NestedBracesT::Brace(inner) => 3 + byte_len_nested_braces(*inner),
        NestedBracesT::Eps => 1,
    }
}

impl SpecByteLen for NestedBracesCombinator {
    type T = NestedBracesT;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        byte_len_nested_braces(v)
    }
}

impl SafeParser for NestedBracesCombinator {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        lemma_parse_length_nested_braces(ibuf);
    }
}

impl SoundParser for NestedBracesCombinator {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        lemma_parse_sound_consumption_nested_braces(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        lemma_parse_wf_nested_braces(ibuf);
    }
}

impl SpecSerializerDps for NestedBracesCombinator {
    type SValue = NestedBracesT;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        s_nested_braces(v, obuf)
    }
}

proof fn lemma_parse_length_nested_braces(ibuf: Seq<u8>)
    ensures
        p_nested_braces(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
    decreases ibuf.len(),
{
    if ibuf.len() >= 2 {
        let rem = ibuf.skip(2);
        lemma_parse_length_nested_braces(rem);
    }
}

proof fn lemma_parse_wf_nested_braces(ibuf: Seq<u8>)
    ensures
        p_nested_braces(ibuf) matches Some((n, v)) ==> wf_nested_braces(v),
    decreases ibuf.len(),
{
    if ibuf.len() >= 2 {
        let rem = ibuf.skip(2);
        lemma_parse_wf_nested_braces(rem);
    }
}

proof fn lemma_parse_sound_consumption_nested_braces(ibuf: Seq<u8>)
    ensures
        p_nested_braces(ibuf) matches Some((n, v)) ==> n == byte_len_nested_braces(v),
    decreases ibuf.len(),
{
    if ibuf.len() >= 2 {
        let rem = ibuf.skip(2);
        lemma_parse_sound_consumption_nested_braces(rem);
    }
}

proof fn lemma_parse_productive_nested_braces(ibuf: Seq<u8>)
    ensures
        p_nested_braces(ibuf) matches Some((n, v)) ==> n > 0,
    decreases ibuf.len(),
{
    if ibuf.len() >= 2 {
        let rem = ibuf.skip(2);
        lemma_parse_productive_nested_braces(rem);
    }
}

// proof fn lemma_serialize_dps_buf_nested_braces(v: NestedBracesT, obuf: Seq<u8>)
//     requires
//         serializable_nested_braces(v, obuf),
//     ensures
//         wf_nested_braces(v) ==> exists|new_buf: Seq<u8>| s_nested_braces(v, obuf) == new_buf + obuf,
//     decreases height(v),
// {
//     if wf_nested_braces(v) {
//         match v {
//             NestedBracesT::Brace(inner) => {
//                 lemma_serialize_dps_buf_nested_braces(*inner, obuf);
//             },
//             NestedBracesT::Eps => {
//             },
//         }
//     }
// }
// proof fn lemma_serialize_dps_buf_nested_braces(v: NestedBracesT, obuf: Seq<u8>)
//     requires
//         serializable_nested_braces(v, obuf),
//     ensures
//         wf_nested_braces(v) ==> exists|new_buf: Seq<u8>| s_nested_braces(v, obuf) == new_buf + obuf,
//     decreases height(v),
// {
//     if wf_nested_braces(v) {
//         // Construct the same SpecFns as in serializable_nested_braces
//         let spec_fns = SpecFns {
//             wf: |val| wf_nested_braces(val),
//             parse: |input| p_nested_braces(input),
//             serialize_dps: |val, buf| s_nested_braces(val, buf),
//             serializable: |rest: NestedBracesT, buf: Seq<u8>|
//                 if height(rest) < height(v) {
//                     serializable_nested_braces(rest, buf)
//                 } else {
//                     false
//                 },
//         };
//         let combinator = Mapped {
//             inner: Choice(
//                 WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U16Le, 0x7Bu16, spec_fns)),
//                 Tag { inner: U8, tag: 0x00u8 },
//             ),
//             mapper: NestedBracesMapper,
//         };
//         combinator.lemma_serialize_dps_buf(v, obuf);
//     }
// }
pub open spec fn wf_nested_braces(v: NestedBracesT) -> bool
    decreases height(v),
{
    match v {
        NestedBracesT::Brace(inner) => wf_nested_braces(*inner),
        NestedBracesT::Eps => true,
    }
}

pub open spec fn p_nested_braces(input: Seq<u8>) -> Option<(int, NestedBracesT)>
    decreases input.len(),
{
    let parse_fn = |rem: Seq<u8>|
        {
            if rem.len() < input.len() {
                p_nested_braces(rem)
            } else {
                None
            }
        };
    Mapped {
        inner: Choice(
            WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U16Le, 0x7Bu16, parse_fn)),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }.spec_parse(input)
}

pub open spec fn s_nested_braces(v: NestedBracesT, buf: Seq<u8>) -> Seq<u8>
    decreases height(v),
{
    let serialize_fn = |inner_v: NestedBracesT, obuf: Seq<u8>|
        {
            if height(inner_v) < height(v) {
                s_nested_braces(inner_v, obuf)
            } else {
                obuf
            }
        };
    Mapped {
        inner: Choice(
            WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U16Le, 0x7Bu16, serialize_fn)),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }.spec_serialize_dps(v, buf)
}

pub trait ProductiveParser: SpecParser {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> n > 0,
    ;
}

// pub open spec fn serializable_nested_braces(v: NestedBracesT, obuf: Seq<u8>) -> bool
//     decreases height(v),
// {
//     let serializable_fn = |inner_v: NestedBracesT, obuf: Seq<u8>|
//         {
//             if height(inner_v) < height(v) {
//                 serializable_nested_braces(inner_v, obuf)
//             } else {
//                 false
//             }
//         };
//     Mapped {
//         inner: Choice(
//             WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U8, 0x7Bu8, serializable_fn)),
//             Tag { inner: U8, tag: 0x00u8 },
//         ),
//         mapper: NestedBracesMapper,
//     }.serializable(v, obuf)
// }
// proof fn lemma_parse_length_nested_braces(ibuf: Seq<u8>)
//     ensures p_nested_braces(ibuf) matches Some((n, _)) ==> 0 <= n <= ibuf.len(),
//     decreases ibuf.len(),
// {
//     let lemma_fn = proof_fn|rem: Seq<u8>|
//         ensures p_nested_braces(rem) matches Some((n, _)) ==> 0 <= n <= rem.len(),
//     {
//         if rem.len() < ibuf.len() {
//             lemma_parse_length_nested_braces(rem);
//         }
//     };
//     Mapped {
//         inner: Choice(
//             WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U8, 0x7Bu8, lemma_fn)),
//             Tag { inner: U8, tag: 0x00u8 },
//         ),
//         mapper: NestedBracesMapper,
//     }.lemma_parse_length(ibuf);
// }
impl ProductiveParser for U8 {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
    }
}

impl ProductiveParser for U16Le {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
    }
}

impl<Inner: ProductiveParser> ProductiveParser for Tag<Inner, Inner::PVal> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_productive(ibuf);
    }
}

impl<
    A: ProductiveParser,
    AVal: DeepView<V = A::PVal>,
    B: ProductiveParser,
    const CHECK: bool,
> ProductiveParser for Preceded<A, AVal, B, CHECK> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.a.lemma_parse_productive(ibuf);
        if let Some((n1, _)) = self.a.spec_parse(ibuf) {
            let rem = ibuf.skip(n1);
            self.b.lemma_parse_productive(rem);
        }
    }
}

impl<
    A: ProductiveParser,
    B: ProductiveParser,
    BVal: DeepView<V = B::PVal>,
    const CHECK: bool,
> ProductiveParser for Terminated<A, B, BVal, CHECK> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.a.lemma_parse_productive(ibuf);
        if let Some((n1, _v1)) = self.a.spec_parse(ibuf) {
            let rem = ibuf.skip(n1);
            self.b.lemma_parse_productive(rem);
        }
    }
}

impl<A: ProductiveParser, B: ProductiveParser> ProductiveParser for Choice<A, B> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.0.lemma_parse_productive(ibuf);
        self.1.lemma_parse_productive(ibuf);
    }
}

impl<Inner: ProductiveParser, M: SpecMapper<In = Inner::PVal>> ProductiveParser for Mapped<
    Inner,
    M,
> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_productive(ibuf);
    }
}

} // verus!
