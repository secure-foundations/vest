use crate::combinators::mapped::spec::{IsoMapper, Mapper};
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

impl Mapper for NestedBracesMapper {
    type In = Either<NestedBracesT, ()>;

    type Out = NestedBracesT;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Either::Left(inner) => NestedBracesT::Brace(Box::new(inner)),
            Either::Right(()) => NestedBracesT::Eps,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            NestedBracesT::Brace(inner) => Either::Left(*inner),
            NestedBracesT::Eps => Either::Right(()),
        }
    }
}

impl IsoMapper for NestedBracesMapper {
    proof fn lemma_map_iso(&self, i: Self::In) {
        match i {
            Either::Left(_) => {},
            Either::Right(u) => {
                assert(u == ());
            },
        }
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
    }
}

pub struct NestedBracesCombinator;

impl SpecType for NestedBracesCombinator {
    type Type = NestedBracesT;

    open spec fn wf(&self, v: Self::Type) -> bool {
        wf_nested_braces(v)
    }
}

impl SpecParser for NestedBracesCombinator {
    type PT = NestedBracesT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        p_nested_braces(ibuf)
    }
}

impl GoodParser for NestedBracesCombinator {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        lemma_parse_length_nested_braces(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        lemma_parse_wf_nested_braces(ibuf);
    }
}

impl SpecSerializerDps for NestedBracesCombinator {
    type ST = NestedBracesT;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        s_nested_braces(v, obuf)
    }
}

impl Serializability for NestedBracesCombinator {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        serializable_nested_braces(v, obuf)
    }
}

impl GoodSerializer for NestedBracesCombinator {
    proof fn lemma_serialize_buf(&self, v: <Self as SpecType>::Type, obuf: Seq<u8>) {
        admit();
        // lemma_serialize_buf_nested_braces(v, obuf);
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

// proof fn lemma_serialize_buf_nested_braces(v: NestedBracesT, obuf: Seq<u8>)
//     requires
//         serializable_nested_braces(v, obuf),
//     ensures
//         wf_nested_braces(v) ==> exists|new_buf: Seq<u8>| s_nested_braces(v, obuf) == new_buf + obuf,
//     decreases height(v),
// {
//     if wf_nested_braces(v) {
//         match v {
//             NestedBracesT::Brace(inner) => {
//                 lemma_serialize_buf_nested_braces(*inner, obuf);
//             },
//             NestedBracesT::Eps => {
//             },
//         }
//     }
// }

// proof fn lemma_serialize_buf_nested_braces(v: NestedBracesT, obuf: Seq<u8>)
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
//                 Terminated(
//                     Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, spec_fns),
//                     Tag { inner: U8, tag: 0x7Du8 },
//                 ),
//                 Tag { inner: U8, tag: 0x00u8 },
//             ),
//             mapper: NestedBracesMapper,
//         };

//         combinator.lemma_serialize_buf(v, obuf);
//     }
// }

pub open spec fn wf_nested_braces(v: NestedBracesT) -> bool
    decreases height(v),
{
    let wf_fn = |inner: NestedBracesT|
        {
            if height(inner) < height(v) {
                wf_nested_braces(inner)
            } else {
                false
            }
        };
    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, wf_fn),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }.wf(v)
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
            Terminated(
                Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, parse_fn),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
        // mapper: |r|
        //     {
        //         match r {
        //             Either::Left(inner) => NestedBracesT::Brace(Box::new(inner)),
        //             Either::Right(_) => NestedBracesT::Eps,
        //         }
        //     },
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
            Terminated(
                Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, serialize_fn),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
        // mapper: |v|
        //     {
        //         match v {
        //             NestedBracesT::Brace(inner) => Either::Left(*inner),
        //             NestedBracesT::Eps => Either::Right(()),
        //         }
        //     },
    }.spec_serialize_dps(v, buf)
}

/// A bundled spec function type that implements all spec-related traits.
#[verifier::reject_recursive_types(T)]
pub struct SpecFns<T> {
    pub wf: spec_fn(T) -> bool,
    pub parse: spec_fn(Seq<u8>) -> Option<(int, T)>,
    pub serialize_dps: spec_fn(T, Seq<u8>) -> Seq<u8>,
    // pub serialize: spec_fn(T) -> Seq<u8>,
    pub serializable: spec_fn(T, Seq<u8>) -> bool,
}

impl<T> SpecType for SpecFns<T> {
    type Type = T;

    open spec fn wf(&self, v: Self::Type) -> bool {
        (self.wf)(v)
    }
}

impl<T> SpecParser for SpecFns<T> {
    type PT = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        (self.parse)(ibuf)
    }
}

impl<T> SpecSerializerDps for SpecFns<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.serialize_dps)(v, obuf)
    }
}

impl<T> Serializability for SpecFns<T> {
    open spec fn serializable(&self, v: <Self as SpecType>::Type, obuf: Seq<u8>) -> bool {
        (self.serializable)(v, obuf)
    }
}

impl<T> GoodSerializer for SpecFns<T> {
    proof fn lemma_serialize_buf(&self, v: <Self as SpecType>::Type, obuf: Seq<u8>) {
        admit();
        // assume(self.wf(v) ==> exists|new_buf: Seq<u8>|
        //     self.spec_serialize_dps(v, obuf) == new_buf + obuf);
    }
}

pub open spec fn serializable_nested_braces(v: NestedBracesT, obuf: Seq<u8>) -> bool
    decreases height(v),
{
    let spec_fns = SpecFns {
        wf: |val| wf_nested_braces(val),
        parse: |input| p_nested_braces(input),
        serialize_dps: |val, buf| s_nested_braces(val, buf),
        serializable: |rest: NestedBracesT, buf: Seq<u8>|
            {
                if height(rest) < height(v) {
                    serializable_nested_braces(rest, buf)
                } else {
                    false
                }
            },
    };

    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, spec_fns),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }.serializable(v, obuf)
}

pub trait ProductiveParser: SpecType + SpecParser<PT = <Self as SpecType>::Type> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>)
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> n > 0,
    ;
}

pub struct NestedBracesLemmaProductive;

impl ProofFnReqEnsDef<(Seq<u8>,), ()> for NestedBracesLemmaProductive {
    open spec fn req(i: (Seq<u8>,)) -> bool {
        true
    }

    open spec fn ens(i: (Seq<u8>,), o: ()) -> bool {
        p_nested_braces(i.0) matches Some((n, v)) ==> n > 0
        // wf_nested_braces(a.0) ==> exists|new_buf: Seq<u8>|
        //     s_nested_braces(a.0, a.1) == new_buf + a.1
    }
}

#[verifier::reject_recursive_types(F)]
pub tracked struct NestedBracesProductive<F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>> {
    // pub tracked serialize_buf_lemma: proof_fn<'static, F>(NestedBracesT, Seq<u8>) -> (),
    pub tracked productive_lemma: proof_fn<'static, F>(Seq<u8>) -> (),
}

impl<F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>> SpecType for NestedBracesProductive<
    F,
> {
    type Type = NestedBracesT;

    open spec fn wf(&self, v: Self::Type) -> bool {
        wf_nested_braces(v)
    }
}

impl<F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>> SpecParser for NestedBracesProductive<
    F,
> {
    type PT = NestedBracesT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        p_nested_braces(ibuf)
    }
}

// impl<
//     F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>,
// > SpecSerializerDps for NestedBracesProofFn<F> {
//     type ST = NestedBracesT;

//     open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
//         s_nested_braces(v, obuf)
//     }
// }

// impl<
//     F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>,
// > Serializability for NestedBracesProofFn<F> {
//     open spec fn serializable(&self, v: NestedBracesT, obuf: Seq<u8>) -> bool {
//         serializable_nested_braces(v, obuf)
//     }
// }

// impl<
//     F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>,
// > GoodSerializer for NestedBracesProofFn<F> {
impl<F: ProofFn + ProofFnReqEns<NestedBracesLemmaProductive>> ProductiveParser for
    NestedBracesProductive<F>
{
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        broadcast use vstd::function::axiom_proof_fn_requires, vstd::function::axiom_proof_fn_ensures;
        (self.productive_lemma)(ibuf);
    }
    // proof fn lemma_serialize_buf(&self, v: NestedBracesT, obuf: Seq<u8>) {
    //     // (self.serialize_buf_lemma)(v, obuf);
    //     assume(self.wf(v) ==> exists|new_buf: Seq<u8>|
    //         self.spec_serialize_dps(v, obuf) == new_buf + obuf);
    // }
}

// proof fn lemma_productive_nested_braces(ibuf: Seq<u8>)
//     ensures
//         p_nested_braces(ibuf) matches Some((n, v)) ==> n > 0,
//     decreases ibuf.len(),
// {
//     let tracked productive_lemma = NestedBracesProductive { 
//         productive_lemma:
//         proof_fn[ReqEns<NestedBracesLemmaProductive>]|rem| {
//             if rem.len() < ibuf.len() {
//                 lemma_productive_nested_braces(rem);
//             }
//         }
//     };

//     Mapped {
//         inner: Choice(
//             Terminated(
//                 Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, productive_lemma),
//                 Tag { inner: U8, tag: 0x7Du8 },
//             ),
//             Tag { inner: U8, tag: 0x00u8 },
//         ),
//         mapper: NestedBracesMapper,
//     }.lemma_parse_productive(ibuf);
// }

// proof fn mode_discrepancy() {
//     let tracked c = Choice(
//             Terminated(
//                 Preceded(Tag { inner: U16Le, tag: 0x7Bu16 }, Refined {
//                     inner: U8,
//                     pred: |x: u8| x < 128u8,
//                 }),
//                 Tag { inner: U8, tag: 0x7Du8 },
//             ),
//             Tag { inner: U8, tag: 0x00u8 },
//         );
// }

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
//             Terminated(
//                 Preceded(Tag { inner: U8, tag: 0x7Bu8 }, serializable_fn),
//                 Tag { inner: U8, tag: 0x7Du8 },
//             ),
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
//             Terminated(
//                 Preceded(Tag { inner: U8, tag: 0x7Bu8 }, lemma_fn),
//                 Tag { inner: U8, tag: 0x7Du8 },
//             ),
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

impl<Inner: ProductiveParser> ProductiveParser for Tag<Inner> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_productive(ibuf);
    }
}

impl<A: ProductiveParser, B: ProductiveParser> ProductiveParser for Preceded<A, B> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.0.lemma_parse_productive(ibuf);
        if let Some((n1, _)) = self.0.spec_parse(ibuf) {
            let rem = ibuf.skip(n1);
            self.1.lemma_parse_productive(rem);
        }
    }
}

impl<A: ProductiveParser, B: ProductiveParser> ProductiveParser for Terminated<A, B> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.0.lemma_parse_productive(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            let rem = ibuf.skip(n1);
            self.1.lemma_parse_productive(rem);
        }
    }
}

impl<A: ProductiveParser, B: ProductiveParser> ProductiveParser for Choice<A, B> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.0.lemma_parse_productive(ibuf);
        self.1.lemma_parse_productive(ibuf);
    }
}

impl<Inner: ProductiveParser, M: Mapper<In = Inner::Type>> ProductiveParser for Mapped<Inner, M> {
    proof fn lemma_parse_productive(tracked &self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_productive(ibuf);
    }
}

} // verus!
