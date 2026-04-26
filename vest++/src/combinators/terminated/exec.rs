use crate::{
    combinators::{Pair, Tag, U8},
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::Serializer,
            DeepEq, ParseError,
        },
        spec::{AdmitsUniqueVal, Consistency, SafeParser, SpecParser},
    },
};
use vstd::prelude::*;

verus! {

impl<I, A, B> Parser<I> for super::Terminated<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, _)) = Pair(&self.0, &self.1).parse(ibuf)?;
        Ok((n, v))
    }
}

// Malleable version
impl<I, A, B, BVal> Parser<I> for super::Terminated2<A, B, BVal, false> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
    BVal: DeepView<V = B::PVal>,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, _)) = Pair(&self.a, &self.b).parse(ibuf)?;
        Ok((n, v))
    }
}

// Non-malleable version
impl<I, A, B, BVal> Parser<I> for super::Terminated2<A, B, BVal, true> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I, PT = BVal> + SafeParser,
    BVal: DeepEq<V = B::PVal>,
 {
    type PT = A::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (v, vb)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if vb.deep_eq(&self.b_val) {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<A, ST> Serializer<ST> for super::Terminated<A, Tag<U8, u8>> where
    ST: DeepView<V = A::SVal>,
    A: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& <Tag<U8, u8> as Serializer<u8>>::exec_inv(&self.1)
    }

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        self.0.ex_serialize(v, obuf);
        let tag = self.1.tag;
        <Tag<U8, u8> as Serializer<u8>>::ex_serialize(&self.1, &tag, obuf);
        proof {
            let witness = choose|b: u8| self.1.consistent(b);
            assert(self.1.consistent(tag));
            self.1.lemma_unique_consistent_val(witness, tag);
        }
    }
}

impl<A, B, BVal, AVal, const NONMAL: bool> Serializer<AVal> for super::Terminated2<
    A,
    B,
    BVal,
    NONMAL,
> where
    AVal: DeepView<V = A::SVal>,
    BVal: DeepView<V = B::SVal>,
    A: Serializer<AVal>,
    B: Serializer<BVal>,
 {
    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn ex_serialize(&self, v: &AVal, obuf: &mut Vec<u8>) {
        self.a.ex_serialize(v, obuf);
        self.b.ex_serialize(&self.b_val, obuf);
    }
}

} // verus!
