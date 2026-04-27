use crate::{
    combinators::Pair,
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::Serializer,
            DeepEq, ParseError,
        },
        spec::SafeParser,
    },
};
use vstd::prelude::*;

verus! {

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

impl<A, B, BVal, AVal, const CHECK: bool> Serializer<AVal> for super::Terminated2<
    A,
    B,
    BVal,
    CHECK,
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
