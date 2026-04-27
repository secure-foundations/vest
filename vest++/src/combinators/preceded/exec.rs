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
impl<I, A, AVal, B> Parser<I> for super::Preceded2<A, AVal, B, false> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
    AVal: DeepView<V = A::PVal>,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (_, v)) = Pair(&self.a, &self.b).parse(ibuf)?;
        Ok((n, v))
    }
}

// Non-malleable version
impl<I, A, AVal, B> Parser<I> for super::Preceded2<A, AVal, B, true> where
    I: InputBuf,
    A: Parser<I, PT = AVal> + SafeParser,
    B: Parser<I> + SafeParser,
    AVal: DeepEq<V = A::PVal>,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        Pair(&self.a, &self.b).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (va, v)) = Pair(&self.a, &self.b).parse(ibuf)?;
        if va.deep_eq(&self.a_val) {
            Ok((n, v))
        } else {
            Err(ParseError::non_canonical())
        }
    }
}

impl<A, AVal, B, BVal, const CHECK: bool> Serializer<BVal> for super::Preceded2<
    A,
    AVal,
    B,
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

    fn ex_serialize(&self, v: &BVal, obuf: &mut Vec<u8>) {
        self.a.ex_serialize(&self.a_val, obuf);
        self.b.ex_serialize(v, obuf);
    }
}

} // verus!
