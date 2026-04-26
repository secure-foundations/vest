use crate::{
    combinators::{Pair, Tag, U8},
    core::{
        exec::{
            input::InputBuf,
            parser::{PResult, Parser},
            serializer::Serializer,
        },
        spec::{AdmitsUniqueVal, Consistency, SafeParser, SpecParser},
    },
};
use vstd::prelude::*;

verus! {

impl<I, A, B> Parser<I> for super::Preceded<A, B> where
    I: InputBuf,
    A: Parser<I> + SafeParser,
    B: Parser<I> + SafeParser,
 {
    type PT = B::PT;

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        let (n, (_, v)) = Pair(&self.0, &self.1).parse(ibuf)?;
        Ok((n, v))
    }
}

impl<B, ST> Serializer<ST> for super::Preceded<Tag<U8, u8>, B> where
    ST: DeepView<V = B::SVal>,
    B: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& <Tag<U8, u8> as Serializer<u8>>::exec_inv(&self.0)
        &&& self.1.exec_inv()
    }

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        let tag = self.0.tag;
        <Tag<U8, u8> as Serializer<u8>>::ex_serialize(&self.0, &tag, obuf);
        self.1.ex_serialize(v, obuf);
        proof {
            let witness = choose|a: u8| self.0.consistent(a);
            assert(self.0.consistent(tag));
            self.0.lemma_unique_consistent_val(witness, tag);
        }
    }
}

} // verus!
