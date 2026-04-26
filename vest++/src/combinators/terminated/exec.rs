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

} // verus!
