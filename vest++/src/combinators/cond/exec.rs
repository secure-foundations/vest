use crate::core::{
    exec::{
        parser::{PResult, Parser},
        serializer::Serializer,
        ParseError,
    },
    spec::SpecParser,
};
use vstd::prelude::*;

verus! {

impl<I, Inner> Parser<I> for super::Cond<Inner> where I: View<V = Seq<u8>>, Inner: Parser<I> {
    type PT = Inner::PT;

    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        if self.0 {
            self.1.parse(ibuf)
        } else {
            Err(ParseError::cond_rejected())
        }
    }
}

impl<Inner, ST> Serializer<ST> for super::Cond<Inner> where
    ST: DeepView<V = Inner::SVal>,
    Inner: Serializer<ST>,
 {
    open spec fn exec_inv(&self) -> bool {
        self.1.exec_inv()
    }

    fn ex_serialize(&self, v: &ST, obuf: &mut Vec<u8>) {
        self.1.ex_serialize(v, obuf);
    }
}

} // verus!
