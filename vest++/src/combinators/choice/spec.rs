use crate::core::spec::{GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: SpecType, B: SpecType> SpecType for super::Choice<A, B> {
    type Type = Either<A::Type, B::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            Either::Left(va) => self.0.wf(va),
            Either::Right(vb) => self.1.wf(vb),
        }
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Choice<A, B> {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n, va)) => Some((n, Either::Left(va))),
            None => match self.1.spec_parse(ibuf) {
                Some((n, vb)) => Some((n, Either::Right(vb))),
                None => None,
            },
        }
    }
}

impl<A: GoodParser, B: GoodParser> GoodParser for super::Choice<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        self.1.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_wf(ibuf);
        self.1.lemma_parse_wf(ibuf);
    }
}

impl<A: SpecSerializer + SpecParser, B: SpecSerializer> SpecSerializer for super::Choice<A, B> {
    #[verusfmt::skip]
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        match v {
            Either::Left(va) => self.0.serializable(va, obuf),
            Either::Right(vb) => {
                &&& self.1.serializable(vb, obuf)
                // To ensure the parser can recover the choice made during serialization
                &&& self.0.spec_parse(self.1.spec_serialize_dps(vb, obuf)) is None
            },
        }
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize_dps(va, obuf),
            Either::Right(vb) => self.1.spec_serialize_dps(vb, obuf),
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize(va),
            Either::Right(vb) => self.1.spec_serialize(vb),
        }
    }
}

impl<A, B> GoodSerializer for super::Choice<A, B> where A: GoodSerializer + SpecParser, B: GoodSerializer {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.lemma_serialize_buf(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.lemma_serialize_buf(vb, obuf);
                },
            }
        }
    }
}

impl<A: SpecCombinator, B: SpecCombinator> SpecCombinator for super::Choice<A, B> {

}

impl<A, B> GoodCombinator for super::Choice<A, B> where A: GoodCombinator, B: GoodCombinator {

}

} // verus!
