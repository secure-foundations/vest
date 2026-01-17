use crate::core::spec::{
    GoodParser, GoodSerializer, Serializability, SpecParser, SpecSerializer, SpecSerializerDps,
    SpecType,
};
use vstd::prelude::*;

verus! {

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Choice<A, B> {
    type PT = Either<A::PT, B::PT>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
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

impl<A, B> SpecSerializerDps for super::Choice<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = Either<A::ST, B::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize_dps(va, obuf),
            Either::Right(vb) => self.1.spec_serialize_dps(vb, obuf),
        }
    }
}

impl<A, B> SpecSerializer for super::Choice<A, B> where A: SpecSerializer, B: SpecSerializer {
    type ST = Either<A::ST, B::ST>;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize(va),
            Either::Right(vb) => self.1.spec_serialize(vb),
        }
    }
}

impl<A, B> Serializability for super::Choice<A, B> where
    A: Serializability + SpecParser,
    B: Serializability,
 {
    #[verusfmt::skip]
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        match v {
            Either::Left(va) => self.0.serializable(va, obuf),
            Either::Right(vb) => {
                &&& self.1.serializable(vb, obuf)
                // To ensure the parser can recover the choice made during serialization
                &&& self.0.spec_parse(self.1.spec_serialize_dps(vb, obuf)) is None
            },
        }
    }
}

impl<A, B> GoodSerializer for super::Choice<A, B> where
    A: GoodSerializer + SpecParser,
    B: GoodSerializer,
 {
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
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

} // verus!
