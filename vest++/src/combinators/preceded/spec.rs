use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer,
    SpecSerializerDps, SpecType, UniqueWfValue,
};
use vstd::prelude::*;

verus! {

impl<A, B> SpecType for super::Preceded<A, B> where A: SpecType, B: SpecType {
    type Type = B::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.1.wf(v)
    }
}

impl<A, B> SpecParser for super::Preceded<A, B> where
    A: SpecParser,
    B: SpecParser,
 {
    type PT = B::PT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match (self.0, self.1).spec_parse(ibuf) {
            Some((n, (_va, vb))) => Some((n, vb)),
            None => None,
        }
    }
}

impl<A, B> GoodParser for super::Preceded<A, B> where A: GoodParser, B: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_wf(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Preceded<A, B> where
    A: SpecType + SpecSerializerDps<ST = <A as SpecType>::Type>,
    B: SpecSerializerDps,
 {
    type ST = B::ST;

    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        // To serialize Preceded, we need a witness value for A
        // We require that there exists some A value that can be serialized before B
        exists|va: A::ST|
            #![trigger self.0.wf(va)]
            { self.0.wf(va) && (self.0, self.1).serializable((va, v), obuf) }
    }

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for A that satisfies the serializable constraint
        let va = choose|va: A::ST|
            #![auto]
            self.0.wf(va) && (self.0, self.1).serializable((va, v), obuf);
        (self.0, self.1).spec_serialize_dps((va, v), obuf)
    }
}

impl<A, B> SpecSerializer for super::Preceded<A, B> where
    A: SpecType + SpecSerializer<ST = <A as SpecType>::Type>,
    B: SpecSerializer,
 {
    type ST = B::ST;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        let va = choose|va: A::ST| self.0.wf(va);
        (self.0, self.1).spec_serialize((va, v))
    }
}

impl<A, B> GoodSerializer for super::Preceded<A, B> where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.serializable(v, obuf) {
            let va = choose|va: A::Type|
                #![auto]
                self.0.wf(va) && (self.0, self.1).serializable((va, v), obuf);
            (self.0, self.1).lemma_serialize_buf((va, v), obuf);
        }
    }
}

} // verus!
