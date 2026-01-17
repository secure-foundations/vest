use crate::core::spec::{
    GoodParser, GoodSerializer, Serializability, SpecParser, SpecSerializer, SpecSerializerDps,
    SpecType, UniqueWfValue,
};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Preceded<A, B> where A: SpecParser, B: SpecParser {
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
    A: Serializability,
    B: SpecSerializerDps,
 {
    type ST = B::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for A that satisfies the serializable constraint
        let va = choose|va: A::ST|
            #![auto]
            va.wf() && self.0.serializable(va, self.1.spec_serialize_dps(v, obuf));
        (self.0, self.1).spec_serialize_dps((va, v), obuf)
    }
}

impl<A, B> SpecSerializer for super::Preceded<A, B> where A: SpecSerializer, B: SpecSerializer {
    type ST = B::ST;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        let va = choose|va: A::ST| va.wf();
        (self.0, self.1).spec_serialize((va, v))
    }
}

impl<A, B> Serializability for super::Preceded<A, B> where A: Serializability, B: Serializability {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        // To serialize Preceded, we need a witness value for A
        // We require that there exists some A value that can be serialized before B
        &&& self.1.serializable(v, obuf)
        &&& exists|va: A::ST|
            #![trigger va.wf()]
            { va.wf() && self.0.serializable(va, self.1.spec_serialize_dps(v, obuf)) }
    }
}

impl<A, B> GoodSerializer for super::Preceded<A, B> where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        if self.serializable(v, obuf) {
            let va = choose|va: A::ST|
                #![auto]
                va.wf() && self.0.serializable(va, self.1.spec_serialize_dps(v, obuf));
            (self.0, self.1).lemma_serialize_buf((va, v), obuf);
        }
    }
}

} // verus!
