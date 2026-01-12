use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, Serializability, SpecCombinator, SpecParser,
    SpecSerializer, SpecSerializerDps, SpecType, UniqueWfValue,
};
use vstd::prelude::*;

verus! {

impl<A, B> SpecType for super::Terminated<A, B> where A: SpecType, B: SpecType {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }
}

impl<A, B> SpecParser for super::Terminated<A, B> where A: SpecParser, B: SpecParser {
    type PT = A::PT;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match (self.0, self.1).spec_parse(ibuf) {
            Some((n, (va, _vb))) => Some((n, va)),
            None => None,
        }
    }
}

impl<A, B> GoodParser for super::Terminated<A, B> where A: GoodParser, B: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_wf(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Terminated<A, B> where
    A: SpecSerializerDps,
    B: Serializability,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for B that satisfies the serializable constraint
        let vb = choose|vb: B::Type| #![auto] self.1.wf(vb) && self.1.serializable(vb, obuf);
        (self.0, self.1).spec_serialize_dps((v, vb), obuf)
    }
}

impl<A, B> SpecSerializer for super::Terminated<A, B> where
    A: SpecSerializer,
    B: SpecType + SpecSerializer<ST = <B as SpecType>::Type>,
 {
    type ST = A::ST;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        let vb = choose|vb: B::ST| self.1.wf(vb);
        (self.0, self.1).spec_serialize((v, vb))
    }
}

impl<A, B> Serializability for super::Terminated<A, B> where
    A: Serializability,
    B: Serializability,
 {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        // To serialize Terminated, we need a witness value for B
        // We require that there exists some B value that can be serialized after A
        &&& exists|vb: B::Type|
            #![trigger self.1.wf(vb)]
            { self.1.wf(vb) && self.1.serializable(vb, obuf) }
        &&& self.0.serializable(
            v,
            self.1.spec_serialize_dps(
                choose|vb: B::Type|
                    #![trigger self.1.wf(vb)]
                    self.1.wf(vb) && self.1.serializable(vb, obuf),
                obuf,
            ),
        )
    }
}

impl<A, B> GoodSerializer for super::Terminated<A, B> where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.serializable(v, obuf) {
            let vb = choose|vb: B::Type| #![auto] self.1.wf(vb) && self.1.serializable(vb, obuf);
            (self.0, self.1).lemma_serialize_buf((v, vb), obuf);
        }
    }
}

} // verus!
