use crate::core::spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType, UniqueWfValue};
use vstd::prelude::*;

verus! {

impl<A, B> SpecType for super::Terminated<A, B> where A: SpecType, B: SpecType {
    type Type = A::Type;

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }
}

impl<A, B> SpecParser for super::Terminated<A, B> where A: SpecParser, B: SpecParser {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match (self.0, self.1).spec_parse(ibuf) {
            Some((n, (va, _vb))) => Some((n, va)),
            None => None,
        }
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        (self.0, self.1).lemma_parse_wf(ibuf);
    }
}

impl<A, B> SpecSerializer for super::Terminated<A, B> where A: SpecSerializer, B: SpecSerializer {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        // To serialize Terminated, we need a witness value for B
        // We require that there exists some B value that can be serialized after A
        exists|vb: B::Type|
            #![auto]
            { self.1.wf(vb) && (self.0, self.1).serializable((v, vb), obuf) }
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for B that satisfies the serializable constraint
        let vb = choose|vb: B::Type|
            #![auto]
            self.1.wf(vb) && (self.0, self.1).serializable((v, vb), obuf);
        (self.0, self.1).spec_serialize_dps((v, vb), obuf)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let vb = choose|vb: B::Type| self.1.wf(vb);
        (self.0, self.1).spec_serialize((v, vb))
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.serializable(v, obuf) {
            let vb = choose|vb: B::Type|
                #![auto]
                self.1.wf(vb) && (self.0, self.1).serializable((v, vb), obuf);
            (self.0, self.1).lemma_serialize_buf((v, vb), obuf);
        }
    }
}

impl<A, B> SpecCombinator for super::Terminated<A, B> where A: SpecCombinator, B: SpecCombinator {

}

} // verus!
