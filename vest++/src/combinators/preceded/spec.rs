use crate::core::{proof::*, spec::*};
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
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = B::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        // Use an arbitrary witness value for A that satisfies the wf constraint
        let va = choose|va: A::ST| va.wf();
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

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Preceded<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& (self.0, self.1).unambiguous()
        &&& exists|va: A::ST| va.wf()
    }
}

impl<A, B> GoodSerializer for super::Preceded<A, B> where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let va = choose|va: A::ST| #![auto] va.wf();
        (self.0, self.1).lemma_serialize_buf((va, v), obuf);
    }
}

} // verus!
