use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for (A, B) where A: SpecParser, B: SpecParser {
    type PT = (A::PT, B::PT);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }
}

impl<A, B> GoodParser for (A, B) where A: GoodParser, B: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_length(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_wf(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_wf(ibuf.skip(n1));
        }
    }
}

impl<A, B> SpecSerializerDps for (A, B) where A: SpecSerializerDps, B: SpecSerializerDps {
    type ST = (A::ST, B::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(v.0, self.1.spec_serialize_dps(v.1, obuf))
    }
}

impl<A, B> SpecSerializer for (A, B) where A: SpecSerializer, B: SpecSerializer {
    type ST = (A::ST, B::ST);

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1)
    }
}

impl<A, B> Serializability for (A, B) where A: Serializability, B: Serializability {
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        self.1.serializable(v.1, obuf) && self.0.serializable(
            v.0,
            self.1.spec_serialize_dps(v.1, obuf),
        )
    }
}

impl<A, B> Unambiguity for (A, B) where A: Unambiguity, B: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        self.1.unambiguous() && self.0.unambiguous()
    }
}

impl<A, B> GoodSerializerDps for (A, B) where A: GoodSerializerDps, B: GoodSerializerDps {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
        self.1.lemma_serialize_dps_buf(v.1, obuf);
        self.0.lemma_serialize_dps_buf(v.0, serialized1);
        let witness1 = choose|wit1: Seq<u8>| self.1.spec_serialize_dps(v.1, obuf) == wit1 + obuf;
        let witness0 = choose|wit0: Seq<u8>|
            self.0.spec_serialize_dps(v.0, serialized1) == wit0 + serialized1;
        assert(serialized0 == witness0 + witness1 + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v.1, obuf);
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        self.0.lemma_serialize_dps_len(v.0, serialized1);
    }
}

impl<A, B> GoodSerializer for (A, B) where A: GoodSerializer, B: GoodSerializer {
    proof fn lemma_serialize_len(&self, v: Self::ST) {
        self.1.lemma_serialize_len(v.1);
        self.0.lemma_serialize_len(v.0);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for (A, B) {
    type T = (A::T, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.0.byte_len(v.0) + self.1.byte_len(v.1)
    }
}

} // verus!
