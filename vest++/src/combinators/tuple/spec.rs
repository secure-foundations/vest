use crate::core::spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

impl<A, B> SpecType for (A, B) where A: SpecType, B: SpecType {
    type Type = (A::Type, B::Type);

    open spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v.0) && self.1.wf(v.1)
    }
}

impl<A, B> SpecParser for (A, B) where A: SpecParser, B: SpecParser {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }

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

impl<A, B> SpecSerializer for (A, B) where A: SpecSerializer, B: SpecSerializer {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        self.1.serializable(v.1, obuf) && self.0.serializable(
            v.0,
            self.1.spec_serialize_dps(v.1, obuf),
        )
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(v.0, self.1.spec_serialize_dps(v.1, obuf))
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1)
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
            let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
            self.1.lemma_serialize_buf(v.1, obuf);
            self.0.lemma_serialize_buf(v.0, serialized1);
            let witness1 = choose|wit1: Seq<u8>|
                self.1.spec_serialize_dps(v.1, obuf) == wit1 + obuf;
            let witness0 = choose|wit0: Seq<u8>|
                self.0.spec_serialize_dps(v.0, serialized1) == wit0 + serialized1;
            assert(serialized0 == witness0 + witness1 + obuf);
        }
    }
}

impl<A, B> SpecCombinator for (A, B) where A: SpecCombinator, B: SpecCombinator {

}

} // verus!
