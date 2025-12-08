use crate::core::spec::{SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

impl SpecType for super::Tail {
    type Type = Seq<u8>;
}

impl SpecParser for super::Tail {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        Some((ibuf.len() as int, ibuf))
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializer for super::Tail {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        obuf.len() == 0
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == v + obuf);
    }

    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
    }
}

impl SpecCombinator for super::Tail {

}

} // verus!
