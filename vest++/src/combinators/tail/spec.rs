use crate::core::spec::{GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecType};
use vstd::prelude::*;

verus! {

impl SpecType for super::Tail {
    type Type = Seq<u8>;
}

impl SpecParser for super::Tail {
    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        Some((ibuf.len() as int, ibuf))
    }
}

impl GoodParser for super::Tail {
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
}

impl GoodSerializer for super::Tail {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == v + obuf);
    }
}

impl SpecCombinator for super::Tail {

}

impl GoodCombinator for super::Tail {

}

} // verus!
