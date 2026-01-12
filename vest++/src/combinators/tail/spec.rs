use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, Serializability, SpecCombinator, SpecParser,
    SpecSerializer, SpecSerializerDps, SpecType,
};
use vstd::prelude::*;

verus! {

impl SpecType for super::Tail {
    type Type = Seq<u8>;
}

impl SpecParser for super::Tail {
    type PT = <Self as SpecType>::Type;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        Some((ibuf.len() as int, ibuf))
    }
}

impl GoodParser for super::Tail {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Tail {
    type ST = <Self as SpecType>::Type;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

impl SpecSerializer for super::Tail {
    type ST = <Self as SpecType>::Type;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        v
    }
}

impl Serializability for super::Tail {
    open spec fn serializable(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
        obuf.len() == 0
    }
}

impl GoodSerializer for super::Tail {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == v + obuf);
    }
}

} // verus!
