use crate::core::spec::{
    GoodCombinator, GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer,
    SpecSerializerDps, SpecType,
};
use vstd::prelude::*;

verus! {

impl<const N: usize> SpecType for super::Fixed<N> {
    type Type = Seq<u8>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() == N as int
    }
}

impl<const N: usize> SpecParser for super::Fixed<N> {
    type PT = <Self as SpecType>::Type;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PT)> {
        if ibuf.len() < N as int {
            None
        } else {
            Some((N as int, ibuf.take(N as int)))
        }
    }
}

impl<const N: usize> GoodParser for super::Fixed<N> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl<const N: usize> SpecSerializerDps for super::Fixed<N> {
    type ST = <Self as SpecType>::Type;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

impl<const N: usize> SpecSerializer for super::Fixed<N> {
    type ST = <Self as SpecType>::Type;

    open spec fn spec_serialize(&self, v: Self::ST) -> Seq<u8> {
        v
    }
}

impl<const N: usize> GoodSerializer for super::Fixed<N> {
    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            assert(self.spec_serialize_dps(v, obuf) == v + obuf);
        }
    }
}

} // verus!
