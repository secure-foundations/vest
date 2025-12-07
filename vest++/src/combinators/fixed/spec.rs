use crate::core::spec::SpecCombinator;
use vstd::prelude::*;

verus! {

impl<const N: usize> SpecCombinator for super::Fixed<N> {
    type Type = Seq<u8>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() == N as int
    }

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::Type)> {
        if ibuf.len() < N as int {
            None
        } else {
            Some((N as int, ibuf.take(N as int)))
        }
    }

    open spec fn spec_serialize_dps(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }

    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            assert(self.spec_serialize_dps(v, obuf) == v + obuf);
        }
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
    }
}

} // verus!
