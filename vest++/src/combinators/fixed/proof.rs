use vstd::prelude::*;
use crate::core::{spec::SpecCombinator, proof::SpecCombinatorProof};

verus! {

impl<const N: usize> SpecCombinatorProof for crate::combinators::fixed::Fixed<N> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            assert(self.spec_serialize(v, obuf) == v + obuf);
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
    }
}

} // verus!
