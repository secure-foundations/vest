use vstd::prelude::*;
use crate::core::{spec::SpecCombinator, proof::SpecCombinatorProof};

verus! {

impl<A: SpecCombinator + SpecCombinatorProof> SpecCombinatorProof for crate::combinators::refined::Refined<A> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_buf(v, obuf);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(v, obuf);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

} // verus!
