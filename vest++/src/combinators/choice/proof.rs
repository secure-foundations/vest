use vstd::prelude::*;
use crate::core::{spec::SpecCombinator, proof::SpecCombinatorProof};
use crate::combinators::Either;

verus! {

impl<A: SpecCombinator + SpecCombinatorProof, B: SpecCombinator + SpecCombinatorProof> SpecCombinatorProof for crate::combinators::choice::Choice<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        self.1.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.lemma_serialize_buf(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.lemma_serialize_buf(vb, obuf);
                },
            }
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            match v {
                Either::Left(va) => {
                    self.0.theorem_serialize_parse_roundtrip(va, obuf);
                },
                Either::Right(vb) => {
                    self.1.theorem_serialize_parse_roundtrip(vb, obuf);
                },
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
        self.1.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

} // verus!
