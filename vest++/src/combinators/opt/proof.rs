use vstd::prelude::*;
use crate::core::{spec::SpecCombinator, proof::SpecCombinatorProof};

verus! {

impl<A> SpecCombinatorProof for crate::combinators::opt::Opt<A> where A: SpecCombinator + SpecCombinatorProof {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize(v, obuf) == Seq::empty() + obuf);
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.lemma_serialize_buf(vv, obuf);
                }
            },
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize(v, obuf) == obuf);
                if let Some((n, v)) = self.spec_parse(obuf) {
                    assert(n == 0);
                    assert(v == Option::<A::Type>::None);
                }
            },
            Some(vv) => {
                if self.wf(v) {
                    self.0.theorem_serialize_parse_roundtrip(vv, obuf);
                }
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n, v)) = self.spec_parse(ibuf) {
            match v {
                None => {
                    assert(n == 0);
                    assert(self.spec_serialize(v, obuf) == obuf);
                },
                Some(vv) => {
                    self.0.theorem_parse_serialize_roundtrip(ibuf, obuf);
                },
            }
        }
    }
}

} // verus!
