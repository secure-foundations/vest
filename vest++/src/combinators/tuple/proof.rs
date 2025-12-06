use vstd::prelude::*;
use crate::core::{spec::SpecCombinator, proof::SpecCombinatorProof};

verus! {

impl<A, B> SpecCombinatorProof for (A, B) where A: SpecCombinator + SpecCombinatorProof, B: SpecCombinator + SpecCombinatorProof {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_length(ibuf.skip(n1));
        }
    }

    proof fn lemma_serialize_buf(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            let serialized1 = self.1.spec_serialize(v.1, obuf);
            let serialized0 = self.0.spec_serialize(v.0, serialized1);
            self.1.lemma_serialize_buf(v.1, obuf);
            self.0.lemma_serialize_buf(v.0, serialized1);
            let witness1 = choose|wit1: Seq<u8>| self.1.spec_serialize(v.1, obuf) == wit1 + obuf;
            let witness0 = choose|wit0: Seq<u8>|
                self.0.spec_serialize(v.0, serialized1) == wit0 + serialized1;
            assert(serialized0 == witness0 + witness1 + obuf);
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) {
            let serialized1 = self.1.spec_serialize(v.1, obuf);
            let serialized0 = self.0.spec_serialize(v.0, serialized1);
            self.1.theorem_serialize_parse_roundtrip(v.1, obuf);
            self.0.theorem_serialize_parse_roundtrip(v.0, serialized1);
            self.1.lemma_serialize_buf(v.1, obuf);
            self.0.lemma_serialize_buf(v.0, serialized1);
            if let Some((n0, v0)) = self.0.spec_parse(serialized0) {
                assert(n0 == serialized0.len() - serialized1.len());
                assert(serialized0.skip(n0) == serialized1);
                if let Some((n1, v1)) = self.1.spec_parse(serialized0.skip(n0)) {
                    assert(n1 == serialized1.len() - obuf.len());
                    assert(v == (v0, v1));
                    assert(self.spec_parse(serialized0) == Some((n0 + n1, (v0, v1))));
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_length(ibuf.skip(n1));
            if let Some((n2, v2)) = self.1.spec_parse(ibuf.skip(n1)) {
                let serialized2 = self.1.spec_serialize(v2, obuf);
                let serialized1 = self.0.spec_serialize(v1, serialized2);
                self.0.theorem_parse_serialize_roundtrip(ibuf, serialized2);
                self.1.theorem_parse_serialize_roundtrip(ibuf.skip(n1), obuf);
            }
        }
    }
}

} // verus!
