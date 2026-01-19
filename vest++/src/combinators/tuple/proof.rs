use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip + GoodSerializer, B: SPRoundTrip> SPRoundTrip for (A, B) {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
            let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
            let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
            self.1.theorem_serialize_parse_roundtrip(v.1, obuf);
            self.0.theorem_serialize_parse_roundtrip(v.0, serialized1);
            // self.1.lemma_serialize_buf(v.1, obuf);
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
}

impl<A: PSRoundTrip + GoodSerializer, B: PSRoundTrip> PSRoundTrip for (A, B) {
}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for (A, B) {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (n1a, _) = self.0.spec_parse(buf1)->0;
                    let (n2a, _) = self.0.spec_parse(buf2)->0;
                    let (n1b, _) = self.1.spec_parse(buf1.skip(n1a))->0;
                    let (n2b, _) = self.1.spec_parse(buf2.skip(n2a))->0;
                    self.0.lemma_parse_length(buf1);
                    self.0.lemma_parse_length(buf2);
                    self.1.lemma_parse_length(buf1.skip(n1a));
                    self.1.lemma_parse_length(buf2.skip(n2a));
                    self.0.lemma_parse_non_malleable(buf1, buf2);
                    self.1.lemma_parse_non_malleable(buf1.skip(n1a), buf2.skip(n2a));
                    assert(n1 == n1a + n1b && n2 == n2a + n2b);
                    assert(buf1.take(n1) == buf2.take(n2)) by {
                        assert(buf1.take(n1) == buf1.take(n1a) + buf1.skip(n1a).take(n1b));
                        assert(buf2.take(n2) == buf2.take(n2a) + buf2.skip(n2a).take(n2b));
                    }
                }
            }
        }
    }
}

impl<A, B> Deterministic for (A, B) where A: Deterministic, B: Deterministic {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
            let obuf1 = self.1.spec_serialize_dps(v.1, obuf);

            self.1.lemma_serialize_equiv(v.1, obuf);
            self.0.lemma_serialize_equiv(v.0, obuf1);

            // From self.1.lemma_serialize_equiv:
            // self.1.spec_serialize_dps(v.1, obuf) == self.1.spec_serialize(v.1) + obuf
            // So: obuf1 == self.1.spec_serialize(v.1) + obuf

            // From self.0.lemma_serialize_equiv:
            // self.0.spec_serialize_dps(v.0, obuf1) == self.0.spec_serialize(v.0) + obuf1

            // Therefore:
            // spec_serialize_dps(v, obuf) = self.0.spec_serialize_dps(v.0, obuf1)
            //                              = self.0.spec_serialize(v.0) + obuf1
            //                              = self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1) + obuf
            //                              = spec_serialize(v) + obuf
    }
}

} // verus!
