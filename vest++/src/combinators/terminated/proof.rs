use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps,
        SpecType, UniqueWfValue,
    },
};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTrip for super::Terminated<A, B> where A: SPRoundTrip, B: SPRoundTrip {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        let vb = choose|vb: B::Type| #![auto] self.1.wf(vb) && self.1.serializable(vb, obuf);
        (self.0, self.1).theorem_serialize_parse_roundtrip((v, vb), obuf);
    }
}

// PSRoundTrip only holds for Terminated when B has a unique well-formed value
impl<A, B> PSRoundTrip for super::Terminated<A, B> where
    A: PSRoundTrip,
    B: PSRoundTrip + UniqueWfValue,
 {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        if let Some((_, (va, vb))) = (self.0, self.1).spec_parse(ibuf) {
            if self.serializable(va, obuf) {
                let vb_witness = choose|vb_w: B::Type|
                    #![auto]
                    self.1.wf(vb_w) && self.1.serializable(vb_w, obuf);
                (self.0, self.1).lemma_parse_wf(ibuf);
                self.1.lemma_unique_wf_value(vb_witness, vb);
                assert(vb_witness == vb);

                (self.0, self.1).theorem_parse_serialize_roundtrip(ibuf, obuf);
            }
        }
    }
}

// NonMalleable only holds for Terminated when B has a unique well-formed value
impl<A, B> NonMalleable for super::Terminated<A, B> where
    A: NonMalleable,
    B: NonMalleable + UniqueWfValue,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    if let Some((_, (va1, vb1))) = (self.0, self.1).spec_parse(buf1) {
                        if let Some((_, (va2, vb2))) = (self.0, self.1).spec_parse(buf2) {
                            (self.0, self.1).lemma_parse_wf(buf1);
                            (self.0, self.1).lemma_parse_wf(buf2);
                            self.1.lemma_unique_wf_value(vb1, vb2);
                            assert((va1, vb1) == (va2, vb2));

                            (self.0, self.1).lemma_parse_non_malleable(buf1, buf2);
                        }
                    }
                }
            }
        }
    }
}

// Deterministic only holds for Terminated when B has a unique well-formed value
impl<A, B> Deterministic for super::Terminated<A, B> where
    A: Deterministic,
    B: Deterministic + UniqueWfValue,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) && self.serializable(v, obuf) {
            let vb_dps = choose|vb: B::Type|
                #![auto]
                self.1.wf(vb) && self.1.serializable(vb, obuf);
            let vb_ser = choose|vb: B::Type| self.1.wf(vb);

            // Since B has unique well-formed values, both witnesses are equal
            self.1.lemma_unique_wf_value(vb_dps, vb_ser);

            (self.0, self.1).lemma_serialize_equiv((v, vb_dps), obuf);
        }
    }
}

} // verus!
