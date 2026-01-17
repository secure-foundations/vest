use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodParser, GoodSerializer, Serializability, SpecCombinator, SpecParser, SpecSerializer,
        SpecSerializerDps, SpecType, UniqueWfValue,
    },
};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTrip for super::Terminated<A, B> where A: SPRoundTrip, B: SPRoundTrip {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        let vb = choose|vb: B::ST| #![auto] vb.wf() && self.1.serializable(vb, obuf);
        (self.0, self.1).theorem_serialize_parse_roundtrip((v, vb), obuf);
    }
}

// PSRoundTrip only holds for Terminated when B has a unique well-formed value
impl<A, B> PSRoundTrip for super::Terminated<A, B> where
    A: PSRoundTrip,
    B: PSRoundTrip,
    <B as SpecParser>::PT: UniqueWfValue,
 {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        if let Some((_, (va, vb))) = (self.0, self.1).spec_parse(ibuf) {
            if self.serializable(va, obuf) {
                let vb_witness = choose|vb_w: B::PT|
                    #![auto]
                    vb_w.wf() && self.1.serializable(vb_w, obuf);
                (self.0, self.1).lemma_parse_wf(ibuf);
                vb_witness.lemma_unique_wf_value(&vb);
                assert(vb_witness == vb);

                (self.0, self.1).theorem_parse_serialize_roundtrip(ibuf, obuf);
            }
        }
    }
}

// NonMalleable only holds for Terminated when B has a unique well-formed value
impl<A, B> NonMalleable for super::Terminated<A, B> where
    A: NonMalleable,
    B: NonMalleable,
    <B as SpecParser>::PT: UniqueWfValue,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    if let Some((_, (va1, vb1))) = (self.0, self.1).spec_parse(buf1) {
                        if let Some((_, (va2, vb2))) = (self.0, self.1).spec_parse(buf2) {
                            (self.0, self.1).lemma_parse_wf(buf1);
                            (self.0, self.1).lemma_parse_wf(buf2);
                            vb1.lemma_unique_wf_value(&vb2);
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
    B: Deterministic,
    <B as SpecSerializer>::ST: UniqueWfValue,
 {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
        if v.wf() && self.serializable(v, obuf) {
            let vb_dps = choose|vb: <B as SpecSerializer>::ST|
                #![auto]
                vb.wf() && self.1.serializable(vb, obuf);
            let vb_ser = choose|vb: <B as SpecSerializer>::ST| vb.wf();

            // Since B has unique well-formed values, both witnesses are equal
            vb_dps.lemma_unique_wf_value(&vb_ser);

            (self.0, self.1).lemma_serialize_equiv((v, vb_dps), obuf);
        }
    }
}

} // verus!
