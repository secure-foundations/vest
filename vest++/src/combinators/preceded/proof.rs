use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        GoodParser, GoodSerializer, SpecCombinator, SpecParser, SpecSerializer, SpecSerializerDps,
        SpecType, UniqueWfValue,
    },
};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTrip for super::Preceded<A, B> where A: SPRoundTrip, B: SPRoundTrip {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        let va = choose|va: A::ST|
            #![auto]
            self.0.wf(va) && self.0.serializable(va, self.1.spec_serialize_dps(v, obuf));
        (self.0, self.1).theorem_serialize_parse_roundtrip((va, v), obuf);
    }
}

// PSRoundTrip only holds for Preceded when A has a unique well-formed value
impl<A, B> PSRoundTrip for super::Preceded<A, B> where
    A: PSRoundTrip + UniqueWfValue,
    B: PSRoundTrip,
 {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        if let Some((_, (va, vb))) = (self.0, self.1).spec_parse(ibuf) {
            if self.serializable(vb, obuf) {
                let va_witness = choose|va: A::Type|
                    #![auto]
                    self.0.wf(va) && self.0.serializable(va, self.1.spec_serialize_dps(vb, obuf));
                (self.0, self.1).lemma_parse_wf(ibuf);
                self.0.lemma_unique_wf_value(va_witness, va);
                assert(va_witness == va);

                (self.0, self.1).theorem_parse_serialize_roundtrip(ibuf, obuf);
            }
        }
    }
}

// NonMalleable only holds for Preceded when A has a unique well-formed value
impl<A, B> NonMalleable for super::Preceded<A, B> where
    A: NonMalleable + UniqueWfValue,
    B: NonMalleable,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    if let Some((_, (va1, vb1))) = (self.0, self.1).spec_parse(buf1) {
                        if let Some((_, (va2, vb2))) = (self.0, self.1).spec_parse(buf2) {
                            (self.0, self.1).lemma_parse_wf(buf1);
                            (self.0, self.1).lemma_parse_wf(buf2);
                            self.0.lemma_unique_wf_value(va1, va2);
                            assert((va1, vb1) == (va2, vb2));

                            (self.0, self.1).lemma_parse_non_malleable(buf1, buf2);
                        }
                    }
                }
            }
        }
    }
}

// Deterministic only holds for Preceded when A has a unique well-formed value
impl<A, B> Deterministic for super::Preceded<A, B> where
    A: Deterministic + UniqueWfValue,
    B: Deterministic,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
        if self.wf(v) && self.serializable(v, obuf) {
            let va_dps = choose|va: A::Type|
                #![auto]
                self.0.wf(va) && self.0.serializable(va, self.1.spec_serialize_dps(v, obuf));
            let va_ser = choose|va: A::Type| self.0.wf(va);

            // Since A has unique well-formed values, both witnesses are equal
            self.0.lemma_unique_wf_value(va_dps, va_ser);

            (self.0, self.1).lemma_serialize_equiv((va_dps, v), obuf);
        }
    }
}

// spec fn in_range(n: int, low: int, high: int) -> bool {
//     low <= n <= high
// }
// spec fn choose_test(a: int, b: int) -> Seq<u8> {
//     let len = choose|n: int| in_range(n, a, b);
//     Seq::new(len as nat, |i: int| 0u8)
// }
// proof fn test_exists_spec() {
//     let s1 = choose_test(3, 8);
//     let s2 = choose_test(3, 8);
//     assert(s1 == s2);
// }
} // verus!
