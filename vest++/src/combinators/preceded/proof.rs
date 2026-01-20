use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTrip for super::Preceded<A, B> where
    A: SPRoundTrip + GoodSerializerDps,
    B: SPRoundTrip,
 {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            let va = choose|va: A::ST| #![auto] va.wf();
            (self.0, self.1).theorem_serialize_parse_roundtrip_internal((va, v), obuf);
        }
    }
}

// PSRoundTrip only holds for Preceded when A has a unique well-formed value
impl<A, B> PSRoundTrip for super::Preceded<A, B> where
    A: PSRoundTrip + GoodSerializerDps,
    <A as SpecParser>::PVal: UniqueWfValue,
    B: PSRoundTrip,
 {

}

// NonMalleable only holds for Preceded when A has a unique well-formed value
impl<A, B> NonMalleable for super::Preceded<A, B> where
    A: NonMalleable,
    <A as SpecParser>::PVal: UniqueWfValue,
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
                            va1.lemma_unique_wf_value(&va2);
                            assert((va1, vb1) == (va2, vb2));

                            (self.0, self.1).lemma_parse_non_malleable(buf1, buf2);
                        }
                    }
                }
            }
        }
    }
}

impl<A, B> SpecSerializers for super::Preceded<A, B> where A: SpecSerializers, B: SpecSerializers {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let va = choose|va: A::SVal| va.wf();
        (self.0, self.1).lemma_serialize_equiv((va, v), obuf);
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
