use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTripDps for super::Preceded<A, B> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let va = choose|va: A::ST| #![auto] self.0.consistent(va);
        (self.0, self.1).theorem_serialize_dps_parse_roundtrip((va, v), obuf);
    }
}

// // PSRoundTrip only holds for Preceded when A has a unique consistent value
// impl<A, B> PSRoundTrip for super::Preceded<A, B> where
//     A: PSRoundTrip + GoodSerializerDps + EquivSerializersGeneral,
//     A: AdmitsUniqueVal<T = A::PVal>,
//     B: PSRoundTrip,
//  {
// }
// NonMalleable only holds for Preceded when A has a unique consistent value
impl<A, B> NonMalleable for super::Preceded<A, B> where
    A: NonMalleable + AdmitsUniqueVal,
    B: NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    if let Some((_, (va1, vb1))) = (self.0, self.1).spec_parse(buf1) {
                        if let Some((_, (va2, vb2))) = (self.0, self.1).spec_parse(buf2) {
                            (self.0, self.1).lemma_parse_sound_value(buf1);
                            (self.0, self.1).lemma_parse_sound_value(buf2);
                            self.0.lemma_unique_consistent_val(va1, va2);
                            assert((va1, vb1) == (va2, vb2));

                            (self.0, self.1).lemma_parse_non_malleable(buf1, buf2);
                        }
                    }
                }
            }
        }
    }
}

impl<A, B> NoLookAhead for super::Preceded<A, B> where
    A: NoLookAhead + AdmitsUniqueVal,
    B: NoLookAhead,
 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, vb)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    (self.0, self.1).lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<A, B> EquivSerializersGeneral for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let va = choose|va: A::SVal| self.0.consistent(va);
        (self.0, self.1).lemma_serialize_equiv((va, v), obuf);
    }
}

impl<A, B> EquivSerializers for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let va = choose|va: A::SVal| self.0.consistent(va);
        let empty = Seq::empty();
        let obuf = self.1.spec_serialize_dps(v, empty);
        self.1.lemma_serialize_equiv_on_empty(v);
        self.0.lemma_serialize_equiv(va, obuf);
    }
}

} // verus!
