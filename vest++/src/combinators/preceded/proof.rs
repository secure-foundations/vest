use crate::{
    combinators::Pair,
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTripDps for super::Preceded<A, B> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        Pair(self.0, self.1).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let va = choose|va: A::T| self.0.consistent(va);
        let pair = Pair(self.0, self.1);
        assert(pair.consistent((va, v)));
        pair.theorem_serialize_dps_parse_roundtrip((va, v), obuf);
        assert(self.byte_len(v) == pair.byte_len((va, v)));
    }
}

impl<A, B> NonMalleable for super::Preceded<A, B> where
    A: SoundParser + NonMalleable + AdmitsUniqueVal,
    B: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& Pair(self.0, self.1).nonmal_inv()
        &&& Pair(self.0, self.1).sound_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    assert(pair.spec_parse(buf1) matches Some((_, _)));
                    assert(pair.spec_parse(buf2) matches Some((_, _)));
                    let (_m1, p1) = pair.spec_parse(buf1)->0;
                    let (_m2, p2) = pair.spec_parse(buf2)->0;
                    assert(p1.1 == v1);
                    assert(p2.1 == v2);
                    pair.lemma_parse_sound_value(buf1);
                    pair.lemma_parse_sound_value(buf2);
                    self.0.lemma_unique_consistent_val(p1.0, p2.0);
                    assert(p1 == p2);
                    pair.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<A, B> NoLookAhead for super::Preceded<A, B> where A: NoLookAhead, B: NoLookAhead {
    open spec fn no_lookahead_inv(&self) -> bool {
        Pair(self.0, self.1).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let pair = Pair(self.0, self.1);
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(pair.spec_parse(i1) matches Some((_, _)));
                    let (_m, p) = pair.spec_parse(i1)->0;
                    assert(p.1 == v);
                    pair.lemma_no_lookahead(i1, i2);
                    assert(self.spec_parse(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<A, B> EquivSerializersGeneral for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        Pair(self.0, self.1).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let va = choose|va: A::SVal| self.0.consistent(va);
        Pair(self.0, self.1).lemma_serialize_equiv((va, v), obuf);
    }
}

impl<A, B> EquivSerializers for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        Pair(self.0, self.1).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let va = choose|va: A::SVal| self.0.consistent(va);
        Pair(self.0, self.1).lemma_serialize_equiv_on_empty((va, v));
    }
}

} // verus!
