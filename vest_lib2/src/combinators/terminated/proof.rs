use super::spec::*;
use crate::{
    combinators::Pair,
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl<A, B, const CHECK: bool> SPRoundTripDps for super::Terminated<A, B, B::SValue, CHECK> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        Pair(self.a, self.b).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<A, B> NonMalleable for super::Terminated<A, B, B::PVal, true> where
    A: SoundParser + NonMalleable,
    B: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& Pair(self.a, self.b).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, true>(self.a, self.b, self.b_val);
        fmt.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A, B> NonMalleable for super::Terminated<A, B, B::PVal, false> where
    A: SoundParser + NonMalleable,
    B: SoundParser + NonMalleable + AdmitsUniqueVal,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& Pair(self.a, self.b).sound_inv()
        &&& Pair(self.a, self.b).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let pair = Pair(self.a, self.b);
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (_m1, p1) = pair.spec_parse(buf1)->0;
                    let (_m2, p2) = pair.spec_parse(buf2)->0;
                    pair.lemma_parse_sound_value(buf1);
                    pair.lemma_parse_sound_value(buf2);
                    self.b.lemma_unique_consistent_val(p1.1, p2.1);
                    pair.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<A, B, const CHECK: bool> NoLookAhead for super::Terminated<A, B, B::PVal, CHECK> where
    A: NoLookAhead,
    B: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_no_lookahead(i1, i2);
    }
}

impl<A, B, const CHECK: bool> EquivSerializersGeneral for super::Terminated<
    A,
    B,
    B::SValue,
    CHECK,
> where A: EquivSerializersGeneral, B: EquivSerializersGeneral + Consistency<Val = B::SVal> {
    open spec fn equiv_general_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, const CHECK: bool> EquivSerializers for super::Terminated<A, B, B::SValue, CHECK> where
    A: EquivSerializersGeneral,
    B: EquivSerializers + Consistency<Val = B::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let fmt = terminated::<_, _, _, _, CHECK>(self.a, self.b, self.b_val);
        fmt.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
