use super::spec::*;
use crate::{
    combinators::{mapped::spec::*, Mapped, Pair, Refined, TryMap},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl<A, B, const CHECK: bool> SPRoundTripDps for super::Preceded<A, A::SValue, B, CHECK> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        // We know that the `BiMap(|pair: (A, B)| pair.1, |b| (a_val, b))` in `preceded` is always sound (the unambiguous condition
        // required by `Mapped<Inner, BiMap<M, MRev>>`).
        // As a result, the unambiguity is equivalent to the unambiguity of the underlying `Pair`.
        Pair(self.a, self.b).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<A, B> NonMalleable for super::Preceded<A, A::PVal, B, true> where
    A: SoundParser + NonMalleable,
    B: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        // When CHECK is true, we check that the value parsed by A is exactly a_val, making the `BiMap` `lossless` (the nonmal_inv condition
        // required by `Mapped<Inner, BiMap<M, MRev>>`).
        // As a result, `nonmal_inv` for `Mapped<Inner, BiMap<M, MRev>>` holds as long as `nonmal_inv` for `Inner` holds.
        &&& Pair(self.a, self.b).sound_inv()
        &&& Pair(self.a, self.b).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, true>(self.a, self.b, self.a_val);
        fmt.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A, B> NonMalleable for super::Preceded<A, A::PVal, B, false> where
    A: SoundParser + NonMalleable + AdmitsUniqueVal,
    B: SoundParser + NonMalleable,
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
                    self.a.lemma_unique_consistent_val(p1.0, p2.0);
                    pair.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<A, B, const CHECK: bool> NoLookAhead for super::Preceded<A, A::PVal, B, CHECK> where
    A: NoLookAhead,
    B: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_no_lookahead(i1, i2);
    }
}

impl<A, B, const CHECK: bool> EquivSerializersGeneral for super::Preceded<
    A,
    A::SValue,
    B,
    CHECK,
> where A: EquivSerializersGeneral + Consistency<Val = A::SVal>, B: EquivSerializersGeneral {
    open spec fn equiv_general_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, const CHECK: bool> EquivSerializers for super::Preceded<A, A::SValue, B, CHECK> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let fmt = preceded::<_, _, _, _, CHECK>(self.a, self.b, self.a_val);
        fmt.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
