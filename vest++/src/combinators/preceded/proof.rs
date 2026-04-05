use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SPRoundTripDps for super::Preceded<A, B> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::T, B::T>(self.0, self.1).sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::T, B::T>(
            self.0,
            self.1,
        ).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<A, B> NonMalleable for super::Preceded<A, B> where
    A: NonMalleable + AdmitsUniqueVal,
    B: NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_parse_non_malleable(
            buf1,
            buf2,
        );
    }
}

impl<A, B> NoLookAhead for super::Preceded<A, B> where
    A: NoLookAhead + AdmitsUniqueVal,
    B: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        super::preceded_fmt::<A, B, A::PVal, B::PVal>(self.0, self.1).lemma_no_lookahead(i1, i2);
    }
}

impl<A, B> EquivSerializersGeneral for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).lemma_serialize_equiv(
            v,
            obuf,
        );
    }
}

impl<A, B> EquivSerializers for super::Preceded<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(self.0, self.1).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        super::preceded_fmt::<A, B, A::SVal, B::SVal>(
            self.0,
            self.1,
        ).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
