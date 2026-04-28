use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner: SPRoundTripDps> SPRoundTripDps for super::Named<Inner> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::Named<Inner> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: NoLookAhead> NoLookAhead for super::Named<Inner> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.0.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        self.0.lemma_no_lookahead(i1, i2);
    }
}

impl<Inner: EquivSerializersGeneral> EquivSerializersGeneral for super::Named<Inner> {
    open spec fn equiv_general_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.0.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner: EquivSerializers> EquivSerializers for super::Named<Inner> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.0.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
