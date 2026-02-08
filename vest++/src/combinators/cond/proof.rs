use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner: SPRoundTripDps> SPRoundTripDps for super::Cond<Inner> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.1.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::Cond<Inner> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.1.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: EquivSerializersGeneral> EquivSerializersGeneral for super::Cond<Inner> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.1.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner: EquivSerializers> EquivSerializers for super::Cond<Inner> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
