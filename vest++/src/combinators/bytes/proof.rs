use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<const N: usize> SPRoundTripDps for super::Fixed<N> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

        if v.wf() {
        }
    }
}

impl<const N: usize> NonMalleable for super::Fixed<N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> EquivSerializersGeneral for super::Fixed<N> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
    }
}

impl<const N: usize> EquivSerializers for super::Fixed<N> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl SPRoundTripDps for super::Varied {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>)
    {
    }
}

impl NonMalleable for super::Varied {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl EquivSerializersGeneral for super::Varied {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
    }
}

impl EquivSerializers for super::Varied {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

proof fn test_varied_sp_roundtrip(v: Seq<u8>, obuf: Seq<u8>)
    requires v.len() == 10
{
    let s = super::Varied(10);
    assert(s.unambiguous());
    s.theorem_serialize_dps_parse_roundtrip(v, obuf);
}

} // verus!
