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

// impl<const N: usize> PSRoundTrip for super::Fixed<N> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         broadcast use super::spec::axiom_array_from_seq;
//     }
// }
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

} // verus!
