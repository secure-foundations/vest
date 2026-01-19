use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<const N: usize> SPRoundTrip for super::Fixed<N> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> PSRoundTrip for super::Fixed<N> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> NonMalleable for super::Fixed<N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> Deterministic for super::Fixed<N> {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
    }
}

} // verus!
