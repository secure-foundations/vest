use crate::core::proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip};
use vstd::prelude::*;

verus! {

impl<const N: usize> SPRoundTrip for super::Fixed<N> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
    }
}

impl<const N: usize> PSRoundTrip for super::Fixed<N> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
    }
}

impl<const N: usize> NonMalleable for super::Fixed<N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl<const N: usize> Deterministic for super::Fixed<N> {
    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
    }
}

} // verus!
