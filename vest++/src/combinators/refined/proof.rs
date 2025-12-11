use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::SpecCombinator,
};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip> SPRoundTrip for super::Refined<A> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(v, obuf);
    }
}

impl<A: PSRoundTrip> PSRoundTrip for super::Refined<A> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

impl<A: NonMalleable> NonMalleable for super::Refined<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A> Deterministic for super::Refined<A> where A: Deterministic + SpecCombinator {
    proof fn lemma_serialize_equiv(&self, v: Self::Type, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(v, obuf);
    }
}

} // verus!
