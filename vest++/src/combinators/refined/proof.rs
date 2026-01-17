use crate::core::{
    proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip},
    spec::{
        SpecCombinator, SpecParser, SpecPred, SpecSerializer, SpecSerializerDps, SpecType, Subset,
    },
};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip> SPRoundTrip for super::Refined<A, SpecPred<A::PT>> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
            self.inner.theorem_serialize_parse_roundtrip(v.val, obuf)
        }
    }
}

impl<A: PSRoundTrip> PSRoundTrip for super::Refined<A, SpecPred<A::PT>> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

impl<A: NonMalleable> NonMalleable for super::Refined<A, SpecPred<A::PT>> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A> Deterministic for super::Refined<A, SpecPred<<A as SpecSerializer>::ST>>
where
    A: Deterministic,
{
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        if v.wf() {
            self.inner.lemma_serialize_equiv(v.val, obuf);
        }
    }
}

impl<Inner: SPRoundTrip> SPRoundTrip for super::Tag<Inner, Inner::PT> {
    proof fn theorem_serialize_parse_roundtrip(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(self.tag, obuf);
    }
}

impl<Inner: PSRoundTrip> PSRoundTrip for super::Tag<Inner, Inner::PT> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf, obuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::Tag<Inner, Inner::PT> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner> Deterministic for super::Tag<Inner, <Inner as SpecSerializer>::ST>
where
    Inner: Deterministic,
{
    proof fn lemma_serialize_equiv(&self, _v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(self.tag, obuf);
    }
}

} // verus!
