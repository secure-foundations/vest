use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip, Pred: SpecPred<A::PT>> SPRoundTrip for super::Refined<A, Pred> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
            self.inner.theorem_serialize_parse_roundtrip(v.val, obuf)
        }
    }
}

impl<A: PSRoundTrip, Pred: SpecPred<A::PT>> PSRoundTrip for super::Refined<A, Pred> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf);
    }
}

impl<A: NonMalleable, Pred: SpecPred<A::PT>> NonMalleable for super::Refined<A, Pred> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: Deterministic, Pred: SpecPred<<A as SpecSerializer>::ST>> Deterministic for super::Refined<A, Pred> {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
            self.inner.lemma_serialize_equiv(v.val, obuf);
    }
}

impl<Inner: SPRoundTrip> SPRoundTrip for super::Tag<Inner, Inner::PT> {
    proof fn theorem_serialize_parse_roundtrip(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip(self.tag, obuf);
    }
}

impl<Inner: PSRoundTrip> PSRoundTrip for super::Tag<Inner, Inner::PT> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::Tag<Inner, Inner::PT> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner> Deterministic for super::Tag<Inner, <Inner as SpecSerializer>::ST> where
    Inner: Deterministic,
 {
    proof fn lemma_serialize_equiv(&self, _v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(self.tag, obuf);
    }
}

} // verus!
