use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTrip, Pred: SpecPred<A::PVal>> SPRoundTrip for super::Refined<A, Pred> {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            self.inner.theorem_serialize_parse_roundtrip_internal(v.val, obuf)
        }
    }
}

impl<A: PSRoundTrip, Pred: SpecPred<A::PVal>> PSRoundTrip for super::Refined<A, Pred> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf);
    }
}

impl<A: NonMalleable, Pred: SpecPred<A::PVal>> NonMalleable for super::Refined<A, Pred> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A, Pred> SpecSerializers for super::Refined<A, Pred> where
    A: SpecSerializers,
    Pred: SpecPred<A::SVal>,
 {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(v.val, obuf);
    }
}

impl<Inner: SPRoundTrip> SPRoundTrip for super::Tag<Inner, Inner::PVal> {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.theorem_serialize_parse_roundtrip_internal(self.tag, obuf);
    }
}

impl<Inner: PSRoundTrip> PSRoundTrip for super::Tag<Inner, Inner::PVal> {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        self.inner.theorem_parse_serialize_roundtrip(ibuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::Tag<Inner, Inner::PVal> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner> SpecSerializers for super::Tag<Inner, Inner::SVal> where Inner: SpecSerializers {
    proof fn lemma_serialize_equiv(&self, _v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(self.tag, obuf);
    }
}

} // verus!
