use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SPRoundTripDps for super::Refined<A, Pred> where
    A: SPRoundTripDps,
    Pred: SpecPred<A::PVal>,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.inner.theorem_serialize_dps_parse_roundtrip(v, obuf)
    }
}

// impl<A: PSRoundTrip, Pred: SpecPred<A::PVal>> PSRoundTrip for super::Refined<A, Pred> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.inner.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<A: NonMalleable, Pred: SpecPred<A::PVal>> NonMalleable for super::Refined<A, Pred> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, Pred: SpecPred<A::PVal>> NoLookAhead for super::Refined<A, Pred> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.inner.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<A, Pred> EquivSerializersGeneral for super::Refined<A, Pred> where
    A: EquivSerializersGeneral,
    Pred: SpecPred<A::SVal>,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, Pred> EquivSerializers for super::Refined<A, Pred> where
    A: EquivSerializers,
    Pred: SpecPred<A::SVal>,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::ST) {
        self.inner.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Inner: SPRoundTripDps> SPRoundTripDps for super::Tag<Inner, Inner::PVal> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.theorem_serialize_dps_parse_roundtrip(self.tag, obuf);
    }
}

// impl<Inner: PSRoundTrip> PSRoundTrip for super::Tag<Inner, Inner::PVal> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.inner.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<Inner: NonMalleable> NonMalleable for super::Tag<Inner, Inner::PVal> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: NoLookAhead> NoLookAhead for super::Tag<Inner, Inner::PVal> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.inner.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<Inner> EquivSerializersGeneral for super::Tag<Inner, Inner::SVal> where
    Inner: EquivSerializersGeneral,
 {
    proof fn lemma_serialize_equiv(&self, _v: <Self as SpecSerializerDps>::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(self.tag, obuf);
    }
}

impl<Inner> EquivSerializers for super::Tag<Inner, Inner::SVal> where Inner: EquivSerializers {
    proof fn lemma_serialize_equiv_on_empty(&self, _v: Self::ST) {
        self.inner.lemma_serialize_equiv_on_empty(self.tag);
    }
}

} // verus!
