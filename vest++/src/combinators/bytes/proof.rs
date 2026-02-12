use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::Varied;

verus! {

impl<const N: usize> SPRoundTripDps for super::Fixed<N> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> NonMalleable for super::Fixed<N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use super::spec::axiom_array_from_seq;

    }
}

impl<const N: usize> NoLookAhead for super::Fixed<N> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
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
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

impl NonMalleable for super::Varied {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl NoLookAhead for super::Varied {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
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

impl<Inner> SPRoundTripDps for super::ExactLen<Inner> where
    Inner: EquivSerializers + GoodSerializer + SPRoundTrip,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize_dps(v, seq![]);
        self.1.lemma_serialize_equiv_on_empty(v);
        self.1.lemma_serialize_len(v);
        self.1.theorem_serialize_parse_roundtrip(v);
        super::Varied(self.0).theorem_serialize_dps_parse_roundtrip(inner_bytes, obuf);
    }
}

impl<Inner: NonMalleable> NonMalleable for super::ExactLen<Inner> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.lemma_parse_byte_len(buf1);
                    self.lemma_parse_byte_len(buf2);
                    self.lemma_parse_consistent(buf1);
                    self.lemma_parse_consistent(buf2);
                    let chunk1 = buf1.take(self.0 as int);
                    let chunk2 = buf2.take(self.0 as int);
                    self.1.lemma_parse_non_malleable(chunk1, chunk2);
                    assert(chunk1.take(self.0 as int) == chunk2.take(self.0 as int));
                    assert(chunk1.take(self.0 as int) == chunk1);
                    assert(chunk2.take(self.0 as int) == chunk2);
                }
            }
        }
    }
}

// [`ExactLen`] can make "look-ahead" parsers (e.g., [`Tail`] and [`Eof`]) non-look-ahead
// (s.t. they can no longer "predict" the future)
// because it always consumes the same number of bytes when it succeeds
impl<Inner: GoodParser + Unambiguity> NoLookAhead for super::ExactLen<Inner> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

////// [`ExactLen`] can make "context-sensitive" serializers (e.g., [`Tail`] and [`Eof`]) "context-free",
// [`ExactLen`] can make "position-sensitive" serializers (e.g., [`Tail`] and [`Eof`]) "position-insensitive"
// (s.t. they can no longer "change" the past)
// because it "boxes" the inner serializer from the outside context `obuf`
impl<Inner: EquivSerializers> EquivSerializersGeneral for super::ExactLen<Inner> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize(v);
        super::Varied(self.0).lemma_serialize_equiv(inner_bytes, obuf);
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Inner: EquivSerializers> EquivSerializers for super::ExactLen<Inner> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Then> SPRoundTripDps for super::AndThen<Varied, Then> where
    Then: EquivSerializers + GoodSerializer + SPRoundTrip,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize_dps(v, seq![]);
        self.1.lemma_serialize_equiv_on_empty(v);
        self.1.lemma_serialize_len(v);
        self.1.theorem_serialize_parse_roundtrip(v);
        self.0.theorem_serialize_dps_parse_roundtrip(inner_bytes, obuf);
    }
}

impl<Then: NonMalleable> NonMalleable for super::AndThen<Varied, Then> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.lemma_parse_byte_len(buf1);
                    self.lemma_parse_byte_len(buf2);
                    self.lemma_parse_consistent(buf1);
                    self.lemma_parse_consistent(buf2);
                    let chunk1 = buf1.take(self.0.0 as int);
                    let chunk2 = buf2.take(self.0.0 as int);
                    self.1.lemma_parse_non_malleable(chunk1, chunk2);
                    assert(chunk1.take(self.0.0 as int) == chunk2.take(self.0.0 as int));
                    assert(chunk1.take(self.0.0 as int) == chunk1);
                    assert(chunk2.take(self.0.0 as int) == chunk2);
                }
            }
        }
    }
}

impl<Then: GoodParser + Unambiguity> NoLookAhead for super::AndThen<Varied, Then> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl<Then: EquivSerializers> EquivSerializersGeneral for super::AndThen<Varied, Then> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize(v);
        self.0.lemma_serialize_equiv(inner_bytes, obuf);
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Then: EquivSerializers> EquivSerializers for super::AndThen<Varied, Then> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
