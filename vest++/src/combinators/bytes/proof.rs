use crate::combinators::length::AsLen;
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

impl<Len: AsLen> SPRoundTripDps for super::Varied<Len> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

impl<Len: AsLen> NonMalleable for super::Varied<Len> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl<Len: AsLen> NoLookAhead for super::Varied<Len> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl<Len: AsLen> EquivSerializersGeneral for super::Varied<Len> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
    }
}

impl<Len: AsLen> EquivSerializers for super::Varied<Len> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl<Inner, Len> SPRoundTripDps for super::ExactLen<Inner, Len> where
    Inner: EquivSerializers + GoodSerializer + SPRoundTrip,
    Len: AsLen,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize_dps(v, seq![]);
        self.1.lemma_serialize_equiv_on_empty(v);
        self.1.lemma_serialize_len(v);
        self.1.theorem_serialize_parse_roundtrip(v);
        super::Varied(self.0).theorem_serialize_dps_parse_roundtrip(inner_bytes, obuf);
    }
}

impl<Inner: NonMalleable, Len: AsLen> NonMalleable for super::ExactLen<Inner, Len> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.lemma_parse_byte_len(buf1);
                    self.lemma_parse_byte_len(buf2);
                    self.lemma_parse_consistent(buf1);
                    self.lemma_parse_consistent(buf2);
                    let chunk1 = buf1.take(self.0.as_usize() as int);
                    let chunk2 = buf2.take(self.0.as_usize() as int);
                    self.1.lemma_parse_non_malleable(chunk1, chunk2);
                    assert(chunk1.take(self.0.as_usize() as int) == chunk2.take(
                        self.0.as_usize() as int,
                    ));
                    assert(chunk1.take(self.0.as_usize() as int) == chunk1);
                    assert(chunk2.take(self.0.as_usize() as int) == chunk2);
                }
            }
        }
    }
}

// [`ExactLen`] can make "look-ahead" parsers (e.g., [`Tail`] and [`Eof`]) non-look-ahead
// (s.t. they can no longer "predict" the future)
// because it always consumes the same number of bytes when it succeeds
impl<Inner: GoodParser + Unambiguity, Len: AsLen> NoLookAhead for super::ExactLen<Inner, Len> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

////// [`ExactLen`] can make "context-sensitive" serializers (e.g., [`Tail`] and [`Eof`]) "context-free",
// [`ExactLen`] can make "position-sensitive" serializers (e.g., [`Tail`] and [`Eof`]) "position-insensitive"
// (s.t. they can no longer "change" the past)
// because it "boxes" the inner serializer from the outside context `obuf`
impl<Inner: EquivSerializers, Len: AsLen> EquivSerializersGeneral for super::ExactLen<Inner, Len> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize(v);
        super::Varied(self.0).lemma_serialize_equiv(inner_bytes, obuf);
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Inner: EquivSerializers, Len: AsLen> EquivSerializers for super::ExactLen<Inner, Len> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Len, Then> SPRoundTripDps for super::AndThen<Varied<Len>, Then> where
    Then: EquivSerializers + GoodSerializer + SPRoundTrip,
    Len: AsLen,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize_dps(v, seq![]);
        self.1.lemma_serialize_equiv_on_empty(v);
        self.1.lemma_serialize_len(v);
        self.1.theorem_serialize_parse_roundtrip(v);
        self.0.theorem_serialize_dps_parse_roundtrip(inner_bytes, obuf);
    }
}

impl<Len: AsLen, Then: NonMalleable> NonMalleable for super::AndThen<Varied<Len>, Then> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.lemma_parse_byte_len(buf1);
                    self.lemma_parse_byte_len(buf2);
                    self.lemma_parse_consistent(buf1);
                    self.lemma_parse_consistent(buf2);
                    let chunk1 = buf1.take(self.0.0.as_usize() as int);
                    let chunk2 = buf2.take(self.0.0.as_usize() as int);
                    self.1.lemma_parse_non_malleable(chunk1, chunk2);
                    assert(chunk1.take(self.0.0.as_usize() as int) == chunk2.take(
                        self.0.0.as_usize() as int,
                    ));
                    assert(chunk1.take(self.0.0.as_usize() as int) == chunk1);
                    assert(chunk2.take(self.0.0.as_usize() as int) == chunk2);
                }
            }
        }
    }
}

impl<Len: AsLen, Then: GoodParser + Unambiguity> NoLookAhead for super::AndThen<Varied<Len>, Then> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl<Len: AsLen, Then: EquivSerializers> EquivSerializersGeneral for super::AndThen<
    Varied<Len>,
    Then,
> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_bytes = self.1.spec_serialize(v);
        self.0.lemma_serialize_equiv(inner_bytes, obuf);
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Len: AsLen, Then: EquivSerializers> EquivSerializers for super::AndThen<Varied<Len>, Then> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
