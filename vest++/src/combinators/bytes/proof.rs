use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

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

impl<Inner: SPRoundTripDps + GoodSerializerDps + NoLookAhead> SPRoundTripDps for super::ExactLen<
    Inner,
> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v, obuf);
        self.1.theorem_serialize_dps_parse_roundtrip(v, obuf);
        let serialized = self.1.spec_serialize_dps(v, obuf);
        let n = self.1.byte_len(v) as int;
        let chunk = serialized.take(n);
        assert(chunk.take(n) == serialized.take(n));
        self.1.lemma_no_lookahead(serialized, chunk);
        assert(self.1.spec_parse(serialized) == Some((n, v)));
        assert(self.1.spec_parse(chunk) == Some((n, v)));
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

impl<Inner: GoodParser + Unambiguity> NoLookAhead for super::ExactLen<Inner> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl<Inner: EquivSerializersGeneral> EquivSerializersGeneral for super::ExactLen<Inner> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.1.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner: EquivSerializers> EquivSerializers for super::ExactLen<Inner> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.1.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
