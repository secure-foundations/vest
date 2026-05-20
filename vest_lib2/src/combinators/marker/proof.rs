use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::Empty {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == obuf);
        assert(self.spec_parse(obuf) == Some((0int, ())));
    }
}

impl NonMalleable for super::Empty {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl NoLookAhead for super::Empty {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl EquivSerializersGeneral for super::Empty {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf);
    }
}

impl EquivSerializers for super::Empty {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl SPRoundTripDps for super::Void {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        assert(false);
    }
}

impl NonMalleable for super::Void {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl NoLookAhead for super::Void {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
    }
}

impl EquivSerializersGeneral for super::Void {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
    }
}

impl EquivSerializers for super::Void {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

} // verus!
