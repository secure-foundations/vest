use crate::{
    combinators::{Optional, Repeat},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::Tail {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

// impl PSRoundTrip for super::Tail {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//     }
// }
impl NonMalleable for super::Tail {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl EquivSerializers for super::Tail {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl SPRoundTripDps for super::Eof {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
    }
}

// impl PSRoundTrip for super::Eof {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//     }
// }
impl NonMalleable for super::Eof {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl EquivSerializers for super::Eof {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
    }
}

impl<C: SPRoundTripDps + NonTailFmt> SPRoundTripDps for super::OptionalEnd<C> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        Optional(self.0, super::Eof).theorem_serialize_dps_parse_roundtrip((v, ()), obuf);
    }
}

impl<C: NonMalleable> NonMalleable for super::OptionalEnd<C> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<C: EquivSerializersGeneral> EquivSerializers for super::OptionalEnd<C> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Optional(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

impl<C: SPRoundTripDps + NonTailFmt> SPRoundTripDps for super::RepeatTillEnd<C> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        Repeat(self.0, super::Eof).theorem_serialize_dps_parse_roundtrip((v, ()), obuf);
    }
}

impl<C: NonMalleable> NonMalleable for super::RepeatTillEnd<C> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<C: EquivSerializersGeneral> EquivSerializers for super::RepeatTillEnd<C> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Repeat(self.0, super::Eof).lemma_serialize_equiv_on_empty((v, ()));
    }
}

} // verus!
