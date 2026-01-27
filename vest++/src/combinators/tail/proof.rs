use crate::core::{proof::*, spec::*};
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

} // verus!
