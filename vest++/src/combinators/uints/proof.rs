use super::spec::*;
use crate::combinators::bytes::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::U8 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u8, obuf: Seq<u8>) {
        assert(self.spec_parse(self.spec_serialize_dps(v, obuf)) == Some((1int, v)));
    }
}

impl NonMalleable for super::U8 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl NoLookAhead for super::U8 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(i2.take(1int)[0] == i1.take(1int)[0]);
                    assert(self.spec_parse(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl EquivSerializersGeneral for super::U8 {
    proof fn lemma_serialize_equiv(&self, v: u8, obuf: Seq<u8>) {
    }
}

impl EquivSerializers for super::U8 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u8) {
    }
}

impl SPRoundTripDps for super::U16Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u16, obuf: Seq<u8>) {
        broadcast use lemma_u16_le_value_roundtrip;
        broadcast use lemma_array_from_seq_roundtrip;

        u16_le_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::U16Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use lemma_u16_le_bytes_roundtrip;
        broadcast use axiom_array_from_seq;

        u16_le_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::U16Le {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        u16_le_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl EquivSerializersGeneral for super::U16Le {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        u16_le_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U16Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u16) {
        u16_le_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U16Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u16, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_u16_be_value_roundtrip;

        u16_be_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::U16Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_u16_be_bytes_roundtrip;

        u16_be_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::U16Be {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        u16_be_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl EquivSerializersGeneral for super::U16Be {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        u16_be_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U16Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u16) {
        u16_be_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U32Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u32, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_u32_le_value_roundtrip;

        u32_le_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::U32Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_u32_le_bytes_roundtrip;

        u32_le_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::U32Le {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        u32_le_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl EquivSerializersGeneral for super::U32Le {
    proof fn lemma_serialize_equiv(&self, v: u32, obuf: Seq<u8>) {
        u32_le_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U32Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u32) {
        u32_le_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U32Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u32, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_u32_be_value_roundtrip;

        u32_be_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::U32Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_u32_be_bytes_roundtrip;

        u32_be_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::U32Be {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        u32_be_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl EquivSerializersGeneral for super::U32Be {
    proof fn lemma_serialize_equiv(&self, v: u32, obuf: Seq<u8>) {
        u32_be_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U32Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u32) {
        u32_be_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
