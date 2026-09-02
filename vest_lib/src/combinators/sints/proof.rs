//! Correctness proofs for fixed-width signed integers.
use vstd::prelude::*;

verus! {

use crate::core::{proof::*, spec::*};
use crate::combinators::sints::spec::*;
use crate::combinators::bytes::spec::*;

impl SPRoundTripDps for super::I8 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i8, obuf: Seq<u8>) {
        broadcast use lemma_i8_value_roundtrip;

        i8_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I8 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use lemma_i8_seq_roundtrip;

        i8_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I8 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i8_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I8 {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i8_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I8 {
    proof fn lemma_serialize_equiv(&self, v: i8, obuf: Seq<u8>) {
        i8_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I8 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i8) {
        i8_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I16Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i16, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i16_le_value_roundtrip;

        i16_le_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I16Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_le_bytes_roundtrip;

        i16_le_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I16Le {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i16_le_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I16Le {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i16_le_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I16Le {
    proof fn lemma_serialize_equiv(&self, v: i16, obuf: Seq<u8>) {
        i16_le_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I16Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i16) {
        i16_le_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I16Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i16, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i16_be_value_roundtrip;

        i16_be_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I16Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i16_be_bytes_roundtrip;

        i16_be_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I16Be {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i16_be_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I16Be {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i16_be_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I16Be {
    proof fn lemma_serialize_equiv(&self, v: i16, obuf: Seq<u8>) {
        i16_be_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I16Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i16) {
        i16_be_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I32Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i32, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i32_le_value_roundtrip;

        i32_le_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I32Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_le_bytes_roundtrip;

        i32_le_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I32Le {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i32_le_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I32Le {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i32_le_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I32Le {
    proof fn lemma_serialize_equiv(&self, v: i32, obuf: Seq<u8>) {
        i32_le_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I32Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i32) {
        i32_le_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I32Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i32, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i32_be_value_roundtrip;

        i32_be_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I32Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i32_be_bytes_roundtrip;

        i32_be_fmt().lemma_parse_sound_consumption(buf1);  // triggers axiom_array_from_seq
        i32_be_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I32Be {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i32_be_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I32Be {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i32_be_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I32Be {
    proof fn lemma_serialize_equiv(&self, v: i32, obuf: Seq<u8>) {
        i32_be_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I32Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i32) {
        i32_be_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I64Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i64, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i64_le_value_roundtrip;

        i64_le_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I64Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_le_bytes_roundtrip;

        i64_le_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I64Le {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i64_le_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I64Le {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i64_le_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I64Le {
    proof fn lemma_serialize_equiv(&self, v: i64, obuf: Seq<u8>) {
        i64_le_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I64Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i64) {
        i64_le_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::I64Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: i64, obuf: Seq<u8>) {
        broadcast use lemma_array_from_seq_roundtrip;
        broadcast use lemma_i64_be_value_roundtrip;

        i64_be_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl NonMalleable for super::I64Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use axiom_array_from_seq;
        broadcast use lemma_i64_be_bytes_roundtrip;

        i64_be_fmt().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl NoLookAhead for super::I64Be {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        i64_be_fmt().lemma_no_lookahead(i1, i2);
    }
}

impl Productive for super::I64Be {
    proof fn lemma_productive(&self, s: Seq<u8>) {
        i64_be_fmt().lemma_productive(s);
    }
}

impl EquivSerializersGeneral for super::I64Be {
    proof fn lemma_serialize_equiv(&self, v: i64, obuf: Seq<u8>) {
        i64_be_fmt().lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::I64Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: i64) {
        i64_be_fmt().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
