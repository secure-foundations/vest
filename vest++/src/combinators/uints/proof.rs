use super::spec::{U16BeMapper, U16LeMapper, U32BeMapper, U32LeMapper};
use crate::combinators::{Fixed, Mapped};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl SPRoundTripDps for super::U8 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u8, obuf: Seq<u8>) {
        if v.wf() {
        }
    }
}

// impl PSRoundTrip for super::U8 {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//     }
// }
impl NonMalleable for super::U8 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
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
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

// impl PSRoundTrip for super::U16Le {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl NonMalleable for super::U16Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for super::U16Le {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U16Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U16Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

// impl PSRoundTrip for super::U16Be {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl NonMalleable for super::U16Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for super::U16Be {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U16Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u16) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U32Le {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl NonMalleable for super::U32Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for super::U32Le {
    proof fn lemma_serialize_equiv(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U32Le {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u32) {
        Mapped { inner: Fixed::<4>, mapper: U32LeMapper }.lemma_serialize_equiv_on_empty(v);
    }
}

impl SPRoundTripDps for super::U32Be {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl NonMalleable for super::U32Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl EquivSerializersGeneral for super::U32Be {
    proof fn lemma_serialize_equiv(&self, v: u32, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

impl EquivSerializers for super::U32Be {
    proof fn lemma_serialize_equiv_on_empty(&self, v: u32) {
        Mapped { inner: Fixed::<4>, mapper: U32BeMapper }.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
