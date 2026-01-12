use super::spec::{U16BeMapper, U16LeMapper};
use crate::combinators::{Fixed, Mapped};
use crate::core::proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip};
use vstd::prelude::*;

verus! {

impl SPRoundTrip for super::U8 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: u8, obuf: Seq<u8>) {
    }
}

impl PSRoundTrip for super::U8 {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
    }
}

impl NonMalleable for super::U8 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
    }
}

impl Deterministic for super::U8 {
    proof fn lemma_serialize_equiv(&self, v: u8, obuf: Seq<u8>) {
    }
}

impl SPRoundTrip for super::U16Le {
    proof fn theorem_serialize_parse_roundtrip(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.theorem_serialize_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl PSRoundTrip for super::U16Le {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.theorem_parse_serialize_roundtrip(
            ibuf,
            obuf,
        );
    }
}

impl NonMalleable for super::U16Le {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl Deterministic for super::U16Le {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16LeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

impl SPRoundTrip for super::U16Be {
    proof fn theorem_serialize_parse_roundtrip(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.theorem_serialize_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl PSRoundTrip for super::U16Be {
    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.theorem_parse_serialize_roundtrip(
            ibuf,
            obuf,
        );
    }
}

impl NonMalleable for super::U16Be {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl Deterministic for super::U16Be {
    proof fn lemma_serialize_equiv(&self, v: u16, obuf: Seq<u8>) {
        Mapped { inner: Fixed::<2>, mapper: U16BeMapper }.lemma_serialize_equiv(v, obuf);
    }
}

} // verus!
