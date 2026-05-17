use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner: SpecParser> SpecParser for super::Named<Inner> {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.1.spec_parse(ibuf)
    }
}

impl<Inner: Consistency> Consistency for super::Named<Inner> {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.1.consistent(v)
    }
}

impl<Inner: AdmitsUniqueVal> AdmitsUniqueVal for super::Named<Inner> {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
        self.1.lemma_unique_consistent_val(v1, v2);
    }
}

impl<Inner: SafeParser> SafeParser for super::Named<Inner> {
    open spec fn safe_inv(&self) -> bool {
        self.1.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.1.lemma_parse_safe(ibuf);
    }
}

impl<Inner: SoundParser> SoundParser for super::Named<Inner> {
    open spec fn sound_inv(&self) -> bool {
        self.1.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.1.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.1.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner: SpecSerializerDps> SpecSerializerDps for super::Named<Inner> {
    type SValue = Inner::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.1.spec_serialize_dps(v, obuf)
    }
}

impl<Inner: SpecSerializer> SpecSerializer for super::Named<Inner> {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.1.spec_serialize(v)
    }
}

impl<Inner: NonTailFmt> NonTailFmt for super::Named<Inner> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner: GoodSerializer> GoodSerializer for super::Named<Inner> {
    open spec fn serialize_inv(&self) -> bool {
        self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.1.lemma_serialize_len(v);
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Named<Inner> {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.1.byte_len(v)
    }
}

impl<Inner: MinMaxByteLen> MinMaxByteLen for super::Named<Inner> {
    open spec fn min(&self) -> nat {
        self.1.min()
    }

    open spec fn max(&self) -> nat {
        self.1.max()
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
        self.1.lemma_min_max_byte_len(v);
    }
}

impl<Inner: StaticByteLen> StaticByteLen for super::Named<Inner> {
    open spec fn static_byte_len() -> nat {
        Inner::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.1.lemma_static_len_matches_byte_len(v);
    }
}

impl<Inner: ValueByteLen> ValueByteLen for super::Named<Inner> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Inner::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        self.1.lemma_value_len_matches_byte_len(v);
    }
}

impl<Inner: BytesCombinator> BytesCombinator for super::Named<Inner> {
    proof fn lemma_byte_len_is_buf_len(&self, buf: Seq<u8>) {
        self.1.lemma_byte_len_is_buf_len(buf);
    }
}

} // verus!
