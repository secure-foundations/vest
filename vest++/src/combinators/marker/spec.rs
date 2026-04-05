use crate::core::{proof::*, spec::*};
use crate::Never;
use vstd::prelude::*;

verus! {

pub const ZERO_BYTE_LEN: usize = 0;

impl SpecParser for super::Empty {
    type PVal = ();

    open spec fn spec_parse(&self, _ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Some((0, ()))
    }
}

impl Consistency for super::Empty {
    type Val = ();

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl AdmitsUniqueVal for super::Empty {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
    }
}

impl SoundParser for super::Empty {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Empty {
    type ST = ();

    open spec fn spec_serialize_dps(&self, _v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        obuf
    }
}

impl SpecSerializer for super::Empty {
    type SVal = ();

    open spec fn spec_serialize(&self, _v: Self::SVal) -> Seq<u8> {
        Seq::empty()
    }
}

impl Unambiguity for super::Empty {

}

impl NonTailFmt for super::Empty {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == Seq::<u8>::empty() + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == 0);
    }
}

impl GoodSerializer for super::Empty {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.spec_serialize(v).len() == 0);
    }
}

impl SpecByteLen for super::Empty {
    type T = ();

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        ZERO_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::Empty {
    open spec fn static_byte_len() -> nat {
        ZERO_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl SpecParser for super::Void {
    type PVal = Never;

    open spec fn spec_parse(&self, _ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        None
    }
}

impl Consistency for super::Void {
    type Val = Never;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        false
    }
}

impl AdmitsUniqueVal for super::Void {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
    }
}

impl SoundParser for super::Void {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Void {
    type ST = Never;

    // It doesn't matter what we put here since there are no consistent values for Void.
    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        obuf
    }
}

impl SpecSerializer for super::Void {
    type SVal = Never;

    // It doesn't matter what we put here since there are no consistent values for Void.
    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Seq::empty()
    }
}

impl Unambiguity for super::Void {

}

impl NonTailFmt for super::Void {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let new_buf = Seq::<u8>::empty();
        assert(obuf == new_buf + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
    }
}

impl GoodSerializer for super::Void {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl SpecByteLen for super::Void {
    type T = Never;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        ZERO_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::Void {
    open spec fn static_byte_len() -> nat {
        ZERO_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

} // verus!
