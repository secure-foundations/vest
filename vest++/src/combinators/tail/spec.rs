use crate::{
    combinators::marker::spec::ZERO_BYTE_LEN,
    combinators::{Optional, Repeat},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

impl SpecParser for super::Tail {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Some((ibuf.len() as int, ibuf))
    }
}

impl Consistency for super::Tail {
    type Val = Seq<u8>;

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl SafeParser for super::Tail {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }
}

impl SoundParser for super::Tail {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Tail {
    type ST = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v
    }
}

impl SpecSerializer for super::Tail {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v
    }
}

impl SpecByteLen for super::Tail {
    type T = Seq<u8>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.len()
    }
}

impl BytesCombinator for super::Tail {
    proof fn lemma_byte_len_is_buf_len(&self, s: Seq<u8>) {
    }
}

impl ValueByteLen for super::Tail {
    open spec fn value_byte_len(v: Self::T) -> nat {
        v.len()
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl GoodSerializer for super::Tail {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl SpecParser for super::Eof {
    type PVal = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() == 0 {
            Some((0, ()))
        } else {
            None
        }
    }
}

impl Consistency for super::Eof {
    type Val = ();

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl AdmitsUniqueVal for super::Eof {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
    }
}

impl SafeParser for super::Eof {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }
}

impl SoundParser for super::Eof {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Eof {
    type ST = ();

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Seq::empty()
    }
}

impl SpecSerializer for super::Eof {
    type SVal = ();

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Seq::empty()
    }
}

impl SpecByteLen for super::Eof {
    type T = ();

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        ZERO_BYTE_LEN as nat
    }
}

impl StaticByteLen for super::Eof {
    open spec fn static_byte_len() -> nat {
        ZERO_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl ValueByteLen for super::Eof {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        ZERO_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl GoodSerializer for super::Eof {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl<C: SpecParser> SpecParser for super::OptionalEnd<C> {
    type PVal = Option<C::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match Optional(self.0, super::Eof).spec_parse(ibuf) {
            Some((n, (v, _))) => Some((n, v)),
            None => None,
        }
    }
}

impl<C> Consistency for super::OptionalEnd<C> where C: Consistency {
    type Val = Option<C::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Optional(self.0, super::Eof).consistent((v, ()))
    }
}

impl<C> SafeParser for super::OptionalEnd<C> where C: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        self.0.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_safe(ibuf)
    }
}

impl<C> SoundParser for super::OptionalEnd<C> where C: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        self.0.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_sound_value(ibuf)
    }
}

impl<C: SpecSerializerDps> SpecSerializerDps for super::OptionalEnd<C> {
    type ST = Option<C::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Optional(self.0, super::Eof).spec_serialize_dps((v, ()), obuf)
    }
}

impl<C: SpecSerializer> SpecSerializer for super::OptionalEnd<C> {
    type SVal = Option<C::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Optional(self.0, super::Eof).spec_serialize((v, ()))
    }
}

impl<C: GoodSerializer> GoodSerializer for super::OptionalEnd<C> {
    open spec fn serialize_inv(&self) -> bool {
        self.0.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Optional(self.0, super::Eof).lemma_serialize_len((v, ()));
    }
}

impl<C: SpecByteLen> SpecByteLen for super::OptionalEnd<C> {
    type T = Option<C::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Optional(self.0, super::Eof).byte_len((v, ()))
    }
}

impl<C: ValueByteLen> ValueByteLen for super::OptionalEnd<C> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        <Optional<C, super::Eof> as ValueByteLen>::value_byte_len((v, ()))
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        Optional(self.0, super::Eof).lemma_value_len_matches_byte_len((v, ()));
    }
}

impl<C: SpecParser> SpecParser for super::RepeatTillEnd<C> {
    type PVal = Seq<C::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match Repeat(self.0, super::Eof).spec_parse(ibuf) {
            Some((n, (vs, _))) => Some((n, vs)),
            None => None,
        }
    }
}

impl<C> Consistency for super::RepeatTillEnd<C> where C: Consistency {
    type Val = Seq<C::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Repeat(self.0, super::Eof).consistent((v, ()))
    }
}

impl<C> SafeParser for super::RepeatTillEnd<C> where C: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        self.0.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_safe(ibuf)
    }
}

impl<C> SoundParser for super::RepeatTillEnd<C> where C: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        self.0.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_sound_value(ibuf)
    }
}

impl<C: SpecSerializerDps> SpecSerializerDps for super::RepeatTillEnd<C> {
    type ST = Seq<C::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Repeat(self.0, super::Eof).spec_serialize_dps((v, ()), obuf)
    }
}

impl<C: SpecSerializer> SpecSerializer for super::RepeatTillEnd<C> {
    type SVal = Seq<C::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Repeat(self.0, super::Eof).spec_serialize((v, ()))
    }
}

impl<C: GoodSerializer> GoodSerializer for super::RepeatTillEnd<C> {
    open spec fn serialize_inv(&self) -> bool {
        self.0.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Repeat(self.0, super::Eof).lemma_serialize_len((v, ()));
    }
}

impl<C: SpecByteLen> SpecByteLen for super::RepeatTillEnd<C> {
    type T = Seq<C::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Repeat(self.0, super::Eof).byte_len((v, ()))
    }
}

impl<C: ValueByteLen> ValueByteLen for super::RepeatTillEnd<C> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        <Repeat<C, super::Eof> as ValueByteLen>::value_byte_len((v, ()))
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        Repeat(self.0, super::Eof).lemma_value_len_matches_byte_len((v, ()));
    }
}

} // verus!
