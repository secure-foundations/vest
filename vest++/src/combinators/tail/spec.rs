use crate::{
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

impl SoundParser for super::Tail {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

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

impl Unambiguity for super::Tail {

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

impl SoundParser for super::Eof {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

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

impl Unambiguity for super::Eof {

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
        0
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

impl<C> SoundParser for super::OptionalEnd<C> where C: SoundParser {
    open spec fn inv(&self) -> bool {
        self.0.inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Optional(self.0, super::Eof).lemma_parse_safe(ibuf)
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

impl<C: Unambiguity> Unambiguity for super::OptionalEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        Optional(self.0, super::Eof).unambiguous()
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

impl<C> SoundParser for super::RepeatTillEnd<C> where C: SoundParser {
    open spec fn inv(&self) -> bool {
        self.0.inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Repeat(self.0, super::Eof).lemma_parse_safe(ibuf)
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

impl<C: Unambiguity> Unambiguity for super::RepeatTillEnd<C> {
    open spec fn unambiguous(&self) -> bool {
        Repeat(self.0, super::Eof).unambiguous()
    }
}

} // verus!
