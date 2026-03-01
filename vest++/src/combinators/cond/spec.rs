use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner: SpecParser> SpecParser for super::Cond<Inner> {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if self.0 {
            self.1.spec_parse(ibuf)
        } else {
            None
        }
    }
}

impl<Inner: Consistency> Consistency for super::Cond<Inner> {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0 && self.1.consistent(v)
    }
}

impl<Inner: SoundParser> SoundParser for super::Cond<Inner> {
    open spec fn sound_inv(&self) -> bool {
        self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_safe(ibuf);
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_sound_consumption(ibuf);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if self.0 {
            self.1.lemma_parse_sound_value(ibuf);
            if let Some((_, v)) = self.1.spec_parse(ibuf) {
                assert(self.consistent(v));
            }
        }
    }
}

impl<Inner: SpecSerializerDps> SpecSerializerDps for super::Cond<Inner> {
    type ST = Inner::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.1.spec_serialize_dps(v, obuf)
    }
}

impl<Inner: SpecSerializer> SpecSerializer for super::Cond<Inner> {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.1.spec_serialize(v)
    }
}

impl<Inner: Unambiguity> Unambiguity for super::Cond<Inner> {
    open spec fn unambiguous(&self) -> bool {
        self.1.unambiguous()
    }
}

impl<Inner: NonTailFmt> NonTailFmt for super::Cond<Inner> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner: GoodSerializer> GoodSerializer for super::Cond<Inner> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.1.lemma_serialize_len(v);
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Cond<Inner> {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.1.byte_len(v)
    }
}

} // verus!
