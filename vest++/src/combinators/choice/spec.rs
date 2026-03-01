use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// The sum type.
pub enum Sum<A, B> {
    /// Left injection.
    Inl(A),
    /// Right injection.
    Inr(B),
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Choice<A, B> {
    type PVal = Sum<A::PVal, B::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n, va)) => Some((n, Sum::Inl(va))),
            None => match self.1.spec_parse(ibuf) {
                Some((n, vb)) => Some((n, Sum::Inr(vb))),
                None => None,
            },
        }
    }
}

impl<A: Consistency, B: Consistency> Consistency for super::Choice<A, B> {
    type Val = Sum<A::Val, B::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        match v {
            Sum::Inl(va) => self.0.consistent(va),
            Sum::Inr(vb) => self.1.consistent(vb),
        }
    }
}

impl<A: SoundParser, B: SoundParser> SoundParser for super::Choice<A, B> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        self.1.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.1.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Choice<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = Sum<A::ST, B::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Sum::Inl(va) => self.0.spec_serialize_dps(va, obuf),
            Sum::Inr(vb) => self.1.spec_serialize_dps(vb, obuf),
        }
    }
}

impl<A, B> SpecSerializer for super::Choice<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = Sum<A::SVal, B::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match v {
            Sum::Inl(va) => self.0.spec_serialize(va),
            Sum::Inr(vb) => self.1.spec_serialize(vb),
        }
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Choice<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> NonTailFmt for super::Choice<A, B> where A: NonTailFmt, B: NonTailFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_dps_prepend(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_dps_prepend(vb, obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_dps_len(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_dps_len(vb, obuf);
            },
        }
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Choice<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_len(va);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_len(vb);
            },
        }
    }
}

impl<A, B> SpecByteLen for super::Choice<A, B> where A: SpecByteLen, B: SpecByteLen {
    type T = Sum<A::T, B::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match v {
            Sum::Inl(va) => self.0.byte_len(va),
            Sum::Inr(vb) => self.1.byte_len(vb),
        }
    }
}

impl<A: SpecParser, B: SpecParser<PVal = A::PVal>> SpecParser for super::Alt<A, B> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if let None = self.0.spec_parse(ibuf) {
            self.1.spec_parse(ibuf)
        } else {
            self.0.spec_parse(ibuf)
        }
    }
}

impl<A: Consistency, B: Consistency<Val = A::Val>> Consistency for super::Alt<A, B> {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v) || self.1.consistent(v)
    }
}

impl<A, B> SoundParser for super::Alt<A, B> where
    A: SoundParser + DisjointFrom<B>,
    B: SoundParser<T = A::T>,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        self.1.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.1.lemma_parse_sound_consumption(ibuf);
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
        if let Some((n, v)) = self.0.spec_parse(ibuf) {
            assert(n == self.byte_len(v));
        } else if let Some((n, v)) = self.1.spec_parse(ibuf) {
            assert(self.1.consistent(v));
            self.0.lemma_disjoint(&self.1, v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        self.1.lemma_parse_sound_value(ibuf);
    }
}

pub open spec fn triv(b: bool) -> bool {
    true
}

impl<A, B> SpecSerializerDps for super::Alt<A, B> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps<ST = A::ST> + Consistency<Val = B::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        if self.0.consistent(v) {
            self.0.spec_serialize_dps(v, obuf)
        } else {
            self.1.spec_serialize_dps(v, obuf)
        }
    }
}

impl<A: Unambiguity, B: Unambiguity<PVal = A::PVal>> Unambiguity for super::Alt<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> NonTailFmt for super::Alt<A, B> where
    A: NonTailFmt + Consistency<Val = A::ST>,
    B: NonTailFmt<T = A::T> + Consistency<Val = B::ST>,
 {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        if self.0.consistent(v) {
            self.0.lemma_serialize_dps_prepend(v, obuf)
        } else {
            self.1.lemma_serialize_dps_prepend(v, obuf)
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        if self.0.consistent(v) {
            self.0.lemma_serialize_dps_len(v, obuf)
        } else {
            self.1.lemma_serialize_dps_len(v, obuf)
        }
    }
}

impl<A, B> SpecSerializer for super::Alt<A, B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer<SVal = A::SVal> + Consistency<Val = B::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        if self.0.consistent(v) {
            self.0.spec_serialize(v)
        } else {
            self.1.spec_serialize(v)
        }
    }
}

impl<A, B> GoodSerializer for super::Alt<A, B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer<T = A::T> + Consistency<Val = B::SVal>,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        if self.0.consistent(v) {
            self.0.lemma_serialize_len(v)
        } else {
            self.1.lemma_serialize_len(v)
        }
    }
}

impl<A, B> SpecByteLen for super::Alt<A, B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen<T = A::T> + Consistency<Val = B::T>,
 {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        if self.0.consistent(v) {
            self.0.byte_len(v)
        } else {
            self.1.byte_len(v)
        }
    }
}

} // verus!
