use crate::combinators::preceded::Preceded;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SpecParser for super::Refined<A, Pred> where A: SpecParser, Pred: SpecPred<A::PVal> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if self.pred.apply(v) => Some((n, v)),
            _ => None,
        }
    }
}

impl<A, Pred> Consistency for super::Refined<A, Pred> where A: Consistency, Pred: SpecPred<A::Val> {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.inner.consistent(v) && self.pred.apply(v)
    }
}

impl<A, Pred> SoundParser for super::Refined<A, Pred> where
    A: SoundParser,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<A, Pred> SpecSerializerDps for super::Refined<A, Pred> where
    A: SpecSerializerDps,
    Pred: SpecPred<A::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<A, Pred> SpecSerializer for super::Refined<A, Pred> where
    A: SpecSerializer,
    Pred: SpecPred<A::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<A, Pred> Unambiguity for super::Refined<A, Pred> where
    A: Unambiguity,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<A, Pred> NonTailFmt for super::Refined<A, Pred> where A: NonTailFmt, Pred: SpecPred<A::ST> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, Pred> GoodSerializer for super::Refined<A, Pred> where
    A: GoodSerializer,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(v);
    }
}

impl<A, Pred> SpecByteLen for super::Refined<A, Pred> where A: SpecByteLen, Pred: SpecPred<A::T> {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v)
    }
}

impl<Inner> SpecParser for super::Tag<Inner, Inner::PVal> where Inner: SpecParser {
    type PVal = ();

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag => Some((n, ())),
            _ => None,
        }
    }
}

impl<Inner> Consistency for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    type Val = ();

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        self.inner.consistent(self.tag)
    }
}

impl<Inner> AdmitsUniqueVal for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
    }
}

impl<Inner> SoundParser for super::Tag<Inner, Inner::PVal> where Inner: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner> SpecSerializerDps for super::Tag<Inner, Inner::ST> where Inner: SpecSerializerDps {
    type ST = ();

    open spec fn spec_serialize_dps(&self, _v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(self.tag, obuf)
    }
}

impl<Inner> SpecSerializer for super::Tag<Inner, Inner::SVal> where Inner: SpecSerializer {
    type SVal = ();

    open spec fn spec_serialize(&self, _v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(self.tag)
    }
}

impl<Inner> Unambiguity for super::Tag<Inner, Inner::PVal> where Inner: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        self.inner.unambiguous()
    }
}

impl<Inner> NonTailFmt for super::Tag<Inner, Inner::ST> where Inner: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(self.tag, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, _v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(self.tag, obuf);
    }
}

impl<Inner> GoodSerializer for super::Tag<Inner, Inner::SVal> where Inner: GoodSerializer {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, _v: Self::SVal) {
        self.inner.lemma_serialize_len(self.tag);
    }
}

impl<Inner> SpecByteLen for super::Tag<Inner, Inner::T> where Inner: SpecByteLen {
    type T = ();

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        self.inner.byte_len(self.tag)
    }
}

impl<Tg, Of> SpecParser for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + SpecParser<PVal = Tg::T>,
    Of: SpecParser,
 {
    type PVal = Of::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).spec_parse(ibuf)
    }
}

impl<Tg, Of> Consistency for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + Consistency<Val = Tg::T>,
    Of: Consistency,
 {
    type Val = Of::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(self.1) && self.2.consistent(
            v,
        )
        // Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).consistent(v)

    }
}

impl<Tg, Of> SoundParser for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + SoundParser,
    Of: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.2.sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_parse_safe(ibuf)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_parse_sound_consumption(
            ibuf,
        )
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_parse_sound_value(ibuf)
    }
}

impl<Tg, Of> SpecSerializerDps for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + SpecSerializerDps<ST = Tg::T> + Consistency<Val = Tg::T>,
    Of: SpecSerializerDps,
 {
    type ST = Of::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).spec_serialize_dps(v, obuf)
    }
}

impl<Tg, Of> SpecSerializer for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + SpecSerializer<SVal = Tg::T> + Consistency<Val = Tg::T>,
    Of: SpecSerializer,
 {
    type SVal = Of::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).spec_serialize(v)
    }
}

impl<Tg, Of> Unambiguity for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + Unambiguity + SpecParser<PVal = Tg::T>,
    Of: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).unambiguous()
    }
}

impl<Tg, Of> NonTailFmt for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + NonTailFmt + Consistency<Val = Tg::T>,
    Of: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.2.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_serialize_dps_prepend(
            v,
            obuf,
        );
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_serialize_dps_len(
            v,
            obuf,
        );
    }
}

impl<Tg, Of> GoodSerializer for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + GoodSerializer + Consistency<Val = Tg::T>,
    Of: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.2.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_serialize_len(v);
    }
}

impl<Tg, Of> SpecByteLen for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + Consistency<Val = Tg::T>,
    Of: SpecByteLen,
 {
    type T = Of::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).byte_len(v)
    }
}

} // verus!
