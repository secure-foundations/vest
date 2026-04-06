use crate::combinators::preceded::Preceded;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SPRoundTripDps for super::Refined<A, Pred> where
    A: SPRoundTripDps,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        self.inner.sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.inner.theorem_serialize_dps_parse_roundtrip(v, obuf)
    }
}

// impl<A: PSRoundTrip, Pred: SpecPred<A::PVal>> PSRoundTrip for super::Refined<A, Pred> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.inner.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<A: NonMalleable, Pred: SpecPred<A::PVal>> NonMalleable for super::Refined<A, Pred> {
    open spec fn nonmal_inv(&self) -> bool {
        self.inner.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, Pred: SpecPred<A::PVal>> NoLookAhead for super::Refined<A, Pred> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.inner.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(self.no_lookahead_inv());
                    assert(self.unambiguous());
                    self.inner.lemma_no_lookahead(i1, i2);
                    assert(self.inner.spec_parse(i2) == Some((n, v)));
                    assert(self.spec_parse(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<A, Pred> EquivSerializersGeneral for super::Refined<A, Pred> where
    A: EquivSerializersGeneral,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, Pred> EquivSerializers for super::Refined<A, Pred> where
    A: EquivSerializers,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        self.inner.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::ST) {
        self.inner.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Inner: SPRoundTripDps> SPRoundTripDps for super::Tag<Inner, Inner::PVal> {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        self.inner.sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(v == self.tag);
        self.inner.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

// impl<Inner: PSRoundTrip> PSRoundTrip for super::Tag<Inner, Inner::PVal> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.inner.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<Inner: NonMalleable> NonMalleable for super::Tag<Inner, Inner::PVal> {
    open spec fn nonmal_inv(&self) -> bool {
        self.inner.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: NoLookAhead> NoLookAhead for super::Tag<Inner, Inner::PVal> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.inner.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.inner.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<Inner> EquivSerializersGeneral for super::Tag<Inner, Inner::SVal> where
    Inner: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::ST, obuf: Seq<u8>) {
        self.inner.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner> EquivSerializers for super::Tag<Inner, Inner::SVal> where Inner: EquivSerializers {
    open spec fn equiv_inv(&self) -> bool {
        self.inner.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::ST) {
        self.inner.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Tg, Of> SPRoundTripDps for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + SPRoundTripDps + NonTailFmt,
    Of: SPRoundTripDps,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let tag = super::Tag { inner: self.0, tag: self.1 };
        assert(tag.consistent(self.1));
        Preceded(tag, self.2).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Tg, Of> NonMalleable for super::Tagged<Tg, Of> where
    Tg: SoundParser + NonMalleable,
    Of: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_parse_non_malleable(
            buf1,
            buf2,
        );
    }
}

impl<Tg, Of> NoLookAhead for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + NoLookAhead<PVal = Tg::T>,
    Of: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_no_lookahead(i1, i2);
    }
}

impl<Tg, Of> EquivSerializersGeneral for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + EquivSerializersGeneral<SVal = Tg::T, ST = Tg::T> + Consistency<Val = Tg::T>,
    Of: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::ST, obuf: Seq<u8>) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_serialize_equiv(v, obuf);
    }
}

impl<Tg, Of> EquivSerializers for super::Tagged<Tg, Of> where
    Tg: SpecByteLen + EquivSerializersGeneral<SVal = Tg::T, ST = Tg::T> + Consistency<Val = Tg::T>,
    Of: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::ST) {
        Preceded(super::Tag { inner: self.0, tag: self.1 }, self.2).lemma_serialize_equiv_on_empty(
            v,
        );
    }
}

} // verus!
