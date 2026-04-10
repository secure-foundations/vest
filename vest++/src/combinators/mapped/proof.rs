use super::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner, M> SPRoundTripDps for super::Mapped<Inner, M> where
    Inner: SPRoundTripDps,
    M: LossyMapper<In = Inner::T>,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        self.inner.sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_v = M::spec_map_rev(v);
        self.inner.theorem_serialize_dps_parse_roundtrip(inner_v, obuf);
        assert(M::wf_out(v));
        M::lemma_sound_mapper(v);
    }
}

// impl<Inner, M> PSRoundTrip for super::Mapped<Inner, M> where
//     Inner: PSRoundTrip,
//     M: LosslessMapper<In = Inner::PVal>,
//  {
// }
impl<Inner, M> NonMalleable for super::Mapped<Inner, M> where
    Inner: SoundParser + NonMalleable,
    M: LosslessMapper<In = Inner::PVal>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.inner.nonmal_inv()
        &&& self.inner.sound_inv()
        &&& forall|v: Inner::T| #![auto] self.inner.consistent(v) ==> M::wf_in(v)
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (i_n1, i_v1) = self.inner.spec_parse(buf1)->0;
                    let (i_n2, i_v2) = self.inner.spec_parse(buf2)->0;
                    self.inner.lemma_parse_sound_value(buf1);
                    self.inner.lemma_parse_sound_value(buf2);
                    assert(M::wf_in(i_v1));
                    assert(M::wf_in(i_v2));
                    M::lemma_lossless_mapper(i_v1);
                    M::lemma_lossless_mapper(i_v2);
                    self.inner.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<Inner, M> NoLookAhead for super::Mapped<Inner, M> where
    Inner: NoLookAhead,
    M: LossyMapper<In = Inner::PVal>,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.inner.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(self.safe_inv());
                    assert(self.no_lookahead_inv());
                    assert(self.unambiguous());
                    self.inner.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<Inner, M> EquivSerializersGeneral for super::Mapped<Inner, M> where
    Inner: EquivSerializersGeneral,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_v = M::spec_map_rev(v);
        self.inner.lemma_serialize_equiv(inner_v, obuf);
    }
}

impl<Inner, M> EquivSerializers for super::Mapped<Inner, M> where
    Inner: EquivSerializers,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        self.inner.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let inner_v = M::spec_map_rev(v);
        self.inner.lemma_serialize_equiv_on_empty(inner_v);
    }
}

impl<Inner: SPRoundTripDps, Out> SPRoundTripDps for super::Mapped<
    Inner,
    FnSpecMapper<Inner::T, Out>,
> {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        &&& self.inner.sp_roundtrip_dps_inv()
        &&& forall|o: Out| #![auto] self.consistent(o) ==> (self.mapper.0)((self.mapper.1)(o)) == o
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_v = self.mapper.1(v);
        self.inner.theorem_serialize_dps_parse_roundtrip(inner_v, obuf);
    }
}

impl<Inner, Out> NonMalleable for super::Mapped<Inner, FnSpecMapper<Inner::PVal, Out>> where
    Inner: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.inner.nonmal_inv()
        &&& self.inner.sound_inv()
        &&& forall|v: Inner::PVal|
            #![auto]
            self.inner.consistent(v) ==> (self.mapper.1)((self.mapper.0)(v)) == v
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (i_n1, i_v1) = self.inner.spec_parse(buf1)->0;
                    let (i_n2, i_v2) = self.inner.spec_parse(buf2)->0;
                    self.inner.lemma_parse_sound_value(buf1);
                    self.inner.lemma_parse_sound_value(buf2);
                    self.inner.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<Inner: NoLookAhead, Out> NoLookAhead for super::Mapped<Inner, FnSpecMapper<Inner::PVal, Out>> {
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

impl<Inner: EquivSerializersGeneral, Out> EquivSerializersGeneral for super::Mapped<
    Inner,
    FnSpecMapper<Inner::SVal, Out>,
> {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_v = self.mapper.1(v);
        self.inner.lemma_serialize_equiv(inner_v, obuf);
    }
}

impl<Inner: EquivSerializers, Out> EquivSerializers for super::Mapped<
    Inner,
    FnSpecMapper<Inner::SVal, Out>,
> {
    open spec fn equiv_inv(&self) -> bool {
        self.inner.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let inner_v = self.mapper.1(v);
        self.inner.lemma_serialize_equiv_on_empty(inner_v);
    }
}

impl<Inner, M> SPRoundTripDps for super::TryMap<Inner, M> where
    Inner: SPRoundTripDps,
    M: LossyMapper<In = Inner::T>,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        self.inner().sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.inner().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Inner, M> NonMalleable for super::TryMap<Inner, M> where
    Inner: SoundParser + NonMalleable,
    M: LosslessMapper<In = Inner::PVal>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        self.inner().nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.inner().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner, M> NoLookAhead for super::TryMap<Inner, M> where
    Inner: NoLookAhead,
    M: LossyMapper<In = Inner::PVal>,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.inner().no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        self.inner().lemma_no_lookahead(i1, i2);
    }
}

impl<Inner, M> EquivSerializersGeneral for super::TryMap<Inner, M> where
    Inner: EquivSerializersGeneral,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner().equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.inner().lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner, M> EquivSerializers for super::TryMap<Inner, M> where
    Inner: EquivSerializers,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        self.inner().equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.inner().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
