use super::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<Inner, M> SPRoundTripDps for super::Mapped<Inner, M> where
    Inner: SPRoundTripDps,
    M: IsoMapper<In = Inner::T>,
 {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        self.inner.sp_roundtrip_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let inner_v = self.mapper.spec_map_rev(v);
        self.inner.theorem_serialize_dps_parse_roundtrip(inner_v, obuf);
        self.mapper.lemma_map_iso_rev(v);
    }
}

// impl<Inner, M> PSRoundTrip for super::Mapped<Inner, M> where
//     Inner: PSRoundTrip,
//     M: IsoMapper<In = Inner::PVal>,
//  {
// }
impl<Inner, M> NonMalleable for super::Mapped<Inner, M> where
    Inner: NonMalleable,
    M: IsoMapper<In = Inner::PVal>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        self.inner.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let (i_n1, i_v1) = self.inner.spec_parse(buf1)->0;
                    let (i_n2, i_v2) = self.inner.spec_parse(buf2)->0;
                    self.mapper.lemma_map_iso(i_v1);
                    self.mapper.lemma_map_iso(i_v2);
                    self.inner.lemma_parse_non_malleable(buf1, buf2);
                }
            }
        }
    }
}

impl<Inner, M> NoLookAhead for super::Mapped<Inner, M> where
    Inner: NoLookAhead,
    M: IsoMapper<In = Inner::PVal>,
 {
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

impl<Inner, M> EquivSerializersGeneral for super::Mapped<Inner, M> where
    Inner: EquivSerializersGeneral,
    M: Mapper<In = Inner::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.inner.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let inner_v = self.mapper.spec_map_rev(v);
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
        let inner_v = self.mapper.spec_map_rev(v);
        self.inner.lemma_serialize_equiv_on_empty(inner_v);
    }
}

} // verus!
