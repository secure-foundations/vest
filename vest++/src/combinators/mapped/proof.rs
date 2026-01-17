use super::spec::*;
use crate::core::proof::{Deterministic, NonMalleable, PSRoundTrip, SPRoundTrip};
use crate::core::spec::{GoodSerializer, SpecParser, SpecSerializer, SpecSerializerDps, SpecType};
use vstd::prelude::*;

verus! {

impl<Inner, M> SPRoundTrip for super::Mapped<Inner, M> where
    Inner: SPRoundTrip,
    M: IsoMapper<In = Inner::PT>,
 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::ST, obuf: Seq<u8>) {
        if v.wf() {
            self.mapper.lemma_map_rev_wf(v);
            let inner_v = self.mapper.spec_map_rev(v);
            self.inner.theorem_serialize_parse_roundtrip(inner_v, obuf);
            self.mapper.lemma_map_iso_rev(v);
        }
    }
}

impl<Inner, M> PSRoundTrip for super::Mapped<Inner, M> where
    Inner: PSRoundTrip,
    M: IsoMapper<In = Inner::PT>,
 {

}

impl<Inner, M> NonMalleable for super::Mapped<Inner, M> where
    Inner: NonMalleable,
    M: IsoMapper<In = Inner::PT>,
 {
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

impl<Inner, M> Deterministic for super::Mapped<Inner, M> where
    Inner: Deterministic,
    M: IsoMapper<In = <Inner as SpecSerializer>::ST>,
 {
    proof fn lemma_serialize_equiv(&self, v: <Self as SpecSerializer>::ST, obuf: Seq<u8>) {
        self.mapper.lemma_map_rev_wf(v);
        let inner_v = self.mapper.spec_map_rev(v);
        self.inner.lemma_serialize_equiv(inner_v, obuf);
    }
}

} // verus!
