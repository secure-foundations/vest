use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: NonMalleable> NonMalleable for super::Opt<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A> SpecSerializers for super::Opt<A> where A: SpecSerializers {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_equiv(vv, obuf);
            },
        }
    }
}

impl<A: SPRoundTrip + GoodSerializerDps, B: SPRoundTrip> SPRoundTrip for super::Optional<A, B> {
    proof fn theorem_serialize_parse_roundtrip_internal(&self, v: Self::T, obuf: Seq<u8>) {
        if v.wf() {
            let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
            self.1.theorem_serialize_parse_roundtrip_internal(v.1, obuf);
            match v.0 {
                Some(v0) => {
                    let serialized0 = self.0.spec_serialize_dps(v0, serialized1);
                    self.0.theorem_serialize_parse_roundtrip_internal(v0, serialized1);
                    self.0.lemma_serialize_dps_buf(v0, serialized1);
                    self.0.lemma_serialize_dps_len(v0, serialized1);
                    if let Some((n0, _)) = self.0.spec_parse(serialized0) {
                        assert(n0 == serialized0.len() - serialized1.len());
                        assert(serialized0.skip(n0) == serialized1);
                    }
                },
                None => {
                    assert(serialized1.skip(0) == serialized1);
                },
            }
        }
    }
}

impl<A: PSRoundTrip + GoodSerializerDps, B: PSRoundTrip> PSRoundTrip for super::Optional<A, B> {

}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Optional<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: SpecSerializers, B: SpecSerializers> SpecSerializers for super::Optional<A, B> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_equiv(v, obuf);
    }
}

} // verus!
