use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTripDps> super::Opt<A> {
    proof fn lemma_serialize_parse_roundtrip(&self, v: Option<A::T>, obuf: Seq<u8>)
        requires
            self.0.unambiguous(),
            parser_fails_on(self.0, obuf),
        ensures
            v.wf() ==> {
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = self.byte_len(v) as int;
                self.spec_parse(ibuf) == Some((n, v))
            },
    {
        match v {
            None => {},
            Some(vv) => {
                self.0.theorem_serialize_dps_parse_roundtrip(vv, obuf);
            },
        }
    }
}

impl<A: NonMalleable> NonMalleable for super::Opt<A> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A> EquivSerializersGeneral for super::Opt<A> where A: EquivSerializersGeneral {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_equiv(vv, obuf);
            },
        }
    }
}

impl<A> EquivSerializers for super::Opt<A> where A: EquivSerializers {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_equiv_on_empty(vv);
            },
        }
    }
}

impl<A: SPRoundTripDps + GoodSerializerDps, B: SPRoundTripDps> SPRoundTripDps for super::Optional<
    A,
    B,
> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let opt = super::Opt(self.0);
        if v.wf() {
            let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
            self.1.theorem_serialize_dps_parse_roundtrip(v.1, obuf);
            let serialized0 = opt.spec_serialize_dps(v.0, serialized1);
            opt.lemma_serialize_parse_roundtrip(v.0, serialized1);
            let n0 = serialized0.len() - serialized1.len();
            opt.lemma_serialize_dps_buf(v.0, serialized1);
            opt.lemma_serialize_dps_len(v.0, serialized1);
            assert(serialized0.skip(n0) == serialized1);
        }
    }
}

// impl<
//     A: PSRoundTrip + GoodSerializerDps + EquivSerializersGeneral,
//     B: PSRoundTrip,
// > PSRoundTrip for super::Optional<A, B> {
// }
impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Optional<A, B> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
> EquivSerializersGeneral for super::Optional<A, B> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_equiv(v, obuf);
    }
}

impl<A: EquivSerializersGeneral, B: EquivSerializers> EquivSerializers for super::Optional<A, B> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        (super::Opt(self.0), self.1).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
