use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTripDps> super::Opt<A> {
    proof fn lemma_serialize_parse_roundtrip(&self, v: Option<A::T>, obuf: Seq<u8>)
        requires
            self.0.unambiguous(),
            parser_fails_on(self.0, obuf),
        ensures
            self.consistent(v) ==> {
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = self.byte_len(v) as int;
                self.spec_parse(ibuf) == Some((n, v))
            },
    {
        match v {
            None => {},
            Some(vv) => {
                if self.consistent(Some(vv)) {
                    self.0.theorem_serialize_dps_parse_roundtrip(vv, obuf);
                }
            },
        }
    }
}

impl<A: NoLookAhead> super::Opt<A> {
    proof fn lemma_opt_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>)
        requires
            self.0.sound_inv(),
            self.0.unambiguous(),
            parser_fails_on(self.0, i1) ==> parser_fails_on(self.0, i2),
        ensures
            self.spec_parse(i1) matches Some((n, v)) ==> 0 <= n <= i2.len() ==> i2.take(n)
                == i1.take(n) ==> self.spec_parse(i2) == Some((n, v)),
    {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n0, v0)) = self.0.spec_parse(i1) {
                        self.0.lemma_no_lookahead(i1, i2);
                    } else {
                        assert(self.0.spec_parse(i2) is None);
                    }
                }
            }
        }
    }
}

impl<A: NonMalleable> NonMalleable for super::Opt<A> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

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

impl<A: SPRoundTripDps + NonTailFmt, B: SPRoundTripDps> SPRoundTripDps for super::Optional<A, B> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let opt = super::Opt(self.0);
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        self.1.theorem_serialize_dps_parse_roundtrip(v.1, obuf);
        let serialized0 = opt.spec_serialize_dps(v.0, serialized1);
        opt.lemma_serialize_parse_roundtrip(v.0, serialized1);
        let n0 = serialized0.len() - serialized1.len();
        opt.lemma_serialize_dps_prepend(v.0, serialized1);
        opt.lemma_serialize_dps_len(v.0, serialized1);
        assert(serialized0.skip(n0) == serialized1);
    }
}

// impl<
//     A: PSRoundTrip + GoodSerializerDps + EquivSerializersGeneral,
//     B: PSRoundTrip,
// > PSRoundTrip for super::Optional<A, B> {
// }
impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Optional<A, B> {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, B: NoLookAhead> NoLookAhead for super::Optional<A, B> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        broadcast use vstd::seq_lib::group_seq_properties;

        use crate::combinators::tuple::proof::lemma_take_skip;

        let opt = super::Opt(self.0);
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    if let Some((n0, a)) = self.0.spec_parse(i1) {
                        if let Some((n1, b)) = self.1.spec_parse(i1.skip(n0)) {
                            opt.lemma_parse_safe(i1);
                            self.1.lemma_parse_safe(i1.skip(n0));
                            assert(i2.take(n0) == i1.take(n0));
                            opt.lemma_opt_no_lookahead(i1, i2);
                            assert(i2.skip(n0).take(n1) == i1.skip(n0).take(n1)) by {
                                lemma_take_skip(i1, n0, n1);
                                lemma_take_skip(i2, n0, n1);
                            };
                            self.1.lemma_no_lookahead(i1.skip(n0), i2.skip(n0));
                        }
                    } else if let Some((n1, b)) = self.1.spec_parse(i1) {
                        assert(disjoint_domains(self.0, self.1));
                        self.1.lemma_no_lookahead(i1, i2);
                    }
                }
            }
        }
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
