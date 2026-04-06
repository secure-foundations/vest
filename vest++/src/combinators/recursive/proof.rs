//! Correctness proofs and recursive-body preservation helpers for [`super::Fix`].
use super::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Functional version of [`SPRoundTripDps`] for parser/serializer callback bundles.
pub open spec fn sp_roundtrip_dps_parser<T>(
    parser: ParserFnSpec<T>,
    consistent: PredFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
    serializer_dps: SerializerDPSFnSpec<T>,
    unambiguous: UnambiguityFnSpec,
) -> bool {
    forall|v: T, obuf: Seq<u8>|
        consistent(v) && unambiguous() ==> #[trigger] parser(serializer_dps(v, obuf)) == Some(
            (byte_len(v) as int, v),
        )
}

/// Functional version of [`NoLookAhead`] for parsers.
pub open spec fn no_lookahead_parser<T>(
    parser: ParserFnSpec<T>,
    unambiguous: UnambiguityFnSpec,
) -> bool {
    forall|i1: Seq<u8>, i2: Seq<u8>|
        unambiguous() ==> (#[trigger] parser(i1) matches Some((n, v)) ==> 0 <= n <= i2.len()
            ==> i2.take(n) == i1.take(n) ==> #[trigger] parser(i2) == Some((n, v)))
}

pub open spec fn parser_pair_some<T>(
    parser: ParserFnSpec<T>,
    buf1: Seq<u8>,
    buf2: Seq<u8>,
) -> Option<((int, T), (int, T))> {
    match parser(buf1) {
        Some((n1, v1)) => match parser(buf2) {
            Some((n2, v2)) => Some(((n1, v1), (n2, v2))),
            None => None,
        },
        None => None,
    }
}

/// Functional non-malleability for parser functions.
pub open spec fn non_malleable_parser<T>(parser: ParserFnSpec<T>) -> bool {
    forall|buf1: Seq<u8>, buf2: Seq<u8>| #[trigger]
        parser_pair_some(parser, buf1, buf2) matches Some(((n1, v1), (n2, v2))) ==> v1 == v2
            ==> buf1.take(n1) == buf2.take(n2)
}

impl<SpecP, Cnstcy, Blen> NonMalleable for ParserSpecs<SpecP, Cnstcy, Blen> where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        let (p, _, _) = *self;
        let p_fn = |ibuf| p.spec_parse(ibuf);
        non_malleable_parser(p_fn)
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let (p, _, _) = *self;
        let p_fn = |ibuf| p.spec_parse(ibuf);
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    assert(self.nonmal_inv());
                    assert(parser_pair_some(p_fn, buf1, buf2) == Some(((n1, v1), (n2, v2))));
                    assert(non_malleable_parser(p_fn));
                    assert(buf1.take(n1) == buf2.take(n2));
                }
            }
        }
    }
}

impl<T> NonMalleable for BundledSpecs<T> {
    open spec fn nonmal_inv(&self) -> bool {
        parser_specs(*self).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        parser_specs(*self).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<T> SPRoundTripDps for BundledSpecs<T> {
    open spec fn sp_roundtrip_dps_inv(&self) -> bool {
        let (c, b, p, _, s_dps, u) = *self;
        sp_roundtrip_dps_parser(p, c, b, s_dps, u)
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let (c, b, p, _, s_dps, u) = *self;
        assert(self.unambiguous());
        assert(sp_roundtrip_dps_parser(p, c, b, s_dps, u));
        assert(p(s_dps(v, obuf)) == Some(((b)(v) as int, v)));
    }
}

impl<T> NoLookAhead for BundledSpecs<T> {
    open spec fn no_lookahead_inv(&self) -> bool {
        let (_, _, p, _, _, u) = *self;
        no_lookahead_parser(p, u)
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let (_, _, p, _, _, u) = *self;
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(self.unambiguous());
                    assert(no_lookahead_parser(p, u));
                    assert(p(i1) == Some((n, v)));
                    assert(p(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<T> EquivSerializersGeneral for BundledSpecs<T> {
    open spec fn equiv_general_inv(&self) -> bool {
        let (_, _, _, s, s_dps, _) = *self;
        forall|v: T, obuf: Seq<u8>| #[trigger] (s_dps)(v, obuf) == (s)(v) + obuf
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let (_, _, _, s, s_dps, _) = *self;
        assert((s_dps)(v, obuf) == (s)(v) + obuf);
    }
}

impl<T> EquivSerializers for BundledSpecs<T> {
    open spec fn equiv_inv(&self) -> bool {
        let (_, _, _, s, s_dps, _) = *self;
        forall|v: T| #[trigger] (s_dps)(v, seq![]) == (s)(v) + seq![]
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let (_, _, _, s, s_dps, _) = *self;
        assert((s_dps)(v, seq![]) == (s)(v) + seq![]);
    }
}

/// Non-malleability preservation for recursive bodies.
pub trait NonMalleableRecBody: SoundParserRecBody where Self::Body: NonMalleable {
    proof fn lemma_body_nonmal_inv_preservation(rec: BundledSpecs<Self::T>)
        requires
            rec.sound_inv(),
            rec.nonmal_inv(),
        ensures
            Self::spec_body(rec).nonmal_inv(),
    ;
}

/// DPS serialize-parse roundtrip preservation for recursive bodies.
/// Similar to [`Star`], the body must also be [`NonTailFmt`].
pub trait SPRoundTripDpsRecBody: NonTailFmtRecBody where Self::Body: SPRoundTripDps + NonTailFmt {
    proof fn lemma_body_sp_roundtrip_dps_inv_preservation(rec: BundledSpecs<Self::T>)
        requires
            rec.sp_roundtrip_dps_inv(),
            rec.serialize_dps_inv(),
        ensures
            Self::spec_body(rec).sp_roundtrip_dps_inv(),
    ;
}

/// No-lookahead invariant preservation for recursive bodies.
pub trait NoLookAheadRecBody: SoundParserRecBody where Self::Body: NoLookAhead {
    proof fn lemma_body_no_lookahead_inv_preservation(rec: BundledSpecs<Self::T>)
        requires
            rec.no_lookahead_inv(),
        ensures
            Self::spec_body(rec).no_lookahead_inv(),
    ;
}

/// Serializer equivalence invariant preservation for recursive bodies.
pub trait EquivSerializersGeneralRecBody: SpecRecBody where Self::Body: EquivSerializersGeneral {
    proof fn lemma_s_body_equiv_general_inv_preservation(rec: BundledSpecs<Self::T>)
        requires
            rec.equiv_general_inv(),
        ensures
            Self::spec_body(rec).equiv_general_inv(),
    ;
}

/// Convenience trait bundling the standard recursive-body preservation obligations.
///
/// Implementing this once is enough to derive the individual `*RecBody` traits via blanket impls.
pub trait StrictRecBody: SpecRecBody where Self::Body: StrictCombinator {
    proof fn lemma_body_all_inv_preservation(rec: BundledSpecs<Self::T>)
        ensures
            rec.sound_inv() ==> Self::spec_body(rec).sound_inv(),
            rec.sound_inv() && rec.nonmal_inv() ==> Self::spec_body(rec).nonmal_inv(),
            rec.serialize_inv() ==> Self::spec_body(rec).serialize_inv(),
            rec.serialize_dps_inv() ==> Self::spec_body(rec).serialize_dps_inv(),
            rec.sp_roundtrip_dps_inv() && rec.serialize_dps_inv() ==> Self::spec_body(
                rec,
            ).sp_roundtrip_dps_inv(),
            rec.no_lookahead_inv() ==> Self::spec_body(rec).no_lookahead_inv(),
            rec.equiv_general_inv() ==> Self::spec_body(rec).equiv_general_inv(),
    ;
}

impl<Body: StrictRecBody> SoundParserRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_sound_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).sound_inv());
    }
}

impl<Body: StrictRecBody> NonMalleableRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_nonmal_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).nonmal_inv());
    }
}

impl<Body: StrictRecBody> GoodSerializerRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_s_body_serialize_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).serialize_inv());
    }
}

impl<Body: StrictRecBody> NonTailFmtRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).serialize_dps_inv());
    }
}

impl<Body: StrictRecBody> SPRoundTripDpsRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_sp_roundtrip_dps_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).sp_roundtrip_dps_inv());
    }
}

impl<Body: StrictRecBody> NoLookAheadRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_no_lookahead_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).no_lookahead_inv());
    }
}

impl<Body: StrictRecBody> EquivSerializersGeneralRecBody for Body where
    Body::Body: StrictCombinator,
 {
    proof fn lemma_s_body_equiv_general_inv_preservation(rec: BundledSpecs<Self::T>) {
        Body::lemma_body_all_inv_preservation(rec);
        assert(Body::spec_body(rec).equiv_general_inv());
    }
}

impl<const LIMIT: usize, Body: NonMalleableRecBody> super::Fix<LIMIT, Body> where
    Body::Body: NonMalleable,
 {
    /// Inductive proof that `spec_parse_gas` is non-malleable.
    #[verusfmt::skip]
    proof fn non_malleable_by_induction(
        &self,
        gas: nat,
        buf1: Seq<u8>,
        buf2: Seq<u8>,
        n1: int,
        n2: int,
        v1: Body::T,
        v2: Body::T,
    )
        ensures
            Self::spec_parse_gas(gas, buf1) == Some((n1, v1)) ==>
            Self::spec_parse_gas(gas, buf2) == Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases gas,
    {
        if !(Self::spec_parse_gas(gas, buf1) == Some((n1, v1))) {
            return ;
        }
        if !(Self::spec_parse_gas(gas, buf2) == Some((n2, v2))) {
            return ;
        }
        if !(v1 == v2) {
            return ;
        }

        let callback = Self::specs_callback(gas);
        let callback_p = callback.2;
        let callback_c = callback.0;
        let callback_b = callback.1;

        // establish sound_parser(callback_p, callback_c, callback_b)
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, rem, nn, vv);
            }
        }

        // establish non_malleable_parser(callback_p)
        assert forall|rem1: Seq<u8>, rem2: Seq<u8>| #[trigger]
            parser_pair_some(callback_p, rem1, rem2) matches Some(((nn1, vv1), (nn2, vv2)))
                ==> vv1 == vv2 ==> rem1.take(nn1) == rem2.take(nn2) by {
            if let Some(((nn1, vv1), (nn2, vv2))) = parser_pair_some(callback_p, rem1, rem2) {
                if vv1 == vv2 {
                    self.non_malleable_by_induction((gas - 1) as nat, rem1, rem2, nn1, nn2, vv1, vv2);
                }
            }
        }

        assert(callback.sound_inv());
        assert(callback.nonmal_inv()) by {
            let p_fn = |ibuf: Seq<u8>| callback.2.spec_parse(ibuf);
            assert(p_fn == callback_p);
        }

        Body::lemma_body_sound_inv_preservation(callback);
        Body::lemma_body_nonmal_inv_preservation(callback);
        let body = Body::spec_body(callback);

        body.lemma_parse_non_malleable(buf1, buf2);

        // By definition
        assert(Self::spec_parse_gas(gas, buf1) == body.spec_parse(buf1));
        assert(Self::spec_parse_gas(gas, buf2) == body.spec_parse(buf2));
    }
}

impl<const LIMIT: usize, Body: NonMalleableRecBody> NonMalleable for super::Fix<LIMIT, Body> where
    Body::Body: NonMalleable,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.non_malleable_by_induction(LIMIT as nat, buf1, buf2, n1, n2, v1, v2);
                }
            }
        }
    }
}

impl<const LIMIT: usize, Body> super::Fix<LIMIT, Body> where
    Body: SPRoundTripDpsRecBody + NonTailFmtRecBody,
    Body::Body: SPRoundTripDps + NonTailFmt,
 {
    /// Inductive proof for DPS serialize-parse roundtrip under bounded unfolding.
    proof fn sp_roundtrip_dps_by_induction(&self, gas: nat, v: Body::T, obuf: Seq<u8>)
        requires
            Self::consistent_gas(gas, v),
            Self::unambiguity_gas(gas),
        ensures
            Self::spec_parse_gas(gas, Self::spec_serialize_dps_gas(gas, v, obuf)) == Some(
                (Self::byte_len_gas(gas, v) as int, v),
            ),
        decreases gas,
    {
        let callback = Self::specs_callback(gas);
        let callback_c = callback.0;
        let callback_b = callback.1;
        let callback_p = callback.2;
        let callback_s_dps = callback.4;
        let callback_u = callback.5;

        // establish sp_roundtrip_dps_parser(callback_p, callback_c, callback_b, callback_s_dps, callback_u)
        assert forall|vv: Body::T, buf: Seq<u8>|
            (callback_c(vv) && callback_u()) implies #[trigger] callback_p(callback_s_dps(vv, buf))
            == Some((callback_b(vv) as int, vv)) by {
            if callback_c(vv) && callback_u() {
                self.sp_roundtrip_dps_by_induction((gas - 1) as nat, vv, buf);
            }
        }

        // establish callback.serialize_dps_inv()
        assert forall|vv: Body::T, buf: Seq<u8>| #[trigger]
            callback_s_dps(vv, buf).len() - buf.len() == callback_b(vv) by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, vv, buf);
            } else {
                assert(callback_s_dps(vv, buf) == buf);
                assert(callback_b(vv) == 0);
            }
        }

        assert forall|vv: Body::T, buf: Seq<u8>|
            exists|new_buf: Seq<u8>| (#[trigger] callback_s_dps(vv, buf)) == new_buf + buf by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, vv, buf);
                let witness = choose|w: Seq<u8>|
                    Self::spec_serialize_dps_gas((gas - 1) as nat, vv, buf) == w + buf;
                assert(callback_s_dps(vv, buf) == witness + buf);
            } else {
                assert(callback_s_dps(vv, buf) == Seq::<u8>::empty() + buf);
            }
        }

        assert(callback.sp_roundtrip_dps_inv());
        assert(callback.serialize_dps_inv());

        Body::lemma_body_sp_roundtrip_dps_inv_preservation(callback);
        let body = Body::spec_body(callback);

        assert(Self::consistent_gas(gas, v) == body.consistent(v));
        assert(Self::unambiguity_gas(gas) == body.unambiguous());

        body.theorem_serialize_dps_parse_roundtrip(v, obuf);

        // By definition
        assert(Self::spec_parse_gas(gas, Self::spec_serialize_dps_gas(gas, v, obuf))
            == body.spec_parse(body.spec_serialize_dps(v, obuf)));
        assert(Self::byte_len_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body> SPRoundTripDps for super::Fix<LIMIT, Body> where
    Body: SPRoundTripDpsRecBody + NonTailFmtRecBody,
    Body::Body: SPRoundTripDps + NonTailFmt,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.sp_roundtrip_dps_by_induction(LIMIT as nat, v, obuf);
    }
}

impl<const LIMIT: usize, Body: EquivSerializersGeneralRecBody> super::Fix<LIMIT, Body> where
    Body::Body: EquivSerializersGeneral,
 {
    /// Inductive proof that DPS and non-DPS serializers are equivalent under bounded unfolding.
    proof fn equiv_serializers_general_by_induction(&self, gas: nat, v: Body::T, obuf: Seq<u8>)
        ensures
            Self::spec_serialize_dps_gas(gas, v, obuf) == Self::spec_serialize_gas(gas, v) + obuf,
        decreases gas,
    {
        let callback = Self::specs_callback(gas);
        let callback_s = callback.3;
        let callback_s_dps = callback.4;

        // establish callback.equiv_general_inv()
        assert forall|vv: Body::T, buf: Seq<u8>| #[trigger]
            callback_s_dps(vv, buf) == callback_s(vv) + buf by {
            if gas > 0 {
                self.equiv_serializers_general_by_induction((gas - 1) as nat, vv, buf);
            } else {
                assert(callback_s_dps(vv, buf) == buf);
                assert(callback_s(vv) == Seq::<u8>::empty());
                assert(callback_s_dps(vv, buf) == callback_s(vv) + buf);
            }
        }

        assert(callback.equiv_general_inv());
        Body::lemma_s_body_equiv_general_inv_preservation(callback);
        let body = Body::spec_body(callback);

        body.lemma_serialize_equiv(v, obuf);

        // By definition
        assert(Self::spec_serialize_dps_gas(gas, v, obuf) == body.spec_serialize_dps(v, obuf));
        assert(Self::spec_serialize_gas(gas, v) == body.spec_serialize(v));
    }
}

impl<const LIMIT: usize, Body> EquivSerializersGeneral for super::Fix<LIMIT, Body> where
    Body: EquivSerializersGeneralRecBody,
    Body::Body: EquivSerializersGeneral,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.equiv_serializers_general_by_induction(LIMIT as nat, v, obuf);
    }
}

impl<const LIMIT: usize, Body> EquivSerializers for super::Fix<LIMIT, Body> where
    Body: EquivSerializersGeneralRecBody,
    Body::Body: EquivSerializersGeneral,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.lemma_serialize_equiv(v, Seq::empty());
    }
}

impl<const LIMIT: usize, Body: NoLookAheadRecBody> super::Fix<LIMIT, Body> where
    Body::Body: NoLookAhead,
 {
    /// One-step induction over `gas` for no-lookahead.
    proof fn no_lookahead_by_induction(
        &self,
        gas: nat,
        i1: Seq<u8>,
        i2: Seq<u8>,
        n: int,
        v: Body::T,
    )
        requires
            Self::spec_parse_gas(gas, i1) == Some((n, v)),
            0 <= n <= i2.len(),
            i2.take(n) == i1.take(n),
            Self::unambiguity_gas(gas),
        ensures
            Self::spec_parse_gas(gas, i2) == Some((n, v)),
        decreases gas,
    {
        let callback = Self::specs_callback(gas);
        let callback_p = callback.2;
        let callback_c = callback.0;
        let callback_b = callback.1;
        let callback_u = callback.5;

        // establish callback.sound_inv()
        assert forall|rem: Seq<u8>| #[trigger]
            callback_p(rem) matches Some((nn, vv)) ==> {
                &&& 0 <= nn <= rem.len()
                &&& callback_c(vv)
                &&& callback_b(vv) == nn
            } by {
            if let Some((nn, vv)) = callback_p(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, rem, nn, vv);
            }
        }

        // establish callback.no_lookahead_inv()
        assert forall|i1: Seq<u8>, i2: Seq<u8>| callback_u() implies (#[trigger] callback_p(
            i1,
        ) matches Some((n, v)) ==> 0 <= n <= i2.len() ==> i2.take(n) == i1.take(n)
            ==> #[trigger] callback_p(i2) == Some((n, v))) by {
            if let Some((n, v)) = callback_p(i1) {
                if 0 <= n && n <= i2.len() && i2.take(n) == i1.take(n) {
                    self.no_lookahead_by_induction((gas - 1) as nat, i1, i2, n, v);
                }
            }
        }

        assert(sound_parser(callback_p, callback_c, callback_b));
        assert(callback.sound_inv());
        assert(callback.no_lookahead_inv());

        Body::lemma_body_sound_inv_preservation(callback);
        Body::lemma_body_no_lookahead_inv_preservation(callback);
        let body = Body::spec_body(callback);

        assert(Self::unambiguity_gas(gas) == body.unambiguous());
        assert(Self::spec_parse_gas(gas, i1) == body.spec_parse(i1));
        assert(Self::spec_parse_gas(gas, i2) == body.spec_parse(i2));

        body.lemma_no_lookahead(i1, i2);

        assert(body.spec_parse(i1) == Some((n, v)));
        assert(body.spec_parse(i2) == Some((n, v)));
    }
}

impl<const LIMIT: usize, Body: NoLookAheadRecBody> NoLookAhead for super::Fix<LIMIT, Body> where
    Body::Body: NoLookAhead,
 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.no_lookahead_by_induction(LIMIT as nat, i1, i2, n, v);
                }
            }
        }
    }
}

} // verus!
