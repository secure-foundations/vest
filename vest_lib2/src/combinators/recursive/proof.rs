//! Correctness proofs and recursive-body preservation helpers for [`super::FixWith`].
use super::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Functional version of [`SPRoundTripDps`] for parser/serializer callback bundles.
pub open spec fn sp_roundtrip_dps<T>(
    parser: ParserFnSpec<T>,
    consistent: PredFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
    serializer_dps: SerializerDPSFnSpec<T>,
) -> bool {
    forall|v: T, obuf: Seq<u8>|
        consistent(v) ==> #[trigger] parser(serializer_dps(v, obuf)) == Some(
            (byte_len(v) as int, v),
        )
}

/// Functional version of [`NoLookAhead`] for parsers.
pub open spec fn no_lookahead_parser<T>(parser: ParserFnSpec<T>) -> bool {
    forall|i1: Seq<u8>, i2: Seq<u8>|
        (#[trigger] parser(i1) matches Some((n, v)) ==> 0 <= n <= i2.len() ==> i2.take(n)
            == i1.take(n) ==> #[trigger] parser(i2) == Some((n, v)))
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
    open spec fn unambiguous(&self) -> bool {
        let (c, b, p, _, s_dps) = *self;
        sp_roundtrip_dps(p, c, b, s_dps)
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let (c, b, p, _, s_dps) = *self;
        assert(sp_roundtrip_dps(p, c, b, s_dps));
        assert(c(v));
        assert(p(s_dps(v, obuf)) == Some(((b)(v) as int, v)));
    }
}

impl<T> NoLookAhead for BundledSpecs<T> {
    open spec fn no_lookahead_inv(&self) -> bool {
        let (_, _, p, _, _) = *self;
        no_lookahead_parser(p)
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let (_, _, p, _, _) = *self;
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(no_lookahead_parser(p));
                    assert(p(i1) == Some((n, v)));
                    assert(p(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<T> EquivSerializersGeneral for BundledSpecs<T> {
    open spec fn equiv_general_inv(&self) -> bool {
        let (_, _, _, s, s_dps) = *self;
        forall|v: T, obuf: Seq<u8>| #[trigger] (s_dps)(v, obuf) == (s)(v) + obuf
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let (_, _, _, s, s_dps) = *self;
        assert((s_dps)(v, obuf) == (s)(v) + obuf);
    }
}

impl<T> EquivSerializers for BundledSpecs<T> {
    open spec fn equiv_inv(&self) -> bool {
        let (_, _, _, s, s_dps) = *self;
        forall|v: T| #[trigger] (s_dps)(v, seq![]) == (s)(v) + seq![]
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let (_, _, _, s, s_dps) = *self;
        assert((s_dps)(v, seq![]) == (s)(v) + seq![]);
    }
}

/// Non-malleability preservation for recursive bodies.
pub trait NonMalleableRecBody: SafeParserRecBody + SoundParserRecBody where
    Self::Body: NonMalleable + SoundParser,
 {
    proof fn lemma_body_nonmal_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).safe_inv(),
            forall|p: Self::Param| #![trigger rec(p)] rec(p).sound_inv(),
            forall|p: Self::Param| #![trigger rec(p)] rec(p).nonmal_inv(),
        ensures
            Self::spec_body(param, rec).nonmal_inv(),
    ;
}

/// DPS serialize-parse roundtrip preservation for recursive bodies.
/// Similar to [`Star`], the body must also be [`NonTailFmt`].
pub trait SPRoundTripDpsRecBody: NonTailFmtRecBody where Self::Body: SPRoundTripDps + NonTailFmt {
    proof fn lemma_body_sp_roundtrip_dps_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).unambiguous(),
            forall|p: Self::Param| #![trigger rec(p)] rec(p).serialize_dps_inv(),
        ensures
            Self::spec_body(param, rec).unambiguous(),
    ;
}

/// No-lookahead invariant preservation for recursive bodies.
pub trait NoLookAheadRecBody: SafeParserRecBody where Self::Body: NoLookAhead {
    proof fn lemma_body_no_lookahead_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).no_lookahead_inv(),
        ensures
            Self::spec_body(param, rec).no_lookahead_inv(),
    ;
}

/// Serializer equivalence invariant preservation for recursive bodies.
pub trait EquivSerializersGeneralRecBody: SpecRecBody where Self::Body: EquivSerializersGeneral {
    proof fn lemma_s_body_equiv_general_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).equiv_general_inv(),
        ensures
            Self::spec_body(param, rec).equiv_general_inv(),
    ;
}

/// Convenience trait bundling the standard recursive-body preservation obligations.
///
/// Implementing this once is enough to derive the individual `*RecBody` traits via blanket impls.
pub trait StrictRecBody: SpecRecBody where Self::Body: StrictCombinator {
    #[verusfmt::skip]
    proof fn lemma_body_all_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        ensures
            (forall|p: Self::Param| #![trigger rec(p)] rec(p).safe_inv())
            ==> Self::spec_body(param, rec).safe_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).sound_inv())
            ==> Self::spec_body(param, rec).sound_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).safe_inv())
            && (forall|p: Self::Param| #![trigger rec(p)] rec(p).sound_inv())
            && (forall|p: Self::Param| #![trigger rec(p)] rec(p).nonmal_inv())
            ==> Self::spec_body(param, rec).nonmal_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).serialize_inv())
            ==> Self::spec_body(param, rec).serialize_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).serialize_dps_inv())
            ==> Self::spec_body(param, rec).serialize_dps_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).unambiguous())
            && (forall| p: Self::Param| #![trigger rec(p)] rec(p).serialize_dps_inv())
            ==> Self::spec_body(param, rec).unambiguous(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).no_lookahead_inv())
            ==> Self::spec_body(param, rec).no_lookahead_inv(),

            (forall|p: Self::Param| #![trigger rec(p)] rec(p).equiv_general_inv())
            ==> Self::spec_body(param, rec).equiv_general_inv(),
    ;
}

impl<Body: StrictRecBody> SafeParserRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_safe_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).safe_inv());
    }
}

impl<Body: StrictRecBody> SoundParserRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_sound_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).sound_inv());
    }
}

impl<Body: StrictRecBody> NonMalleableRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_nonmal_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).nonmal_inv());
    }
}

impl<Body: StrictRecBody> GoodSerializerRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_s_body_serialize_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).serialize_inv());
    }
}

impl<Body: StrictRecBody> NonTailFmtRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).serialize_dps_inv());
    }
}

impl<Body: StrictRecBody> SPRoundTripDpsRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_sp_roundtrip_dps_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).unambiguous());
    }
}

impl<Body: StrictRecBody> NoLookAheadRecBody for Body where Body::Body: StrictCombinator {
    proof fn lemma_body_no_lookahead_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).no_lookahead_inv());
    }
}

impl<Body: StrictRecBody> EquivSerializersGeneralRecBody for Body where
    Body::Body: StrictCombinator,
 {
    proof fn lemma_s_body_equiv_general_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
        Body::lemma_body_all_inv_preservation(param, rec);
        assert(Body::spec_body(param, rec).equiv_general_inv());
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: NonMalleableRecBody,
    Body::Body: NonMalleable + SoundParser,
    Param: DeepView<V = Body::Param>,
 {
    /// Inductive proof that `spec_parse_gas` is non-malleable.
    #[verusfmt::skip]
    proof fn non_malleable_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        buf1: Seq<u8>,
        buf2: Seq<u8>,
        n1: int,
        n2: int,
        v1: Body::T,
        v2: Body::T,
    )
        ensures
            Self::spec_parse_gas(gas, param, buf1) == Some((n1, v1)) ==>
            Self::spec_parse_gas(gas, param, buf2) == Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases gas,
    {
        if !(Self::spec_parse_gas(gas, param, buf1) == Some((n1, v1))) {
            return ;
        }
        if !(Self::spec_parse_gas(gas, param, buf2) == Some((n2, v2))) {
            return ;
        }
        if !(v1 == v2) {
            return ;
        }

        let callback = Self::specs_callback(gas);
        let callback_p = callback(param).2;
        let callback_c = callback(param).0;
        let callback_b = callback(param).1;

        assert forall|p: Body::Param, rem: Seq<u8>| #[trigger]
            callback(p).2(rem) matches Some((nn, _vv)) ==> 0 <= nn <= rem.len() by {
            if let Some((nn, vv)) = callback(p).2(rem) {
                self.safe_parser_by_induction((gas - 1) as nat, p, rem, nn, vv);
            }
        }

        assert forall|p: Body::Param, rem: Seq<u8>| #[trigger]
            callback(p).2(rem) matches Some((nn, vv)) ==> {
                &&& callback(p).0(vv)
                &&& callback(p).1(vv) == nn
            } by {
            if let Some((nn, vv)) = callback(p).2(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, p, rem, nn, vv);
            }
        }

        assert forall|p: Body::Param, rem1: Seq<u8>, rem2: Seq<u8>| #[trigger]
            parser_pair_some(callback(p).2, rem1, rem2) matches Some(((nn1, vv1), (nn2, vv2)))
                ==> vv1 == vv2 ==> rem1.take(nn1) == rem2.take(nn2) by {
            if let Some(((nn1, vv1), (nn2, vv2))) = parser_pair_some(callback(p).2, rem1, rem2) {
                if vv1 == vv2 {
                    self.non_malleable_by_induction((gas - 1) as nat, p, rem1, rem2, nn1, nn2, vv1, vv2);
                }
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).safe_inv() by {
            assert(callback(p).safe_inv());
        }
        assert forall|p: Body::Param| #[trigger] callback(p).sound_inv() by {
            assert(callback(p).sound_inv());
        }
        assert forall|p: Body::Param| #[trigger] callback(p).nonmal_inv() by {
            let p_fn = |ibuf: Seq<u8>| callback(p).2.spec_parse(ibuf);
            assert(p_fn == callback(p).2);
            assert(callback(p).nonmal_inv());
        }

        Body::lemma_body_safe_inv_preservation(param, callback);
        Body::lemma_body_nonmal_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        body.lemma_parse_non_malleable(buf1, buf2);

        assert(Self::spec_parse_gas(gas, param, buf1) == body.spec_parse(buf1));
        assert(Self::spec_parse_gas(gas, param, buf2) == body.spec_parse(buf2));
    }
}

impl<const LIMIT: usize, Body, Param> NonMalleable for super::FixWith<LIMIT, Body, Param> where
    Body: NonMalleableRecBody,
    Body::Body: NonMalleable + SafeParser + SoundParser,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    self.non_malleable_by_induction(
                        LIMIT as nat,
                        self.1.deep_view(),
                        buf1,
                        buf2,
                        n1,
                        n2,
                        v1,
                        v2,
                    );
                }
            }
        }
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: SPRoundTripDpsRecBody + NonTailFmtRecBody,
    Body::Body: SPRoundTripDps + NonTailFmt,
    Param: DeepView<V = Body::Param>,
 {
    proof fn sp_roundtrip_dps_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        v: Body::T,
        obuf: Seq<u8>,
    )
        requires
            Self::consistent_gas(gas, param, v),
        ensures
            Self::spec_parse_gas(gas, param, Self::spec_serialize_dps_gas(gas, param, v, obuf))
                == Some((Self::byte_len_gas(gas, param, v) as int, v)),
        decreases gas,
    {
        let callback = Self::specs_callback(gas);

        assert forall|p: Body::Param, vv: Body::T, buf: Seq<u8>|
            (callback(p).0(vv)) implies #[trigger] callback(p).2(callback(p).4(vv, buf)) == Some(
            (callback(p).1(vv) as int, vv),
        ) by {
            if callback(p).0(vv) {
                self.sp_roundtrip_dps_by_induction((gas - 1) as nat, p, vv, buf);
            }
        }

        assert forall|p: Body::Param, vv: Body::T, buf: Seq<u8>| #[trigger]
            callback(p).4(vv, buf).len() - buf.len() == callback(p).1(vv) by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, p, vv, buf);
            } else {
                assert(callback(p).4(vv, buf) == buf);
                assert(callback(p).1(vv) == 0);
            }
        }

        assert forall|p: Body::Param, vv: Body::T, buf: Seq<u8>|
            exists|new_buf: Seq<u8>| (#[trigger] callback(p).4(vv, buf)) == new_buf + buf by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, p, vv, buf);
                let witness = choose|w: Seq<u8>|
                    Self::spec_serialize_dps_gas((gas - 1) as nat, p, vv, buf) == w + buf;
                assert(callback(p).4(vv, buf) == witness + buf);
            } else {
                assert(callback(p).4(vv, buf) == Seq::<u8>::empty() + buf);
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).unambiguous() by {
            assert(callback(p).unambiguous());
        }
        assert forall|p: Body::Param| #[trigger] callback(p).serialize_dps_inv() by {
            assert(callback(p).serialize_dps_inv());
        }

        Body::lemma_body_sp_roundtrip_dps_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        assert(Self::consistent_gas(gas, param, v) == body.consistent(v));

        body.theorem_serialize_dps_parse_roundtrip(v, obuf);

        assert(Self::spec_parse_gas(gas, param, Self::spec_serialize_dps_gas(gas, param, v, obuf))
            == body.spec_parse(body.spec_serialize_dps(v, obuf)));
        assert(Self::byte_len_gas(gas, param, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body, Param> SPRoundTripDps for super::FixWith<LIMIT, Body, Param> where
    Body: SPRoundTripDpsRecBody + NonTailFmtRecBody,
    Body::Body: SPRoundTripDps + NonTailFmt,
    Param: DeepView<V = Body::Param>,
 {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.sp_roundtrip_dps_by_induction(LIMIT as nat, self.1.deep_view(), v, obuf);
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: EquivSerializersGeneralRecBody,
    Body::Body: EquivSerializersGeneral,
    Param: DeepView<V = Body::Param>,
 {
    proof fn equiv_serializers_general_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        v: Body::T,
        obuf: Seq<u8>,
    )
        ensures
            Self::spec_serialize_dps_gas(gas, param, v, obuf) == Self::spec_serialize_gas(
                gas,
                param,
                v,
            ) + obuf,
        decreases gas,
    {
        let callback = Self::specs_callback(gas);

        assert forall|p: Body::Param, vv: Body::T, buf: Seq<u8>| #[trigger]
            callback(p).4(vv, buf) == callback(p).3(vv) + buf by {
            if gas > 0 {
                self.equiv_serializers_general_by_induction((gas - 1) as nat, p, vv, buf);
            } else {
                assert(callback(p).4(vv, buf) == buf);
                assert(callback(p).3(vv) == Seq::<u8>::empty());
                assert(callback(p).4(vv, buf) == callback(p).3(vv) + buf);
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).equiv_general_inv() by {
            assert(callback(p).equiv_general_inv());
        }
        Body::lemma_s_body_equiv_general_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        body.lemma_serialize_equiv(v, obuf);

        assert(Self::spec_serialize_dps_gas(gas, param, v, obuf) == body.spec_serialize_dps(
            v,
            obuf,
        ));
        assert(Self::spec_serialize_gas(gas, param, v) == body.spec_serialize(v));
    }
}

impl<const LIMIT: usize, Body, Param> EquivSerializersGeneral for super::FixWith<
    LIMIT,
    Body,
    Param,
> where
    Body: EquivSerializersGeneralRecBody,
    Body::Body: EquivSerializersGeneral,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.equiv_serializers_general_by_induction(LIMIT as nat, self.1.deep_view(), v, obuf);
    }
}

impl<const LIMIT: usize, Body, Param> EquivSerializers for super::FixWith<LIMIT, Body, Param> where
    Body: EquivSerializersGeneralRecBody,
    Body::Body: EquivSerializersGeneral,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.lemma_serialize_equiv(v, Seq::empty());
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: NoLookAheadRecBody,
    Body::Body: NoLookAhead,
    Param: DeepView<V = Body::Param>,
 {
    proof fn no_lookahead_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        i1: Seq<u8>,
        i2: Seq<u8>,
        n: int,
        v: Body::T,
    )
        requires
            Self::spec_parse_gas(gas, param, i1) == Some((n, v)),
            0 <= n <= i2.len(),
            i2.take(n) == i1.take(n),
        ensures
            Self::spec_parse_gas(gas, param, i2) == Some((n, v)),
        decreases gas,
    {
        let callback = Self::specs_callback(gas);

        assert forall|p: Body::Param, rem: Seq<u8>| #[trigger]
            callback(p).2(rem) matches Some((nn, _vv)) ==> 0 <= nn <= rem.len() by {
            if let Some((nn, vv)) = callback(p).2(rem) {
                self.safe_parser_by_induction((gas - 1) as nat, p, rem, nn, vv);
            }
        }

        assert forall|p: Body::Param, j1: Seq<u8>, j2: Seq<u8>|
            (#[trigger] callback(p).2(j1) matches Some((nn, vv)) ==> 0 <= nn <= j2.len()
                ==> j2.take(nn) == j1.take(nn) ==> #[trigger] callback(p).2(j2) == Some(
                (nn, vv),
            )) by {
            if let Some((nn, vv)) = callback(p).2(j1) {
                if 0 <= nn && nn <= j2.len() && j2.take(nn) == j1.take(nn) {
                    self.no_lookahead_by_induction((gas - 1) as nat, p, j1, j2, nn, vv);
                }
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).safe_inv() by {
            assert(callback(p).safe_inv());
        }
        assert forall|p: Body::Param| #[trigger] callback(p).no_lookahead_inv() by {
            assert(callback(p).no_lookahead_inv());
        }

        Body::lemma_body_safe_inv_preservation(param, callback);
        Body::lemma_body_no_lookahead_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        assert(Self::spec_parse_gas(gas, param, i1) == body.spec_parse(i1));
        assert(Self::spec_parse_gas(gas, param, i2) == body.spec_parse(i2));

        body.lemma_no_lookahead(i1, i2);

        assert(body.spec_parse(i1) == Some((n, v)));
        assert(body.spec_parse(i2) == Some((n, v)));
    }
}

impl<const LIMIT: usize, Body, Param> NoLookAhead for super::FixWith<LIMIT, Body, Param> where
    Body: NoLookAheadRecBody,
    Body::Body: NoLookAhead,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.no_lookahead_by_induction(LIMIT as nat, self.1.deep_view(), i1, i2, n, v);
                }
            }
        }
    }
}

} // verus!
