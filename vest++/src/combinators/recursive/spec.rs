use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Bundled triple of parser, consistency, and byte-length spec functions.
pub type ParserSpecs<SpecP, Cnstcy, Blen> = (SpecP, Cnstcy, Blen);

pub type ParserFnSpecs<T> = (ParserFnSpec<T>, PredFnSpec<T>, ByteLenFnSpec<T>);

impl<SpecP, Cnstcy, Blen> SpecByteLen for ParserSpecs<SpecP, Cnstcy, Blen> where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    type T = Blen::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.2).byte_len(v)
    }
}

impl<SpecP, Cnstcy, Blen> Consistency for ParserSpecs<SpecP, Cnstcy, Blen> where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    type Val = Blen::T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.1).consistent(v)
    }
}

impl<SpecP, Cnstcy, Blen> SpecParser for ParserSpecs<SpecP, Cnstcy, Blen> where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    type PVal = Blen::T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0).spec_parse(ibuf)
    }
}

/// The functional version of [`SafeParser`].
pub open spec fn safe_parser<T>(parser: ParserFnSpec<T>) -> bool {
    forall|input: Seq<u8>| #[trigger] parser(input) matches Some((n, _)) ==> 0 <= n <= input.len()
}

/// A bundled non-DPS serializer: pairs a [`SerializerFnSpec`] with a [`ByteLenFnSpec`].
pub type SerializerSpecs<SpecS, Blen> = (SpecS, Blen);

pub type SerializerFnSpecs<T> = (SerializerFnSpec<T>, ByteLenFnSpec<T>);

impl<SpecS, Blen> SpecByteLen for SerializerSpecs<SpecS, Blen> where
    Blen: SpecByteLen,
    SpecS: SpecSerializer<SVal = Blen::T>,
 {
    type T = Blen::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1).byte_len(v)
    }
}

impl<SpecS, Blen> SpecSerializer for SerializerSpecs<SpecS, Blen> where
    Blen: SpecByteLen,
    SpecS: SpecSerializer<SVal = Blen::T>,
 {
    type SVal = Blen::T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.0).spec_serialize(v)
    }
}

/// Functional version of [`NonTailFmt`] for DPS serializer functions.
pub open spec fn non_tail_fmt_dps<T>(
    serializer_dps: SerializerDPSFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
) -> bool {
    &&& forall|v: T, obuf: Seq<u8>| #[trigger]
        serializer_dps(v, obuf).len() - obuf.len() == byte_len(
            v,
        )
    // FIXME: Using existentials here cause verus fail to verify
    &&& forall|v: T, obuf: Seq<u8>| #[trigger]
        serializer_dps(v, obuf) == (choose|w: Seq<u8>| serializer_dps(v, obuf) == w + obuf) + obuf
}

/// Functional version of [`GoodSerializer`] for serializer functions.
pub open spec fn good_serializer_fn<T>(
    serializer: SerializerFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
) -> bool {
    forall|v: T| #[trigger] serializer(v).len() == byte_len(v)
}

impl<SpecS, Blen> GoodSerializer for SerializerSpecs<SpecS, Blen> where
    Blen: SpecByteLen,
    SpecS: SpecSerializer<SVal = Blen::T>,
 {
    open spec fn serialize_inv(&self) -> bool {
        let (s, b) = *self;
        let (s_fn, b_fn) = (|v| s.spec_serialize(v), |v| b.byte_len(v));
        good_serializer_fn(s_fn, b_fn)
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let (s, b) = *self;
        let (s_fn, b_fn) = (|v| s.spec_serialize(v), |v| b.byte_len(v));
        assert(good_serializer_fn(s_fn, b_fn));
        assert(s_fn(v).len() == b_fn(v));
    }
}

impl<SpecP, Cnstcy, Blen> SafeParser for (SpecP, Cnstcy, Blen) where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    open spec fn safe_inv(&self) -> bool {
        let (p, _, _) = *self;
        let p_fn = |ibuf| p.spec_parse(ibuf);
        safe_parser(p_fn)
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let (p, _, _) = *self;
        let p_fn = |i: Seq<u8>| p.spec_parse(i);
        assert(self.safe_inv());
        if let Some((n, v)) = self.spec_parse(ibuf) {
            assert(safe_parser(p_fn));
            assert(p_fn(ibuf) == Some((n, v)));
            assert(0 <= n <= ibuf.len());
        }
    }
}

impl<SpecP, Cnstcy, Blen> SoundParser for (SpecP, Cnstcy, Blen) where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 {
    open spec fn sound_inv(&self) -> bool {
        let (p, c, b) = *self;
        let (p_fn, c_fn, b_fn) = (
            |ibuf| p.spec_parse(ibuf),
            |v| c.consistent(v),
            |v| b.byte_len(v),
        );
        sound_parser(p_fn, c_fn, b_fn)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let (p, c, b) = *self;
        let (p_fn, c_fn, b_fn) = (
            |i: Seq<u8>| p.spec_parse(i),
            |v: Blen::T| c.consistent(v),
            |v: Blen::T| b.byte_len(v),
        );
        assert(self.sound_inv());
        if let Some((n, v)) = self.spec_parse(ibuf) {
            assert(sound_parser(p_fn, c_fn, b_fn));
            assert(p_fn(ibuf) == Some((n, v)));
            assert(b_fn(v) == n);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let (p, c, b) = *self;
        let (p_fn, c_fn, b_fn) = (
            |i: Seq<u8>| p.spec_parse(i),
            |v: Blen::T| c.consistent(v),
            |v: Blen::T| b.byte_len(v),
        );
        assert(self.sound_inv());
        if let Some((n, v)) = self.spec_parse(ibuf) {
            assert(sound_parser(p_fn, c_fn, b_fn));
            assert(p_fn(ibuf) == Some((n, v)));
            assert(c_fn(v));
        }
    }
}

/// The functional version of [`SoundParser`].
pub open spec fn sound_parser<T>(
    parser: ParserFnSpec<T>,
    consistent: PredFnSpec<T>,
    byte_len: ByteLenFnSpec<T>,
) -> bool {
    forall|input: Seq<u8>| #[trigger]
        parser(input) matches Some((n, v)) ==> {
            &&& consistent(v)
            &&& byte_len(v) == n
        }
}

pub type BundledSpecs<T> = (
    PredFnSpec<T>,
    ByteLenFnSpec<T>,
    ParserFnSpec<T>,
    SerializerFnSpec<T>,
    SerializerDPSFnSpec<T>,
);

pub type ParamRecSpecs<P, T> = spec_fn(P) -> BundledSpecs<T>;

pub open spec fn parser_specs<T>(bundled: BundledSpecs<T>) -> ParserSpecs<
    ParserFnSpec<T>,
    PredFnSpec<T>,
    ByteLenFnSpec<T>,
> {
    (bundled.2, bundled.0, bundled.1)
}

pub open spec fn serializer_specs<T>(bundled: BundledSpecs<T>) -> SerializerSpecs<
    SerializerFnSpec<T>,
    ByteLenFnSpec<T>,
> {
    (bundled.3, bundled.1)
}

impl<T> Consistency for BundledSpecs<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.0)(v)
    }
}

impl<T> SpecByteLen for BundledSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecParser for BundledSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.2)(input)
    }
}

impl<T> SpecSerializer for BundledSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.3)(v)
    }
}

impl<T> SpecSerializerDps for BundledSpecs<T> {
    type SValue = T;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        (self.4)(v, obuf)
    }
}

impl<T> SafeParser for BundledSpecs<T> {
    open spec fn safe_inv(&self) -> bool {
        parser_specs(*self).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        parser_specs(*self).lemma_parse_safe(ibuf);
    }
}

impl<T> SoundParser for BundledSpecs<T> {
    open spec fn sound_inv(&self) -> bool {
        parser_specs(*self).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        parser_specs(*self).lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        parser_specs(*self).lemma_parse_sound_value(ibuf);
    }
}

impl<T> GoodSerializer for BundledSpecs<T> {
    open spec fn serialize_inv(&self) -> bool {
        serializer_specs(*self).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        serializer_specs(*self).lemma_serialize_len(v);
    }
}

impl<T> NonTailFmt for BundledSpecs<T> {
    open spec fn serialize_dps_inv(&self) -> bool {
        let (_, b, _, _, s_dps) = *self;
        non_tail_fmt_dps(s_dps, b)
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps) = *self;
        let witness = choose|w: Seq<u8>| (s_dps)(v, obuf) == w + obuf;
        assert((s_dps)(v, obuf) == witness + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps) = *self;
        assert((s_dps)(v, obuf).len() - obuf.len() == (b)(v));
    }
}

/// Defines one level of a recursive format for use with [`super::FixWith`].
pub trait SpecRecBody {
    type Param;

    type T;

    type Body: SpecCombinator<T = Self::T>;

    /// Define one recursive unfolding for `param`, where `rec` provides callbacks for all
    /// recursive positions in the body.
    spec fn spec_body(param: Self::Param, rec: ParamRecSpecs<Self::Param, Self::T>) -> Self::Body;
}

/// Safety preservation for recursive bodies.
pub trait SafeParserRecBody: SpecRecBody where Self::Body: SafeParser {
    proof fn lemma_body_safe_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).safe_inv(),
        ensures
            Self::spec_body(param, rec).safe_inv(),
    ;
}

/// Soundness preservation for recursive bodies.
pub trait SoundParserRecBody: SpecRecBody where Self::Body: SoundParser {
    proof fn lemma_body_sound_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).sound_inv(),
        ensures
            Self::spec_body(param, rec).sound_inv(),
    ;
}

/// Serializer's properties preservation for recursive bodies.
pub trait GoodSerializerRecBody: SpecRecBody where Self::Body: GoodSerializer {
    proof fn lemma_s_body_serialize_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).serialize_inv(),
        ensures
            Self::spec_body(param, rec).serialize_inv(),
    ;
}

/// DPS serializer's properties preservation for recursive bodies.
pub trait NonTailFmtRecBody: SpecRecBody where Self::Body: NonTailFmt {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(
        param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    )
        requires
            forall|p: Self::Param| #![trigger rec(p)] rec(p).serialize_dps_inv(),
        ensures
            Self::spec_body(param, rec).serialize_dps_inv(),
    ;
}

impl<const LIMIT: usize, Body, Param> SpecByteLen for super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    type T = Body::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Self::byte_len_gas(LIMIT as nat, self.1.deep_view(), v)
    }
}

impl<const LIMIT: usize, Body, Param> Consistency for super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    type Val = Body::T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Self::consistent_gas(LIMIT as nat, self.1.deep_view(), v)
    }
}

impl<const LIMIT: usize, Body, Param> SpecParser for super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    type PVal = Body::T;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        Self::spec_parse_gas(LIMIT as nat, self.1.deep_view(), input)
    }
}

impl<const LIMIT: usize, Body, Param> SpecSerializer for super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    type SVal = Body::T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Self::spec_serialize_gas(LIMIT as nat, self.1.deep_view(), v)
    }
}

impl<const LIMIT: usize, Body, Param> SpecSerializerDps for super::FixWith<
    LIMIT,
    Body,
    Param,
> where Body: SpecRecBody, Param: DeepView<V = Body::Param> {
    type SValue = Body::T;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        Self::spec_serialize_dps_gas(LIMIT as nat, self.1.deep_view(), v, obuf)
    }
}

impl<const LIMIT: usize, Body> ValueByteLen for super::FixWith<LIMIT, Body, ()> where
    Body: SpecRecBody<Param = ()>,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Self::byte_len_gas(LIMIT as nat, (), v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: SpecRecBody,
    Param: DeepView<V = Body::Param>,
 {
    pub open spec fn byte_len_gas(gas: nat, param: Body::Param, v: Body::T) -> nat
        decreases gas, 2nat,
    {
        Body::spec_body(param, Self::specs_callback(gas)).byte_len(v)
    }

    pub open spec fn consistent_gas(gas: nat, param: Body::Param, v: Body::T) -> bool
        decreases gas, 2nat,
    {
        Body::spec_body(param, Self::specs_callback(gas)).consistent(v)
    }

    pub open spec fn spec_parse_gas(gas: nat, param: Body::Param, input: Seq<u8>) -> Option<
        (int, Body::T),
    >
        decreases gas, 2nat,
    {
        Body::spec_body(param, Self::specs_callback(gas)).spec_parse(input)
    }

    pub open spec fn spec_serialize_gas(gas: nat, param: Body::Param, v: Body::T) -> Seq<u8>
        decreases gas, 2nat,
    {
        Body::spec_body(param, Self::specs_callback(gas)).spec_serialize(v)
    }

    pub open spec fn spec_serialize_dps_gas(
        gas: nat,
        param: Body::Param,
        v: Body::T,
        obuf: Seq<u8>,
    ) -> Seq<u8>
        decreases gas, 2nat,
    {
        Body::spec_body(param, Self::specs_callback(gas)).spec_serialize_dps(v, obuf)
    }

    pub open spec fn spec_parse_callback(gas: nat, param: Body::Param) -> ParserFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |ibuf: Seq<u8>|
            if gas > 0 {
                Self::spec_parse_gas((gas - 1) as nat, param, ibuf)
            } else {
                None
            }
    }

    pub open spec fn consistent_callback(gas: nat, param: Body::Param) -> PredFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                Self::consistent_gas((gas - 1) as nat, param, vv)
            } else {
                false
            }
    }

    pub open spec fn byte_len_callback(gas: nat, param: Body::Param) -> ByteLenFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                Self::byte_len_gas((gas - 1) as nat, param, vv)
            } else {
                0
            }
    }

    pub open spec fn spec_serialize_callback(gas: nat, param: Body::Param) -> SerializerFnSpec<
        Body::T,
    >
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                Self::spec_serialize_gas((gas - 1) as nat, param, vv)
            } else {
                Seq::empty()
            }
    }

    pub open spec fn spec_serialize_dps_callback(
        gas: nat,
        param: Body::Param,
    ) -> SerializerDPSFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T, obuf: Seq<u8>|
            if gas > 0 {
                Self::spec_serialize_dps_gas((gas - 1) as nat, param, vv, obuf)
            } else {
                obuf
            }
    }

    /// Bundled callbacks used when unfolding one recursive level.
    pub open spec fn specs_callback(gas: nat) -> ParamRecSpecs<Body::Param, Body::T>
        decreases gas, 1nat,
    {
        |param: Body::Param|
            (
                Self::consistent_callback(gas, param),
                Self::byte_len_callback(gas, param),
                Self::spec_parse_callback(gas, param),
                Self::spec_serialize_callback(gas, param),
                Self::spec_serialize_dps_callback(gas, param),
            )
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: SafeParserRecBody,
    Body::Body: SafeParser,
    Param: DeepView<V = Body::Param>,
 {
    /// Inductive proof that `spec_parse_gas` satisfies [`safe_parser`].
    pub(crate) proof fn safe_parser_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        input: Seq<u8>,
        n: int,
        v: Body::T,
    )
        ensures
            Self::spec_parse_gas(gas, param, input) == Some((n, v)) ==> 0 <= n <= input.len(),
        decreases gas,
    {
        if !(Self::spec_parse_gas(gas, param, input) == Some((n, v))) {
            return ;
        }
        let callback = Self::specs_callback(gas);
        let callback_p = callback(param).2;

        assert forall|p: Body::Param, rem: Seq<u8>| #[trigger]
            callback(p).2(rem) matches Some((nn, _vv)) ==> 0 <= nn <= rem.len() by {
            if let Some((nn, vv)) = callback(p).2(rem) {
                self.safe_parser_by_induction((gas - 1) as nat, p, rem, nn, vv);
                assert(Self::spec_parse_gas((gas - 1) as nat, p, rem) == Some((nn, vv)));
                assert(0 <= nn <= rem.len());
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).safe_inv() by {
            assert(safe_parser(callback(p).2));
        }

        Body::lemma_body_safe_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);
        body.lemma_parse_safe(input);

        assert(Self::spec_parse_gas(gas, param, input) == body.spec_parse(input));
    }
}

impl<const LIMIT: usize, Body, Param> SafeParser for super::FixWith<LIMIT, Body, Param> where
    Body: SafeParserRecBody,
    Body::Body: SafeParser,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.safe_parser_by_induction(LIMIT as nat, self.1.deep_view(), ibuf, n, v);
        }
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: SoundParserRecBody,
    Body::Body: SoundParser,
    Param: DeepView<V = Body::Param>,
 {
    /// Inductive proof that `spec_parse_gas` satisfies [`sound_parser`].
    pub(crate) proof fn sound_parser_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        input: Seq<u8>,
        n: int,
        v: Body::T,
    )
        ensures
            Self::spec_parse_gas(gas, param, input) == Some((n, v)) ==> {
                &&& Self::consistent_gas(gas, param, v)
                &&& Self::byte_len_gas(gas, param, v) == n
            },
        decreases gas,
    {
        if !(Self::spec_parse_gas(gas, param, input) == Some((n, v))) {
            return ;
        }
        let callback = Self::specs_callback(gas);
        let callback_p = callback(param).2;
        let callback_c = callback(param).0;
        let callback_b = callback(param).1;

        assert forall|p: Body::Param, rem: Seq<u8>| #[trigger]
            callback(p).2(rem) matches Some((nn, vv)) ==> {
                &&& callback(p).0(vv)
                &&& callback(p).1(vv) == nn
            } by {
            if let Some((nn, vv)) = callback(p).2(rem) {
                self.sound_parser_by_induction((gas - 1) as nat, p, rem, nn, vv);
                assert(Self::spec_parse_gas((gas - 1) as nat, p, rem) == Some((nn, vv)));
                assert(Self::consistent_gas((gas - 1) as nat, p, vv) == callback(p).0(vv));
                assert(Self::byte_len_gas((gas - 1) as nat, p, vv) == callback(p).1(vv));
                assert(callback(p).0(vv));
                assert(callback(p).1(vv) == nn);
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).sound_inv() by {
            assert(sound_parser(callback(p).2, callback(p).0, callback(p).1));
        }

        Body::lemma_body_sound_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        body.lemma_parse_sound_consumption(input);
        body.lemma_parse_sound_value(input);

        assert(Self::spec_parse_gas(gas, param, input) == body.spec_parse(input));
        assert(Self::consistent_gas(gas, param, v) == body.consistent(v));
        assert(Self::byte_len_gas(gas, param, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body, Param> SoundParser for super::FixWith<LIMIT, Body, Param> where
    Body: SoundParserRecBody,
    Body::Body: SoundParser,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, self.1.deep_view(), ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, self.1.deep_view(), ibuf, n, v);
        }
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: GoodSerializerRecBody,
    Body::Body: GoodSerializer,
    Param: DeepView<V = Body::Param>,
 {
    /// Inductive proof that `spec_serialize_gas` satisfies [`good_serializer_fn`].
    proof fn good_serializer_by_induction(&self, gas: nat, param: Body::Param, v: Body::T)
        ensures
            Self::spec_serialize_gas(gas, param, v).len() == Self::byte_len_gas(gas, param, v),
        decreases gas,
    {
        let callback = Self::specs_callback(gas);

        assert forall|p: Body::Param, vv: Body::T| #[trigger]
            callback(p).3(vv).len() == callback(p).1(vv) by {
            if gas > 0 {
                self.good_serializer_by_induction((gas - 1) as nat, p, vv);
            }
        }

        assert forall|p: Body::Param| #[trigger] callback(p).serialize_inv() by {
            assert(good_serializer_fn(callback(p).3, callback(p).1));
        }

        Body::lemma_s_body_serialize_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        body.lemma_serialize_len(v);

        assert(Self::spec_serialize_gas(gas, param, v) == body.spec_serialize(v));
        assert(Self::byte_len_gas(gas, param, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body, Param> GoodSerializer for super::FixWith<LIMIT, Body, Param> where
    Body: GoodSerializerRecBody,
    Body::Body: GoodSerializer,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.good_serializer_by_induction(LIMIT as nat, self.1.deep_view(), v);
    }
}

impl<const LIMIT: usize, Body, Param> super::FixWith<LIMIT, Body, Param> where
    Body: NonTailFmtRecBody,
    Body::Body: NonTailFmt,
    Param: DeepView<V = Body::Param>,
 {
    /// Inductive proof that `spec_serialize_gas` satisfies [`non_tail_fmt_dps`].
    pub(crate) proof fn nontail_dps_by_induction(
        &self,
        gas: nat,
        param: Body::Param,
        v: Body::T,
        obuf: Seq<u8>,
    )
        ensures
            exists|new_buf: Seq<u8>|
                (#[trigger] Self::spec_serialize_dps_gas(gas, param, v, obuf) == new_buf + obuf),
            Self::spec_serialize_dps_gas(gas, param, v, obuf).len() - obuf.len()
                == Self::byte_len_gas(gas, param, v),
        decreases gas, 1nat,
    {
        let callback = Self::specs_callback(gas);

        assert forall|p: Body::Param, vv: Body::T, buf: Seq<u8>| #[trigger]
            callback(p).4(vv, buf).len() - buf.len() == callback(p).1(vv) by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, p, vv, buf);
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

        assert forall|p: Body::Param| #[trigger] callback(p).serialize_dps_inv() by {
            assert(non_tail_fmt_dps(callback(p).4, callback(p).1));
        }
        Body::lemma_s_body_dps_serialize_dps_inv_preservation(param, callback);
        let body = Body::spec_body(param, callback);

        body.lemma_serialize_dps_prepend(v, obuf);
        body.lemma_serialize_dps_len(v, obuf);

        assert(Self::spec_serialize_dps_gas(gas, param, v, obuf) == body.spec_serialize_dps(
            v,
            obuf,
        ));
        assert(Self::byte_len_gas(gas, param, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body, Param> NonTailFmt for super::FixWith<LIMIT, Body, Param> where
    Body: NonTailFmtRecBody,
    Body::Body: NonTailFmt,
    Param: DeepView<V = Body::Param>,
 {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.nontail_dps_by_induction(LIMIT as nat, self.1.deep_view(), v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.nontail_dps_by_induction(LIMIT as nat, self.1.deep_view(), v, obuf);
    }
}

} // verus!
