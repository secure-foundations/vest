use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Bundled triple of parser, consistency, and byte-length spec functions.
// pub type ParserSpecs<T> = (ParserFnSpec<T>, PredFnSpec<T>, ByteLenFnSpec<T>);
pub type ParserSpecs<SpecP, Cnstcy, Blen> where
    Blen: SpecByteLen,
    SpecP: SpecParser<PVal = Blen::T>,
    Cnstcy: Consistency<Val = Blen::T>,
 = (SpecP, Cnstcy, Blen);

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

/// A bundled non-DPS serializer: pairs a [`SerializerFnSpec`] with a [`ByteLenFnSpec`].
pub type SerializerSpecs<SpecS, Blen> where
    Blen: SpecByteLen,
    SpecS: SpecSerializer<SVal = Blen::T>,
 = (SpecS, Blen);

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

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
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
            assert(0 <= n <= ibuf.len());
        }
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
            &&& 0 <= n <= input.len()
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
    UnambiguityFnSpec,
);

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
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.4)(v, obuf)
    }
}

impl<T> SoundParser for BundledSpecs<T> {
    open spec fn sound_inv(&self) -> bool {
        parser_specs(*self).sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        parser_specs(*self).lemma_parse_safe(ibuf);
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
        let (_, b, _, _, s_dps, _) = *self;
        non_tail_fmt_dps(s_dps, b)
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps, _) = *self;
        let witness = choose|w: Seq<u8>| (s_dps)(v, obuf) == w + obuf;
        assert((s_dps)(v, obuf) == witness + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps, _) = *self;
        assert((s_dps)(v, obuf).len() - obuf.len() == (b)(v));
    }
}

impl<T> Unambiguity for BundledSpecs<T> {
    open spec fn unambiguous(&self) -> bool {
        let (_, _, p, _, _, u) = *self;
        (u)()
    }
}

/// Defines one level of a recursive format for use with [`super::Fix`].
pub trait SpecRecBody {
    type T;

    type Body: SpecCombinator<T = Self::T>;

    /// Define one recursive unfolding, where `rec` provides callbacks for all recursive positions.
    /// the callback for recursive positions in the body.
    spec fn spec_body(&self, rec: BundledSpecs<Self::T>) -> Self::Body;
}

/// Soundness preservation for recursive bodies.
pub trait SoundParserRecBody: SpecRecBody where Self::Body: SoundParser {
    proof fn lemma_body_sound_inv_preservation(&self, rec: BundledSpecs<Self::T>)
        requires
            rec.sound_inv(),
        ensures
            self.spec_body(rec).sound_inv(),
    ;
}

/// Serializer's properties preservation for recursive bodies.
pub trait GoodSerializerRecBody: SpecRecBody where Self::Body: GoodSerializer {
    proof fn lemma_s_body_serialize_inv_preservation(&self, rec: BundledSpecs<Self::T>)
        requires
            rec.serialize_inv(),
        ensures
            self.spec_body(rec).serialize_inv(),
    ;
}

/// DPS serializer's properties preservation for recursive bodies.
pub trait NonTailFmtRecBody: SpecRecBody where Self::Body: NonTailFmt {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(&self, rec: BundledSpecs<Self::T>)
        requires
            rec.serialize_dps_inv(),
        ensures
            self.spec_body(rec).serialize_dps_inv(),
    ;
}

impl<const LIMIT: usize, Body: SpecRecBody> SpecByteLen for super::Fix<LIMIT, Body> {
    type T = Body::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.byte_len_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> Consistency for super::Fix<LIMIT, Body> {
    type Val = Body::T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.consistent_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> SpecParser for super::Fix<LIMIT, Body> {
    type PVal = Body::T;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.spec_parse_gas(LIMIT as nat, input)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> SpecSerializer for super::Fix<LIMIT, Body> {
    type SVal = Body::T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.spec_serialize_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> SpecSerializerDps for super::Fix<LIMIT, Body> {
    type ST = Body::T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.spec_serialize_dps_gas(LIMIT as nat, v, obuf)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> Unambiguity for super::Fix<LIMIT, Body> {
    open spec fn unambiguous(&self) -> bool {
        self.unambiguity_gas(LIMIT as nat)
    }
}

impl<const LIMIT: usize, Body: SpecRecBody> super::Fix<LIMIT, Body> {
    pub open spec fn byte_len_gas(&self, gas: nat, v: Body::T) -> nat
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).byte_len(v)
    }

    pub open spec fn consistent_gas(&self, gas: nat, v: Body::T) -> bool
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).consistent(v)
    }

    pub open spec fn spec_parse_gas(&self, gas: nat, input: Seq<u8>) -> Option<(int, Body::T)>
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).spec_parse(input)
    }

    pub open spec fn spec_serialize_gas(&self, gas: nat, v: Body::T) -> Seq<u8>
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).spec_serialize(v)
    }

    pub open spec fn spec_serialize_dps_gas(&self, gas: nat, v: Body::T, obuf: Seq<u8>) -> Seq<u8>
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).spec_serialize_dps(v, obuf)
    }

    pub open spec fn unambiguity_gas(&self, gas: nat) -> bool
        decreases gas, 2nat,
    {
        self.0.spec_body(self.specs_callback(gas)).unambiguous()
    }

    pub open spec fn spec_parse_callback(&self, gas: nat) -> ParserFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |ibuf: Seq<u8>|
            if gas > 0 {
                self.spec_parse_gas((gas - 1) as nat, ibuf)
            } else {
                None
            }
    }

    pub open spec fn consistent_callback(&self, gas: nat) -> PredFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                self.consistent_gas((gas - 1) as nat, vv)
            } else {
                false
            }
    }

    pub open spec fn byte_len_callback(&self, gas: nat) -> ByteLenFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                self.byte_len_gas((gas - 1) as nat, vv)
            } else {
                0
            }
    }

    pub open spec fn spec_serialize_callback(&self, gas: nat) -> SerializerFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            if gas > 0 {
                self.spec_serialize_gas((gas - 1) as nat, vv)
            } else {
                Seq::empty()
            }
    }

    pub open spec fn spec_serialize_dps_callback(&self, gas: nat) -> SerializerDPSFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T, obuf: Seq<u8>|
            if gas > 0 {
                self.spec_serialize_dps_gas((gas - 1) as nat, vv, obuf)
            } else {
                obuf
            }
    }

    pub open spec fn unambiguity_callback(&self, gas: nat) -> UnambiguityFnSpec
        decreases gas, 0nat,
    {
        ||
            if gas > 0 {
                self.unambiguity_gas((gas - 1) as nat)
            } else {
                true
            }
    }

    /// Bundled callbacks used when unfolding one recursive level.
    pub open spec fn specs_callback(&self, gas: nat) -> BundledSpecs<Body::T>
        decreases gas, 1nat,
    {
        (
            self.consistent_callback(gas),
            self.byte_len_callback(gas),
            self.spec_parse_callback(gas),
            self.spec_serialize_callback(gas),
            self.spec_serialize_dps_callback(gas),
            self.unambiguity_callback(gas),
        )
    }
}

impl<const LIMIT: usize, Body: SoundParserRecBody> super::Fix<LIMIT, Body> where
    Body::Body: SoundParser,
 {
    /// Inductive proof that `spec_parse_gas` satisfies [`sound_parser`].
    pub(crate) proof fn sound_parser_by_induction(
        &self,
        gas: nat,
        input: Seq<u8>,
        n: int,
        v: Body::T,
    )
        ensures
            self.spec_parse_gas(gas, input) == Some((n, v)) ==> {
                &&& 0 <= n <= input.len()
                &&& self.consistent_gas(gas, v)
                &&& self.byte_len_gas(gas, v) == n
            },
        decreases gas,
    {
        // vacuous case
        if !(self.spec_parse_gas(gas, input) == Some((n, v))) {
            return ;
        }
        let callback = self.specs_callback(gas);
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
                assert(0 <= nn <= rem.len());
                assert(self.spec_parse_gas((gas - 1) as nat, rem) == Some((nn, vv)));
                assert(self.consistent_gas((gas - 1) as nat, vv) == callback_c(vv));
                assert(self.byte_len_gas((gas - 1) as nat, vv) == callback_b(vv));
                assert(callback_c(vv));
                assert(callback_b(vv) == nn);
            }
        }

        assert(sound_parser(callback_p, callback_c, callback_b));

        self.0.lemma_body_sound_inv_preservation(callback);
        let body = self.0.spec_body(callback);

        body.lemma_parse_safe(input);
        body.lemma_parse_sound_consumption(input);
        body.lemma_parse_sound_value(input);

        // By definition
        assert(self.spec_parse_gas(gas, input) == body.spec_parse(input));
        assert(self.consistent_gas(gas, v) == body.consistent(v));
        assert(self.byte_len_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: SoundParserRecBody> SoundParser for super::Fix<LIMIT, Body> where
    Body::Body: SoundParser,
 {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            self.sound_parser_by_induction(LIMIT as nat, ibuf, n, v);
        }
    }
}

impl<const LIMIT: usize, Body: GoodSerializerRecBody> super::Fix<LIMIT, Body> where
    Body::Body: GoodSerializer,
 {
    /// Inductive proof that `spec_serialize_gas` satisfies [`good_serializer_fn`].
    proof fn good_serializer_by_induction(&self, gas: nat, v: Body::T)
        ensures
            self.spec_serialize_gas(gas, v).len() == self.byte_len_gas(gas, v),
        decreases gas,
    {
        let callback = self.specs_callback(gas);
        let callback_s = callback.3;
        let callback_b = callback.1;

        // establish good_serializer_fn(callback_s, callback_b)
        assert forall|vv: Body::T| #[trigger] callback_s(vv).len() == callback_b(vv) by {
            if gas > 0 {
                self.good_serializer_by_induction((gas - 1) as nat, vv);
            }
        }

        assert(good_serializer_fn(callback_s, callback_b));

        self.0.lemma_s_body_serialize_inv_preservation(callback);
        let body = self.0.spec_body(callback);

        body.lemma_serialize_len(v);

        // By definition
        assert(self.spec_serialize_gas(gas, v) == body.spec_serialize(v));
        assert(self.byte_len_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: GoodSerializerRecBody> GoodSerializer for super::Fix<
    LIMIT,
    Body,
> where Body::Body: GoodSerializer {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.good_serializer_by_induction(LIMIT as nat, v);
    }
}

impl<const LIMIT: usize, Body: NonTailFmtRecBody> super::Fix<LIMIT, Body> where
    Body::Body: NonTailFmt,
 {
    /// Inductive proof that `spec_serialize_gas` satisfies [`non_tail_fmt_dps`].
    pub(crate) proof fn nontail_dps_by_induction(&self, gas: nat, v: Body::T, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>|
                (#[trigger] self.spec_serialize_dps_gas(gas, v, obuf) == new_buf + obuf),
            self.spec_serialize_dps_gas(gas, v, obuf).len() - obuf.len() == self.byte_len_gas(
                gas,
                v,
            ),
        decreases gas, 1nat,
    {
        let callback = self.specs_callback(gas);
        let callback_s_dps = callback.4;
        let callback_b = callback.1;

        // establish non_tail_fmt_dps
        assert forall|v: Body::T, obuf: Seq<u8>| #[trigger]
            callback_s_dps(v, obuf).len() - obuf.len() == callback_b(v) by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, v, obuf);
            }
        }

        assert forall|vv: Body::T, buf: Seq<u8>|
            exists|new_buf: Seq<u8>| (#[trigger] callback_s_dps(vv, buf)) == new_buf + buf by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, vv, buf);
                let witness = choose|w: Seq<u8>|
                    self.spec_serialize_dps_gas((gas - 1) as nat, vv, buf) == w + buf;
                assert(callback_s_dps(vv, buf) == witness + buf);
            } else {
                assert(callback_s_dps(vv, buf) == Seq::<u8>::empty() + buf);
            }
        }

        assert(callback.serialize_dps_inv());
        self.0.lemma_s_body_dps_serialize_dps_inv_preservation(callback);
        let body = self.0.spec_body(callback);

        body.lemma_serialize_dps_prepend(v, obuf);
        body.lemma_serialize_dps_len(v, obuf);

        // By definition
        assert(self.spec_serialize_dps_gas(gas, v, obuf) == body.spec_serialize_dps(v, obuf));
        assert(self.byte_len_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: NonTailFmtRecBody> NonTailFmt for super::Fix<LIMIT, Body> where
    Body::Body: NonTailFmt,
 {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        self.nontail_dps_by_induction(LIMIT as nat, v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.nontail_dps_by_induction(LIMIT as nat, v, obuf);
    }
}

} // verus!
