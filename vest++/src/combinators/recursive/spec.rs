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
    &&& forall|v: T, obuf: Seq<u8>|
        exists|new_buf: Seq<u8>| (#[trigger] serializer_dps(v, obuf)) == new_buf + obuf
    &&& forall|v: T, obuf: Seq<u8>| #[trigger]
        serializer_dps(v, obuf).len() - obuf.len() == byte_len(v)
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

pub type BundledSpecs<T> = (
    PredFnSpec<T>,
    ByteLenFnSpec<T>,
    ParserFnSpec<T>,
    SerializerFnSpec<T>,
    SerializerDPSFnSpec<T>,
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

impl<T> NonMalleable for BundledSpecs<T> {
    open spec fn nonmal_inv(&self) -> bool {
        parser_specs(*self).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        parser_specs(*self).lemma_parse_non_malleable(buf1, buf2);
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

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps) = *self;
        let witness = choose|w: Seq<u8>| s_dps.spec_serialize_dps(v, obuf) == w + obuf;
        assert(self.spec_serialize_dps(v, obuf) == witness + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let (_, b, _, _, s_dps) = *self;
        assert(s_dps.spec_serialize_dps(v, obuf).len() - obuf.len() == b.byte_len(v));
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

/// Non-malleability preservation for recursive bodies.
pub trait NonMalleableRecBody: SoundParserRecBody where Self::Body: NonMalleable {
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: BundledSpecs<Self::T>)
        requires
            rec.sound_inv(),
            rec.nonmal_inv(),
        ensures
            self.spec_body(rec).nonmal_inv(),
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
        )
    }
}

impl<const LIMIT: usize, Body: SoundParserRecBody> super::Fix<LIMIT, Body> where
    Body::Body: SoundParser,
 {
    /// Inductive proof that `spec_parse_gas` satisfies [`sound_parser`].
    proof fn sound_parser_by_induction(&self, gas: nat, input: Seq<u8>, n: int, v: Body::T)
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
            self.spec_parse_gas(gas, buf1) == Some((n1, v1)) ==>
            self.spec_parse_gas(gas, buf2) == Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases gas,
    {
        if !(self.spec_parse_gas(gas, buf1) == Some((n1, v1))) {
            return ;
        }
        if !(self.spec_parse_gas(gas, buf2) == Some((n2, v2))) {
            return ;
        }
        if !(v1 == v2) {
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

        self.0.lemma_body_sound_inv_preservation(callback);
        self.0.lemma_body_nonmal_inv_preservation(callback);
        let body = self.0.spec_body(callback);

        body.lemma_parse_non_malleable(buf1, buf2);

        // By definition
        assert(self.spec_parse_gas(gas, buf1) == body.spec_parse(buf1));
        assert(self.spec_parse_gas(gas, buf2) == body.spec_parse(buf2));
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
    proof fn nontail_dps_by_induction(&self, gas: nat, v: Body::T, obuf: Seq<u8>)
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
            exists|new_buf: Seq<u8>| (#[trigger] callback_s_dps(vv, buf) == new_buf + buf) by {
            if gas > 0 {
                self.nontail_dps_by_induction((gas - 1) as nat, vv, buf);
                let witness = choose|w: Seq<u8>|
                    self.spec_serialize_dps_gas((gas - 1) as nat, vv, buf) == w + buf;
                assert(callback_s_dps(vv, buf) == witness + buf);
                assert(exists|new_buf: Seq<u8>| callback_s_dps(vv, buf) == new_buf + buf);
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

/*
 * Example recursive parser: nested braces
 */

use crate::combinators::*;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};

/// Example recursive value type: nested braces `{...}` or empty `\0`.
pub enum NestedBracesT {
    /// A brace-wrapped recursive value: `'{' inner '}'`.
    Brace(Box<NestedBracesT>),
    /// The empty (base case) value: `'\0'`.
    Eps,
}

/// Mapper between `Sum<NestedBracesT, ()>` and `NestedBracesT`.
pub struct NestedBracesMapper;

impl Mapper for NestedBracesMapper {
    type In = Sum<NestedBracesT, ()>;

    type Out = NestedBracesT;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(inner) => NestedBracesT::Brace(Box::new(inner)),
            Sum::Inr(()) => NestedBracesT::Eps,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            NestedBracesT::Brace(inner) => Sum::Inl(*inner),
            NestedBracesT::Eps => Sum::Inr(()),
        }
    }
}

impl IsoMapper for NestedBracesMapper {
    proof fn lemma_map_iso(&self, i: Self::In) {
        match i {
            Sum::Inl(_) => {},
            Sum::Inr(u) => {
                assert(u == ());
            },
        }
    }

    proof fn lemma_map_iso_rev(&self, o: Self::Out) {
        match o {
            NestedBracesT::Brace(_) => {},
            NestedBracesT::Eps => {},
        }
    }
}

/// One level of the nested-braces format: `'{' rec '}' | '\0'`.
pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec> {
    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U8, tag: 0x7Bu8 }, rec),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }
}

type NestedBracesBodyComb<Rec> = Mapped<
    Choice<Terminated<Preceded<Tag<U8, u8>, Rec>, Tag<U8, u8>>, Tag<U8, u8>>,
    NestedBracesMapper,
>;

/// [`SpecRecBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl SpecRecBody for NestedBracesBody {
    type T = NestedBracesT;

    type Body = NestedBracesBodyComb<BundledSpecs<Self::T>>;

    open spec fn spec_body(&self, rec: BundledSpecs<Self::T>) -> Self::Body {
        nested_braces_body(rec)
    }
}

impl SoundParserRecBody for NestedBracesBody {
    proof fn lemma_body_sound_inv_preservation(&self, rec: BundledSpecs<Self::T>) {
    }
}

impl NonMalleableRecBody for NestedBracesBody {
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: BundledSpecs<Self::T>) {
    }
}

impl GoodSerializerRecBody for NestedBracesBody {
    proof fn lemma_s_body_serialize_inv_preservation(&self, rec: BundledSpecs<Self::T>) {
    }
}

impl NonTailFmtRecBody for NestedBracesBody {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(&self, rec: BundledSpecs<Self::T>) {
        assert(self.spec_body(rec).serialize_dps_inv());
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = super::Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
    )) by {
        let cb = nested_braces.specs_callback(10);
        let body10 = nested_braces_body(cb);
        assert(body10.spec_parse(input) == Some(
            (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
        ));
    };

    let input2 = seq![0x7Bu8, 0x00u8, 0x7Du8, 0x7Bu8, 0x00u8, 0x7Du8];

    nested_braces.lemma_parse_sound_consumption(input);
    nested_braces.lemma_parse_sound_value(input);
    nested_braces.lemma_parse_safe(input);
    nested_braces.lemma_parse_non_malleable(input, input2);
    let (n, v) = nested_braces.spec_parse(input)->0;
    nested_braces.lemma_serialize_len(v);
}

} // verus!
