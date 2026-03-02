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

/// A bundled DPS serializer: pairs a [`SerializerDPSFnSpec`] with a [`ByteLenFnSpec`].
pub struct SerializerDPSSpecs<SpecSDPS, Blen>(pub SpecSDPS, pub Blen) where
    Blen: SpecByteLen,
    SpecSDPS: SpecSerializerDps<ST = Blen::T>,
;

pub type SerializerDPSFnSpecs<T> = (SerializerDPSFnSpec<T>, ByteLenFnSpec<T>);

impl<SpecSDPS, Blen> SpecByteLen for SerializerDPSSpecs<SpecSDPS, Blen> where
    Blen: SpecByteLen,
    SpecSDPS: SpecSerializerDps<ST = Blen::T>,
 {
    type T = Blen::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1).byte_len(v)
    }
}

impl<SpecSDPS, Blen> SpecSerializerDps for SerializerDPSSpecs<SpecSDPS, Blen> where
    Blen: SpecByteLen,
    SpecSDPS: SpecSerializerDps<ST = Blen::T>,
 {
    type ST = Blen::T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.0).spec_serialize_dps(v, obuf)
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
        exists|new_buf: Seq<u8>| (#[trigger] serializer_dps(v, obuf)) =~= new_buf.add(obuf)
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

impl<SpecSDPS, Blen> NonTailFmt for SerializerDPSSpecs<SpecSDPS, Blen> where
    Blen: SpecByteLen,
    SpecSDPS: SpecSerializerDps<ST = Blen::T>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        let SerializerDPSSpecs(s_dps, b) = *self;
        &&& forall|v: SpecSDPS::ST, obuf: Seq<u8>|
            exists|new_buf: Seq<u8>| #[trigger] s_dps.spec_serialize_dps(v, obuf) == new_buf + obuf
        &&& forall|v: SpecSDPS::ST, obuf: Seq<u8>| #[trigger]
            s_dps.spec_serialize_dps(v, obuf).len() - obuf.len() == b.byte_len(v)
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(self.serialize_dps_inv());
        let SerializerDPSSpecs(s_dps, b) = *self;
        let witness = choose|w: Seq<u8>| s_dps.spec_serialize_dps(v, obuf) == w + obuf;
        assert(self.spec_serialize_dps(v, obuf) == witness + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(self.serialize_dps_inv());
        let SerializerDPSSpecs(s_dps, b) = *self;
        assert(s_dps.spec_serialize_dps(v, obuf).len() - obuf.len() == b.byte_len(v));
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

/// The functional version of [`GoodParser`].
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

// pub type BundledSpecs<T> = (
//     PredFnSpec<T>,
//     ByteLenFnSpec<T>,
//     ParserFnSpec<T>,
//     SerializerFnSpec<T>,
//     SerializerDPSFnSpec<T>,
// );
// pub open spec fn parser_specs<T>(bundled: BundledSpecs<T>) -> ParserSpecs<T> {
//     (bundled.2, bundled.0, bundled.1)
// }
// pub open spec fn serializer_specs<T>(bundled: BundledSpecs<T>) -> SerializerSpecs<T> {
//     (bundled.3, bundled.1)
// }
// pub open spec fn serializer_dps_specs<T>(bundled: BundledSpecs<T>) -> SerializerDPSSpecs<T> {
//     (bundled.4, bundled.1)
// }
// impl<T> Consistency for BundledSpecs<T> {
//     type Val = T;
//     open spec fn consistent(&self, v: Self::Val) -> bool {
//         (self.0)(v)
//     }
// }
// impl<T> SpecByteLen for BundledSpecs<T> {
//     type T = T;
//     open spec fn byte_len(&self, v: Self::T) -> nat {
//         (self.1)(v)
//     }
// }
// impl<T> SpecParser for BundledSpecs<T> {
//     type PVal = T;
//     open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
//         (self.2)(input)
//     }
// }
// impl<T> SpecSerializer for BundledSpecs<T> {
//     type SVal = T;
//     open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
//         (self.3)(v)
//     }
// }
// impl<T> SpecSerializerDps for BundledSpecs<T> {
//     type ST = T;
//     open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
//         (self.4)(v, obuf)
//     }
// }
// impl<T> SoundParser for BundledSpecs<T> {
//     open spec fn sound_inv(&self) -> bool {
//         let parser_specs = parser_specs(*self);
//         parser_specs.sound_inv()
//     }
//     proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
//         let parser_specs = parser_specs(*self);
//         parser_specs.lemma_parse_safe(ibuf);
//     }
//     proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
//         let parser_specs = parser_specs(*self);
//         parser_specs.lemma_parse_sound_consumption(ibuf);
//     }
//     proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
//         let parser_specs = parser_specs(*self);
//         parser_specs.lemma_parse_sound_value(ibuf);
//     }
// }
// impl<T> NonMalleable for BundledSpecs<T> {
//     open spec fn nonmal_inv(&self) -> bool {
//         let parser_specs = parser_specs(*self);
//         parser_specs.nonmal_inv()
//     }
//     proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
//         let parser_specs = parser_specs(*self);
//         parser_specs.lemma_parse_non_malleable(buf1, buf2);
//     }
// }
// impl<T> GoodSerializer for BundledSpecs<T> {
//     open spec fn serialize_inv(&self) -> bool {
//         let serializer_specs = serializer_specs(*self);
//         serializer_specs.serialize_inv()
//     }
//     proof fn lemma_serialize_len(&self, v: Self::SVal) {
//         let serializer_specs = serializer_specs(*self);
//         serializer_specs.lemma_serialize_len(v);
//     }
// }
// impl<T> NonTailFmt for BundledSpecs<T> {
//     open spec fn serialize_dps_inv(&self) -> bool {
//         let serializer_dps_specs = serializer_dps_specs(*self);
//         serializer_dps_specs.serialize_dps_inv()
//     }
//     proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
//         let serializer_dps_specs = serializer_dps_specs(*self);
//         serializer_dps_specs.lemma_serialize_dps_prepend(v, obuf);
//     }
//     proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
//         let serializer_dps_specs = serializer_dps_specs(*self);
//         serializer_dps_specs.lemma_serialize_dps_len(v, obuf);
//     }
// }
/// Defines one level of a recursive byte-length computation for use with [`super::Fix`].
pub trait RecBLenBody {
    type T;

    type BLenBody: SpecByteLen<T = Self::T>;

    /// Define the byte-length body for one level of the recursive format, where `rec` represents
    /// the callback for recursive positions in the body.
    spec fn blen_body(&self, rec: ByteLenFnSpec<Self::T>) -> Self::BLenBody;
}

/// Defines one level of a recursive consistency predicate for use with [`super::Fix`].
pub trait RecCnstcyBody {
    type Val;

    type CnstcyBody: Consistency<Val = Self::Val>;

    /// Define the consistency body for one level of the recursive format, where `rec` represents
    /// the callback for recursive positions in the body.
    spec fn cnstcy_body(&self, rec: PredFnSpec<Self::Val>) -> Self::CnstcyBody;
}

/// Defines one level of a recursive parser for use with [`super::Fix`].
pub trait RecPBody {
    /// The type of values parsed by this recursive format.
    type PVal;

    type PBody: SpecParser<PVal = Self::PVal>;

    /// Define the parser body for one level of the recursive format, where `rec` represents
    /// the callback for recursive positions in the body.
    spec fn p_body(&self, rec: ParserFnSpec<Self::PVal>) -> Self::PBody;
}

/// Defines one level of a recursive serializer for use with [`super::Fix`].
pub trait RecSBody {
    /// The type of values serialized by this recursive format.
    type SVal;

    type SBody: SpecSerializer<SVal = Self::SVal>;

    /// Define the serializer body for one level of the recursive format, where `rec` represents
    /// the callback for recursive positions in the body.
    spec fn s_body(&self, rec: SerializerFnSpec<Self::SVal>) -> Self::SBody;
}

/// Defines one level of a recursive DPS serializer for use with [`super::Fix`].
pub trait RecSBodyDPS {
    /// The type of values serialized by this recursive format.
    type ST;

    type SBodyDPS: SpecSerializerDps<ST = Self::ST>;

    /// Define the DPS serializer body for one level of the recursive format, where `rec` represents
    /// the callback for recursive positions in the body.
    spec fn s_body_dps(&self, rec: SerializerDPSFnSpec<Self::ST>) -> Self::SBodyDPS;
}

/// Soundness for [`RecPBody`] w.r.t. [`RecCnstcyBody`] and [`RecBLenBody`].
pub trait SoundRecPBody: RecPBody + RecCnstcyBody<Val = Self::PVal> + RecBLenBody<T = Self::PVal> {
    /// Induction: if the callbacks `rec` satisfies `sound_inv`, then unfolding the body also satisfies `sound_inv`.
    proof fn lemma_body_sound_inv_preservation(&self, rec: ParserFnSpecs<Self::PVal>)
        requires
            rec.sound_inv(),
        ensures
            ({
                let (p_cb, c_cb, b_cb) = rec;
                let rec_unfold = (self.p_body(p_cb), self.cnstcy_body(c_cb), self.blen_body(b_cb));
                rec_unfold.sound_inv()
            }),
    ;
}

/// Non-malleability for [`SoundRecPBody`].
pub trait NonMalleableRecPBody: SoundRecPBody {
    /// Induction: if the callbacks `rec` satisfies `sound_inv` and `nonmal_inv`,
    /// then unfolding the body also satisfies `nonmal_inv`.
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: ParserFnSpecs<Self::PVal>)
        requires
            rec.sound_inv(),
            rec.nonmal_inv(),
        ensures
            ({
                let (p_cb, c_cb, b_cb) = rec;
                let rec_unfold = (self.p_body(p_cb), self.cnstcy_body(c_cb), self.blen_body(b_cb));
                rec_unfold.nonmal_inv()
            }),
    ;
}

/// Goodness for [`RecSBody`] w.r.t. [`RecBLenBody`].
pub trait GoodRecSBody: RecSBody + RecBLenBody<T = Self::SVal> {
    /// Induction: if the callbacks `rec` satisfies `serialize_inv`, then unfolding the body also satisfies `serialize_inv`.
    proof fn lemma_s_body_serialize_inv_preservation(&self, rec: SerializerFnSpecs<Self::SVal>)
        requires
            rec.serialize_inv(),
        ensures
            ({
                let (s_cb, b_cb) = rec;
                let rec_unfold = (self.s_body(s_cb), self.blen_body(b_cb));
                rec_unfold.serialize_inv()
            }),
    ;
}

/// Non-tail format for [`RecSBodyDPS`] w.r.t. [`RecBLenBody`].
pub trait NonTailRecSBodyDPS: RecSBodyDPS + RecBLenBody<T = Self::ST> {
    /// Induction: if the callbacks `rec` satisfies `serialize_dps_inv`, then unfolding the body also satisfies `serialize_dps_inv`.
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(
        &self,
        rec: SerializerDPSFnSpecs<Self::ST>,
    )
        ensures
            ({
                let (s_dps_cb, b_cb) = rec;
                let rec_unfold = SerializerDPSSpecs(
                    self.s_body_dps(s_dps_cb),
                    self.blen_body(b_cb),
                );
                rec_unfold.serialize_dps_inv()
            }),
    ;
}

impl<const LIMIT: usize, Body: RecBLenBody> SpecByteLen for super::Fix<LIMIT, Body> {
    type T = Body::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.byte_len_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecCnstcyBody> Consistency for super::Fix<LIMIT, Body> {
    type Val = Body::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.consistent_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecPBody> SpecParser for super::Fix<LIMIT, Body> {
    type PVal = Body::PVal;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.spec_parse_with_gas(LIMIT as nat, input)
    }
}

impl<const LIMIT: usize, Body: RecSBody> SpecSerializer for super::Fix<LIMIT, Body> {
    type SVal = Body::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.spec_serialize_with_gas(LIMIT as nat, v)
    }
}

impl<const LIMIT: usize, Body: RecSBodyDPS> SpecSerializerDps for super::Fix<LIMIT, Body> {
    type ST = Body::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.spec_serialize_dps_with_gas(LIMIT as nat, v, obuf)
    }
}

impl<const LIMIT: usize, Body: RecBLenBody> super::Fix<LIMIT, Body> {
    /// Byte length with a given amount of gas. Unfolds one level via `body` with a callback that recurses at `gas - 1`.
    pub open spec fn byte_len_with_gas(&self, gas: nat, v: Body::T) -> nat
        decreases gas, 1nat,
    {
        self.0.blen_body(self.byte_len_callback(gas)).byte_len(v)
    }

    /// Recursive callback for byte-length computation, which wraps the recursive call to `byte_len_with_gas` with `gas - 1`.
    pub open spec fn byte_len_callback(&self, gas: nat) -> ByteLenFnSpec<Body::T>
        decreases gas, 0nat,
    {
        |vv: Body::T|
            {
                if gas > 0 {
                    self.byte_len_with_gas((gas - 1) as nat, vv)
                } else {
                    0
                }
            }
    }
}

impl<const LIMIT: usize, Body: RecCnstcyBody> super::Fix<LIMIT, Body> {
    /// Consistency check with a given amount of gas. Unfolds one level via `body` with a callback that recurses at `gas - 1`.
    pub open spec fn consistent_with_gas(&self, gas: nat, v: Body::Val) -> bool
        decreases gas, 1nat,
    {
        self.0.cnstcy_body(self.consistent_callback(gas)).consistent(v)
    }

    /// Recursive callback for consistency checking, which wraps the recursive call to `consistent_with_gas` with `gas - 1`.
    pub open spec fn consistent_callback(&self, gas: nat) -> PredFnSpec<Body::Val>
        decreases gas, 0nat,
    {
        |vv: Body::Val|
            {
                if gas > 0 {
                    self.consistent_with_gas((gas - 1) as nat, vv)
                } else {
                    false
                }
            }
    }
}

impl<const LIMIT: usize, Body: RecPBody> super::Fix<LIMIT, Body> {
    /// Parse with a given amount of gas. Unfolds one level via `body` with a callback that recurses at `gas - 1`.
    pub open spec fn spec_parse_with_gas(&self, gas: nat, input: Seq<u8>) -> Option<
        (int, Body::PVal),
    >
        decreases gas, 1nat,
    {
        self.0.p_body(self.spec_parse_callback(gas)).spec_parse(input)
    }

    /// Recursive callback for parsing, which wraps the recursive call to `spec_parse_with_gas` with `gas - 1`.
    pub open spec fn spec_parse_callback(&self, gas: nat) -> ParserFnSpec<Body::PVal>
        decreases gas, 0nat,
    {
        |ibuf: Seq<u8>|
            {
                if gas > 0 {
                    self.spec_parse_with_gas((gas - 1) as nat, ibuf)
                } else {
                    None
                }
            }
    }
}

impl<const LIMIT: usize, Body: RecSBody> super::Fix<LIMIT, Body> {
    /// Serializer with a given amount of gas. Unfolds one level via `body` with a callback that recurses at `gas - 1`.
    pub open spec fn spec_serialize_with_gas(&self, gas: nat, v: Body::SVal) -> Seq<u8>
        decreases gas, 1nat,
    {
        self.0.s_body(self.spec_serialize_callback(gas)).spec_serialize(v)
    }

    /// Recursive callback for serialization, which wraps the recursive call to `spec_serialize_with_gas` with `gas - 1`.
    pub open spec fn spec_serialize_callback(&self, gas: nat) -> SerializerFnSpec<Body::SVal>
        decreases gas, 0nat,
    {
        |vv: Body::SVal|
            {
                if gas > 0 {
                    self.spec_serialize_with_gas((gas - 1) as nat, vv)
                } else {
                    Seq::empty()
                }
            }
    }
}

impl<const LIMIT: usize, Body: RecSBodyDPS> super::Fix<LIMIT, Body> {
    /// DPS serializer with a given amount of gas. Unfolds one level via `body` with a callback that recurses at `gas - 1`.
    pub open spec fn spec_serialize_dps_with_gas(
        &self,
        gas: nat,
        v: Body::ST,
        obuf: Seq<u8>,
    ) -> Seq<u8>
        decreases gas, 1nat,
    {
        self.0.s_body_dps(self.spec_serialize_dps_callback(gas)).spec_serialize_dps(v, obuf)
    }

    /// Recursive callback for DPS serialization, which wraps the recursive call to `spec_serialize_dps_with_gas` with `gas - 1`.
    pub open spec fn spec_serialize_dps_callback(&self, gas: nat) -> SerializerDPSFnSpec<Body::ST>
        decreases gas, 0nat,
    {
        |vv: Body::ST, obuf: Seq<u8>|
            {
                if gas > 0 {
                    self.spec_serialize_dps_with_gas((gas - 1) as nat, vv, obuf)
                } else {
                    obuf
                }
            }
    }
}

impl<const LIMIT: usize, Body: SoundRecPBody> super::Fix<LIMIT, Body> {
    /// Inductive proof that `spec_parse_with_gas` satisfies [`sound_parser`].
    proof fn sound_parser_by_induction(&self, gas: nat, input: Seq<u8>, n: int, v: Body::PVal)
        ensures
            self.spec_parse_with_gas(gas, input) == Some((n, v)) ==> {
                &&& 0 <= n <= input.len()
                &&& self.consistent_with_gas(gas, v)
                &&& self.byte_len_with_gas(gas, v) == n
            },
        decreases gas,
    {
        // vacuous case
        if !(self.spec_parse_with_gas(gas, input) == Some((n, v))) {
            return ;
        }
        let callback_p = self.spec_parse_callback(gas);
        let callback_c = self.consistent_callback(gas);
        let callback_b = self.byte_len_callback(gas);

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
                assert(self.spec_parse_with_gas((gas - 1) as nat, rem) == Some((nn, vv)));
                assert(self.consistent_with_gas((gas - 1) as nat, vv) == callback_c(vv));
                assert(self.byte_len_with_gas((gas - 1) as nat, vv) == callback_b(vv));
                assert(callback_c(vv));
                assert(callback_b(vv) == nn);
            }
        }

        let bundled_callback = (callback_p, callback_c, callback_b);
        assert(sound_parser(callback_p, callback_c, callback_b));

        self.0.lemma_body_sound_inv_preservation(bundled_callback);
        let body = (
            self.0.p_body(callback_p),
            self.0.cnstcy_body(callback_c),
            self.0.blen_body(callback_b),
        );
        assert(body.sound_inv());

        body.lemma_parse_safe(input);
        body.lemma_parse_sound_consumption(input);
        body.lemma_parse_sound_value(input);

        // By definition
        assert(self.spec_parse_with_gas(gas, input) == body.spec_parse(input));
        assert(self.consistent_with_gas(gas, v) == body.consistent(v));
        assert(self.byte_len_with_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: SoundRecPBody> SoundParser for super::Fix<LIMIT, Body> {
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

impl<const LIMIT: usize, Body: NonMalleableRecPBody> super::Fix<LIMIT, Body> {
    /// Inductive proof that `spec_parse_with_gas` is non-malleable.
    #[verusfmt::skip]
    proof fn non_malleable_by_induction(
        &self,
        gas: nat,
        buf1: Seq<u8>,
        buf2: Seq<u8>,
        n1: int,
        n2: int,
        v1: Body::PVal,
        v2: Body::PVal,
    )
        ensures
            self.spec_parse_with_gas(gas, buf1) == Some((n1, v1)) ==>
            self.spec_parse_with_gas(gas, buf2) == Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
        decreases gas,
    {
        if !(self.spec_parse_with_gas(gas, buf1) == Some((n1, v1))) {
            return ;
        }
        if !(self.spec_parse_with_gas(gas, buf2) == Some((n2, v2))) {
            return ;
        }
        if !(v1 == v2) {
            return ;
        }

        let callback_p = self.spec_parse_callback(gas);
        let callback_c = self.consistent_callback(gas);
        let callback_b = self.byte_len_callback(gas);

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

        let bundled_callback = (callback_p, callback_c, callback_b);
        assert(sound_parser(callback_p, callback_c, callback_b));
        assert(bundled_callback.nonmal_inv()) by {
            let p_fn = |ibuf: Seq<u8>| bundled_callback.0.spec_parse(ibuf);
            assert(p_fn == callback_p);
        }

        self.0.lemma_body_sound_inv_preservation(bundled_callback);
        self.0.lemma_body_nonmal_inv_preservation(bundled_callback);
        let body = (
            self.0.p_body(callback_p),
            self.0.cnstcy_body(callback_c),
            self.0.blen_body(callback_b),
        );
        assert(body.sound_inv());
        assert(body.nonmal_inv());

        body.lemma_parse_non_malleable(buf1, buf2);

        // By definition
        assert(self.spec_parse_with_gas(gas, buf1) == body.spec_parse(buf1));
        assert(self.spec_parse_with_gas(gas, buf2) == body.spec_parse(buf2));
    }
}

impl<const LIMIT: usize, Body: NonMalleableRecPBody> NonMalleable for super::Fix<LIMIT, Body> {
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

impl<const LIMIT: usize, Body: GoodRecSBody> super::Fix<LIMIT, Body> {
    /// Inductive proof that `spec_serialize_with_gas` satisfies [`good_serializer_fn`].
    proof fn good_serializer_by_induction(&self, gas: nat, v: Body::SVal)
        ensures
            self.spec_serialize_with_gas(gas, v).len() == self.byte_len_with_gas(gas, v),
        decreases gas,
    {
        let callback_s = self.spec_serialize_callback(gas);
        let callback_b = self.byte_len_callback(gas);

        // establish good_serializer_fn(callback_s, callback_b)
        assert forall|vv: Body::SVal| #[trigger] callback_s(vv).len() == callback_b(vv) by {
            if gas > 0 {
                self.good_serializer_by_induction((gas - 1) as nat, vv);
            }
        }

        let bundled_callback = (callback_s, callback_b);
        assert(good_serializer_fn(callback_s, callback_b));

        self.0.lemma_s_body_serialize_inv_preservation(bundled_callback);
        let body = (self.0.s_body(callback_s), self.0.blen_body(callback_b));

        body.lemma_serialize_len(v);

        // By definition
        assert(self.spec_serialize_with_gas(gas, v) == body.spec_serialize(v));
        assert(self.byte_len_with_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: GoodRecSBody> GoodSerializer for super::Fix<LIMIT, Body> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.good_serializer_by_induction(LIMIT as nat, v);
    }
}

impl<const LIMIT: usize, Body: NonTailRecSBodyDPS> super::Fix<LIMIT, Body> {
    /// Inductive proof that `spec_serialize_with_gas` satisfies [`non_tail_fmt_dps`].
    proof fn nontail_dps_by_induction(&self, gas: nat, v: Body::ST, obuf: Seq<u8>)
        ensures
            exists|new_buf: Seq<u8>|
                self.spec_serialize_dps_with_gas(gas, v, obuf) == new_buf + obuf,
            self.spec_serialize_dps_with_gas(gas, v, obuf).len() - obuf.len()
                == self.byte_len_with_gas(gas, v),
        decreases gas, 1nat,
    {
        let callback_s = self.spec_serialize_dps_callback(gas);
        let callback_b = self.byte_len_callback(gas);
        let bundled_callback = (callback_s, callback_b);

        self.0.lemma_s_body_dps_serialize_dps_inv_preservation(bundled_callback);
        let body = SerializerDPSSpecs(self.0.s_body_dps(callback_s), self.0.blen_body(callback_b));

        body.lemma_serialize_dps_prepend(v, obuf);
        body.lemma_serialize_dps_len(v, obuf);

        // By definition
        assert(self.spec_serialize_dps_with_gas(gas, v, obuf) == body.spec_serialize_dps(v, obuf));
        assert(self.byte_len_with_gas(gas, v) == body.byte_len(v));
    }
}

impl<const LIMIT: usize, Body: NonTailRecSBodyDPS> NonTailFmt for super::Fix<LIMIT, Body> {
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

/// [`RecPBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl RecPBody for NestedBracesBody {
    type PVal = NestedBracesT;

    type PBody = NestedBracesBodyComb<ParserFnSpec<Self::PVal>>;

    open spec fn p_body(&self, rec: ParserFnSpec<Self::PVal>) -> Self::PBody {
        nested_braces_body(rec)
    }
}

impl RecCnstcyBody for NestedBracesBody {
    type Val = NestedBracesT;

    type CnstcyBody = NestedBracesBodyComb<PredFnSpec<Self::Val>>;

    open spec fn cnstcy_body(&self, rec: PredFnSpec<Self::Val>) -> Self::CnstcyBody {
        nested_braces_body(rec)
    }
}

impl RecBLenBody for NestedBracesBody {
    type T = NestedBracesT;

    type BLenBody = NestedBracesBodyComb<ByteLenFnSpec<Self::T>>;

    open spec fn blen_body(&self, rec: ByteLenFnSpec<Self::T>) -> Self::BLenBody {
        nested_braces_body(rec)
    }
}

impl RecSBody for NestedBracesBody {
    type SVal = NestedBracesT;

    type SBody = NestedBracesBodyComb<SerializerFnSpec<Self::SVal>>;

    open spec fn s_body(&self, rec: SerializerFnSpec<Self::SVal>) -> Self::SBody {
        nested_braces_body(rec)
    }
}

impl RecSBodyDPS for NestedBracesBody {
    type ST = NestedBracesT;

    type SBodyDPS = NestedBracesBodyComb<SerializerDPSFnSpec<Self::ST>>;

    open spec fn s_body_dps(&self, rec: SerializerDPSFnSpec<Self::ST>) -> Self::SBodyDPS {
        nested_braces_body(rec)
    }
}

impl SoundRecPBody for NestedBracesBody {
    proof fn lemma_body_sound_inv_preservation(&self, rec: ParserFnSpecs<Self::PVal>) {
        let (p_cb, c_cb, b_cb) = rec;
        let rec_unfold = (self.p_body(p_cb), self.cnstcy_body(c_cb), self.blen_body(b_cb));
        assert(rec_unfold.sound_inv());
    }
}

impl NonMalleableRecPBody for NestedBracesBody {
    proof fn lemma_body_nonmal_inv_preservation(&self, rec: ParserFnSpecs<Self::PVal>) {
        let (p_cb, c_cb, b_cb) = rec;
        let rec_unfold = (self.p_body(p_cb), self.cnstcy_body(c_cb), self.blen_body(b_cb));
        assert(rec_unfold.nonmal_inv());
    }
}

impl GoodRecSBody for NestedBracesBody {
    proof fn lemma_s_body_serialize_inv_preservation(&self, rec: SerializerFnSpecs<Self::SVal>) {
        let (s_cb, b_cb) = rec;
        let rec_unfold = (self.s_body(s_cb), self.blen_body(b_cb));
        assert(rec_unfold.serialize_inv());
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = super::Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
    )) by {
        let cb = nested_braces.spec_parse_callback(10);
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
}

} // verus!
