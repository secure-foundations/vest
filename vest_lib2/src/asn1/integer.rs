use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::exec::output::*;
use crate::core::exec::{
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::primitives::base256::*;
use crate::{
    combinators::{
        mapped::spec::{FnSpecMapper, LosslessMapper, LossyMapper, SpecMapper},
        I16Be, Mapped, Refined, Tail, I8,
    },
    core::{proof::*, spec::*},
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power::*;
use vstd::arithmetic::power2::*;
use vstd::assert_seqs_equal;
use vstd::bits::*;
use vstd::prelude::*;

verus! {

pub type IntegerInnerFmt = Mapped<Refined<Tail, PredFnSpec<Seq<u8>>>, FnSpecMapper<Seq<u8>, int>>;

pub open spec fn integer_fmt() -> IntegerInnerFmt {
    Mapped {
        inner: Refined(Tail, |bytes: Seq<u8>| integer_bytes_wf(bytes)),
        mapper: (|bytes: Seq<u8>| int_from_be_bytes(bytes), |o: int| int_to_be_bytes(o)),
    }
}

pub open spec fn sign_bit_set(b: u8) -> bool {
    0x80u8 <= b
}

pub open spec fn invert_byte(b: u8) -> u8 {
    !b
}

pub open spec fn invert_bytes(bytes: Seq<u8>) -> Seq<u8> {
    bytes.map_values(|b: u8| invert_byte(b))
}

/// 8.3.2 If the contents octets of an integer value encoding consist of more than one octet, then the bits of the first octet and
/// bit 8 of the second octet:
///
/// a) shall not all be ones; and
/// b) shall not all be zero.
///
/// NOTE – These rules ensure that an integer value is always encoded in the smallest possible number of octets.
pub open spec fn integer_bytes_minimal(bytes: Seq<u8>) -> bool {
    bytes.len() > 1 ==> {
        &&& !(bytes[0] == 0x00u8 && !sign_bit_set(bytes[1]))
        &&& !(bytes[0] == 0xFFu8 && sign_bit_set(bytes[1]))
    }
}

pub open spec fn integer_bytes_wf(bytes: Seq<u8>) -> bool {
    // 8.3.1 The encoding of an integer value shall be primitive. The contents octets shall consist of one or more octets.
    &&& bytes.len() > 0
    &&& integer_bytes_minimal(bytes)
}

pub open spec fn int_from_be_bytes(bytes: Seq<u8>) -> int {
    let unsigned = nat_from_be_bytes(bytes);
    if sign_bit_set(bytes[0]) {
        unsigned as int - pow(256, bytes.len()) as int
    } else {
        unsigned as int
    }
}

pub open spec fn nonnegative_int_to_bytes(n: nat) -> Seq<u8> {
    let body = nat_to_be_bytes(n);
    if sign_bit_set(body[0]) {
        seq![0x00u8] + body
    } else {
        body
    }
}

pub open spec fn negative_int_to_bytes(n: nat) -> Seq<u8> {
    let body = invert_bytes(nat_to_be_bytes(n));
    if sign_bit_set(body[0]) {
        body
    } else {
        seq![0xFFu8] + body
    }
}

pub open spec fn int_to_be_bytes(v: int) -> Seq<u8> {
    if v >= 0 {
        nonnegative_int_to_bytes(v as nat)
    } else {
        negative_int_to_bytes((-1 - v) as nat)
    }
}

pub proof fn lemma_invert_byte_props(b: u8)
    ensures
        invert_byte(b) as nat + b as nat == 0xFF,
        invert_byte(invert_byte(b)) == b,
        sign_bit_set(invert_byte(b)) <==> !sign_bit_set(b),
{
    assert(invert_byte(b) == (0xFFu8 - b)) by (bit_vector);
    assert(invert_byte(b) as nat + b as nat == 0xFF);
    assert(invert_byte(invert_byte(b)) == b) by (bit_vector);
    assert(sign_bit_set(invert_byte(b)) <==> !sign_bit_set(b));
}

pub proof fn lemma_invert_bytes_involutive(bytes: Seq<u8>)
    ensures
        invert_bytes(invert_bytes(bytes)) == bytes,
{
    assert_seqs_equal!(invert_bytes(invert_bytes(bytes)) == bytes, i => {
        lemma_invert_byte_props(bytes[i]);
    });
}

pub proof fn lemma_from_be_bytes_invert(bytes: Seq<u8>)
    ensures
        nat_from_be_bytes(invert_bytes(bytes)) + nat_from_be_bytes(bytes) + 1 == pow(
            256,
            bytes.len(),
        ),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        let last = bytes.last();
        lemma_from_be_bytes_invert(prefix);
        prefix.lemma_push_map_commute(|x: u8| invert_byte(x), last);
        lemma_from_be_bytes_push(invert_bytes(prefix), invert_byte(last));
        lemma_invert_byte_props(last);
        lemma_pow256_succ(prefix.len());
        assert(bytes == prefix.push(last));
    }
}

pub proof fn lemma_integer_from_to_bytes(i: Seq<u8>)
    requires
        integer_bytes_wf(i),
    ensures
        int_to_be_bytes(int_from_be_bytes(i)) == i,
{
    if sign_bit_set(i[0]) {
        let c = invert_bytes(i);
        lemma_invert_bytes_involutive(i);
        lemma_from_be_bytes_invert(i);
        assert((-1 - int_from_be_bytes(i)) as nat == nat_from_be_bytes(invert_bytes(i)));
        if i.len() > 1 && i[0] == 0xFFu8 {
            let body = i.drop_first();
            let c_body = c.drop_first();
            assert(!sign_bit_set(body[0]));
            lemma_invert_byte_props(body[0]);
            lemma_from_be_bytes_prepend(c_body, 0x00u8);
            lemma_from_to_be_bytes_roundtrip(c_body);
            lemma_invert_bytes_involutive(body);
            let first = i[0];
            assert(first == 0xFFu8);
            assert(invert_byte(0xFFu8) == 0x00u8) by (bit_vector);
            assert_seqs_equal!(c == seq![0x00u8] + c_body);
            assert(i == seq![0xFFu8] + body);
        } else {
            if c.len() > 1 {
                lemma_invert_byte_props(i[0]);
                assert(c[0] != 0x00u8);
            }
            lemma_from_to_be_bytes_roundtrip(c);
        }
        lemma_from_be_bytes_upper_bound(i);
        assert(int_from_be_bytes(i) < 0);
        assert(int_to_be_bytes(int_from_be_bytes(i)) == i);
    } else {
        if i.len() == 1 {
            lemma_from_be_bytes_singleton(i[0]);
            assert(i == seq![i[0]]);
        } else if i[0] == 0x00u8 {
            let body = i.drop_first();
            assert(sign_bit_set(body[0]));
            lemma_from_be_bytes_prepend(body, 0x00u8);
            lemma_from_to_be_bytes_roundtrip(body);
            assert(i == seq![0x00u8] + body);
        } else {
            lemma_from_to_be_bytes_roundtrip(i);
        }
    }
}

pub proof fn lemma_integer_to_from_bytes(o: int)
    ensures
        int_from_be_bytes(int_to_be_bytes(o)) == o,
        integer_bytes_wf(int_to_be_bytes(o)),
{
    if o >= 0 {
        let n = o as nat;
        let body = nat_to_be_bytes(n);
        lemma_to_from_be_bytes_roundtrip(n);
        if sign_bit_set(body[0]) {
            lemma_from_be_bytes_prepend(body, 0x00u8);
        }
        lemma_to_be_bytes_props(n);
    } else {
        let n = (-1 - o) as nat;
        let unsigned = nat_to_be_bytes(n);
        let body = invert_bytes(unsigned);
        lemma_to_from_be_bytes_roundtrip(n);
        lemma_from_be_bytes_invert(unsigned);
        if !sign_bit_set(body[0]) {
            lemma_from_be_bytes_prepend(body, 0xFFu8);
            lemma_pow256_succ(unsigned.len());
        }
        lemma_to_be_bytes_props(n);
        lemma_invert_byte_props(nat_to_be_bytes(n)[0]);
    }
}

pub proof fn lemma_integer_fmt_sound_nonmal_inv()
    ensures
        integer_fmt().sound_inv(),
        integer_fmt().nonmal_inv(),
{
    assert forall|v: Seq<u8>| #[trigger] integer_fmt().inner.consistent(v) implies (
    integer_fmt().mapper.1)((integer_fmt().mapper.0)(v)) == v by {
        lemma_integer_from_to_bytes(v);
    }
}

pub proof fn lemma_integer_fmt_unambiguous()
    ensures
        integer_fmt().unambiguous(),
{
    assert forall|o: int| #[trigger] integer_fmt().consistent(o) implies (integer_fmt().mapper.0)(
        (integer_fmt().mapper.1)(o),
    ) == o by {
        lemma_integer_to_from_bytes(o);
    }
}

#[derive(Copy, Clone)]
pub struct BigInt<'a> {
    raw: &'a [u8],
}

proof fn lemma_large_nonnegative_integer(bytes: Seq<u8>)
    requires
        bytes.len() > 8,
        !sign_bit_set(bytes[0]),
        bytes[0] == 0 ==> sign_bit_set(bytes[1]),
    ensures
        nat_from_be_bytes(bytes) > i64::MAX as int,
{
    broadcast use lemma_pow_increases;

    reveal_with_fuel(pow, 9);
    if bytes[0] != 0 {
        lemma_from_be_bytes_lower_bound(bytes);
        lemma_pow_increases(256, 8, (bytes.len() - 1) as nat);
    } else {
        let rest = bytes.drop_first();
        let tail = rest.drop_first();
        assert(bytes == seq![bytes[0]] + rest);
        assert(rest == seq![rest[0]] + tail);
        lemma_from_be_bytes_prepend(rest, 0);
        lemma_from_be_bytes_prepend(tail, rest[0]);
        lemma_pow_increases(256, 7, tail.len());
        let first_int: int = rest[0] as int;
        let power: int = pow(256, tail.len());
        lemma_mul_inequality(128, first_int, power);
    }
}

proof fn lemma_large_integer_outside_i64(bytes: Seq<u8>)
    requires
        bytes.len() > 8,
        integer_bytes_wf(bytes),
    ensures
        sign_bit_set(bytes[0]) ==> int_from_be_bytes(bytes) < i64::MIN as int,
        !sign_bit_set(bytes[0]) ==> int_from_be_bytes(bytes) > i64::MAX as int,
{
    if sign_bit_set(bytes[0]) {
        let inverted = invert_bytes(bytes);
        lemma_invert_byte_props(bytes[0]);
        if inverted[0] == 0 {
            let first = bytes[0];
            lemma_invert_byte_props(first);
            lemma_invert_byte_props(bytes[1]);
        }
        lemma_large_nonnegative_integer(inverted);
        lemma_from_be_bytes_invert(bytes);
    } else {
        lemma_large_nonnegative_integer(bytes);
    }
}

impl<'a> BigInt<'a> {
    pub closed spec fn view(&self) -> Seq<u8> {
        self.raw.deep_view()
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        integer_bytes_wf(self.view()) && self.view().len() > 8
    }

    fn new(raw: &'a [u8]) -> (res: Self)
        requires
            integer_bytes_wf(raw.deep_view()),
            raw.len() > 8,
        ensures
            res.view() == raw.deep_view(),
    {
        BigInt { raw }
    }

    pub fn as_slice(&self) -> (res: &'a [u8])
        ensures
            res.deep_view() == self.view(),
    {
        self.raw
    }

    /// Returns the sign of an arbitrary-size integer.
    ///
    /// `BigInt` values are canonical encodings longer than eight octets, so
    /// their values are strictly outside the signed 64-bit range.
    pub fn is_negative(&self) -> (negative: bool)
        ensures
            negative ==> int_from_be_bytes(self.view()) < i64::MIN as int,
            !negative ==> int_from_be_bytes(self.view()) > i64::MAX as int,
    {
        proof {
            use_type_invariant(self);
            lemma_large_integer_outside_i64(self.view());
        }
        self.raw[0] >= 0x80
    }
}

#[derive(Copy, Clone)]
pub enum Integer<'a> {
    Small { v: i64 },
    Big { raw: BigInt<'a> },
}

impl<'a> DeepView for Integer<'a> {
    type V = int;

    closed spec fn deep_view(&self) -> Self::V {
        match *self {
            Integer::Small { v } => v as int,
            Integer::Big { raw } => int_from_be_bytes(raw.view()),
        }
    }
}

impl<'a> Integer<'a> {
    /// Constructs the exact ASN.1 INTEGER value represented by an `i64`.
    pub const fn from_i64(v: i64) -> Self {
        Integer::Small { v }
    }

    /// Returns the value as an `i64` when it is represented by the small variant.
    pub fn as_i64(&self) -> (value: Option<i64>)
        ensures
            value matches Some(v) ==> self.deep_view() == v as int,
    {
        match *self {
            Integer::Small { v } => Some(v),
            Integer::Big { .. } => None,
        }
    }

    /// Tests an inclusive interval whose endpoints are representable as `i64`.
    pub fn in_i64_range<const HAS_MIN: bool, const MIN: i64, const HAS_MAX: bool, const MAX: i64>(
        &self,
    ) -> (ok: bool)
        ensures
            ok == ({
                &&& HAS_MIN ==> MIN as int <= self.deep_view()
                &&& HAS_MAX ==> self.deep_view() <= MAX as int
            }),
    {
        match *self {
            Integer::Small { v } => { (!HAS_MIN || MIN <= v) && (!HAS_MAX || v <= MAX) },
            Integer::Big { raw } => {
                let negative = raw.is_negative();
                (!HAS_MIN || !negative) && (!HAS_MAX || negative)
            },
        }
    }
}

/// ASN.1 INTEGER contents specialized to the `i8` representation.
///
/// Every `i8` value has a canonical one-octet two's-complement encoding.
#[derive(Clone, Copy)]
pub struct Integer8Fmt;

/// ASN.1 INTEGER contents specialized to the `i16` representation.
///
/// Values in the `i8` range use one octet; all other values use two
/// big-endian octets. Redundant two-octet encodings are rejected.
#[derive(Clone, Copy)]
pub struct Integer16Fmt;

#[verifier::allow_in_spec]
pub fn fits_i8(v: i16) -> bool
    returns
        i8::MIN <= v <= i8::MAX,
{
    i8::MIN as i16 <= v && v <= i8::MAX as i16
}

pub(crate) proof fn lemma_integer8_fmt_byte_len(value: i8)
    ensures
        Integer8Fmt.byte_len(value) == 1,
{
}

pub(crate) proof fn lemma_integer16_fmt_byte_len_bound(value: i16)
    ensures
        Integer16Fmt.byte_len(value) <= 2,
{
}

mod derived_specs {
    use super::*;
    use super::super::IntegerFmt;

    impl SpecParser for IntegerFmt {
        type PVal = int;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            integer_fmt().spec_parse(ibuf)
        }
    }

    impl Consistency for IntegerFmt {
        type Val = int;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            integer_fmt().consistent(v)
        }
    }

    impl SpecSerializerDps for IntegerFmt {
        type SValue = int;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            integer_fmt().spec_serialize_dps(v, obuf)
        }
    }

    impl SpecSerializer for IntegerFmt {
        type SVal = int;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            integer_fmt().spec_serialize(v)
        }
    }

    impl SpecByteLen for IntegerFmt {
        type T = int;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            integer_fmt().byte_len(v)
        }
    }

    impl SpecParser for Integer8Fmt {
        type PVal = i8;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            if ibuf.len() == 1 {
                I8.spec_parse(ibuf)
            } else {
                None
            }
        }
    }

    impl Consistency for Integer8Fmt {
        type Val = i8;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            true
        }
    }

    impl SpecSerializerDps for Integer8Fmt {
        type SValue = i8;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, _obuf: Seq<u8>) -> Seq<u8> {
            I8.spec_serialize(v)
        }
    }

    impl SpecSerializer for Integer8Fmt {
        type SVal = i8;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            I8.spec_serialize(v)
        }
    }

    impl SpecByteLen for Integer8Fmt {
        type T = i8;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            I8.byte_len(v)
        }
    }

    impl ValueByteLen for Integer8Fmt {
        open spec fn value_byte_len(v: Self::T) -> nat {
            I8.byte_len(v)
        }

        proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        }
    }

    impl SpecParser for Integer16Fmt {
        type PVal = i16;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            if ibuf.len() == 1 {
                let (_, v) = I8.spec_parse(ibuf)->0;
                Some((1, v as i16))
            } else if ibuf.len() == 2 {
                match I16Be.spec_parse(ibuf) {
                    Some((_, v)) if !fits_i8(v) => Some((2, v)),
                    _ => None,
                }
            } else {
                None
            }
        }
    }

    impl Consistency for Integer16Fmt {
        type Val = i16;

        open spec fn consistent(&self, v: Self::Val) -> bool {
            true
        }
    }

    impl SpecSerializerDps for Integer16Fmt {
        type SValue = i16;

        open spec fn spec_serialize_dps(&self, v: Self::SValue, _obuf: Seq<u8>) -> Seq<u8> {
            if fits_i8(v) {
                I8.spec_serialize(v as i8)
            } else {
                I16Be.spec_serialize(v)
            }
        }
    }

    impl SpecSerializer for Integer16Fmt {
        type SVal = i16;

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            if fits_i8(v) {
                I8.spec_serialize(v as i8)
            } else {
                I16Be.spec_serialize(v)
            }
        }
    }

    impl SpecByteLen for Integer16Fmt {
        type T = i16;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            if fits_i8(v) {
                I8.byte_len(v as i8)
            } else {
                I16Be.byte_len(v)
            }
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::IntegerFmt;

    impl SafeParser for IntegerFmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            integer_fmt().lemma_parse_safe(ibuf);
        }
    }

    impl Productive for IntegerFmt {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            if let Some((n, _)) = integer_fmt().spec_parse(s) {
                assert(n > 0);
            }
        }
    }

    impl SoundParser for IntegerFmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_integer_fmt_sound_nonmal_inv();
            integer_fmt().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_integer_fmt_sound_nonmal_inv();
            integer_fmt().lemma_parse_sound_value(ibuf);
        }
    }

    impl GoodSerializer for IntegerFmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            integer_fmt().lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for IntegerFmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_integer_fmt_sound_nonmal_inv();
            lemma_integer_fmt_unambiguous();
            integer_fmt().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl NonMalleable for IntegerFmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_integer_fmt_sound_nonmal_inv();
            integer_fmt().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl EquivSerializers for IntegerFmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            integer_fmt().lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Integer8Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_safe(ibuf);
            }
        }
    }

    impl Productive for Integer8Fmt {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            if s.len() == 1 {
                I8.lemma_productive(s);
            }
        }
    }

    impl SoundParser for Integer8Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_sound_consumption(ibuf);
            }
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_sound_value(ibuf);
            }
        }
    }

    impl GoodSerializer for Integer8Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            I8.lemma_serialize_len(v);
        }
    }

    impl SPRoundTripDps for Integer8Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            I8.theorem_serialize_dps_parse_roundtrip(v, Seq::empty());
        }
    }

    impl NonMalleable for Integer8Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            if buf1.len() == 1 && buf2.len() == 1 {
                I8.lemma_parse_non_malleable(buf1, buf2);
            }
        }
    }

    impl EquivSerializers for Integer8Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            I8.lemma_serialize_equiv_on_empty(v);
        }
    }

    impl SafeParser for Integer16Fmt {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_safe(ibuf);
            } else if ibuf.len() == 2 {
                I16Be.lemma_parse_safe(ibuf);
            }
        }
    }

    impl Productive for Integer16Fmt {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            if s.len() == 1 {
                I8.lemma_productive(s);
            } else if s.len() == 2 {
                I16Be.lemma_productive(s);
            }
        }
    }

    impl SoundParser for Integer16Fmt {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_sound_consumption(ibuf);
            } else if ibuf.len() == 2 {
                I16Be.lemma_parse_sound_consumption(ibuf);
            }
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            if ibuf.len() == 1 {
                I8.lemma_parse_sound_value(ibuf);
            } else if ibuf.len() == 2 {
                I16Be.lemma_parse_sound_value(ibuf);
            }
        }
    }

    impl GoodSerializer for Integer16Fmt {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            if fits_i8(v) {
                I8.lemma_serialize_len(v as i8);
            } else {
                I16Be.lemma_serialize_len(v);
            }
        }
    }

    impl SPRoundTripDps for Integer16Fmt {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            if fits_i8(v) {
                I8.theorem_serialize_dps_parse_roundtrip(v as i8, Seq::empty());
            } else {
                I16Be.theorem_serialize_dps_parse_roundtrip(v, Seq::empty());
            }
        }
    }

    impl NonMalleable for Integer16Fmt {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            if buf1.len() == 1 && buf2.len() == 1 {
                I8.lemma_parse_non_malleable(buf1, buf2);
            } else if buf1.len() == 2 && buf2.len() == 2 {
                I16Be.lemma_parse_non_malleable(buf1, buf2);
            }
        }
    }

    impl EquivSerializers for Integer16Fmt {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            if fits_i8(v) {
                I8.lemma_serialize_equiv_on_empty(v as i8);
            } else {
                I16Be.lemma_serialize_equiv_on_empty(v);
            }
        }
    }

}

impl<'i> Parser<&'i [u8]> for super::IntegerFmt {
    type PT = Integer<'i>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, bytes) = Tail.parse(ibuf)?;
        if bytes.len() == 0 {
            return Err(ParseError::custom("Empty integer"));
        }
        if bytes.len() > 1 {
            let b0 = bytes[0];
            let b1 = bytes[1];
            if b0 == 0x00 && b1 < 0x80 {
                return Err(ParseError::custom("Non-minimal integer"));
            }
            if b0 == 0xFF && b1 >= 0x80 {
                return Err(ParseError::custom("Non-minimal integer"));
            }
        }
        if bytes.len() <= 8 {
            Ok((n, Integer::Small { v: i64_from_be_bytes(bytes) }))
        } else {
            Ok((n, Integer::Big { raw: BigInt::new(bytes) }))
        }
    }
}

impl<'i> Parser<&'i [u8]> for Integer8Fmt {
    type PT = i8;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        if ibuf.len() == 1 {
            I8.parse(ibuf)
        } else {
            Err(ParseError::custom("Integer out of range for i8"))
        }
    }
}

impl<'i> Parser<&'i [u8]> for Integer16Fmt {
    type PT = i16;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        if ibuf.len() == 1 {
            let (n, v) = I8.parse(ibuf)?;
            Ok((n, v as i16))
        } else if ibuf.len() == 2 {
            let (n, v) = I16Be.parse(ibuf)?;
            if fits_i8(v) {
                Err(ParseError::non_canonical())
            } else {
                Ok((n, v))
            }
        } else {
            Err(ParseError::custom("Integer out of range for i16"))
        }
    }
}

impl<Output: OutputBuf> Serializer<Output, i8> for Integer8Fmt {
    fn serialize_into(&self, v: &i8, obuf: &mut Output) {
        I8.serialize_into(v, obuf);
    }
}

impl Prepare<i8> for Integer8Fmt {
    fn prepare(&self, v: &i8) -> Result<usize, PreSerializeError> {
        I8.prepare(v)
    }
}

impl ByteLen<i8> for Integer8Fmt {
    fn length(&self, v: &i8) -> usize {
        I8.length(v)
    }
}

impl<Output: OutputBuf> Serializer<Output, i16> for Integer16Fmt {
    fn serialize_into(&self, v: &i16, obuf: &mut Output) {
        if fits_i8(*v) {
            I8.serialize_into(&(*v as i8), obuf);
        } else {
            I16Be.serialize_into(v, obuf);
        }
    }
}

impl Prepare<i16> for Integer16Fmt {
    fn prepare(&self, v: &i16) -> Result<usize, PreSerializeError> {
        if fits_i8(*v) {
            I8.prepare(&(*v as i8))
        } else {
            I16Be.prepare(v)
        }
    }
}

impl ByteLen<i16> for Integer16Fmt {
    fn length(&self, v: &i16) -> usize {
        if fits_i8(*v) {
            I8.length(&(*v as i8))
        } else {
            I16Be.length(v)
        }
    }
}

impl<Output: OutputBuf, 'i> Serializer<Output, Integer<'i>> for super::IntegerFmt {
    fn serialize_into(&self, v: &Integer<'i>, obuf: &mut Output) {
        match v {
            Integer::Small { v } => {
                let len = i64_to_be_bytes_len(*v);
                let mut bytes = [0u8;size_of::<i64>() + 1];
                let (encoded, _) = bytes.split_at_mut(len);
                i64_to_be_bytes_in_place(*v, encoded);
                Tail.serialize_into(&bytes[0..len], obuf);
            },
            Integer::Big { raw } => {
                let bytes = raw.as_slice();
                proof {
                    use_type_invariant(raw);
                    lemma_integer_fmt_sound_nonmal_inv();
                    lemma_integer_from_to_bytes(bytes.deep_view());
                }
                Tail.serialize_into(&bytes, obuf);
            },
        }
    }
}

impl<'i> Prepare<Integer<'i>> for super::IntegerFmt {
    fn prepare(&self, v: &Integer<'i>) -> Result<usize, PreSerializeError> {
        match v {
            Integer::Small { v } => {
                let len = i64_to_be_bytes_len(*v);
                proof {
                    lemma_integer_to_from_bytes(*v as int);
                }
                Ok(len)
            },
            Integer::Big { raw } => {
                let bytes = raw.as_slice();
                proof {
                    use_type_invariant(raw);
                    lemma_integer_fmt_sound_nonmal_inv();
                    lemma_integer_from_to_bytes(bytes.deep_view());
                }
                Tail.prepare(&bytes)
            },
        }
    }
}

impl<'i> ByteLen<Integer<'i>> for super::IntegerFmt {
    fn length(&self, v: &Integer<'i>) -> usize {
        match v {
            Integer::Small { v } => { i64_to_be_bytes_len(*v) },
            Integer::Big { raw } => {
                let bytes = raw.as_slice();
                proof {
                    use_type_invariant(raw);
                    lemma_integer_fmt_sound_nonmal_inv();
                    lemma_integer_from_to_bytes(bytes.deep_view());
                }
                Tail.length(&bytes)
            },
        }
    }
}

broadcast proof fn lemma_u64_as_i64(u: u64)
    by (bit_vector)
    ensures
        u < 0x8000000000000000 ==> #[trigger] (u as i64) as int == u as int,
        u >= 0x8000000000000000 ==> #[trigger] (u as i64) as int == u as int - 0x10000000000000000,
{
}

/// Executable big-endian two's-complement decoding into `i64`.
pub fn i64_from_be_bytes(bytes: &[u8]) -> (r: i64)
    requires
        usize::BITS == 64,
        1 <= bytes.len() <= 8,
    ensures
        r as int == int_from_be_bytes(bytes.deep_view()),
{
    broadcast use {lemma_pow_multiplies, lemma_pow2, lemma_pow_increases};
    broadcast use lemma_from_be_bytes_upper_bound;
    broadcast use lemma_u64_as_i64;

    let n = bytes.len();
    let u = u64_from_be_bytes(bytes);

    let ghost s = bytes.deep_view();
    let ghost (first, rest) = (s.first(), s.drop_first());
    let ghost pw = pow(256, (n - 1) as nat);
    let ghost nfb_rest = nat_from_be_bytes(rest);
    proof {
        assert(s == seq![first] + rest);
        lemma_from_be_bytes_prepend(rest, first);
        // nat_from_be_bytes(s) == first * pow(256, n-1) + nfb_rest, with nfb_rest < pow(256, n-1)
        assert(nat_from_be_bytes(s) == first * pw + nfb_rest);
        reveal_with_fuel(pow, 9);
    }
    if bytes[0] >= 0x80 {
        // Sign bit is set: int_from_be_bytes(s) == nat_from_be_bytes(s) - pow(256, n).
        if n == 8 {
            proof {
                // u == nat_from_be_bytes(s) >= first * 2^56 >= 0x80 * 2^56 == 2^63
                assert(first * pw + nfb_rest >= 0x8000000000000000) by (nonlinear_arith)
                    requires
                        first >= 0x80,
                        pw == 0x100000000000000,
                ;
            }
            // u >= 2^63, so (u as i64) reinterprets as u - 2^64 == nat_from_be_bytes(s) - pow(256,8).
            u as i64
        } else {  // n < 8
            let shift: u64 = 8 * (n as u64);
            proof {
                // Establish pow(256, n) == pow2(8n) == 1u64 << (8n)
                assert(pow(2, 8) == 256) by (compute_only);
                lemma_u64_shl_is_mul(1u64, shift);
            }
            let sub: u64 = 1u64 << shift;
            // u < pow(256, n) == sub <= 2^56, so both fit in i64 and the
            // subtraction yields nat_from_be_bytes(s) - pow(256, n).
            (u as i64) - (sub as i64)
        }
    } else {
        // Sign bit clear: int_from_be_bytes(s) == nat_from_be_bytes(s), which fits in i64.
        proof {
            // nat_from_be_bytes(s) < (first + 1) * pow(256, n-1) <= 0x80 * 2^56 == 2^63
            assert(nat_from_be_bytes(s) < 0x8000000000000000) by (nonlinear_arith)
                requires
                    nat_from_be_bytes(s) == first as nat * pw + nfb_rest,
                    nfb_rest < pw,
                    first < 0x80,
                    pw <= 0x100000000000000,
            ;
        }
        u as i64
    }
}

/// Executable big-endian two's-complement encoding from `i64`.
/// TODO: Optimize this function?
#[cfg(feature = "alloc")]
pub fn i64_to_be_bytes(v: i64) -> (buf: Vec<u8>)
    requires
        usize::BITS == 64,
    ensures
        buf@ == int_to_be_bytes(v as int),
{
    if v >= 0 {
        let mut body = u64_to_be_bytes(v as u64);
        if body[0] >= 0x80 {  // sign bit set
            body.insert(0, 0x00u8);
            body
        } else {  // sign bit clear
            body
        }
    } else {
        let m: u64 = (-1 - v) as u64;
        let mut body = u64_to_be_bytes(m);
        // Invert the bytes in place.
        let ghost orig = body@;
        invert_bytes_in_place(&mut body);
        if body[0] >= 0x80 {  // sign bit set
            body
        } else {  // sign bit clear
            body.insert(0, 0xFFu8);
            body
        }
    }
}

/// Allocation-free length of the minimal big-endian two's-complement encoding.
pub fn i64_to_be_bytes_len(v: i64) -> (len: usize)
    requires
        usize::BITS == 64,
    ensures
        len == int_to_be_bytes(v as int).len(),
        len <= size_of::<i64>() + 1,
{
    let magnitude = if v >= 0 {
        v as u64
    } else {
        (-1 - v) as u64
    };
    let body_len = u64_to_be_bytes_len(magnitude);
    let first = u64_to_be_bytes_first(magnitude);
    proof {
        lemma_usize_to_be_bytes_len_bound(magnitude as usize);
        assert(body_len <= 8);
        if v >= 0 {
            assert(magnitude as nat == v as int);
        } else {
            assert(-1i64 - v >= 0);
            assert(magnitude as int == (-1i64 - v) as int);
            assert((-1i64 - v) as int == -1 - v as int);
            lemma_invert_byte_props(first);
        }
    }
    if first >= 0x80 {
        body_len + 1
    } else {
        body_len
    }
}

/// Inverts every byte of `obuf` in place (bitwise NOT).
fn invert_bytes_in_place(obuf: &mut [u8])
    ensures
        final(obuf)@ == invert_bytes(old(obuf)@),
{
    let n = obuf.len();
    for i in 0..n
        invariant
            n == obuf.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] obuf@[k] == invert_byte(old(obuf)@[k]),
            forall|k: int| i <= k < n ==> #[trigger] obuf@[k] == old(obuf)@[k],
    {
        obuf[i] = !obuf[i];
    }
    assert(obuf@ =~= invert_bytes(old(obuf)@));
}

/// Writes the minimal big-endian two's-complement encoding of `v` into an exactly-sized slice.
pub fn i64_to_be_bytes_in_place(v: i64, obuf: &mut [u8])
    requires
        usize::BITS == 64,
        old(obuf)@.len() == int_to_be_bytes(v as int).len(),
    ensures
        final(obuf)@ == int_to_be_bytes(v as int),
{
    let magnitude = if v >= 0 {
        v as u64
    } else {
        (-1 - v) as u64
    };
    let first = u64_to_be_bytes_first(magnitude);
    proof {
        if v < 0 {
            lemma_invert_byte_props(first);
        }
    }
    if first >= 0x80 {
        let (sign, body) = obuf.split_at_mut(1);
        if v >= 0 {
            sign[0] = 0x00u8;
        } else {
            sign[0] = 0xFFu8;
        }
        usize_to_be_bytes_in_place(magnitude as usize, body);
        if v < 0 {
            invert_bytes_in_place(body);
        }
    } else {
        usize_to_be_bytes_in_place(magnitude as usize, obuf);
        if v < 0 {
            invert_bytes_in_place(obuf);
        }
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::{Integer16Fmt, Integer8Fmt};
    use crate::core::exec::{Parser, Prepare, SerializerExt};

    #[test]
    fn integer8_boundaries_and_noncanonical_lengths() {
        for (bytes, expected) in [(&[0x80u8][..], -128i8), (&[0x7fu8][..], 127i8)] {
            let (_, value) = Integer8Fmt.parse(&bytes).unwrap();
            assert_eq!(value, expected);
        }

        let two_bytes = &[0x00u8, 0x7f][..];
        assert!(Integer8Fmt.parse(&two_bytes).is_err());
    }

    #[test]
    fn integer16_uses_minimal_one_or_two_octets() {
        for (value, expected) in [
            (-32768i16, &[0x80u8, 0x00][..]),
            (-129i16, &[0xffu8, 0x7f][..]),
            (-128i16, &[0x80u8][..]),
            (127i16, &[0x7fu8][..]),
            (128i16, &[0x00u8, 0x80][..]),
            (32767i16, &[0x7fu8, 0xff][..]),
        ] {
            let mut encoded = vec![0; Integer16Fmt.prepare(&value).unwrap()];
            Integer16Fmt.serialize(&value, &mut encoded);
            assert_eq!(encoded, expected);

            let (_, decoded) = Integer16Fmt.parse(&expected).unwrap();
            assert_eq!(decoded, value);
        }

        for bytes in [&[0x00u8, 0x7f][..], &[0xffu8, 0x80][..]] {
            assert!(Integer16Fmt.parse(&bytes).is_err());
        }
    }

    #[test]
    fn test_integer8_equivalence_with_general_integer() {
        use super::Integer;
        use crate::asn1::IntegerFmt;

        for v in -128..=127 {
            // Serialize using Integer8Fmt
            let mut enc8 = vec![0; Integer8Fmt.prepare(&v).unwrap()];
            Integer8Fmt.serialize(&v, &mut enc8);

            // Serialize using general Integer
            let val = Integer::Small { v: v as i64 };
            let mut enc_gen = vec![0; IntegerFmt.prepare(&val).unwrap()];
            IntegerFmt.serialize(&val, &mut enc_gen);

            assert_eq!(enc8, enc_gen, "Mismatch serialization at {}", v);

            // Parse using Integer8Fmt
            let enc8_slice = enc8.as_slice();
            let (_, dec8) = Integer8Fmt.parse(&enc8_slice).unwrap();
            assert_eq!(dec8, v);

            // Parse using general Integer
            let (_, dec_gen) = IntegerFmt.parse(&enc8_slice).unwrap();
            match dec_gen {
                Integer::Small { v: val_i64 } => {
                    assert_eq!(val_i64, v as i64);
                }
                _ => panic!("Expected Small for {}", v),
            }
        }
    }

    #[test]
    fn test_integer16_equivalence_with_general_integer() {
        use super::Integer;
        use crate::asn1::IntegerFmt;

        for v in -32768..=32767 {
            // Serialize using Integer16Fmt
            let mut enc16 = vec![0; Integer16Fmt.prepare(&v).unwrap()];
            Integer16Fmt.serialize(&v, &mut enc16);

            // Serialize using general Integer
            let val = Integer::Small { v: v as i64 };
            let mut enc_gen = vec![0; IntegerFmt.prepare(&val).unwrap()];
            IntegerFmt.serialize(&val, &mut enc_gen);

            assert_eq!(enc16, enc_gen, "Mismatch serialization at {}", v);

            // Parse using Integer16Fmt
            let enc16_slice = enc16.as_slice();
            let (_, dec16) = Integer16Fmt.parse(&enc16_slice).unwrap();
            assert_eq!(dec16, v);

            // Parse using general Integer
            let (_, dec_gen) = IntegerFmt.parse(&enc16_slice).unwrap();
            match dec_gen {
                Integer::Small { v: val_i64 } => {
                    assert_eq!(val_i64, v as i64);
                }
                _ => panic!("Expected Small for {}", v),
            }
        }
    }
}
