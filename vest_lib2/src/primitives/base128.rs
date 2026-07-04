use super::leb128::*;
use crate::combinators::disjoint::disjointness_lemmas;
use crate::core::exec::parser::*;
use crate::{
    combinators::mapped::spec::*,
    combinators::*,
    core::{exec::*, proof::*, spec::*},
};
use input::InputBuf;
use vstd::arithmetic::power::*;
use vstd::calc;
use vstd::prelude::*;

verus! {

/// Unsigned big-endian base-128 decoding.
pub open spec fn nat_from_base128(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        nat_from_base128(bytes.drop_last()) * 128 + (bytes.last() % 128) as nat
    }
}

/// Unsigned big-endian base-128 encoding.
pub open spec fn nat_to_base128(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 128 {
        seq![n as u8]
    } else {
        nat_to_base128((n / 128) as nat).push((n % 128) as u8)
    }
}

pub proof fn lemma_from_base128_push(bytes: Seq<u8>, b: u8)
    ensures
        nat_from_base128(bytes.push(b)) == nat_from_base128(bytes) * 128 + (b % 128) as nat,
{
    assert(bytes.push(b).drop_last() == bytes);
}

pub proof fn lemma_pow128_succ(exp: nat)
    ensures
        pow(128, exp + 1) == pow(128, exp) * 128,
{
    lemma_pow_adds(128, exp, 1);
    lemma_pow1(128);
}

pub proof fn lemma_from_base128_upper_bound(bytes: Seq<u8>)
    ensures
        nat_from_base128(bytes) < pow(128, bytes.len()),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        lemma_pow0(128);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_base128_upper_bound(prefix);
        lemma_pow128_succ(prefix.len());
    }
}

pub proof fn lemma_nat_from_base128_bounds(bytes: Seq<u8>)
    ensures
        bytes.len() <= 4 ==> nat_from_base128(bytes) <= u32::MAX,
        bytes.len() <= 9 ==> nat_from_base128(bytes) <= u64::MAX,
{
    lemma_from_base128_upper_bound(bytes);
    reveal_with_fuel(pow, 10);
}

pub proof fn lemma_to_base128_props(n: nat)
    ensures
        nat_to_base128(n).len() > 0,
        n > 0 ==> nat_to_base128(n)[0] != 0,
        n > 0 ==> pow(128, (nat_to_base128(n).len() - 1) as nat) <= n,
        forall|i: int| 0 <= i < nat_to_base128(n).len() ==> #[trigger] nat_to_base128(n)[i] < 128,
    decreases n,
{
    if n < 128 {
        lemma_pow0(128);
    } else {
        let q = (n / 128) as nat;
        lemma_to_base128_props(q);
        lemma_pow128_succ((nat_to_base128(q).len() - 1) as nat);
        assert(pow(128, (nat_to_base128(q).len() - 1) as nat) * 128 <= q * 128) by (nonlinear_arith)
            requires
                pow(128, (nat_to_base128(q).len() - 1) as nat) <= q,
        ;
    }
}

pub proof fn lemma_to_base128_len_bound(n: nat, max_len: nat)
    requires
        0 < max_len,
        n < pow(128, max_len),
    ensures
        nat_to_base128(n).len() <= max_len,
{
    if n == 0 {
    } else {
        lemma_to_base128_props(n);
        lemma_pow_strictly_increases_converse(128, (nat_to_base128(n).len() - 1) as nat, max_len);
    }
}

pub proof fn lemma_to_base128_len_bounds()
    ensures
        forall|n: u32| #[trigger] nat_to_base128(n as nat).len() <= 5,
        forall|n: u64| #[trigger] nat_to_base128(n as nat).len() <= 10,
{
    reveal_with_fuel(pow, 11);
    assert forall|n: u32| #[trigger] nat_to_base128(n as nat).len() <= 5 by {
        lemma_to_base128_len_bound(n as nat, 5);
    }
    assert forall|n: u64| #[trigger] nat_to_base128(n as nat).len() <= 10 by {
        lemma_to_base128_len_bound(n as nat, 10);
    }
}

pub proof fn lemma_to_from_base128_roundtrip(n: nat)
    ensures
        nat_from_base128(nat_to_base128(n)) == n,
    decreases n,
{
    if n < 128 {
        reveal_with_fuel(nat_from_base128, 2);
    } else {
        let q = (n / 128) as nat;
        let r = (n % 128) as nat;
        lemma_to_from_base128_roundtrip(q);
        lemma_from_base128_push(nat_to_base128(q), r as u8);
    }
}

pub proof fn lemma_from_to_base128_roundtrip(bytes: Seq<u8>)
    requires
        bytes.len() > 0,
        bytes.len() > 1 ==> bytes[0] != 0,
        forall|i: int| 0 <= i < bytes.len() ==> bytes[i] < 128,
    ensures
        nat_to_base128(nat_from_base128(bytes)) == bytes,
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        reveal_with_fuel(nat_from_base128, 2);
        assert(bytes == seq![bytes[0]]);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_to_base128_roundtrip(prefix);
    }
}

pub const CONTINUATION_MASK: u8 = 0b1000_0000;

pub const PAYLOAD_MASK: u8 = 0b0111_1111;

// ceil(log_128(2^32)) = 5
// pub const BASE128_MAX_BYTES: usize = 4;
// pub type UInt = u32;
// ceil(log_128(2^64)) = 10
pub const BASE128_MAX_BYTES: usize = 9;

pub type UInt = u64;

pub type Base128Fmt__<const MINIMAL: bool> = Mapped<
    Refined<
        Repeat<Refined<U8, PredFnSpec<u8>>, Refined<U8, PredFnSpec<u8>>>,
        PredFnSpec<(Seq<u8>, u8)>,
    >,
    FnSpecMapper<(Seq<u8>, u8), UInt>,
>;

pub open spec fn base128_fmt<const MINIMAL: bool>() -> Base128Fmt__<MINIMAL> {
    Mapped {
        inner: Refined(
            Repeat(
                Refined(U8, |b: u8| b & CONTINUATION_MASK != 0),
                Refined(U8, |b: u8| b & CONTINUATION_MASK == 0),
            ),
            |pair: (Seq<u8>, u8)|
                {
                    // 1. No overflow: the number of bytes must be <= BASE128_MAX_BYTES
                    // 2. No leading zeros if MINIMAL is true
                    let (cont_bytes, term_byte) = pair;
                    &&& cont_bytes.len() <= BASE128_MAX_BYTES - 1
                    &&& MINIMAL ==> (cont_bytes.len() > 0 ==> cont_bytes[0] & PAYLOAD_MASK != 0)
                },
        ),
        mapper: (
            |pair: (Seq<u8>, u8)|
                {
                    let (cont_bytes, term_byte) = pair;
                    let bytes = cont_bytes.push(term_byte);
                    nat_from_base128(bytes) as UInt
                },
            |n: UInt|
                {
                    let bytes = nat_to_base128(n as nat);
                    let cont_bytes = bytes.drop_last().map_values(|b: u8| b | CONTINUATION_MASK);
                    let term_byte = bytes.last();
                    (cont_bytes, term_byte)
                },
        ),
    }
}

proof fn lemma_nat_from_base128_modulo(bytes: Seq<u8>)
    ensures
        nat_from_base128(bytes) == nat_from_base128(bytes.map_values(|b: u8| (b % 128) as u8)),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
    } else {
        let prefix = bytes.drop_last();
        lemma_nat_from_base128_modulo(prefix);
        assert(bytes.map_values(|b: u8| (b % 128) as u8).drop_last() == prefix.map_values(
            |b: u8| (b % 128) as u8,
        ));
    }
}

broadcast proof fn lemma_mask_modulo(b: u8)
    by (bit_vector)
    ensures
        #[trigger] (b & PAYLOAD_MASK) == (b % 128) as u8,
{
}

pub proof fn lemma_base128_fmt_sound_nonmal_inv()
    ensures
        base128_fmt::<true>().sound_inv(),
        base128_fmt::<true>().nonmal_inv(),
{
    reveal(<Star<_> as Consistency>::consistent);
    let fmt = base128_fmt::<true>();
    assert forall|pair| fmt.inner.consistent(pair) implies (fmt.mapper.1)((fmt.mapper.0)(pair))
        == pair by {
        let (cont_bytes, term_byte) = pair;
        let bytes = cont_bytes.push(term_byte);
        assert(bytes.len() <= BASE128_MAX_BYTES);
        lemma_nat_from_base128_bounds(bytes);

        broadcast use lemma_mask_modulo;

        let payload_bytes = bytes.map_values(|b: u8| (b % 128) as u8);
        let n = nat_from_base128(bytes);
        lemma_from_to_base128_roundtrip(payload_bytes);  // ==> nat_to_base128(nat_from_base128(payload_bytes)) == payload_bytes
        lemma_nat_from_base128_modulo(bytes);  // ==> nat_from_base128(bytes) == nat_from_base128(payload_bytes)
        // need to show: map_rev(nat_from_base128(bytes) as UInt) == (cont_bytes, term_byte)

        let encoded_bytes = nat_to_base128(n);
        assert(encoded_bytes == payload_bytes);

        assert(term_byte & PAYLOAD_MASK == term_byte) by (bit_vector)
            requires
                term_byte & CONTINUATION_MASK == 0,
        ;
        assert(encoded_bytes.last() == term_byte);
        assert forall|i: int|
            0 <= i < cont_bytes.len() implies encoded_bytes.drop_last().map_values(
            |b: u8| b | CONTINUATION_MASK,
        )[i] == cont_bytes[i] by {
            let b_orig = cont_bytes[i];
            assert(b_orig & CONTINUATION_MASK != 0);
            assert(((b_orig & PAYLOAD_MASK) | 128) == b_orig) by (bit_vector)
                requires
                    b_orig & CONTINUATION_MASK != 0,
            ;
        }
        assert(encoded_bytes.drop_last().map_values(|b: u8| b | CONTINUATION_MASK) =~= cont_bytes);
    }
}

pub proof fn lemma_base128_fmt_unambiguous<const MINIMAL: bool>()
    ensures
        base128_fmt::<MINIMAL>().unambiguous(),
{
    broadcast use disjointness_lemmas;

    let fmt = base128_fmt::<MINIMAL>();
    // the following holds true even without `fmt.consistent(o) implies`
    assert forall|o: UInt| #[trigger] (fmt.mapper.0)((fmt.mapper.1)(o)) == o by {
        let bytes = nat_to_base128(o as nat);
        let cont_bytes = bytes.drop_last().map_values(|b: u8| b | CONTINUATION_MASK);
        let term_byte = bytes.last();
        let bytes2 = cont_bytes.push(term_byte);

        lemma_to_from_base128_roundtrip(o as nat);  // ==> nat_from_base128(bytes) == o
        // need to show: nat_from_base128(bytes) == nat_from_base128(bytes2)
        lemma_nat_from_base128_modulo(bytes);
        lemma_nat_from_base128_modulo(bytes2);
        let m1 = bytes2.map_values(|b: u8| (b % 128) as u8);
        let m2 = bytes.map_values(|b: u8| (b % 128) as u8);
        // need to show: m1 == m2
        assert(forall|b: u8| ((b | 128) % 128) as u8 == b % 128) by (bit_vector);
        assert(m1 == m2);

    }
}

proof fn lemma_uint_shr7_is_div128(v: u64)
    by (bit_vector)
    ensures
        (v >> 7usize) as nat == v as nat / 128,
{
}

proof fn lemma_uint_low7_is_mod128(v: u64)
    by (bit_vector)
    ensures
        (v & PAYLOAD_MASK as u64) as nat == v as nat % 128,
{
}

proof fn lemma_uint64_shl7_or_is_base128(v: u64, b: u8)
    by (bit_vector)
    ensures
        (((v << 7usize) | (b & 0x7fu8) as u64) as nat) == (v as nat * 128 + (b % 128) as nat) % (
        0x1_0000_0000_0000_0000nat),
{
}

proof fn lemma_base128_fmt_consistent<const MINIMAL: bool>(v: UInt)
    requires
        nat_to_base128(v as nat).len() <= BASE128_MAX_BYTES,
    ensures
        base128_fmt::<MINIMAL>().consistent(v),
{
    reveal(<Star<_> as Consistency>::consistent);
    lemma_to_base128_props(v as nat);

    assert(forall|byte: u8| #![auto] (byte | CONTINUATION_MASK) & CONTINUATION_MASK != 0)
        by (bit_vector);
    assert(forall|byte: u8| #![auto] byte < CONTINUATION_MASK ==> byte & CONTINUATION_MASK == 0)
        by (bit_vector);
    assert(forall|byte: u8|
        #![auto]
        byte < CONTINUATION_MASK ==> (byte | CONTINUATION_MASK) & PAYLOAD_MASK == byte)
        by (bit_vector);
}

proof fn lemma_base128_fmt_byte_len<const MINIMAL: bool>(v: UInt)
    ensures
        base128_fmt::<MINIMAL>().byte_len(v) == nat_to_base128(v as nat).len(),
{
    let bytes = nat_to_base128(v as nat);
    let cont_bytes = bytes.drop_last().map_values(|b: u8| b | CONTINUATION_MASK);
    lemma_star_byte_len_seq_u8(cont_bytes);
}

proof fn lemma_star_serialize_seq_u8(vs: Seq<u8>)
    ensures
        Star(Refined(U8, |b: u8| b & CONTINUATION_MASK != 0)).spec_serialize(vs) == vs,
    decreases vs.len(),
{
    reveal(<Star<_> as SpecSerializer>::spec_serialize);
    if vs.len() > 0 {
        let prefix = vs.drop_last();
        lemma_star_serialize_seq_u8(prefix);
    }
}

proof fn lemma_star_byte_len_seq_u8(vs: Seq<u8>)
    ensures
        Star(Refined(U8, |b: u8| b & CONTINUATION_MASK != 0)).byte_len(vs) == vs.len(),
    decreases vs.len(),
{
    reveal(<Star<_> as SpecByteLen>::byte_len);
    if vs.len() == 0 {
    } else {
        let prefix = vs.drop_last();
        lemma_star_byte_len_seq_u8(prefix);
    }
}

proof fn lemma_star_parse_rec_from_scan(ibuf: Seq<u8>, n: int)
    requires
        0 < n <= ibuf.len(),
        ibuf[n - 1] & CONTINUATION_MASK == 0,
        forall|i: int| #![auto] 0 <= i < n - 1 ==> ibuf[i] & CONTINUATION_MASK != 0,
    ensures
        Star(Refined(U8, |b: u8| b & CONTINUATION_MASK != 0)).parse_rec(ibuf) == (
            n - 1,
            ibuf.take(n - 1),
        ),
    decreases n,
{
    if n > 1 {
        lemma_star_parse_rec_from_scan(ibuf.skip(1), (n - 1) as int);
    }
}

#[verifier::loop_isolation(false)]
fn scan_base128_bytes<'a, const MINIMAL: bool>(ibuf: &&'a [u8]) -> (out: PResult<&'a [u8]>)
    ensures
        out matches Ok((n, bytes)) ==> {
            let scanned = bytes.deep_view();
            &&& 0 < n <= BASE128_MAX_BYTES
            &&& n <= ibuf@.len()
            &&& scanned == ibuf@.take(n as int)
            &&& base128_fmt::<MINIMAL>().inner.spec_parse(ibuf@) == Some(
                (n as int, (scanned.drop_last(), scanned.last())),
            )
        },
        out is Err ==> base128_fmt::<MINIMAL>().inner.spec_parse(ibuf@) is None,
{
    let ghost fmt = base128_fmt::<MINIMAL>();
    let ghost star = Star(Refined(U8, |b: u8| b & CONTINUATION_MASK != 0));

    let mut i = 0usize;
    while i < ibuf.len()
        invariant
            i <= BASE128_MAX_BYTES,
            i <= ibuf@.len(),
            forall|j: int| #![auto] 0 <= j < i as int ==> ibuf@[j] & CONTINUATION_MASK != 0,
        decreases ibuf@.len() - i,
    {
        reveal(<Star<_> as SpecParser>::spec_parse);

        if i == BASE128_MAX_BYTES {
            proof {
                if fmt.inner.spec_parse(ibuf@) is Some {
                    fmt.inner.lemma_parse_safe(ibuf@);
                    let (n, (cont_bytes, term_byte)) = fmt.inner.spec_parse(ibuf@)->0;
                    star.lemma_parse_sound_consumption(ibuf@);
                    lemma_star_byte_len_seq_u8(cont_bytes);
                    assert(term_byte == ibuf@[n - 1]);
                    assert(term_byte & CONTINUATION_MASK == 0);
                    assert(term_byte & CONTINUATION_MASK != 0);
                }
            }
            return Err(ParseError::overflow());
        }
        let b = ibuf[i];
        i += 1;
        if b & CONTINUATION_MASK == 0 {
            let bytes = ibuf.take(i);
            if MINIMAL && i > 1 && (bytes[0] & PAYLOAD_MASK == 0) {
                return Err(ParseError::non_canonical());
            }
            proof {
                let scanned = bytes.deep_view();
                let (cont_bytes, term_byte) = (scanned.drop_last(), scanned.last());
                lemma_star_parse_rec_from_scan(ibuf@, i as int);
                assert(star.parse_rec(ibuf@) == (i - 1, cont_bytes));
                assert(fmt.inner.spec_parse(ibuf@) == Some((i as int, (cont_bytes, term_byte))));
            }
            return Ok((i, bytes));
        }
    }
    proof {
        if fmt.spec_parse(ibuf@) is Some {
            fmt.inner.lemma_parse_safe(ibuf@);
            let (n, (cont_bytes, term_byte)) = fmt.inner.spec_parse(ibuf@)->0;
            star.lemma_parse_sound_consumption(ibuf@);
            lemma_star_byte_len_seq_u8(cont_bytes);
            assert(term_byte == ibuf@[n - 1]);
            assert(term_byte & CONTINUATION_MASK == 0);
            assert(term_byte & CONTINUATION_MASK != 0);
        }
    }
    Err(ParseError::unexpected_eof())
}

pub fn uint_from_base128(bytes: &[u8]) -> (result: UInt)
    requires
        bytes.len() <= BASE128_MAX_BYTES,
    ensures
        result as nat == nat_from_base128(bytes.deep_view()),
{
    let n = bytes.len();
    let mut acc: UInt = 0;
    for i in 0..n
        invariant
            n == bytes.len(),
            n <= BASE128_MAX_BYTES,
            acc == nat_from_base128(bytes@.take(i as int)),
    {
        let b = bytes[i];
        proof {
            let prefix = bytes@.take(i as int);
            let current = prefix.push(b);
            assert(bytes@.take(i as int + 1) == current);
            assert(current.drop_last() == prefix);
            lemma_nat_from_base128_bounds(current);
            lemma_uint64_shl7_or_is_base128(acc, b);
        }
        acc = (acc << 7usize) | ((b & PAYLOAD_MASK) as UInt);
    }
    assert(bytes@.take(n as int) == bytes.deep_view());
    acc
}

pub fn uint_to_base128(v: UInt) -> (buf: Vec<u8>)
    ensures
        buf@ == nat_to_base128(v as nat),
    decreases v,
{
    if v < 128 {
        vec![v as u8]
    } else {
        proof {
            lemma_uint_shr7_is_div128(v);
            lemma_uint_low7_is_mod128(v);
        }
        let mut buf = uint_to_base128(v >> 7);
        buf.push((v & PAYLOAD_MASK as u64) as u8);
        buf
    }
}

pub fn uint_to_base128_len(v: UInt) -> (len: usize)
    ensures
        len == nat_to_base128(v as nat).len(),
{
    let mut cur = v;
    let mut len: usize = 1;
    while cur >= 128
        invariant
            len + nat_to_base128(cur as nat).len() == nat_to_base128(v as nat).len() + 1,
        decreases cur,
    {
        proof {
            lemma_uint_shr7_is_div128(cur);
            lemma_to_base128_len_bounds();
        }
        cur >>= 7;
        len += 1;
    }
    len
}

#[derive(Clone, Copy)]
pub struct Base128Fmt<const MINIMAL: bool = true>;

mod derived_specs {
    use super::*;

    impl<const MINIMAL: bool> SpecParser for Base128Fmt<MINIMAL> {
        type PVal = UInt;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            base128_fmt::<MINIMAL>().spec_parse(ibuf)
        }
    }

    impl<const MINIMAL: bool> Consistency for Base128Fmt<MINIMAL> {
        type Val = UInt;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            base128_fmt::<MINIMAL>().consistent(v)
        }
    }

    impl<const MINIMAL: bool> SpecSerializerDps for Base128Fmt<MINIMAL> {
        type SValue = UInt;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            base128_fmt::<MINIMAL>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const MINIMAL: bool> SpecSerializer for Base128Fmt<MINIMAL> {
        type SVal = UInt;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            base128_fmt::<MINIMAL>().spec_serialize(v)
        }
    }

    impl<const MINIMAL: bool> SpecByteLen for Base128Fmt<MINIMAL> {
        type T = UInt;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            base128_fmt::<MINIMAL>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const MINIMAL: bool> SafeParser for Base128Fmt<MINIMAL> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            base128_fmt::<MINIMAL>().lemma_parse_safe(ibuf);
        }
    }

    impl<const MINIMAL: bool> Productive for Base128Fmt<MINIMAL> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            base128_fmt::<MINIMAL>().lemma_productive(s);
        }
    }

    impl SoundParser for Base128Fmt<true> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            lemma_base128_fmt_sound_nonmal_inv();
            base128_fmt::<true>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            lemma_base128_fmt_sound_nonmal_inv();
            base128_fmt::<true>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const MINIMAL: bool> NonTailFmt for Base128Fmt<MINIMAL> {
        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            base128_fmt::<MINIMAL>().lemma_serialize_dps_prepend(v, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            base128_fmt::<MINIMAL>().lemma_serialize_dps_len(v, obuf);
        }
    }

    impl<const MINIMAL: bool> GoodSerializer for Base128Fmt<MINIMAL> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            base128_fmt::<MINIMAL>().lemma_serialize_len(v);
        }
    }

    impl<const MINIMAL: bool> SPRoundTripDps for Base128Fmt<MINIMAL> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            lemma_base128_fmt_unambiguous::<MINIMAL>();
            base128_fmt::<MINIMAL>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const MINIMAL: bool> NoLookAhead for Base128Fmt<MINIMAL> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            broadcast use disjointness_lemmas;

            base128_fmt::<MINIMAL>().lemma_no_lookahead(i1, i2);
        }
    }

    impl NonMalleable for Base128Fmt<true> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            lemma_base128_fmt_sound_nonmal_inv();
            base128_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const MINIMAL: bool> EquivSerializersGeneral for Base128Fmt<MINIMAL> {
        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            base128_fmt::<MINIMAL>().lemma_serialize_equiv(v, obuf);
        }
    }

    impl<const MINIMAL: bool> EquivSerializers for Base128Fmt<MINIMAL> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            base128_fmt::<MINIMAL>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<const MINIMAL: bool> Parser<&[u8]> for Base128Fmt<MINIMAL> {
    type PT = UInt;

    fn parse(&self, ibuf: &&[u8]) -> PResult<Self::PT> {
        let (n, bytes) = scan_base128_bytes::<MINIMAL>(ibuf)?;
        proof {
            let (_, (cont_bytes, term_byte)) = base128_fmt::<MINIMAL>().inner.spec_parse(ibuf@)->0;
            assert(cont_bytes.push(term_byte) == bytes.deep_view());
        }
        let value = uint_from_base128(bytes);
        Ok((n, value))
    }
}

impl<const MINIMAL: bool> Serializer<UInt> for Base128Fmt<MINIMAL> {
    fn serialize(&self, v: &UInt, obuf: &mut Vec<u8>) {
        let bytes = uint_to_base128(*v);
        let n = bytes.len();
        let ghost cont_bytes = bytes@.drop_last().map_values(|b: u8| b | CONTINUATION_MASK);
        for i in 0..n - 1
            invariant
                n == bytes.len(),
                cont_bytes.len() == n - 1,
                obuf@ == old(obuf)@ + cont_bytes.take(i as int),
                forall|j: int|
                    #![auto]
                    0 <= j < cont_bytes.len() ==> cont_bytes[j] == bytes@.drop_last()[j]
                        | CONTINUATION_MASK,
        {
            let b = bytes[i];
            obuf.push((b | CONTINUATION_MASK) as u8);
        }
        obuf.push(bytes[n - 1]);
        proof {
            lemma_star_serialize_seq_u8(cont_bytes);
        }
    }
}

impl<const MINIMAL: bool> ByteLen<UInt> for Base128Fmt<MINIMAL> {
    fn length(&self, v: &UInt) -> (len: usize) {
        let len = uint_to_base128_len(*v);
        proof {
            lemma_base128_fmt_byte_len::<MINIMAL>(*v);
        }
        len
    }
}

impl<const MINIMAL: bool> Prepare<UInt> for Base128Fmt<MINIMAL> {
    fn prepare(&self, v: &UInt) -> (checked: Result<usize, PreSerializeError>) {
        let len = uint_to_base128_len(*v);
        if len <= BASE128_MAX_BYTES {
            proof {
                lemma_base128_fmt_byte_len::<MINIMAL>(*v);
                lemma_base128_fmt_consistent::<MINIMAL>(*v);
            }
            Ok(len)
        } else {
            Err(PreSerializeError::length_too_large())
        }
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::exec::serializer::PreSerializeErrorKind;
    use crate::core::exec::{ByteLen, ParseErrorKind, Parser, Prepare, Serializer};

    #[test]
    fn base128_minimal_roundtrip_boundaries() {
        let fmt = Base128Fmt::<true>;

        let cases: &[(u64, &[u8])] = &[
            (0, &[0x00]),
            (1, &[0x01]),
            (127, &[0x7f]),
            (128, &[0x81, 0x00]),
            (16383, &[0xff, 0x7f]),
        ];

        for &(value, expected) in cases {
            let mut out = Vec::new();
            fmt.serialize(&value, &mut out);
            assert_eq!(out, expected);

            let parsed = fmt.parse(&&out[..]);
            assert_eq!(parsed, Ok((expected.len(), value)));

            let prepared = fmt.prepare(&value);
            assert_eq!(prepared, Ok(expected.len()));
            assert_eq!(fmt.length(&value), expected.len());
        }
    }

    #[test]
    fn base128_minimal_rejects_non_canonical_zero() {
        let input = [0x80, 0x00];

        let err = Base128Fmt::<true>.parse(&&input[..]).unwrap_err();
        assert_eq!(err.kind, ParseErrorKind::NonCanonical);

        let parsed = Base128Fmt::<false>.parse(&&input[..]);
        assert_eq!(parsed, Ok((2, 0)));
    }

    #[test]
    fn base128_distinguishes_unexpected_eof_from_overflow() {
        let eof = [0x80];
        let eof_err = Base128Fmt::<true>.parse(&&eof[..]).unwrap_err();
        assert_eq!(eof_err.kind, ParseErrorKind::UnexpectedEof);

        let overflow = [0x80; BASE128_MAX_BYTES + 1];
        let overflow_err = Base128Fmt::<true>.parse(&&overflow[..]).unwrap_err();
        assert_eq!(overflow_err.kind, ParseErrorKind::Overflow);
    }

    #[test]
    fn base128_prepare_rejects_values_needing_ten_bytes() {
        let fmt = Base128Fmt::<true>;
        let max_supported = (1u64 << 63) - 1;
        let too_large = 1u64 << 63;

        let mut out = Vec::new();
        fmt.serialize(&max_supported, &mut out);
        assert_eq!(out.len(), BASE128_MAX_BYTES);
        assert_eq!(fmt.prepare(&max_supported), Ok(BASE128_MAX_BYTES));
        assert_eq!(fmt.length(&max_supported), BASE128_MAX_BYTES);

        let len = fmt.length(&too_large);
        assert_eq!(len, BASE128_MAX_BYTES + 1);

        let err = fmt.prepare(&too_large).unwrap_err();
        assert_eq!(err.kind, PreSerializeErrorKind::LengthTooLarge);
    }
}
