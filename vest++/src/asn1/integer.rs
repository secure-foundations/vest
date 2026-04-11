use super::base256::{
    lemma_from_be_bytes_prepend, lemma_from_be_bytes_push, lemma_from_be_bytes_singleton,
    lemma_from_be_bytes_upper_bound, lemma_from_to_be_bytes_roundtrip, lemma_pow256_succ,
    lemma_to_be_bytes_props, lemma_to_from_be_bytes_roundtrip, nat_from_be_bytes, nat_to_be_bytes,
};
use crate::{
    combinators::{
        bytes::Varied,
        length::AsLen,
        mapped::spec::{LosslessMapper, LossyMapper, Mapper},
        TryMap,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::power::{lemma_pow0, pow};
use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

pub struct IntFromToBytes;

pub type IntegerFmt<Len> = TryMap<Varied<Len>, IntFromToBytes>;

pub open spec fn integer_fmt<Len: AsLen>(len: Len) -> IntegerFmt<Len> {
    TryMap { inner: Varied(len), mapper: IntFromToBytes }
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

impl Mapper for IntFromToBytes {
    type In = Seq<u8>;

    type Out = int;

    open spec fn wf_in(i: Self::In) -> bool {
        integer_bytes_wf(i)
    }

    open spec fn wf_out(_o: Self::Out) -> bool {
        true
    }

    open spec fn spec_map(i: Self::In) -> Self::Out {
        int_from_be_bytes(i)
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        int_to_be_bytes(o)
    }
}

impl LossyMapper for IntFromToBytes {
    proof fn lemma_sound_mapper(o: Self::Out) {
        if o >= 0 {
            let n = o as nat;
            let body = nat_to_be_bytes(n);
            lemma_to_from_be_bytes_roundtrip(n);
            if sign_bit_set(body[0]) {
                lemma_from_be_bytes_prepend(body, 0x00u8);
            }
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
        }
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
        if o >= 0 {
            let n = o as nat;
            lemma_to_be_bytes_props(n);
        } else {
            let n = (-1 - o) as nat;
            lemma_to_be_bytes_props(n);
            lemma_invert_byte_props(nat_to_be_bytes(n)[0]);
        }
    }
}

impl LosslessMapper for IntFromToBytes {
    proof fn lemma_lossless_mapper(i: Self::In) {
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

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

impl<Len: AsLen> SpecParser for super::Integer<Len> {
    type PVal = int;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        integer_fmt(self.0).spec_parse(ibuf)
    }
}

impl<Len: AsLen> Consistency for super::Integer<Len> {
    type Val = int;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        integer_fmt(self.0).consistent(v)
    }
}

impl<Len: AsLen> SafeParser for super::Integer<Len> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        integer_fmt(self.0).lemma_parse_safe(ibuf);
    }
}

impl<Len: AsLen> SoundParser for super::Integer<Len> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        integer_fmt(self.0).lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        integer_fmt(self.0).lemma_parse_sound_value(ibuf);
    }
}

impl<Len: AsLen> SpecSerializerDps for super::Integer<Len> {
    type ST = int;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        integer_fmt(self.0).spec_serialize_dps(v, obuf)
    }
}

impl<Len: AsLen> SpecSerializer for super::Integer<Len> {
    type SVal = int;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        integer_fmt(self.0).spec_serialize(v)
    }
}

impl<Len: AsLen> NonTailFmt for super::Integer<Len> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        integer_fmt(self.0).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        integer_fmt(self.0).lemma_serialize_dps_len(v, obuf);
    }
}

impl<Len: AsLen> GoodSerializer for super::Integer<Len> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        integer_fmt(self.0).lemma_serialize_len(v);
    }
}

impl<Len: AsLen> SpecByteLen for super::Integer<Len> {
    type T = int;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        integer_fmt(self.0).byte_len(v)
    }
}

impl<Len: AsLen> ValueByteLen for super::Integer<Len> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        IntegerFmt::<Len>::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        integer_fmt(self.0).lemma_value_len_matches_byte_len(v);
    }
}

impl<Len: AsLen> SPRoundTripDps for super::Integer<Len> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        integer_fmt(self.0).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Len: AsLen> NoLookAhead for super::Integer<Len> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        integer_fmt(self.0).lemma_no_lookahead(i1, i2);
    }
}

impl<Len: AsLen> NonMalleable for super::Integer<Len> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        integer_fmt(self.0).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Len: AsLen> EquivSerializersGeneral for super::Integer<Len> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        integer_fmt(self.0).lemma_serialize_equiv(v, obuf);
    }
}

impl<Len: AsLen> EquivSerializers for super::Integer<Len> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        integer_fmt(self.0).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
