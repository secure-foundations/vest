use crate::{
    combinators::{
        implicit::{VLData, VariedLen},
        length::AsLen,
        mapped::spec::{LosslessMapper, LossyMapper, Mapper},
        Alt, Implicit, Mapped, Refined, TryMap, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::{
    div_mod::{
        lemma_div_decreases, lemma_div_non_zero, lemma_fundamental_div_mod,
        lemma_fundamental_div_mod_converse, lemma_mod_bound,
    },
    power::{
        lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_increases,
        lemma_pow_strictly_increases_converse, pow,
    },
};
use vstd::prelude::*;

verus! {

pub const SHORT_FORM_MAX: u8 = 0x7F;

pub const LONG_FORM_MIN_COUNT: u8 = 1;

pub const LONG_FORM_MAX_COUNT: u8 = 126;

pub type LengthFmt<const DER: bool> = Alt<ShortLenFmt, LongLenFmt<DER>>;

pub type ShortLenFmt = TryMap<U8, NatFromToU8>;

pub struct NatFromToU8;

pub type LongLenFmt<const DER: bool> = Mapped<LongLenBytes<DER>, NatFromToBytes<DER>>;

pub type LongLenBytes<const DER: bool> = Refined<LenPrefixedBytes, PredFnSpec<Seq<u8>>>;

pub type LenPrefixedBytes = Implicit<NBytes, VariedLen>;

pub type NBytes = TryMap<U8, NBytesMasks>;

pub struct NBytesMasks;

pub struct NatFromToBytes<const DER: bool>;

pub open spec fn length_fmt<const DER: bool>() -> LengthFmt<DER> {
    Alt(short_len_fmt(), long_len_fmt::<DER>())
}

pub open spec fn short_len_fmt() -> ShortLenFmt {
    TryMap { inner: U8, mapper: NatFromToU8 }
}

pub open spec fn long_len_fmt<const DER: bool>() -> LongLenFmt<DER> {
    Mapped { inner: long_len_bytes::<DER>(), mapper: NatFromToBytes::<DER> }
}

pub open spec fn long_len_bytes<const DER: bool>() -> LongLenBytes<DER> {
    Refined {
        inner: len_prefixed_bytes(),
        pred: |bytes: Seq<u8>|
            {
                // by `inner.consistent(bytes)` we already know:
                // 0 < bytes.len() <= LONG_FORM_MAX_COUNT
                if DER {
                    der_long_len_bytes_minimal(bytes)
                } else {
                    true
                }
            },
    }
}

pub open spec fn len_prefixed_bytes() -> LenPrefixedBytes {
    Implicit(TryMap { inner: U8, mapper: NBytesMasks }, VLData())
}

pub open spec fn der_long_len_bytes_minimal(bytes: Seq<u8>) -> bool {
    // DER requires minimality, so
    // 1. for single-byte length in the long form, the value must be > 127 (i.e. not encodable in short form)
    // 2. for multi-byte length in the long form, the first byte must be non-zero (i.e. no leading zeros)
    &&& bytes.len() == 1 ==> bytes[0] > SHORT_FORM_MAX
    &&& bytes.len() > 1 ==> bytes[0] != 0x00u8
}

pub open spec fn from_be_bytes(bytes: Seq<u8>) -> nat
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        from_be_bytes(bytes.drop_last()) * 256 + bytes.last() as nat
    }
}

pub open spec fn to_be_bytes(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 256 {
        seq![n as u8]
    } else {
        to_be_bytes((n / 256) as nat).push((n % 256) as u8)
    }
}

pub proof fn lemma_from_be_bytes_singleton(b: u8)
    ensures
        from_be_bytes(seq![b]) == (b as nat),
{
    assert(Seq::<u8>::empty() == Seq::<u8>::empty().push(b).drop_last());
    assert(from_be_bytes(seq![b]) == from_be_bytes(seq![]) * 256 + b as nat);
}

pub proof fn lemma_pow256_succ(exp: nat)
    ensures
        pow(256, exp + 1) == pow(256, exp) * 256,
{
    lemma_pow_adds(256, exp, 1);
    lemma_pow1(256);
}

pub proof fn lemma_from_be_bytes_upper_bound(bytes: Seq<u8>)
    ensures
        from_be_bytes(bytes) < pow(256, bytes.len()),
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_be_bytes_upper_bound(prefix);
        lemma_pow256_succ(prefix.len());
    }
}

pub proof fn lemma_from_be_bytes_lower_bound(bytes: Seq<u8>)
    requires
        bytes.len() > 0,
        bytes[0] != 0,
    ensures
        pow(256, (bytes.len() - 1) as nat) <= from_be_bytes(bytes),
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        lemma_pow0(256);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_be_bytes_lower_bound(prefix);
        lemma_pow256_succ((prefix.len() - 1) as nat);
    }
}

pub proof fn lemma_to_be_bytes_props(n: nat)
    ensures
        to_be_bytes(n).len() > 0,
        n > 0 ==> to_be_bytes(n)[0] != 0,
        n > 0 ==> pow(256, (to_be_bytes(n).len() - 1) as nat) <= n,
    decreases n,
{
    if n < 256 {
        lemma_pow0(256);
    } else {
        let q = (n / 256) as nat;
        lemma_to_be_bytes_props(q);
        lemma_pow256_succ((to_be_bytes(q).len() - 1) as nat);
    }
}

pub proof fn lemma_to_be_bytes_len_bound(n: nat, max_len: nat)
    requires
        0 < max_len,
        n < pow(256, max_len),
    ensures
        to_be_bytes(n).len() <= max_len,
{
    if n == 0 {
    } else {
        lemma_to_be_bytes_props(n);
        // b^e1 < b^e2 ==> e1 < e2
        lemma_pow_strictly_increases_converse(256, (to_be_bytes(n).len() - 1) as nat, max_len);
    }
}

pub proof fn lemma_to_from_be_bytes_roundtrip(n: nat)
    ensures
        from_be_bytes(to_be_bytes(n)) == n,
    decreases n,
{
    if n < 256 {
        lemma_from_be_bytes_singleton(n as u8);
    } else {
        let q = (n / 256) as nat;
        let r = (n % 256) as nat;
        lemma_to_from_be_bytes_roundtrip(q);
        assert(to_be_bytes(q).push(r as u8).drop_last() == to_be_bytes(q));
    }
}

pub proof fn lemma_from_to_be_bytes_roundtrip(bytes: Seq<u8>)
    requires
        bytes.len() > 0,
        bytes.len() > 1 ==> bytes[0] != 0,
    ensures
        to_be_bytes(from_be_bytes(bytes)) == bytes,
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        lemma_from_be_bytes_singleton(bytes[0]);
        assert(bytes == seq![bytes[0]]);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_to_be_bytes_roundtrip(prefix);
    }
}

pub proof fn lemma_long_len_bytes_consistent(bytes: Seq<u8>)
    requires
        LONG_FORM_MIN_COUNT as nat <= bytes.len() <= LONG_FORM_MAX_COUNT as nat,
    ensures
        len_prefixed_bytes().consistent(bytes),
{
    NBytesMasks::lemma_mapper_wf_out_in(bytes.len() as u8);
}

pub proof fn lemma_der_minimal_sufficient(bytes: Seq<u8>)
    requires
        len_prefixed_bytes().consistent(bytes),
        der_long_len_bytes_minimal(bytes),
    ensures
        SHORT_FORM_MAX < from_be_bytes(bytes),
{
    if bytes.len() == 1 {
        assert(bytes == seq![bytes[0]]);
        lemma_from_be_bytes_singleton(bytes[0]);
    } else {
        lemma_from_be_bytes_lower_bound(bytes);
        lemma_pow1(256);
        lemma_pow_increases(256, 1, (bytes.len() - 1) as nat);
    }
}

pub proof fn lemma_to_be_bytes_minimal(n: nat)
    requires
        SHORT_FORM_MAX < n,
    ensures
        der_long_len_bytes_minimal(to_be_bytes(n)),
{
    if to_be_bytes(n).len() == 1 {
        assert(to_be_bytes(n) == seq![to_be_bytes(n)[0]]);
        lemma_to_from_be_bytes_roundtrip(n);
        lemma_from_be_bytes_singleton(to_be_bytes(n)[0]);
    } else {
        lemma_to_be_bytes_props(n);
    }
}

impl Mapper for NatFromToU8 {
    type In = u8;

    type Out = nat;

    open spec fn wf_in(i: Self::In) -> bool {
        i <= SHORT_FORM_MAX
    }

    open spec fn wf_out(o: Self::Out) -> bool {
        o <= SHORT_FORM_MAX
    }

    open spec fn spec_map(i: Self::In) -> Self::Out {
        i as nat
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        o as u8
    }
}

impl LossyMapper for NatFromToU8 {
    proof fn lemma_sound_mapper(o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
    }
}

impl LosslessMapper for NatFromToU8 {
    proof fn lemma_lossless_mapper(i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

impl Mapper for NBytesMasks {
    type In = u8;

    type Out = u8;

    /// 8.1.3.5 In the long form, the length octets shall consist of an initial octet and **one or more** subsequent octets. The initial
    /// octet shall be encoded as follows:
    ///
    /// a) bit 8 shall be one;
    /// b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
    /// bit 7 as the most significant bit;
    /// c) the value 11111111 shall not be used.
    open spec fn wf_in(i: Self::In) -> bool {
        0b1000_0000 < i < 0b1111_1111
    }

    open spec fn wf_out(o: Self::Out) -> bool {
        LONG_FORM_MIN_COUNT <= o <= LONG_FORM_MAX_COUNT
    }

    open spec fn spec_map(i: Self::In) -> Self::Out {
        // clear the high bit to get the count
        i & 0b0111_1111
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        // set the high bit to indicate long form
        0b1000_0000 | o
    }
}

impl LossyMapper for NBytesMasks {
    proof fn lemma_sound_mapper(o: Self::Out) {
        assert(Self::spec_map(Self::spec_map_rev(o)) == o) by (bit_vector)
            requires
                Self::wf_out(o),
        ;
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
        assert(Self::wf_in(Self::spec_map_rev(o))) by (bit_vector)
            requires
                Self::wf_out(o),
        ;
    }
}

impl LosslessMapper for NBytesMasks {
    proof fn lemma_lossless_mapper(i: Self::In) {
        assert(Self::spec_map_rev(Self::spec_map(i)) == i) by (bit_vector)
            requires
                Self::wf_in(i),
        ;
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
        assert(Self::wf_out(Self::spec_map(i))) by (bit_vector)
            requires
                Self::wf_in(i),
        ;
    }
}

impl<const DER: bool> Mapper for NatFromToBytes<DER> {
    type In = Seq<u8>;

    type Out = nat;

    open spec fn wf_in(bytes: Self::In) -> bool {
        long_len_bytes::<DER>().consistent(bytes)
    }

    open spec fn wf_out(v: Self::Out) -> bool {
        // the largest representable length is (2^8)^LEN_FORM_MAX_COUNT - 1
        &&& v < pow(256, LONG_FORM_MAX_COUNT as nat)
        &&& if DER {
            // DER requires minimality
            SHORT_FORM_MAX < v
        } else {
            true
        }
    }

    open spec fn spec_map(i: Self::In) -> Self::Out {
        from_be_bytes(i)
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        to_be_bytes(o)
    }
}

impl<const DER: bool> LossyMapper for NatFromToBytes<DER> {
    proof fn lemma_sound_mapper(o: Self::Out) {
        lemma_to_from_be_bytes_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
        lemma_to_be_bytes_len_bound(o, LONG_FORM_MAX_COUNT as nat);
        lemma_long_len_bytes_consistent(to_be_bytes(o));
        if DER {
            lemma_to_be_bytes_minimal(o);
        }
    }
}

impl LosslessMapper for NatFromToBytes<true> {
    proof fn lemma_lossless_mapper(i: Self::In) {
        lemma_from_to_be_bytes_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
        lemma_from_be_bytes_upper_bound(i);
        lemma_pow_increases(256, i.len(), LONG_FORM_MAX_COUNT as nat);
        lemma_der_minimal_sufficient(i);
    }
}

impl<const DER: bool> SpecParser for super::Length<DER> {
    type PVal = nat;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        length_fmt::<DER>().spec_parse(ibuf)
    }
}

impl<const DER: bool> Consistency for super::Length<DER> {
    type Val = nat;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        length_fmt::<DER>().consistent(v)
    }
}

impl<const DER: bool> SafeParser for super::Length<DER> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        length_fmt::<DER>().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for super::Length<true> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        length_fmt::<true>().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        length_fmt::<true>().lemma_parse_sound_value(ibuf);
    }
}

impl<const DER: bool> SpecSerializerDps for super::Length<DER> {
    type ST = nat;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        length_fmt::<DER>().spec_serialize_dps(v, obuf)
    }
}

impl<const DER: bool> SpecSerializer for super::Length<DER> {
    type SVal = nat;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        length_fmt::<DER>().spec_serialize(v)
    }
}

impl<const DER: bool> NonTailFmt for super::Length<DER> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        length_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
    }
}

impl<const DER: bool> GoodSerializer for super::Length<DER> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        length_fmt::<DER>().lemma_serialize_len(v);
    }
}

impl<const DER: bool> SpecByteLen for super::Length<DER> {
    type T = nat;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        length_fmt::<DER>().byte_len(v)
    }
}

impl<const DER: bool> SPRoundTripDps for super::Length<DER> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        length_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const DER: bool> NoLookAhead for super::Length<DER> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        length_fmt::<DER>().lemma_no_lookahead(i1, i2);
    }
}

impl NonMalleable for super::Length<true> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        length_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const DER: bool> EquivSerializersGeneral for super::Length<DER> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        length_fmt::<DER>().lemma_serialize_equiv(v, obuf);
    }
}

impl<const DER: bool> EquivSerializers for super::Length<DER> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        length_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
