use super::base256::*;
use crate::{
    combinators::{
        implicit::*,
        length::AsLen,
        mapped::spec::{LosslessMapper, LossyMapper, SpecMapper},
        Alt, Implicit, Mapped, Refined, TryMap, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::power::*;
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
    Refined(
        len_prefixed_bytes(),
        |bytes: Seq<u8>|
            {
                // by `inner.consistent(bytes)` we already know:
                // 0 < bytes.len() <= LONG_FORM_MAX_COUNT
                if DER {
                    der_long_len_bytes_minimal(bytes)
                } else {
                    true
                }
            },
    )
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

pub proof fn lemma_long_len_bytes_consistent(bytes: Seq<u8>)
    requires
        LONG_FORM_MIN_COUNT as nat <= bytes.len() <= LONG_FORM_MAX_COUNT as nat,
    ensures
        len_prefixed_bytes().consistent(bytes),
{
    NBytesMasks.lemma_mapper_wf_out_in(bytes.len() as u8);
}

pub proof fn lemma_der_minimal_sufficient(bytes: Seq<u8>)
    requires
        len_prefixed_bytes().consistent(bytes),
        der_long_len_bytes_minimal(bytes),
    ensures
        SHORT_FORM_MAX < nat_from_be_bytes(bytes),
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
        der_long_len_bytes_minimal(nat_to_be_bytes(n)),
{
    if nat_to_be_bytes(n).len() == 1 {
        assert(nat_to_be_bytes(n) == seq![nat_to_be_bytes(n)[0]]);
        lemma_to_from_be_bytes_roundtrip(n);
        lemma_from_be_bytes_singleton(nat_to_be_bytes(n)[0]);
    } else {
        lemma_to_be_bytes_props(n);
    }
}

impl SpecMapper for NatFromToU8 {
    type In = u8;

    type Out = nat;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        i <= SHORT_FORM_MAX
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= SHORT_FORM_MAX
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as nat
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u8
    }
}

impl LossyMapper for NatFromToU8 {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for NatFromToU8 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

impl SpecMapper for NBytesMasks {
    type In = u8;

    type Out = u8;

    /// 8.1.3.5 In the long form, the length octets shall consist of an initial octet and **one or more** subsequent octets. The initial
    /// octet shall be encoded as follows:
    ///
    /// a) bit 8 shall be one;
    /// b) bits 7 to 1 shall encode the number of subsequent octets in the length octets, as an unsigned binary integer with
    /// bit 7 as the most significant bit;
    /// c) the value 11111111 shall not be used.
    open spec fn wf_in(&self, i: Self::In) -> bool {
        0b1000_0000 < i < 0b1111_1111
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        LONG_FORM_MIN_COUNT <= o <= LONG_FORM_MAX_COUNT
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        // clear the high bit to get the count
        i & 0b0111_1111
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        // set the high bit to indicate long form
        0b1000_0000 | o
    }
}

impl LossyMapper for NBytesMasks {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        assert(self.spec_map(self.spec_map_rev(o)) == o) by (bit_vector)
            requires
                self.wf_out(o),
        ;
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        assert(self.wf_in(self.spec_map_rev(o))) by (bit_vector)
            requires
                self.wf_out(o),
        ;
    }
}

impl LosslessMapper for NBytesMasks {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        assert(self.spec_map_rev(self.spec_map(i)) == i) by (bit_vector)
            requires
                self.wf_in(i),
        ;
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
        assert(self.wf_out(self.spec_map(i))) by (bit_vector)
            requires
                self.wf_in(i),
        ;
    }
}

impl<const DER: bool> SpecMapper for NatFromToBytes<DER> {
    type In = Seq<u8>;

    type Out = nat;

    open spec fn wf_in(&self, bytes: Self::In) -> bool {
        long_len_bytes::<DER>().consistent(bytes)
    }

    open spec fn wf_out(&self, v: Self::Out) -> bool {
        // the largest representable length is (2^8)^LEN_FORM_MAX_COUNT - 1
        &&& v < pow(256, LONG_FORM_MAX_COUNT as nat)
        &&& if DER {
            // DER requires minimality
            SHORT_FORM_MAX < v
        } else {
            true
        }
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        nat_from_be_bytes(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        nat_to_be_bytes(o)
    }
}

impl<const DER: bool> LossyMapper for NatFromToBytes<DER> {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_to_from_be_bytes_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        lemma_to_be_bytes_len_bound(o, LONG_FORM_MAX_COUNT as nat);
        lemma_long_len_bytes_consistent(nat_to_be_bytes(o));
        if DER {
            lemma_to_be_bytes_minimal(o);
        }
    }
}

impl LosslessMapper for NatFromToBytes<true> {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_from_to_be_bytes_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
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
    type SValue = nat;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
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
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        length_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
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
