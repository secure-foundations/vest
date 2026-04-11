use crate::{
    combinators::{
        implicit::{VLData, VariedLen},
        mapped::spec::{LosslessMapper, LossyMapper, Mapper},
        Alt, Implicit, Mapped, Refined, TryMap, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::assert_seqs_equal;
use vstd::endian::{base_upper_bound_excl, endianness, Base, Endian, EndianNat};
use vstd::prelude::*;
use vstd::{
    arithmetic::power::{lemma_pow1, pow},
    pervasive::arbitrary,
};

verus! {

pub const SHORT_FORM_MAX: u8 = 0x7F;

pub const LONG_FORM_MIN_COUNT: u8 = 1;

pub const LONG_FORM_MAX_COUNT: u8 = 126;

pub type LengthFmt<const DER: bool> = Alt<ShortLenFmt, LongLenFmt<DER>>;

pub type ShortLenFmt = TryMap<U8, ShortLenMapper>;

pub struct ShortLenMapper;

pub type LongLenFmt<const DER: bool> = Mapped<LongLenInner<DER>, LongLenMapper<DER>>;

pub type LongLenInner<const DER: bool> = Refined<LongLenBytes, PredFnSpec<Seq<u8>>>;

pub type LongLenBytes = Implicit<BytesCount, VariedLen>;

pub type BytesCount = TryMap<U8, CountMapper>;

pub struct CountMapper;

pub struct LongLenMapper<const DER: bool>;

pub open spec fn length_fmt<const DER: bool>() -> LengthFmt<DER> {
    Alt(short_len_fmt(), long_len_fmt::<DER>())
}

pub open spec fn short_len_fmt() -> ShortLenFmt {
    TryMap { inner: U8, mapper: ShortLenMapper }
}

pub open spec fn long_len_fmt<const DER: bool>() -> LongLenFmt<DER> {
    Mapped { inner: long_len_inner::<DER>(), mapper: LongLenMapper::<DER> }
}

pub open spec fn long_len_inner<const DER: bool>() -> LongLenInner<DER> {
    Refined {
        inner: Implicit(TryMap { inner: U8, mapper: CountMapper }, VLData()),
        pred: |bytes: Seq<u8>|
            {
                // by `inner.consistent(bytes)` we already know:
                // 0 < bytes.len() <= 126
                if DER {
                    // DER requires minimality, so
                    // 1. for single-byte length in the long form, the value must be > 127 (i.e. not encodable in short form)
                    // 2. for multi-byte length in the long form, the first byte must be non-zero (i.e. no leading zeros)
                    &&& bytes.len() == 1 ==> bytes[0] > SHORT_FORM_MAX
                    &&& bytes.len() > 1 ==> bytes[0] != 0x00u8
                } else {
                    true
                }
            },
    }
}

pub open spec fn be_nat(bytes: Seq<u8>) -> nat {
    arbitrary()
}

pub open spec fn nat_be_bytes(n: nat) -> Seq<u8> {
    arbitrary()
}

impl Mapper for ShortLenMapper {
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

impl LossyMapper for ShortLenMapper {
    proof fn lemma_sound_mapper(o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
    }
}

impl LosslessMapper for ShortLenMapper {
    proof fn lemma_lossless_mapper(i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

impl Mapper for CountMapper {
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

impl LossyMapper for CountMapper {
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

impl LosslessMapper for CountMapper {
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

impl<const DER: bool> Mapper for LongLenMapper<DER> {
    type In = Seq<u8>;

    type Out = nat;

    open spec fn wf_in(bytes: Self::In) -> bool {
        long_len_inner::<DER>().consistent(bytes)
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
        be_nat(i)
    }

    open spec fn spec_map_rev(o: Self::Out) -> Self::In {
        nat_be_bytes(o)
    }
}

impl<const DER: bool> LossyMapper for LongLenMapper<DER> {
    proof fn lemma_sound_mapper(o: Self::Out) {
        admit()
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
        admit()
    }
}

impl LosslessMapper for LongLenMapper<true> {
    proof fn lemma_lossless_mapper(i: Self::In) {
        admit()
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
        admit()
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
