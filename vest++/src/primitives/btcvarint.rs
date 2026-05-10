use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::{Alt, Mapped, Refined, Tagged, U16Le, U32Le, U64Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/*
// =============================================================================
// Bitcoin VarInt
// =============================================================================
//
// Real Bitcoin VarInt uses four wire forms:
// - [0x00 ..= 0xFC]                                => value directly
// - 0xFD ++ u16le                                  => values up to 0xFFFF
// - 0xFE ++ u32le                                  => values up to 0xFFFF_FFFF
// - 0xFF ++ u64le                                  => values above 0xFFFF_FFFF
*/
pub const VARINT_TAG_U16: u8 = 0xFDu8;

pub const VARINT_TAG_U32: u8 = 0xFEu8;

pub const VARINT_TAG_U64: u8 = 0xFFu8;

pub type VarIntFmt<const MINIMAL: bool> = Alt<
    VarIntU8Form,
    Alt<VarIntU16Form<MINIMAL>, Alt<VarIntU32Form<MINIMAL>, VarIntU64Form<MINIMAL>>>,
>;

pub type VarIntU8Form = Mapped<Refined<U8, PredFnSpec<u8>>, U8AsU64>;

pub type VarIntU16Form<const MINIMAL: bool> = Tagged<
    U8,
    Mapped<Refined<U16Le, PredFnSpec<u16>>, U16FromToU64>,
>;

pub type VarIntU32Form<const MINIMAL: bool> = Tagged<
    U8,
    Mapped<Refined<U32Le, PredFnSpec<u32>>, U32FromToU64>,
>;

pub type VarIntU64Form<const MINIMAL: bool> = Tagged<U8, Refined<U64Le, PredFnSpec<u64>>>;

pub open spec fn varint_fmt<const MINIMAL: bool>() -> VarIntFmt<MINIMAL> {
    Alt(
        varint_u8_form(),
        Alt(
            varint_u16_form::<MINIMAL>(),
            Alt(varint_u32_form::<MINIMAL>(), varint_u64_form::<MINIMAL>()),
        ),
    )
}

pub open spec fn varint_u8_form() -> VarIntU8Form {
    Mapped { inner: Refined(U8, |v: u8| v < VARINT_TAG_U16), mapper: U8AsU64 }
}

pub open spec fn varint_u16_form<const MINIMAL: bool>() -> VarIntU16Form<MINIMAL> {
    Tagged(
        U8,
        VARINT_TAG_U16,
        Mapped {
            inner: Refined(U16Le, |v: u16| MINIMAL ==> VARINT_TAG_U16 <= v),
            mapper: U16FromToU64,
        },
    )
}

pub open spec fn varint_u32_form<const MINIMAL: bool>() -> VarIntU32Form<MINIMAL> {
    Tagged(
        U8,
        VARINT_TAG_U32,
        Mapped { inner: Refined(U32Le, |v: u32| MINIMAL ==> u16::MAX < v), mapper: U32FromToU64 },
    )
}

pub open spec fn varint_u64_form<const MINIMAL: bool>() -> VarIntU64Form<MINIMAL> {
    Tagged(U8, VARINT_TAG_U64, Refined(U64Le, |v: u64| MINIMAL ==> u32::MAX < v))
}

pub struct U8AsU64;

impl SpecMapper for U8AsU64 {
    type In = u8;

    type Out = u64;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u64
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= u8::MAX
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u8
    }
}

impl LossyMapper for U8AsU64 {
    proof fn lemma_sound_mapper(&self, _o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for U8AsU64 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, _i: Self::In) {
    }
}

pub struct U16FromToU64;

impl SpecMapper for U16FromToU64 {
    type In = u16;

    type Out = u64;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u64
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= u16::MAX
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u16
    }
}

impl LossyMapper for U16FromToU64 {
    proof fn lemma_sound_mapper(&self, _o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for U16FromToU64 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, _i: Self::In) {
    }
}

pub struct U32FromToU64;

impl SpecMapper for U32FromToU64 {
    type In = u32;

    type Out = u64;

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as u64
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o <= u32::MAX
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u32
    }
}

impl LossyMapper for U32FromToU64 {
    proof fn lemma_sound_mapper(&self, _o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, _o: Self::Out) {
    }
}

impl LosslessMapper for U32FromToU64 {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, _i: Self::In) {
    }
}

pub struct VarInt<const MINIMAL: bool>;

impl<const MINIMAL: bool> SpecParser for VarInt<MINIMAL> {
    type PVal = u64;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        varint_fmt::<MINIMAL>().spec_parse(ibuf)
    }
}

impl<const MINIMAL: bool> Consistency for VarInt<MINIMAL> {
    type Val = u64;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        varint_fmt::<MINIMAL>().consistent(v)
    }
}

impl<const MINIMAL: bool> SafeParser for VarInt<MINIMAL> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        varint_fmt::<MINIMAL>().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for VarInt<true> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        varint_fmt::<true>().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        varint_fmt::<true>().lemma_parse_sound_value(ibuf);
    }
}

impl<const MINIMAL: bool> SpecSerializerDps for VarInt<MINIMAL> {
    type SValue = u64;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        varint_fmt::<MINIMAL>().spec_serialize_dps(v, obuf)
    }
}

impl<const MINIMAL: bool> SpecSerializer for VarInt<MINIMAL> {
    type SVal = u64;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        varint_fmt::<MINIMAL>().spec_serialize(v)
    }
}

impl<const MINIMAL: bool> NonTailFmt for VarInt<MINIMAL> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        varint_fmt::<MINIMAL>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        varint_fmt::<MINIMAL>().lemma_serialize_dps_len(v, obuf);
    }
}

impl<const MINIMAL: bool> GoodSerializer for VarInt<MINIMAL> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        varint_fmt::<MINIMAL>().lemma_serialize_len(v);
    }
}

impl<const MINIMAL: bool> SpecByteLen for VarInt<MINIMAL> {
    type T = u64;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        varint_fmt::<MINIMAL>().byte_len(v)
    }
}

impl<const MINIMAL: bool> SPRoundTripDps for VarInt<MINIMAL> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        varint_fmt::<MINIMAL>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const MINIMAL: bool> NoLookAhead for VarInt<MINIMAL> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        varint_fmt::<MINIMAL>().lemma_no_lookahead(i1, i2);
    }
}

impl NonMalleable for VarInt<true> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        varint_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const MINIMAL: bool> EquivSerializersGeneral for VarInt<MINIMAL> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        varint_fmt::<MINIMAL>().lemma_serialize_equiv(v, obuf);
    }
}

impl<const MINIMAL: bool> EquivSerializers for VarInt<MINIMAL> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        varint_fmt::<MINIMAL>().lemma_serialize_equiv_on_empty(v);
    }
}

proof fn test_varint_roundtrip() {
    let fmt = VarInt::<true>;
    let v_u8 = 100u64;
    let v_u16 = VARINT_TAG_U16 as u64;
    let v_u32 = 0x1_0000u64;
    let v_u64 = 0x1_0000_0000u64;

    assert(fmt.consistent(v_u8));
    assert(fmt.consistent(v_u16));
    assert(fmt.consistent(v_u32));
    assert(fmt.consistent(v_u64));

    fmt.theorem_serialize_parse_roundtrip(v_u8);
    fmt.theorem_serialize_parse_roundtrip(v_u16);
    fmt.theorem_serialize_parse_roundtrip(v_u32);
    fmt.theorem_serialize_parse_roundtrip(v_u64);
}

} // verus!
