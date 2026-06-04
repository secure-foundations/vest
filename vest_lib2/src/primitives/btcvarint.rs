use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, SpecMapper};
use crate::combinators::{Alt, Mapped, PrefixTagged, Refined, U16Le, U32Le, U64Le, U8};
use crate::core::exec::input::{InputBuf, InputSlice};
use crate::core::{exec::*, proof::*, spec::*};
use vstd::prelude::*;

use PrefixTagged as Tagged;
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

mod bitcoin_varint_derived_specs {
    use super::*;

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

    impl<const MINIMAL: bool> SpecByteLen for VarInt<MINIMAL> {
        type T = u64;

        open spec fn byte_len(&self, v: Self::T) -> nat {
            varint_fmt::<MINIMAL>().byte_len(v)
        }
    }

}

mod bitcoin_varint_derived_proofs {
    use super::*;

    impl<const MINIMAL: bool> SafeParser for VarInt<MINIMAL> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            varint_fmt::<MINIMAL>().lemma_parse_safe(ibuf);
        }
    }

    impl<const MINIMAL: bool> Productive for VarInt<MINIMAL> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            varint_fmt::<MINIMAL>().lemma_productive(s);
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

    impl<const MINIMAL: bool> MinMaxByteLen for VarInt<MINIMAL> {
        open spec fn min(&self) -> nat {
            varint_fmt::<MINIMAL>().min()
        }

        open spec fn max(&self) -> nat {
            varint_fmt::<MINIMAL>().max()
        }

        proof fn lemma_min_max_byte_len(&self, v: Self::T) {
            varint_fmt::<MINIMAL>().lemma_min_max_byte_len(v);
        }
    }

    impl<const MINIMAL: bool> SPRoundTripDps for VarInt<MINIMAL> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            assert(varint_fmt::<MINIMAL>().unambiguous()) by {
                reveal(disjoint_domains);
            }
            varint_fmt::<MINIMAL>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const MINIMAL: bool> NoLookAhead for VarInt<MINIMAL> {
        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            assert(varint_fmt::<MINIMAL>().no_lookahead_inv()) by {
                reveal(disjoint_domains);
            }
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

}

impl<'i, const MINIMAL: bool> Parser<&'i [u8]> for VarInt<MINIMAL> {
    type PT = u64;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let rest = *ibuf;

        let (n1, tag) = U8.parse(&rest)?;
        let rest = rest.skip(n1);
        match tag {
            t if t < VARINT_TAG_U16 => Ok((1usize, t as u64)),
            VARINT_TAG_U16 => {
                let (_, v) = U16Le.parse(&rest)?;
                if MINIMAL && v < VARINT_TAG_U16 as u16 {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((3usize, v as u64))
                }
            },
            VARINT_TAG_U32 => {
                let (_, v) = U32Le.parse(&rest)?;
                if MINIMAL && v <= u16::MAX as u32 {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((5usize, v as u64))
                }
            },
            VARINT_TAG_U64 => {
                let (_, v) = U64Le.parse(&rest)?;
                if MINIMAL && v <= u32::MAX as u64 {
                    Err(ParseError::non_canonical())
                } else {
                    Ok((9usize, v))
                }
            },
            _ => Err(ParseError::invalid_tag()),
        }
    }
}

impl<const MINIMAL: bool> Serializer<u64> for VarInt<MINIMAL> {
    fn serialize(&self, v: &u64, obuf: &mut Vec<u8>) {
        let ghost old_obuf = obuf@;

        match *v {
            0..0xFD => {
                let val = *v as u8;
                U8.serialize(&val, obuf);
            },
            0xFD..=0xFFFF => {
                let tag = VARINT_TAG_U16;
                let val = *v as u16;
                U8.serialize(&tag, obuf);
                U16Le.serialize(&val, obuf);
            },
            0x1_0000..=0xFFFF_FFFF => {
                let tag = VARINT_TAG_U32;
                let val = *v as u32;
                U8.serialize(&tag, obuf);
                U32Le.serialize(&val, obuf);
            },
            _ => {
                let tag = VARINT_TAG_U64;
                U8.serialize(&tag, obuf);
                U64Le.serialize(v, obuf);
            },
        }

        assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));
    }
}

impl<const MINIMAL: bool> Prepare<u64> for VarInt<MINIMAL> {
    fn prepare(&self, v: &u64) -> (checked: Result<usize, PreSerializeError>) {
        match *v {
            0..0xFD => Ok(1usize),
            0xFD..=0xFFFF => Ok(3usize),
            0x1_0000..=0xFFFF_FFFF => Ok(5usize),
            _ => Ok(9usize),
        }
    }
}

} // verus!
