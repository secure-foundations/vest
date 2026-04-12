use crate::{
    combinators::{bytes::ExactLen, length::AsLen, DepPair, Refined, Tail, U8},
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

/// Primitive BIT STRING contents, represented as:
/// `(number_of_unused_bits_in_final_octet, payload_octets)`.
pub type BitStringValue = (u8, Seq<u8>);

pub type BitStringFmt<const DER: bool> = DepPair<
    Refined<U8, PredFnSpec<u8>>,
    spec_fn(u8) -> Refined<Tail, PredFnSpec<Seq<u8>>>,
>;

pub open spec fn bitstring_fmt<const DER: bool>() -> BitStringFmt<DER> {
    #[verusfmt::skip]
    DepPair(
        // 8.6.2.2 The initial octet shall encode, as an unsigned binary integer with bit 1 as the least significant bit, the number of
        // unused bits in the final subsequent octet. The number shall be in the range zero to seven.
        Refined { inner: U8, pred: |unused: u8| unused <= 7 },
        |unused: u8|
            Refined {
                inner: Tail,
                pred: |payload: Seq<u8>|
                    {
                        // 8.6.2.3 If the bitstring is empty, there shall be no subsequent octets, and the initial octet shall be zero.
                        &&& payload.len() == 0 ==> unused == 0
                        // 11.2.1 Each unused bit in the final octet of the encoding of a bit string value shall be set to zero.
                        &&& payload.len() > 0 ==> DER ==> payload.last().trailing_zeros() >= unused
                    },
            },
    )
}

impl<const DER: bool> SpecParser for super::BitString<DER> {
    type PVal = BitStringValue;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        bitstring_fmt::<DER>().spec_parse(ibuf)
    }
}

impl<const DER: bool> Consistency for super::BitString<DER> {
    type Val = BitStringValue;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        bitstring_fmt::<DER>().consistent(v)
    }
}

impl<const DER: bool> SafeParser for super::BitString<DER> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        bitstring_fmt::<DER>().lemma_parse_safe(ibuf);
    }
}

impl<const DER: bool> SoundParser for super::BitString<DER> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        bitstring_fmt::<DER>().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        bitstring_fmt::<DER>().lemma_parse_sound_value(ibuf);
    }
}

impl<const DER: bool> SpecSerializerDps for super::BitString<DER> {
    type ST = BitStringValue;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        bitstring_fmt::<DER>().spec_serialize_dps(v, obuf)
    }
}

impl<const DER: bool> SpecSerializer for super::BitString<DER> {
    type SVal = BitStringValue;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        bitstring_fmt::<DER>().spec_serialize(v)
    }
}

impl<const DER: bool> GoodSerializer for super::BitString<DER> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        bitstring_fmt::<DER>().lemma_serialize_len(v);
    }
}

impl<const DER: bool> SpecByteLen for super::BitString<DER> {
    type T = BitStringValue;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        bitstring_fmt::<DER>().byte_len(v)
    }
}

impl<const DER: bool> ValueByteLen for super::BitString<DER> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        BitStringFmt::<DER>::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        bitstring_fmt::<DER>().lemma_value_len_matches_byte_len(v);
    }
}

impl<const DER: bool> SPRoundTripDps for super::BitString<DER> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        bitstring_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const DER: bool> NonMalleable for super::BitString<DER> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        bitstring_fmt::<DER>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const DER: bool> EquivSerializers for super::BitString<DER> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        bitstring_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
