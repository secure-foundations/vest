use crate::{
    combinators::{
        mapped::spec::{LosslessMapper, LossyMapper, SpecMapper},
        TryMap, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

pub const BOOL_BYTE_LEN: usize = 1;

pub const FALSE_BYTE: u8 = 0x00;

pub const CANONICAL_TRUE_BYTE: u8 = 0xFF;

pub struct BoolMapper<const DER: bool>;

pub open spec fn non_zero(b: u8) -> bool {
    b != FALSE_BYTE
}

pub open spec fn der_bool_byte(b: u8) -> bool {
    b == CANONICAL_TRUE_BYTE || b == FALSE_BYTE
}

pub open spec fn true_byte<const DER: bool>() -> u8 {
    if DER {
        CANONICAL_TRUE_BYTE
    } else {
        choose|x: u8| non_zero(x)
    }
}

pub type BoolFmt<const DER: bool> = TryMap<U8, BoolMapper<DER>>;

pub open spec fn bool_fmt<const DER: bool>() -> BoolFmt<DER> {
    TryMap { inner: U8, mapper: BoolMapper::<DER> }
}

impl<const DER: bool> SpecMapper for BoolMapper<DER> {
    type In = u8;

    type Out = bool;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        if DER {
            der_bool_byte(i)
        } else {
            true
        }
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        non_zero(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        if o {
            true_byte::<DER>()
        } else {
            FALSE_BYTE
        }
    }
}

impl<const DER: bool> LossyMapper for BoolMapper<DER> {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        assert(non_zero(CANONICAL_TRUE_BYTE));
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        assert(non_zero(CANONICAL_TRUE_BYTE));
    }
}

impl LosslessMapper for BoolMapper<true> {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

impl<const DER: bool> SpecParser for super::Bool<DER> {
    type PVal = bool;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        bool_fmt::<DER>().spec_parse(ibuf)
    }
}

impl<const DER: bool> Consistency for super::Bool<DER> {
    type Val = bool;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        bool_fmt::<DER>().consistent(v)
    }
}

impl<const DER: bool> SafeParser for super::Bool<DER> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        bool_fmt::<DER>().lemma_parse_safe(ibuf);
    }
}

impl<const DER: bool> SoundParser for super::Bool<DER> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl<const DER: bool> SpecSerializerDps for super::Bool<DER> {
    type SValue = bool;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        bool_fmt::<DER>().spec_serialize_dps(v, obuf)
    }
}

impl<const DER: bool> SpecSerializer for super::Bool<DER> {
    type SVal = bool;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        bool_fmt::<DER>().spec_serialize(v)
    }
}

impl<const DER: bool> NonTailFmt for super::Bool<DER> {
    proof fn lemma_serialize_dps_prepend(&self, v: bool, obuf: Seq<u8>) {
        bool_fmt::<DER>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: bool, obuf: Seq<u8>) {
        bool_fmt::<DER>().lemma_serialize_dps_len(v, obuf);
    }
}

impl<const DER: bool> GoodSerializer for super::Bool<DER> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        bool_fmt::<DER>().lemma_serialize_len(v);
    }
}

impl<const DER: bool> SpecByteLen for super::Bool<DER> {
    type T = bool;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        BOOL_BYTE_LEN as nat
    }
}

impl<const DER: bool> StaticByteLen for super::Bool<DER> {
    open spec fn static_byte_len() -> nat {
        BOOL_BYTE_LEN as nat
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        bool_fmt::<DER>().lemma_static_len_matches_byte_len(v);
    }
}

impl<const DER: bool> ValueByteLen for super::Bool<DER> {
    open spec fn value_byte_len(_v: Self::T) -> nat {
        BOOL_BYTE_LEN as nat
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        bool_fmt::<DER>().lemma_static_len_matches_byte_len(v);
    }
}

impl<const DER: bool> SPRoundTripDps for super::Bool<DER> {
    open spec fn unambiguous(&self) -> bool {
        bool_fmt::<DER>().unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        bool_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const DER: bool> NoLookAhead for super::Bool<DER> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        bool_fmt::<DER>().lemma_no_lookahead(i1, i2);
    }
}

impl NonMalleable for super::Bool<true> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        bool_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const DER: bool> EquivSerializersGeneral for super::Bool<DER> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        bool_fmt::<DER>().lemma_serialize_equiv(v, obuf);
    }
}

impl<const DER: bool> EquivSerializers for super::Bool<DER> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        bool_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
