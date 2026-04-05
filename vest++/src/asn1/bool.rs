use crate::{
    combinators::{
        mapped::spec::{LosslessMapper, LossyMapper, Mapper},
        Mapped, Refined, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::prelude::*;

verus! {

pub struct BoolBytePred<const DER: bool>;

pub struct BoolMapper<const DER: bool>;

pub open spec fn non_zero(b: u8) -> bool {
    b != 0x00u8
}

pub open spec fn der_bool(b: u8) -> bool {
    b == 0x00u8 || b == 0xFFu8
}

pub open spec fn true_byte<const DER: bool>() -> u8 {
    if DER {
        0xFFu8
    } else {
        choose|x: u8| non_zero(x)
    }
}

pub type BoolFmt<const DER: bool> = Mapped<Refined<U8, BoolBytePred<DER>>, BoolMapper<DER>>;

pub open spec fn bool_fmt<const DER: bool>() -> BoolFmt<DER> {
    Mapped { inner: Refined { inner: U8, pred: BoolBytePred::<DER> }, mapper: BoolMapper::<DER> }
}

impl<const DER: bool> SpecPred<u8> for BoolBytePred<DER> {
    open spec fn apply(&self, byte: u8) -> bool {
        if DER {
            der_bool(byte)
        } else {
            true
        }
    }
}

impl<const DER: bool> Mapper for BoolMapper<DER> {
    type In = u8;

    type Out = bool;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        BoolBytePred::<DER>.apply(i)
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        non_zero(i)
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        if o {
            true_byte::<DER>()
        } else {
            0x00u8
        }
    }
}

impl<const DER: bool> LossyMapper for BoolMapper<DER> {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        if o {
            if DER {
                assert(true_byte::<DER>() == 0xFFu8);
            } else {
                assert(exists|x: u8| non_zero(x)) by {
                    assert(non_zero(0x01u8));
                }
            }
        }
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

impl<const DER: bool> SoundParser for super::Bool<DER> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
    }
}

impl<const DER: bool> SpecSerializerDps for super::Bool<DER> {
    type ST = bool;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        bool_fmt::<DER>().spec_serialize_dps(v, obuf)
    }
}

impl<const DER: bool> SpecSerializer for super::Bool<DER> {
    type SVal = bool;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        bool_fmt::<DER>().spec_serialize(v)
    }
}

impl<const DER: bool> Unambiguity for super::Bool<DER> {

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
        bool_fmt::<DER>().byte_len(v)
    }
}

impl<const DER: bool> SPRoundTripDps for super::Bool<DER> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        bool_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const DER: bool> NoLookAhead for super::Bool<DER> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let inner = Refined { inner: U8, pred: BoolBytePred::<DER> };
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.lemma_parse_safe(i1);
                    let (m, b) = inner.spec_parse(i1)->0;
                    inner.lemma_no_lookahead(i1, i2);
                    assert(inner.spec_parse(i2) == Some((m, b)));
                    assert(self.spec_parse(i2) == Some((m, v)));
                }
            }
        }
    }
}

impl NonMalleable for super::Bool<true> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        bool_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
    }
}

// Bool<false> intentionally does NOT implement PSRoundTrip or NonMalleable:
// any non-zero byte parses as true, so BER BOOLEAN remains malleable.
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
