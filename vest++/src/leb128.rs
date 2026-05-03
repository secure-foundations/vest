use crate::{
    combinators::{
        mapped::spec::{LosslessMapper, LossyMapper, SpecMapper},
        recursive::{
            BundledSpecs, EquivSerializersGeneralRecBody, GoodSerializerRecBody,
            NoLookAheadRecBody, NonMalleableRecBody, NonTailFmtRecBody, SPRoundTripDpsRecBody,
            SafeParserRecBody, SoundParserRecBody, SpecRecBody,
        },
        Alt, Fix, Mapped, Pair, Refined, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

pub type ULeb128Fmt<const MINIMAL: bool, const RECLIMIT: usize> = Fix<
    RECLIMIT,
    ULeb128RecBody<MINIMAL>,
>;

pub open spec fn uleb128_fmt<const MINIMAL: bool, const N: usize>() -> ULeb128Fmt<MINIMAL, N> {
    Fix(ULeb128RecBody::<MINIMAL>)
}

pub struct ULeb128RecBody<const MINIMAL: bool>;

impl<const MINIMAL: bool> SpecRecBody for ULeb128RecBody<MINIMAL> {
    type T = nat;

    type Body = Alt<
        TerminalByte,
        Mapped<
            Refined<Pair<ContinuationByte, BundledSpecs<nat>>, PredFnSpec<(u8, nat)>>,
            PairFromToNat,
        >,
    >;

    /// 𝚞𝑁	::=	𝑛:𝚋𝚢𝚝𝚎          		⇒		𝑛		if 𝑛 < 2^7
    ///
    /// |	𝑛:𝚋𝚢𝚝𝚎  𝑚:𝚞(𝑁−7)		⇒		2^7 * 𝑚 + (𝑛 − 2^7)		  if 𝑛 >= 2^7
    open spec fn spec_body(rec: BundledSpecs<Self::T>) -> Self::Body {
        Alt(
            terminal_byte(),
            Mapped {
                inner: Refined(
                    Pair(continuation_byte(), rec),
                    // No trailing zeros (e.g., 0x80 0x00) allowed if MINIMAL
                    |x: (u8, nat)| MINIMAL ==> x.1 > 0,
                ),
                mapper: PairFromToNat,
            },
        )
    }
}

pub type TerminalByte = Mapped<Refined<U8, PredFnSpec<u8>>, TermByteFromToNat>;

pub type ContinuationByte = Mapped<Refined<U8, PredFnSpec<u8>>, LowBitsMask>;

pub const LEB128_CONT_BIT: u8 = 0x80;

/// Check that high bit is not set, and map to the corresponding nat value.
pub open spec fn terminal_byte() -> TerminalByte {
    Mapped { inner: Refined(U8, |b: u8| b < LEB128_CONT_BIT), mapper: TermByteFromToNat }
}

/// Check that high bit is set, and map to the corresponding low 7 bits.
pub open spec fn continuation_byte() -> ContinuationByte {
    Mapped { inner: Refined(U8, |b: u8| b >= LEB128_CONT_BIT), mapper: LowBitsMask }
}

pub struct TermByteFromToNat;

impl SpecMapper for TermByteFromToNat {
    type In = u8;

    type Out = nat;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        i < LEB128_CONT_BIT
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o < LEB128_CONT_BIT
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as nat
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u8
    }
}

pub struct LowBitsMask;

impl SpecMapper for LowBitsMask {
    type In = u8;

    type Out = u8;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        i >= LEB128_CONT_BIT
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o < LEB128_CONT_BIT
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        // Mask off the high bit to get the low 7 bits as a nat value
        // i & 0x7Fu8
        (i - LEB128_CONT_BIT) as u8
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        // Set the high bit to get the continuation wire format
        // o | LEB128_CONT_BIT
        (o + LEB128_CONT_BIT) as u8
    }
}

pub struct PairFromToNat;

impl SpecMapper for PairFromToNat {
    type In = (u8, nat);

    type Out = nat;

    // NOTE: the check `MINIMAL ==> x.1 > 0` in `ULeb128RecBody`'s
    // `spec_body` ensures that if MINIMAL is true, then rest > 0, so we don't need to check that here.
    open spec fn wf_in(&self, i: Self::In) -> bool {
        let (low, rest) = i;
        low < LEB128_CONT_BIT
    }

    // NOTE: the check `MINIMAL ==> x.1 > 0` in `ULeb128RecBody`'s `spec_body` ensures that if `MINIMAL` is true, then the output of the mapper is always at least 128, so we don't need to check that here.
    // open spec fn wf_out(&self, o: Self::Out) -> bool {
    //     MINIMAL ==> o >= LEB128_CONT_BIT as nat
    // }
    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (low, rest) = i;
        // low | (rest << 7)
        128 * rest + low as nat
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        // low = o & 0x7F, rest = o >> 7
        ((o % 128) as u8, o / 128)
    }
}

impl LossyMapper for TermByteFromToNat {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for TermByteFromToNat {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

impl LossyMapper for LowBitsMask {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for LowBitsMask {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

impl LossyMapper for PairFromToNat {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
    }
}

impl LosslessMapper for PairFromToNat {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

impl<const MINIMAL: bool> SafeParserRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_body_safe_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl SoundParserRecBody for ULeb128RecBody<true> {
    proof fn lemma_body_sound_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl<const MINIMAL: bool> GoodSerializerRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_s_body_serialize_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl<const MINIMAL: bool> NonTailFmtRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_s_body_dps_serialize_dps_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl<const MINIMAL: bool> SPRoundTripDpsRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_body_sp_roundtrip_dps_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl<const MINIMAL: bool> NoLookAheadRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_body_no_lookahead_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl NonMalleableRecBody for ULeb128RecBody<true> {
    proof fn lemma_body_nonmal_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

impl<const MINIMAL: bool> EquivSerializersGeneralRecBody for ULeb128RecBody<MINIMAL> {
    proof fn lemma_s_body_equiv_general_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

pub struct ULeb128<const MINIMAL: bool, const N: usize>;

impl<const MINIMAL: bool, const N: usize> SpecParser for ULeb128<MINIMAL, N> {
    type PVal = nat;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        uleb128_fmt::<MINIMAL, N>().spec_parse(ibuf)
    }
}

impl<const MINIMAL: bool, const N: usize> Consistency for ULeb128<MINIMAL, N> {
    type Val = nat;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        uleb128_fmt::<MINIMAL, N>().consistent(v)
    }
}

impl<const MINIMAL: bool, const N: usize> SafeParser for ULeb128<MINIMAL, N> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().lemma_parse_safe(ibuf);
    }
}

impl<const N: usize> SoundParser for ULeb128<true, N> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        uleb128_fmt::<true, N>().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        uleb128_fmt::<true, N>().lemma_parse_sound_value(ibuf);
    }
}

impl<const MINIMAL: bool, const N: usize> SpecSerializerDps for ULeb128<MINIMAL, N> {
    type SValue = nat;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        uleb128_fmt::<MINIMAL, N>().spec_serialize_dps(v, obuf)
    }
}

impl<const MINIMAL: bool, const N: usize> SpecSerializer for ULeb128<MINIMAL, N> {
    type SVal = nat;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        uleb128_fmt::<MINIMAL, N>().spec_serialize(v)
    }
}

impl<const MINIMAL: bool, const N: usize> NonTailFmt for ULeb128<MINIMAL, N> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().lemma_serialize_dps_len(v, obuf);
    }
}

impl<const MINIMAL: bool, const N: usize> GoodSerializer for ULeb128<MINIMAL, N> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        uleb128_fmt::<MINIMAL, N>().lemma_serialize_len(v);
    }
}

impl<const MINIMAL: bool, const N: usize> SpecByteLen for ULeb128<MINIMAL, N> {
    type T = nat;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        uleb128_fmt::<MINIMAL, N>().byte_len(v)
    }
}

impl<const MINIMAL: bool, const N: usize> SPRoundTripDps for ULeb128<MINIMAL, N> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const MINIMAL: bool, const N: usize> NoLookAhead for ULeb128<MINIMAL, N> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().lemma_no_lookahead(i1, i2);
    }
}

impl<const N: usize> NonMalleable for ULeb128<true, N> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        uleb128_fmt::<true, N>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const MINIMAL: bool, const N: usize> EquivSerializersGeneral for ULeb128<MINIMAL, N> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        uleb128_fmt::<MINIMAL, N>().lemma_serialize_equiv(v, obuf);
    }
}

impl<const MINIMAL: bool, const N: usize> EquivSerializers for ULeb128<MINIMAL, N> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        uleb128_fmt::<MINIMAL, N>().lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
