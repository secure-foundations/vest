use alloc::vec::Vec;

use crate::{
    properties::*,
    regular::{
        bytes::Fixed,
        modifier::{
            Cond, PartialIso, Pred, Refined, SpecPartialIso, SpecPartialIsoProof, SpecPred, TryMap,
        },
        sequence::{Continuation, POrSType, Pair, SpecPair},
        uints::*,
        variant::*,
    },
};
use vstd::prelude::*;

verus! {

/// Combinator for parsing and serializing [Bitcoin variable-length integers](https://en.bitcoin.it/wiki/Protocol_documentation#Variable_length_integer)
pub struct BtcVarint;

impl View for BtcVarint {
    type V = BtcVarint;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Enum representing a Bitcoin variable-length integer
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarInt {
    /// u8 that's [..=0xFC]
    U8(u8),
    /// u16 that's [0xFD..=0xFFFF]
    U16(u16),
    /// u32 that's [0x10000..=0xFFFFFFFF]
    U32(u32),
    /// u64 that's [0x100000000..=0xFFFFFFFFFFFFFFFF]
    U64(u64),
}

impl View for VarInt {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecFrom<VarInt> for usize {
    open spec fn spec_from(t: VarInt) -> usize {
        match t {
            VarInt::U8(t) => t as usize,
            VarInt::U16(t) => t as usize,
            VarInt::U32(t) => t as usize,
            VarInt::U64(t) => t as usize,
        }
    }
}

impl From<VarInt> for usize {
    fn ex_from(t: VarInt) -> usize {
        match t {
            VarInt::U8(t) => t as usize,
            VarInt::U16(t) => t as usize,
            VarInt::U32(t) => t as usize,
            VarInt::U64(t) => t as usize,
        }
    }
}

impl VarInt {
    /// Spec version of [`VarInt::as_usize`]
    pub open spec fn spec_as_usize(self) -> usize {
        self.spec_into()
    }

    /// Converts a `VarInt` into a `usize`
    pub fn as_usize(self) -> (o: usize)
        ensures
            o@ == self.spec_as_usize(),
    {
        self.ex_into()
    }
}

type VarintChoice = Choice<
    Cond<Fixed<0>>,
    Choice<
        Cond<Refined<U16Le, PredU16LeFit>>,
        Choice<Cond<Refined<U32Le, PredU32LeFit>>, Cond<Refined<U64Le, PredU64LeFit>>>,
    >,
>;

type SpecBtcVarintInner = TryMap<SpecPair<U8, VarintChoice>, VarIntMapper>;

type BtcVarintInner = TryMap<Pair<U8, VarintChoice, BtVarintCont>, VarIntMapper>;

pub spec const SPEC_TAG_U16: u8 = 0xFD;

pub spec const SPEC_TAG_U32: u8 = 0xFE;

pub spec const SPEC_TAG_U64: u8 = 0xFF;

pub exec static TAG_U16: u8
    ensures
        TAG_U16 == SPEC_TAG_U16,
{
    0xFD
}

pub exec static TAG_U32: u8
    ensures
        TAG_U32 == SPEC_TAG_U32,
{
    0xFE
}

pub exec static TAG_U64: u8
    ensures
        TAG_U64 == SPEC_TAG_U64,
{
    0xFF
}

pub exec static EMPTY_SLICE: &'static [u8]
    ensures
        EMPTY_SLICE@ == Seq::<u8>::empty(),
{
    assert(<_ as View>::view(&[]) =~= Seq::<u8>::empty());
    &[]
}

pub exec static EMPTY: &'static &'static [u8]
    ensures
        EMPTY@ == Seq::<u8>::empty(),
{
    &EMPTY_SLICE
}

/// Inner Spec combinator for parsing and serializing Bitcoin variable-length integers
pub open spec fn spec_btc_varint_inner() -> SpecBtcVarintInner {
    TryMap {
        inner: Pair::spec_new(
            U8,
            |t: u8|
                ord_choice!(
                    Cond { cond: t <= 0xFC, inner: Fixed::<0> },
                    Cond { cond: t ==  SPEC_TAG_U16, inner: Refined { inner: U16Le, predicate: PredU16LeFit } },
                    Cond { cond: t ==  SPEC_TAG_U32, inner: Refined { inner: U32Le, predicate: PredU32LeFit } },
                    Cond { cond: t ==  SPEC_TAG_U64, inner: Refined { inner: U64Le, predicate: PredU64LeFit } },
                ),
        ),
        mapper: VarIntMapper,
    }
}

fn btc_varint_inner() -> (o: BtcVarintInner)
    ensures
        o@ == spec_btc_varint_inner(),
{
    TryMap { inner: Pair::new(U8, BtVarintCont), mapper: VarIntMapper }
}

/// Predicate for checking if a u16 is greater than or equal to 0xFD
pub struct PredU16LeFit;

impl View for PredU16LeFit {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred<u16> for PredU16LeFit {
    fn apply(&self, i: &u16) -> bool {
        *i >= 0xFD
    }
}

impl SpecPred<u16> for PredU16LeFit {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        *i >= 0xFD
    }
}

/// Predicate for checking if a u32 is greater than or equal to 0x10000
pub struct PredU32LeFit;

impl View for PredU32LeFit {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred<u32> for PredU32LeFit {
    fn apply(&self, i: &u32) -> bool {
        *i >= 0x10000
    }
}

impl SpecPred<u32> for PredU32LeFit {
    open spec fn spec_apply(&self, i: &u32) -> bool {
        *i >= 0x10000
    }
}

/// Predicate for checking if a u64 is greater than or equal to 0x100000000
pub struct PredU64LeFit;

impl View for PredU64LeFit {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred<u64> for PredU64LeFit {
    fn apply(&self, i: &u64) -> bool {
        *i >= 0x100000000
    }
}

impl SpecPred<u64> for PredU64LeFit {
    open spec fn spec_apply(&self, i: &u64) -> bool {
        *i >= 0x100000000
    }
}

impl SpecTryFrom<(u8, Either<Seq<u8>, Either<u16, Either<u32, u64>>>)> for VarInt {
    type Error = ();

    open spec fn spec_try_from(t: (u8, Either<Seq<u8>, Either<u16, Either<u32, u64>>>)) -> Result<
        Self,
        Self::Error,
    > {
        match t.1 {
            inj_ord_choice_pat!(x, *, *, *) => {
                if x == Seq::<u8>::empty() {
                    Ok(VarInt::U8(t.0))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, x, *, *) => {
                if t.0 == SPEC_TAG_U16 {
                    Ok(VarInt::U16(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, x, *) => {
                if t.0 == SPEC_TAG_U32 {
                    Ok(VarInt::U32(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, *, x) => {
                if t.0 == SPEC_TAG_U64 {
                    Ok(VarInt::U64(x))
                } else {
                    Err(())
                }
            },
        }
    }
}

impl TryFrom<(u8, Either<&[u8], Either<u16, Either<u32, u64>>>)> for VarInt {
    type Error = ();

    fn ex_try_from(t: (u8, Either<&[u8], Either<u16, Either<u32, u64>>>)) -> Result<
        Self,
        Self::Error,
    > {
        match t.1 {
            inj_ord_choice_pat!(x, *, *, *) => {
                if compare_slice(EMPTY, x) {
                    assert(x@ == Seq::<u8>::empty());
                    Ok(VarInt::U8(t.0))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, x, *, *) => {
                if t.0 == TAG_U16 {
                    Ok(VarInt::U16(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, x, *) => {
                if t.0 == TAG_U32 {
                    Ok(VarInt::U32(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, *, x) => {
                if t.0 == TAG_U64 {
                    Ok(VarInt::U64(x))
                } else {
                    Err(())
                }
            },
        }
    }
}

impl SpecTryFrom<VarInt> for (u8, Either<Seq<u8>, Either<u16, Either<u32, u64>>>) {
    type Error = ();

    open spec fn spec_try_from(t: VarInt) -> Result<Self, Self::Error> {
        match t {
            VarInt::U8(t) => Ok((t, inj_ord_choice_result!(Seq::<u8>::empty(), *, *, *))),
            VarInt::U16(x) => Ok((SPEC_TAG_U16, inj_ord_choice_result!(*, x, *, *))),
            VarInt::U32(x) => Ok((SPEC_TAG_U32, inj_ord_choice_result!(*, *, x, *))),
            VarInt::U64(x) => Ok((SPEC_TAG_U64, inj_ord_choice_result!(*, *, *, x))),
        }
    }
}

impl<'x> TryFrom<&'x VarInt> for (
    &'x u8,
    Either<&'x &'x [u8], Either<&'x u16, Either<&'x u32, &'x u64>>>,
) {
    type Error = ();

    fn ex_try_from(t: &'x VarInt) -> Result<Self, Self::Error> {
        match t {
            VarInt::U8(t) => { Ok((t, inj_ord_choice_result!(EMPTY, *, *, *))) },
            VarInt::U16(x) => Ok((&TAG_U16, inj_ord_choice_result!(*, x, *, *))),
            VarInt::U32(x) => Ok((&TAG_U32, inj_ord_choice_result!(*, *, x, *))),
            VarInt::U64(x) => Ok((&TAG_U64, inj_ord_choice_result!(*, *, *, x))),
        }
    }
}

/// Mapper for converting between Bitcoin variable-length integers and their internal representations
pub struct VarIntMapper;

impl View for VarIntMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for VarIntMapper {
    type Src = (u8, Either<Seq<u8>, Either<u16, Either<u32, u64>>>);

    type Dst = VarInt;
}

impl SpecPartialIsoProof for VarIntMapper {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'x> PartialIso<'x> for VarIntMapper {
    type Src = (u8, Either<&'x [u8], Either<u16, Either<u32, u64>>>);

    type Dst = VarInt;

    type RefSrc = (&'x u8, Either<&'x &'x [u8], Either<&'x u16, Either<&'x u32, &'x u64>>>);
}

impl SpecCombinator for BtcVarint {
    type Type = VarInt;

    open spec fn requires(&self) -> bool {
        spec_btc_varint_inner().requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        spec_btc_varint_inner().wf(v)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        spec_btc_varint_inner().spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        spec_btc_varint_inner().spec_serialize(v)
    }
}

impl SecureSpecCombinator for BtcVarint {
    open spec fn is_prefix_secure() -> bool {
        SpecBtcVarintInner::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        spec_btc_varint_inner().is_productive()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        spec_btc_varint_inner().lemma_prefix_secure(s1, s2);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        spec_btc_varint_inner().theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        spec_btc_varint_inner().theorem_parse_serialize_roundtrip(s);
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        spec_btc_varint_inner().lemma_parse_length(s);
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        spec_btc_varint_inner().lemma_parse_productive(s);
    }
}

/// Continuation for parsing and serializing Bitcoin variable-length integers
pub struct BtVarintCont;

impl View for BtVarintCont {
    type V = spec_fn(u8) -> VarintChoice;

    open spec fn view(&self) -> Self::V {
        spec_btc_varint_inner().inner.snd
    }
}

impl<'a> Continuation<POrSType<&'a u8, &u8>> for BtVarintCont {
    type Output = VarintChoice;

    open spec fn requires(&self, t: POrSType<&'a u8, &u8>) -> bool {
        true
    }

    open spec fn ensures(&self, t: POrSType<&'a u8, &u8>, o: Self::Output) -> bool {
        // o@ == (spec_btc_varint_inner().inner.snd)(t@)
        o@ == (self@)(t@)
    }

    fn apply(&self, t: POrSType<&'a u8, &u8>) -> Self::Output {
        let t = match t {
            POrSType::P(t) => t,
            POrSType::S(t) => t,
        };
        ord_choice!(
                    Cond { cond: *t <= 0xFC, inner: Fixed::<0> },
                    Cond { cond: *t ==  0xFD, inner: Refined { inner: U16Le, predicate: PredU16LeFit } },
                    Cond { cond: *t ==  0xFE, inner: Refined { inner: U32Le, predicate: PredU32LeFit } },
                    Cond { cond: *t ==  0xFF, inner: Refined { inner: U64Le, predicate: PredU64LeFit } },
                )
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for BtcVarint {
    type Type = VarInt;

    type SType = &'a VarInt;

    fn length(&self, v: Self::SType) -> usize {
        match v {
            VarInt::U8(_) => 1,
            VarInt::U16(_) => 3,
            VarInt::U32(_) => 5,
            VarInt::U64(_) => 9,
        }
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&btc_varint_inner(), s)
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        btc_varint_inner().serialize(v, data, pos)
    }
}

// verify well-formed VarInt
#[cfg(test)]
mod tests {
    use super::*;

    proof fn well_formed_varint() {
        let good1 = VarInt::U8(0xFC);
        let good2 = VarInt::U16(0xFD);
        let good3 = VarInt::U32(0x10000);
        let good4 = VarInt::U64(0x100000000);
        assert(BtcVarint.wf(good1));
        assert(BtcVarint.wf(good2));
        assert(BtcVarint.wf(good3));
        assert(BtcVarint.wf(good4));

        let bad1 = VarInt::U8(0xFD);
        let bad2 = VarInt::U16(0xFC);
        let bad3 = VarInt::U32(0xFFFF);
        let bad4 = VarInt::U64(0xFFFFFFFF);
        assert(!BtcVarint.wf(bad1));
        assert(!BtcVarint.wf(bad2));
        assert(!BtcVarint.wf(bad3));
        assert(!BtcVarint.wf(bad4));
    }

}

} // verus!
