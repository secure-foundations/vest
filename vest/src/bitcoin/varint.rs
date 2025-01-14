use crate::{
    properties::*,
    regular::{
        bytes_n::BytesN,
        choice::*,
        cond::Cond,
        depend::{Continuation, Depend, SpecDepend},
        map::{SpecTryFromInto, TryFromInto, TryMap},
        refined::{Pred, Refined, SpecPred},
        uints::*,
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

type VarintChoice = OrdChoice<
    Cond<BytesN<0>>,
    OrdChoice<
        Cond<Refined<U16Le, PredU16LeFit>>,
        OrdChoice<Cond<Refined<U32Le, PredU32LeFit>>, Cond<Refined<U64Le, PredU64LeFit>>>,
    >,
>;

type SpecBtcVarintInner = TryMap<SpecDepend<U8, VarintChoice>, VarIntMapper<'static>>;

type BtcVarintInner<'a> = TryMap<
    Depend<&'a [u8], Vec<u8>, U8, VarintChoice, BtVarintCont>,
    VarIntMapper<'a>,
>;

/// Inner Spec combinator for parsing and serializing Bitcoin variable-length integers
pub closed spec fn spec_btc_varint_inner() -> SpecBtcVarintInner {
    TryMap {
        inner: SpecDepend {
            fst: U8,
            snd: |t: u8|
                ord_choice!(
                    Cond { cond: t <= 0xFC, inner: BytesN::<0> },
                    Cond { cond: t ==  0xFD, inner: Refined { inner: U16Le, predicate: PredU16LeFit } },
                    Cond { cond: t ==  0xFE, inner: Refined { inner: U32Le, predicate: PredU32LeFit } },
                    Cond { cond: t ==  0xFF, inner: Refined { inner: U64Le, predicate: PredU64LeFit } },
                ),
        },
        mapper: VarIntMapper::spec_new(),
    }
}

fn btc_varint_inner<'a>() -> (o: BtcVarintInner<'a>)
    ensures
        o@ == spec_btc_varint_inner(),
{
    TryMap {
        inner: Depend {
            fst: U8,
            snd: BtVarintCont,
            spec_snd: Ghost(spec_btc_varint_inner().inner.snd),
        },
        mapper: VarIntMapper::new(),
    }
}

/// Predicate for checking if a u16 is greater than or equal to 0xFD
pub struct PredU16LeFit;

impl View for PredU16LeFit {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for PredU16LeFit {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        *i >= 0xFD
    }
}

impl SpecPred for PredU16LeFit {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
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

impl Pred for PredU32LeFit {
    type Input = u32;

    fn apply(&self, i: &Self::Input) -> bool {
        *i >= 0x10000
    }
}

impl SpecPred for PredU32LeFit {
    type Input = u32;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
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

impl Pred for PredU64LeFit {
    type Input = u64;

    fn apply(&self, i: &Self::Input) -> bool {
        *i >= 0x100000000
    }
}

impl SpecPred for PredU64LeFit {
    type Input = u64;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
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
                if t.0 == 0xFD {
                    Ok(VarInt::U16(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, x, *) => {
                if t.0 == 0xFE {
                    Ok(VarInt::U32(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, *, x) => {
                if t.0 == 0xFF {
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
                if compare_slice((&[]).as_slice(), x) {
                    assert(x@ == Seq::<u8>::empty());
                    Ok(VarInt::U8(t.0))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, x, *, *) => {
                if t.0 == 0xFD {
                    Ok(VarInt::U16(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, x, *) => {
                if t.0 == 0xFE {
                    Ok(VarInt::U32(x))
                } else {
                    Err(())
                }
            },
            inj_ord_choice_pat!(*, *, *, x) => {
                if t.0 == 0xFF {
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
            VarInt::U16(x) => Ok((0xFD, inj_ord_choice_result!(*, x, *, *))),
            VarInt::U32(x) => Ok((0xFE, inj_ord_choice_result!(*, *, x, *))),
            VarInt::U64(x) => Ok((0xFF, inj_ord_choice_result!(*, *, *, x))),
        }
    }
}

impl TryFrom<VarInt> for (u8, Either<&[u8], Either<u16, Either<u32, u64>>>) {
    type Error = ();

    fn ex_try_from(t: VarInt) -> Result<Self, Self::Error> {
        match t {
            VarInt::U8(t) => {
                let empty = (&[]).as_slice();
                assert(empty@ == Seq::<u8>::empty());
                Ok((t, inj_ord_choice_result!(empty, *, *, *)))
            },
            VarInt::U16(x) => Ok((0xFD, inj_ord_choice_result!(*, x, *, *))),
            VarInt::U32(x) => Ok((0xFE, inj_ord_choice_result!(*, *, x, *))),
            VarInt::U64(x) => Ok((0xFF, inj_ord_choice_result!(*, *, *, x))),
        }
    }
}

/// Mapper for converting between Bitcoin variable-length integers and their internal representations
pub struct VarIntMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> VarIntMapper<'a> {
    /// Spec version of [`VarIntMapper::new`]
    pub closed spec fn spec_new() -> Self {
        VarIntMapper(std::marker::PhantomData)
    }

    /// Creates a new `VarIntMapper`
    pub fn new() -> Self {
        VarIntMapper(std::marker::PhantomData)
    }
}

impl View for VarIntMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for VarIntMapper<'_> {
    type Src = (u8, Either<Seq<u8>, Either<u16, Either<u32, u64>>>);

    type Dst = VarInt;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> TryFromInto for VarIntMapper<'a> {
    type Src = (u8, Either<&'a [u8], Either<u16, Either<u32, u64>>>);

    type Dst = VarInt;
}

impl SpecCombinator for BtcVarint {
    type Type = VarInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        spec_btc_varint_inner().spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        spec_btc_varint_inner().spec_serialize(v)
    }
}

impl SecureSpecCombinator for BtcVarint {
    open spec fn is_prefix_secure() -> bool {
        SpecBtcVarintInner::is_prefix_secure()
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
}

/// Continuation for parsing and serializing Bitcoin variable-length integers
pub struct BtVarintCont;

impl Continuation<&u8> for BtVarintCont {
    type Output = VarintChoice;

    open spec fn requires(&self, t: &u8) -> bool {
        true
    }

    open spec fn ensures(&self, t: &u8, o: Self::Output) -> bool {
        o@ == (spec_btc_varint_inner().inner.snd)(t@)
    }

    fn apply(&self, t: &u8) -> Self::Output {
        ord_choice!(
                    Cond { cond: *t <= 0xFC, inner: BytesN::<0> },
                    Cond { cond: *t ==  0xFD, inner: Refined { inner: U16Le, predicate: PredU16LeFit } },
                    Cond { cond: *t ==  0xFE, inner: Refined { inner: U32Le, predicate: PredU32LeFit } },
                    Cond { cond: *t ==  0xFF, inner: Refined { inner: U64Le, predicate: PredU64LeFit } },
                )
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for BtcVarint {
    type Type = VarInt;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        btc_varint_inner().parse(s)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        btc_varint_inner().serialize(v, data, pos)
    }
}

} // verus!
