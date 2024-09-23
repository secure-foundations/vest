#![allow(unused_imports)]
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

pub enum SpecARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type SpecARegularChooseInner = Either<Either<u8, u16>, u32>;

impl SpecFrom<SpecARegularChoose> for SpecARegularChooseInner {
    open spec fn spec_from(m: SpecARegularChoose) -> SpecARegularChooseInner {
        match m {
            SpecARegularChoose::A(m) => Either::Left(Either::Left(m)),
            SpecARegularChoose::B(m) => Either::Left(Either::Right(m)),
            SpecARegularChoose::C(m) => Either::Right(m),
        }
    }
}

impl SpecFrom<SpecARegularChooseInner> for SpecARegularChoose {
    open spec fn spec_from(m: SpecARegularChooseInner) -> SpecARegularChoose {
        match m {
            Either::Left(Either::Left(m)) => SpecARegularChoose::A(m),
            Either::Left(Either::Right(m)) => SpecARegularChoose::B(m),
            Either::Right(m) => SpecARegularChoose::C(m),
        }
    }
}

pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseInner = Either<Either<u8, u16>, u32>;

impl View for ARegularChoose {
    type V = SpecARegularChoose;

    open spec fn view(&self) -> Self::V {
        match self {
            ARegularChoose::A(m) => SpecARegularChoose::A(m@),
            ARegularChoose::B(m) => SpecARegularChoose::B(m@),
            ARegularChoose::C(m) => SpecARegularChoose::C(m@),
        }
    }
}

impl From<ARegularChoose> for ARegularChooseInner {
    fn ex_from(m: ARegularChoose) -> ARegularChooseInner {
        match m {
            ARegularChoose::A(m) => Either::Left(Either::Left(m)),
            ARegularChoose::B(m) => Either::Left(Either::Right(m)),
            ARegularChoose::C(m) => Either::Right(m),
        }
    }
}

impl From<ARegularChooseInner> for ARegularChoose {
    fn ex_from(m: ARegularChooseInner) -> ARegularChoose {
        match m {
            Either::Left(Either::Left(m)) => ARegularChoose::A(m),
            Either::Left(Either::Right(m)) => ARegularChoose::B(m),
            Either::Right(m) => ARegularChoose::C(m),
        }
    }
}

pub struct ARegularChooseMapper;

impl View for ARegularChooseMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for ARegularChooseMapper {
    type Src = SpecARegularChooseInner;

    type Dst = SpecARegularChoose;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for ARegularChooseMapper {
    type Src<'a> = ARegularChooseInner;

    type Dst<'a> = ARegularChoose;

    type SrcOwned = ARegularChooseOwnedInner;

    type DstOwned = ARegularChooseOwned;
}

pub enum ARegularChooseOwned {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseOwnedInner = Either<Either<u8, u16>, u32>;

impl View for ARegularChooseOwned {
    type V = SpecARegularChoose;

    open spec fn view(&self) -> Self::V {
        match self {
            ARegularChooseOwned::A(m) => SpecARegularChoose::A(m@),
            ARegularChooseOwned::B(m) => SpecARegularChoose::B(m@),
            ARegularChooseOwned::C(m) => SpecARegularChoose::C(m@),
        }
    }
}

impl From<ARegularChooseOwned> for ARegularChooseOwnedInner {
    fn ex_from(m: ARegularChooseOwned) -> ARegularChooseOwnedInner {
        match m {
            ARegularChooseOwned::A(m) => Either::Left(Either::Left(m)),
            ARegularChooseOwned::B(m) => Either::Left(Either::Right(m)),
            ARegularChooseOwned::C(m) => Either::Right(m),
        }
    }
}

impl From<ARegularChooseOwnedInner> for ARegularChooseOwned {
    fn ex_from(m: ARegularChooseOwnedInner) -> ARegularChooseOwned {
        match m {
            Either::Left(Either::Left(m)) => ARegularChooseOwned::A(m),
            Either::Left(Either::Right(m)) => ARegularChooseOwned::B(m),
            Either::Right(m) => ARegularChooseOwned::C(m),
        }
    }
}

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAClosedEnum = AClosedEnum;

pub type AClosedEnumOwned = AClosedEnum;

pub type AClosedEnumInner = u8;

impl View for AClosedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AClosedEnum> for AClosedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnum) -> Result<AClosedEnumInner, ()> {
        match v {
            AClosedEnum::A => Ok(0u8),
            AClosedEnum::B => Ok(1u8),
            AClosedEnum::C => Ok(2u8),
        }
    }
}

impl TryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    fn ex_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl TryFrom<AClosedEnum> for AClosedEnumInner {
    type Error = ();

    fn ex_try_from(v: AClosedEnum) -> Result<AClosedEnumInner, ()> {
        match v {
            AClosedEnum::A => Ok(0u8),
            AClosedEnum::B => Ok(1u8),
            AClosedEnum::C => Ok(2u8),
        }
    }
}

pub struct AClosedEnumMapper;

impl View for AClosedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for AClosedEnumMapper {
    type Src = AClosedEnumInner;

    type Dst = AClosedEnum;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl TryFromInto for AClosedEnumMapper {
    type Src<'a> = AClosedEnumInner;

    type Dst<'a> = AClosedEnum;

    type SrcOwned = AClosedEnumInner;

    type DstOwned = AClosedEnum;
}

pub type SpecAnOpenEnum = u8;

pub type AnOpenEnum = u8;

pub type AnOpenEnumOwned = u8;

pub enum SpecAChooseWithDefault {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecAChooseWithDefaultInner = Either<Either<Either<u8, u16>, u32>, Seq<u8>>;

impl SpecFrom<SpecAChooseWithDefault> for SpecAChooseWithDefaultInner {
    open spec fn spec_from(m: SpecAChooseWithDefault) -> SpecAChooseWithDefaultInner {
        match m {
            SpecAChooseWithDefault::A(m) => Either::Left(Either::Left(Either::Left(m))),
            SpecAChooseWithDefault::B(m) => Either::Left(Either::Left(Either::Right(m))),
            SpecAChooseWithDefault::C(m) => Either::Left(Either::Right(m)),
            SpecAChooseWithDefault::Unrecognized(m) => Either::Right(m),
        }
    }
}

impl SpecFrom<SpecAChooseWithDefaultInner> for SpecAChooseWithDefault {
    open spec fn spec_from(m: SpecAChooseWithDefaultInner) -> SpecAChooseWithDefault {
        match m {
            Either::Left(Either::Left(Either::Left(m))) => SpecAChooseWithDefault::A(m),
            Either::Left(Either::Left(Either::Right(m))) => SpecAChooseWithDefault::B(m),
            Either::Left(Either::Right(m)) => SpecAChooseWithDefault::C(m),
            Either::Right(m) => SpecAChooseWithDefault::Unrecognized(m),
        }
    }
}

pub enum AChooseWithDefault<'a> {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(&'a [u8]),
}

pub type AChooseWithDefaultInner<'a> = Either<Either<Either<u8, u16>, u32>, &'a [u8]>;

impl View for AChooseWithDefault<'_> {
    type V = SpecAChooseWithDefault;

    open spec fn view(&self) -> Self::V {
        match self {
            AChooseWithDefault::A(m) => SpecAChooseWithDefault::A(m@),
            AChooseWithDefault::B(m) => SpecAChooseWithDefault::B(m@),
            AChooseWithDefault::C(m) => SpecAChooseWithDefault::C(m@),
            AChooseWithDefault::Unrecognized(m) => SpecAChooseWithDefault::Unrecognized(m@),
        }
    }
}

impl<'a> From<AChooseWithDefault<'a>> for AChooseWithDefaultInner<'a> {
    fn ex_from(m: AChooseWithDefault<'a>) -> AChooseWithDefaultInner<'a> {
        match m {
            AChooseWithDefault::A(m) => Either::Left(Either::Left(Either::Left(m))),
            AChooseWithDefault::B(m) => Either::Left(Either::Left(Either::Right(m))),
            AChooseWithDefault::C(m) => Either::Left(Either::Right(m)),
            AChooseWithDefault::Unrecognized(m) => Either::Right(m),
        }
    }
}

impl<'a> From<AChooseWithDefaultInner<'a>> for AChooseWithDefault<'a> {
    fn ex_from(m: AChooseWithDefaultInner<'a>) -> AChooseWithDefault<'a> {
        match m {
            Either::Left(Either::Left(Either::Left(m))) => AChooseWithDefault::A(m),
            Either::Left(Either::Left(Either::Right(m))) => AChooseWithDefault::B(m),
            Either::Left(Either::Right(m)) => AChooseWithDefault::C(m),
            Either::Right(m) => AChooseWithDefault::Unrecognized(m),
        }
    }
}

pub struct AChooseWithDefaultMapper;

impl View for AChooseWithDefaultMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for AChooseWithDefaultMapper {
    type Src = SpecAChooseWithDefaultInner;

    type Dst = SpecAChooseWithDefault;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for AChooseWithDefaultMapper {
    type Src<'a> = AChooseWithDefaultInner<'a>;

    type Dst<'a> = AChooseWithDefault<'a>;

    type SrcOwned = AChooseWithDefaultOwnedInner;

    type DstOwned = AChooseWithDefaultOwned;
}

pub enum AChooseWithDefaultOwned {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Vec<u8>),
}

pub type AChooseWithDefaultOwnedInner = Either<Either<Either<u8, u16>, u32>, Vec<u8>>;

impl View for AChooseWithDefaultOwned {
    type V = SpecAChooseWithDefault;

    open spec fn view(&self) -> Self::V {
        match self {
            AChooseWithDefaultOwned::A(m) => SpecAChooseWithDefault::A(m@),
            AChooseWithDefaultOwned::B(m) => SpecAChooseWithDefault::B(m@),
            AChooseWithDefaultOwned::C(m) => SpecAChooseWithDefault::C(m@),
            AChooseWithDefaultOwned::Unrecognized(m) => SpecAChooseWithDefault::Unrecognized(m@),
        }
    }
}

impl From<AChooseWithDefaultOwned> for AChooseWithDefaultOwnedInner {
    fn ex_from(m: AChooseWithDefaultOwned) -> AChooseWithDefaultOwnedInner {
        match m {
            AChooseWithDefaultOwned::A(m) => Either::Left(Either::Left(Either::Left(m))),
            AChooseWithDefaultOwned::B(m) => Either::Left(Either::Left(Either::Right(m))),
            AChooseWithDefaultOwned::C(m) => Either::Left(Either::Right(m)),
            AChooseWithDefaultOwned::Unrecognized(m) => Either::Right(m),
        }
    }
}

impl From<AChooseWithDefaultOwnedInner> for AChooseWithDefaultOwned {
    fn ex_from(m: AChooseWithDefaultOwnedInner) -> AChooseWithDefaultOwned {
        match m {
            Either::Left(Either::Left(Either::Left(m))) => AChooseWithDefaultOwned::A(m),
            Either::Left(Either::Left(Either::Right(m))) => AChooseWithDefaultOwned::B(m),
            Either::Left(Either::Right(m)) => AChooseWithDefaultOwned::C(m),
            Either::Right(m) => AChooseWithDefaultOwned::Unrecognized(m),
        }
    }
}

pub type ARegularChooseCombinator = Mapped<
    OrdChoice<OrdChoice<Cond<U8>, Cond<U16>>, Cond<U32>>,
    ARegularChooseMapper,
>;

pub type AClosedEnumCombinator = TryMap<U8, AClosedEnumMapper>;

pub type AnOpenEnumCombinator = U8;

pub type AChooseWithDefaultCombinator = Mapped<
    OrdChoice<OrdChoice<OrdChoice<Cond<U8>, Cond<U16>>, Cond<U32>>, Cond<Tail>>,
    AChooseWithDefaultMapper,
>;

pub open spec fn spec_a_regular_choose(e: SpecAClosedEnum) -> ARegularChooseCombinator {
    Mapped {
        inner: OrdChoice(
            OrdChoice(
                Cond { cond: e == AClosedEnum::A, inner: U8 },
                Cond { cond: e == AClosedEnum::B, inner: U16 },
            ),
            Cond { cond: e == AClosedEnum::C, inner: U32 },
        ),
        mapper: ARegularChooseMapper,
    }
}

pub fn a_regular_choose(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures
        o@ == spec_a_regular_choose(e@),
{
    Mapped {
        inner: OrdChoice(
            OrdChoice(
                Cond { cond: e == AClosedEnum::A, inner: U8 },
                Cond { cond: e == AClosedEnum::B, inner: U16 },
            ),
            Cond { cond: e == AClosedEnum::C, inner: U32 },
        ),
        mapper: ARegularChooseMapper,
    }
}

pub open spec fn spec_a_closed_enum() -> AClosedEnumCombinator {
    TryMap { inner: U8, mapper: AClosedEnumMapper }
}

pub fn a_closed_enum() -> (o: AClosedEnumCombinator)
    ensures
        o@ == spec_a_closed_enum(),
{
    TryMap { inner: U8, mapper: AClosedEnumMapper }
}

pub open spec fn spec_an_open_enum() -> AnOpenEnumCombinator {
    U8
}

pub fn an_open_enum() -> (o: AnOpenEnumCombinator)
    ensures
        o@ == spec_an_open_enum(),
{
    U8
}

pub open spec fn spec_a_choose_with_default(e: SpecAnOpenEnum) -> AChooseWithDefaultCombinator {
    Mapped {
        inner: OrdChoice(
            OrdChoice(
                OrdChoice(Cond { cond: e == 0, inner: U8 }, Cond { cond: e == 1, inner: U16 }),
                Cond { cond: e == 2, inner: U32 },
            ),
            Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
        ),
        mapper: AChooseWithDefaultMapper,
    }
}

pub fn a_choose_with_default<'a>(e: AnOpenEnum) -> (o: AChooseWithDefaultCombinator)
    ensures
        o@ == spec_a_choose_with_default(e@),
{
    Mapped {
        inner: OrdChoice(
            OrdChoice(
                OrdChoice(Cond { cond: e == 0, inner: U8 }, Cond { cond: e == 1, inner: U16 }),
                Cond { cond: e == 2, inner: U32 },
            ),
            Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
        ),
        mapper: AChooseWithDefaultMapper,
    }
}

pub open spec fn parse_spec_a_regular_choose(i: Seq<u8>, e: SpecAClosedEnum) -> Result<
    (usize, SpecARegularChoose),
    (),
> {
    spec_a_regular_choose(e).spec_parse(i)
}

pub open spec fn serialize_spec_a_regular_choose(
    msg: SpecARegularChoose,
    e: SpecAClosedEnum,
) -> Result<Seq<u8>, ()> {
    spec_a_regular_choose(e).spec_serialize(msg)
}

pub fn parse_a_regular_choose(i: &[u8], e: AClosedEnum) -> (o: Result<(usize, ARegularChoose), ()>)
    ensures
        o matches Ok(r) ==> parse_spec_a_regular_choose(i@, e@) matches Ok(r_) && r@ == r_,
{
    a_regular_choose(e).parse(i)
}

pub fn serialize_a_regular_choose(
    msg: ARegularChoose,
    data: &mut Vec<u8>,
    pos: usize,
    e: AClosedEnum,
) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_regular_choose(msg@, e@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    a_regular_choose(e).serialize(msg, data, pos)
}

pub open spec fn parse_spec_a_closed_enum(i: Seq<u8>) -> Result<(usize, SpecAClosedEnum), ()> {
    spec_a_closed_enum().spec_parse(i)
}

pub open spec fn serialize_spec_a_closed_enum(msg: SpecAClosedEnum) -> Result<Seq<u8>, ()> {
    spec_a_closed_enum().spec_serialize(msg)
}

pub fn parse_a_closed_enum(i: &[u8]) -> (o: Result<(usize, AClosedEnum), ()>)
    ensures
        o matches Ok(r) ==> parse_spec_a_closed_enum(i@) matches Ok(r_) && r@ == r_,
{
    a_closed_enum().parse(i)
}

pub fn serialize_a_closed_enum(msg: AClosedEnum, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    (),
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_closed_enum(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    a_closed_enum().serialize(msg, data, pos)
}

pub open spec fn parse_spec_an_open_enum(i: Seq<u8>) -> Result<(usize, SpecAnOpenEnum), ()> {
    spec_an_open_enum().spec_parse(i)
}

pub open spec fn serialize_spec_an_open_enum(msg: SpecAnOpenEnum) -> Result<Seq<u8>, ()> {
    spec_an_open_enum().spec_serialize(msg)
}

pub fn parse_an_open_enum(i: &[u8]) -> (o: Result<(usize, AnOpenEnum), ()>)
    ensures
        o matches Ok(r) ==> parse_spec_an_open_enum(i@) matches Ok(r_) && r@ == r_,
{
    an_open_enum().parse(i)
}

pub fn serialize_an_open_enum(msg: AnOpenEnum, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    (),
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_an_open_enum(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    an_open_enum().serialize(msg, data, pos)
}

pub open spec fn parse_spec_a_choose_with_default(i: Seq<u8>, e: SpecAnOpenEnum) -> Result<
    (usize, SpecAChooseWithDefault),
    (),
> {
    spec_a_choose_with_default(e).spec_parse(i)
}

pub open spec fn serialize_spec_a_choose_with_default(
    msg: SpecAChooseWithDefault,
    e: SpecAnOpenEnum,
) -> Result<Seq<u8>, ()> {
    spec_a_choose_with_default(e).spec_serialize(msg)
}

pub fn parse_a_choose_with_default(i: &[u8], e: AnOpenEnum) -> (o: Result<
    (usize, AChooseWithDefault<'_>),
    (),
>)
    ensures
        o matches Ok(r) ==> parse_spec_a_choose_with_default(i@, e@) matches Ok(r_) && r@ == r_,
{
    a_choose_with_default(e).parse(i)
}

pub fn serialize_a_choose_with_default(
    msg: AChooseWithDefault<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    e: AnOpenEnum,
) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_choose_with_default(msg@, e@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    a_choose_with_default(e).serialize(msg, data, pos)
}

} // verus!
