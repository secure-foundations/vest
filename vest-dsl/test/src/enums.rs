#![allow(unused_imports)]
use std::marker::PhantomData;
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

pub type SpecAnOpenEnum = u8;

pub type AnOpenEnum = u8;

pub type SpecAnOpenEnumCombinator = U8;

pub type AnOpenEnumCombinator = U8;

pub open spec fn spec_an_open_enum() -> SpecAnOpenEnumCombinator {
    U8
}

pub fn an_open_enum() -> (o: AnOpenEnumCombinator)
    ensures
        o@ == spec_an_open_enum(),
{
    U8
}

pub open spec fn parse_spec_an_open_enum(i: Seq<u8>) -> Result<(usize, SpecAnOpenEnum), ()> {
    spec_an_open_enum().spec_parse(i)
}

pub open spec fn serialize_spec_an_open_enum(msg: SpecAnOpenEnum) -> Result<Seq<u8>, ()> {
    spec_an_open_enum().spec_serialize(msg)
}

pub fn parse_an_open_enum(i: &[u8]) -> (o: Result<(usize, AnOpenEnum), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_an_open_enum(i@) matches Ok(r_) && r@ == r_,
{
    let c = an_open_enum();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_an_open_enum(msg: AnOpenEnum, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_an_open_enum(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = an_open_enum();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAClosedEnum = AClosedEnum;

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
    type Src = AClosedEnumInner;

    type Dst = AClosedEnum;
}

pub type SpecAClosedEnumCombinator = TryMap<U8, AClosedEnumMapper>;

pub type AClosedEnumCombinator = TryMap<U8, AClosedEnumMapper>;

pub open spec fn spec_a_closed_enum() -> SpecAClosedEnumCombinator {
    TryMap { inner: U8, mapper: AClosedEnumMapper }
}

pub fn a_closed_enum() -> (o: AClosedEnumCombinator)
    ensures
        o@ == spec_a_closed_enum(),
{
    TryMap { inner: U8, mapper: AClosedEnumMapper }
}

pub open spec fn parse_spec_a_closed_enum(i: Seq<u8>) -> Result<(usize, SpecAClosedEnum), ()> {
    spec_a_closed_enum().spec_parse(i)
}

pub open spec fn serialize_spec_a_closed_enum(msg: SpecAClosedEnum) -> Result<Seq<u8>, ()> {
    spec_a_closed_enum().spec_serialize(msg)
}

pub fn parse_a_closed_enum(i: &[u8]) -> (o: Result<(usize, AClosedEnum), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_a_closed_enum(i@) matches Ok(r_) && r@ == r_,
{
    let c = a_closed_enum();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_a_closed_enum(msg: AClosedEnum, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_closed_enum(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = a_closed_enum();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub enum SpecARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type SpecARegularChooseInner = Either<u8, Either<u16, u32>>;

impl SpecFrom<SpecARegularChoose> for SpecARegularChooseInner {
    open spec fn spec_from(m: SpecARegularChoose) -> SpecARegularChooseInner {
        match m {
            SpecARegularChoose::A(m) => Either::Left(m),
            SpecARegularChoose::B(m) => Either::Right(Either::Left(m)),
            SpecARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl SpecFrom<SpecARegularChooseInner> for SpecARegularChoose {
    open spec fn spec_from(m: SpecARegularChooseInner) -> SpecARegularChoose {
        match m {
            Either::Left(m) => SpecARegularChoose::A(m),
            Either::Right(Either::Left(m)) => SpecARegularChoose::B(m),
            Either::Right(Either::Right(m)) => SpecARegularChoose::C(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseInner = Either<u8, Either<u16, u32>>;

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
            ARegularChoose::A(m) => Either::Left(m),
            ARegularChoose::B(m) => Either::Right(Either::Left(m)),
            ARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl From<ARegularChooseInner> for ARegularChoose {
    fn ex_from(m: ARegularChooseInner) -> ARegularChoose {
        match m {
            Either::Left(m) => ARegularChoose::A(m),
            Either::Right(Either::Left(m)) => ARegularChoose::B(m),
            Either::Right(Either::Right(m)) => ARegularChoose::C(m),
        }
    }
}

pub struct ARegularChooseMapper;

impl ARegularChooseMapper {
    pub closed spec fn spec_new() -> Self {
        ARegularChooseMapper
    }

    pub fn new() -> Self {
        ARegularChooseMapper
    }
}

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
    type Src = ARegularChooseInner;

    type Dst = ARegularChoose;
}

pub type SpecARegularChooseCombinator = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>,
    ARegularChooseMapper,
>;

pub type ARegularChooseCombinator = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, Cond<U32Le>>>,
    ARegularChooseMapper,
>;

pub open spec fn spec_a_regular_choose(e: SpecAClosedEnum) -> SpecARegularChooseCombinator {
    Mapped {
        inner: OrdChoice(
            Cond { cond: e == AClosedEnum::A, inner: U8 },
            OrdChoice(
                Cond { cond: e == AClosedEnum::B, inner: U16Le },
                Cond { cond: e == AClosedEnum::C, inner: U32Le },
            ),
        ),
        mapper: ARegularChooseMapper::spec_new(),
    }
}

pub fn a_regular_choose(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures
        o@ == spec_a_regular_choose(e@),
{
    Mapped {
        inner: OrdChoice(
            Cond { cond: e == AClosedEnum::A, inner: U8 },
            OrdChoice(
                Cond { cond: e == AClosedEnum::B, inner: U16Le },
                Cond { cond: e == AClosedEnum::C, inner: U32Le },
            ),
        ),
        mapper: ARegularChooseMapper::new(),
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

pub fn parse_a_regular_choose(i: &[u8], e: AClosedEnum) -> (o: Result<
    (usize, ARegularChoose),
    ParseError,
>)
    ensures
        o matches Ok(r) ==> parse_spec_a_regular_choose(i@, e@) matches Ok(r_) && r@ == r_,
{
    let c = a_regular_choose(e);
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_a_regular_choose(
    msg: ARegularChoose,
    data: &mut Vec<u8>,
    pos: usize,
    e: AClosedEnum,
) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_regular_choose(msg@, e@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = a_regular_choose(e);
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub enum SpecAChooseWithDefault {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecAChooseWithDefaultInner = Either<u8, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecAChooseWithDefault> for SpecAChooseWithDefaultInner {
    open spec fn spec_from(m: SpecAChooseWithDefault) -> SpecAChooseWithDefaultInner {
        match m {
            SpecAChooseWithDefault::A(m) => Either::Left(m),
            SpecAChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            SpecAChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecAChooseWithDefault::Unrecognized(m) => Either::Right(
                Either::Right(Either::Right(m)),
            ),
        }
    }
}

impl SpecFrom<SpecAChooseWithDefaultInner> for SpecAChooseWithDefault {
    open spec fn spec_from(m: SpecAChooseWithDefaultInner) -> SpecAChooseWithDefault {
        match m {
            Either::Left(m) => SpecAChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => SpecAChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecAChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecAChooseWithDefault::Unrecognized(
                m,
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AChooseWithDefault<'a> {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(&'a [u8]),
}

pub type AChooseWithDefaultInner<'a> = Either<u8, Either<u16, Either<u32, &'a [u8]>>>;

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
            AChooseWithDefault::A(m) => Either::Left(m),
            AChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            AChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            AChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl<'a> From<AChooseWithDefaultInner<'a>> for AChooseWithDefault<'a> {
    fn ex_from(m: AChooseWithDefaultInner<'a>) -> AChooseWithDefault<'a> {
        match m {
            Either::Left(m) => AChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => AChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => AChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => AChooseWithDefault::Unrecognized(m),
        }
    }
}

pub struct AChooseWithDefaultMapper<'a>(PhantomData<&'a ()>);

impl<'a> AChooseWithDefaultMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        AChooseWithDefaultMapper(PhantomData)
    }

    pub fn new() -> Self {
        AChooseWithDefaultMapper(PhantomData)
    }
}

impl View for AChooseWithDefaultMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for AChooseWithDefaultMapper<'_> {
    type Src = SpecAChooseWithDefaultInner;

    type Dst = SpecAChooseWithDefault;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for AChooseWithDefaultMapper<'a> {
    type Src = AChooseWithDefaultInner<'a>;

    type Dst = AChooseWithDefault<'a>;
}

pub type SpecAChooseWithDefaultCombinator = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
    AChooseWithDefaultMapper<'static>,
>;

pub type AChooseWithDefaultCombinator<'a> = Mapped<
    OrdChoice<Cond<U8>, OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>,
    AChooseWithDefaultMapper<'a>,
>;

pub open spec fn spec_a_choose_with_default(e: SpecAnOpenEnum) -> SpecAChooseWithDefaultCombinator {
    Mapped {
        inner: OrdChoice(
            Cond { cond: e == 0, inner: U8 },
            OrdChoice(
                Cond { cond: e == 1, inner: U16Le },
                OrdChoice(
                    Cond { cond: e == 2, inner: U32Le },
                    Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
                ),
            ),
        ),
        mapper: AChooseWithDefaultMapper::spec_new(),
    }
}

pub fn a_choose_with_default<'a>(e: AnOpenEnum) -> (o: AChooseWithDefaultCombinator<'a>)
    ensures
        o@ == spec_a_choose_with_default(e@),
{
    Mapped {
        inner: OrdChoice(
            Cond { cond: e == 0, inner: U8 },
            OrdChoice(
                Cond { cond: e == 1, inner: U16Le },
                OrdChoice(
                    Cond { cond: e == 2, inner: U32Le },
                    Cond { cond: !(e == 0 || e == 1 || e == 2), inner: Tail },
                ),
            ),
        ),
        mapper: AChooseWithDefaultMapper::new(),
    }
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
    ParseError,
>)
    ensures
        o matches Ok(r) ==> parse_spec_a_choose_with_default(i@, e@) matches Ok(r_) && r@ == r_,
{
    let c = a_choose_with_default(e);
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_a_choose_with_default(
    msg: AChooseWithDefault<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    e: AnOpenEnum,
) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_choose_with_default(msg@, e@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = a_choose_with_default(e);
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

} // verus!
