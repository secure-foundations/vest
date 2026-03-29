#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
use vest_lib::properties::*;
use vest_lib::errors::*;
use vest_lib::regular::*;
use vest_lib::regular::sequence::{Pair, Preceded, Terminated, DepCombinator};
use vest_lib::regular::variant::{Either, Dispatch, Opt, OptThen, Choice};
use vest_lib::regular::repetition::{Repeat, RepeatN};
use vest_lib::regular::modifier::{
    Refined, Mapped, FixedLen, Length, RuntimeValue, AndThen, CondEq, Mapper,
};
use vest_lib::regular::tag::Tag;
use vest_lib::regular::bytes::{Fixed, Variable, Tail};
use vest_lib::regular::success::Success;
use vest_lib::regular::fail::Fail;
use vest_lib::regular::end::End;
use vest_lib::regular::uints::*;
use vest_lib::buf_traits::{VestInput, VestOutput};
///Type alias for Header combinator
pub type HeaderCombinatorAlias = (Tag<U16Le, u16>, (U8, U8));
///Wrapper struct for Header combinator
pub struct HeaderCombinator(pub HeaderCombinatorAlias);
impl<I, O> Combinator<I, O> for HeaderCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    HeaderCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <HeaderCombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <HeaderCombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <HeaderCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <HeaderCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <HeaderCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <HeaderCombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <HeaderCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <HeaderCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for Header combinator
pub fn Header() -> HeaderCombinator {
    HeaderCombinator((Tag::new(U16Le, 51966), (U8, U8)))
}

///Parse function for Header combinator
pub fn parse_Header(
    input: &[u8],
) -> Result<
    (usize, <HeaderCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Header();
    <HeaderCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for Header combinator
pub fn serialize_Header(
    v: <HeaderCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Header();
    <HeaderCombinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for Header combinator
pub fn Header_len(
    v: <HeaderCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Header();
    <HeaderCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

///Type alias for Record combinator
pub type RecordCombinatorAlias = (U32Le, U32Le);
///Wrapper struct for Record combinator
pub struct RecordCombinator(pub RecordCombinatorAlias);
impl<I, O> Combinator<I, O> for RecordCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    RecordCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <RecordCombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <RecordCombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <RecordCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <RecordCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <RecordCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <RecordCombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <RecordCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <RecordCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for Record combinator
pub fn Record() -> RecordCombinator {
    RecordCombinator((U32Le, U32Le))
}

///Parse function for Record combinator
pub fn parse_Record(
    input: &[u8],
) -> Result<
    (usize, <RecordCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Record();
    <RecordCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for Record combinator
pub fn serialize_Record(
    v: <RecordCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Record();
    <RecordCombinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for Record combinator
pub fn Record_len(
    v: <RecordCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Record();
    <RecordCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

#[derive(Clone, Copy)]
pub struct RefinedPacketDep1 {}
impl<I, O> DepCombinator<Refined<U16Le, fn(u16) -> bool>, I, O> for RefinedPacketDep1
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Refined<U16Le, fn(u16) -> bool>: Combinator<I, O>,
    FixedLen<'static, Repeat<RecordCombinator>>: Combinator<I, O>,
{
    type Out = FixedLen<'static, Repeat<RecordCombinator>>;
    type OutGen<'g> = FixedLen<'g, Repeat<RecordCombinator>>;
    fn dep_snd<'s>(
        &self,
        fst: <Refined<U16Le, fn(u16) -> bool> as Combinator<I, O>>::SType<'s>,
    ) -> Self::Out {
        let payload_len = fst;
        FixedLen(Length::from_value(payload_len as usize), Repeat::new(Record()))
    }
    fn dep_snd_gen<'g>(
        &self,
        fst: &'g mut <Refined<U16Le, fn(u16) -> bool> as Combinator<I, O>>::GType,
    ) -> Self::OutGen<'g> {
        let payload_len = fst;
        FixedLen(Length::from_u16_mut(payload_len), Repeat::new(Record()))
    }
}

///Type alias for RefinedPacket combinator
pub type RefinedPacketCombinatorAlias = (
    HeaderCombinator,
    Pair<Refined<U16Le, fn(u16) -> bool>, RefinedPacketDep1>,
);
///Wrapper struct for RefinedPacket combinator
pub struct RefinedPacketCombinator(pub RefinedPacketCombinatorAlias);
impl<I, O> Combinator<I, O> for RefinedPacketCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    RefinedPacketCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <RefinedPacketCombinatorAlias as Combinator<I, O>>::Type<'p>
    where
        I: 'p;
    type SType<'s> = <RefinedPacketCombinatorAlias as Combinator<I, O>>::SType<'s>
    where
        I: 's;
    type GType = <RefinedPacketCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <RefinedPacketCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<
            I,
            O,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <RefinedPacketCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for RefinedPacket combinator
pub fn RefinedPacket() -> RefinedPacketCombinator {
    RefinedPacketCombinator((
        Header(),
        Pair::new(
            Refined {
                inner: U16Le,
                predicate: |v: u16| (v as i128 >= 8 && v as i128 <= 10000),
            },
            RefinedPacketDep1 {},
        ),
    ))
}

///Parse function for RefinedPacket combinator
pub fn parse_RefinedPacket(
    input: &[u8],
) -> Result<
    (usize, <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = RefinedPacket();
    <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for RefinedPacket combinator
pub fn serialize_RefinedPacket(
    v: <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = RefinedPacket();
    <RefinedPacketCombinator as Combinator<
        [u8],
        Vec<u8>,
    >>::serialize(&combinator, v, data, pos)
}

///Length function for RefinedPacket combinator
pub fn RefinedPacket_len(
    v: <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = RefinedPacket();
    <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

///Type alias for msg3 combinator
pub type Msg3CombinatorAlias = (U16Le, U16Le);
///Wrapper struct for msg3 combinator
pub struct Msg3Combinator(pub Msg3CombinatorAlias);
impl<I, O> Combinator<I, O> for Msg3Combinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg3CombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <Msg3CombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <Msg3CombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <Msg3CombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <Msg3CombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <Msg3CombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <Msg3CombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg3CombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <Msg3CombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for msg3 combinator
pub fn msg3() -> Msg3Combinator {
    Msg3Combinator((U16Le, U16Le))
}

///Parse function for msg3 combinator
pub fn parse_msg3(
    input: &[u8],
) -> Result<
    (usize, <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg3();
    <Msg3Combinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for msg3 combinator
pub fn serialize_msg3(
    v: <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg3();
    <Msg3Combinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for msg3 combinator
pub fn msg3_len(v: <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg3();
    <Msg3Combinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

///Type alias for msg1 combinator
pub type Msg1CombinatorAlias = Fixed<32>;
///Wrapper struct for msg1 combinator
pub struct Msg1Combinator(pub Msg1CombinatorAlias);
impl<I, O> Combinator<I, O> for Msg1Combinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg1CombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <Msg1CombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <Msg1CombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <Msg1CombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <Msg1CombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <Msg1CombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <Msg1CombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg1CombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <Msg1CombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for msg1 combinator
pub fn msg1() -> Msg1Combinator {
    Msg1Combinator(Fixed::<32>)
}

///Parse function for msg1 combinator
pub fn parse_msg1(
    input: &[u8],
) -> Result<
    (usize, <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg1();
    <Msg1Combinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for msg1 combinator
pub fn serialize_msg1(
    v: <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg1();
    <Msg1Combinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for msg1 combinator
pub fn msg1_len(v: <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg1();
    <Msg1Combinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

///Type alias for msg2 combinator
pub type Msg2CombinatorAlias = RefinedPacketCombinator;
///Wrapper struct for msg2 combinator
pub struct Msg2Combinator(pub Msg2CombinatorAlias);
impl<I, O> Combinator<I, O> for Msg2Combinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg2CombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <Msg2CombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <Msg2CombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <Msg2CombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <Msg2CombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <Msg2CombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <Msg2CombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg2CombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <Msg2CombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for msg2 combinator
pub fn msg2() -> Msg2Combinator {
    Msg2Combinator(RefinedPacket())
}

///Parse function for msg2 combinator
pub fn parse_msg2(
    input: &[u8],
) -> Result<
    (usize, <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg2();
    <Msg2Combinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for msg2 combinator
pub fn serialize_msg2(
    v: <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg2();
    <Msg2Combinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for msg2 combinator
pub fn msg2_len(v: <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg2();
    <Msg2Combinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

pub enum MsgValDispatchCase0 {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
}

impl<I, O> Combinator<I, O> for MsgValDispatchCase0
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg1Combinator: Combinator<I, O>,
    Msg2Combinator: Combinator<I, O>,
    Msg3Combinator: Combinator<I, O>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<I, O>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::Type<'p>,
            <Msg3Combinator as Combinator<I, O>>::Type<'p>,
        >,
    >
    where
        I: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<I, O>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::SType<'s>,
            <Msg3Combinator as Combinator<I, O>>::SType<'s>,
        >,
    >
    where
        I: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<I, O>>::GType,
        Either<
            <Msg2Combinator as Combinator<I, O>>::GType,
            <Msg3Combinator as Combinator<I, O>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCase0::V1(inner), Either::Left(v0)) => inner.length(v0),
            (MsgValDispatchCase0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.length(v1)
            }
            (MsgValDispatchCase0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.length(v2)
            }
            _ => panic!("dispatch branch combinator does not match value"),
        }
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        match self {
            MsgValDispatchCase0::V1(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Left(v)))
            }
            MsgValDispatchCase0::V2(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgValDispatchCase0::V3(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
        }
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCase0::V1(inner), Either::Left(v0)) => {
                inner.serialize(v0, data, pos)
            }
            (MsgValDispatchCase0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.serialize(v1, data, pos)
            }
            (MsgValDispatchCase0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.serialize(v2, data, pos)
            }
            _ => {
                Err(
                    SerializeError::Other(
                        "dispatch branch combinator does not match value".into(),
                    ),
                )
            }
        }
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        match self {
            MsgValDispatchCase0::V1(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Left(v)))
            }
            MsgValDispatchCase0::V2(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgValDispatchCase0::V3(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
        }
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCase0::V1(inner), Either::Left(v0)) => inner.well_formed(v0),
            (MsgValDispatchCase0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.well_formed(v1)
            }
            (MsgValDispatchCase0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.well_formed(v2)
            }
            _ => false,
        }
    }
}

pub enum MsgValDispatchCaseGen0<'g> {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
    __Phantom(std::marker::PhantomData<&'g ()>),
}

impl<'g, I, O> Combinator<I, O> for MsgValDispatchCaseGen0<'g>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg1Combinator: Combinator<I, O>,
    Msg2Combinator: Combinator<I, O>,
    Msg3Combinator: Combinator<I, O>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<I, O>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::Type<'p>,
            <Msg3Combinator as Combinator<I, O>>::Type<'p>,
        >,
    >
    where
        I: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<I, O>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::SType<'s>,
            <Msg3Combinator as Combinator<I, O>>::SType<'s>,
        >,
    >
    where
        I: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<I, O>>::GType,
        Either<
            <Msg2Combinator as Combinator<I, O>>::GType,
            <Msg3Combinator as Combinator<I, O>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCaseGen0::V1(inner), Either::Left(v0)) => inner.length(v0),
            (MsgValDispatchCaseGen0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.length(v1)
            }
            (MsgValDispatchCaseGen0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.length(v2)
            }
            _ => panic!("dispatch branch combinator does not match value"),
        }
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        match self {
            MsgValDispatchCaseGen0::V1(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Left(v)))
            }
            MsgValDispatchCaseGen0::V2(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgValDispatchCaseGen0::V3(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
            MsgValDispatchCaseGen0::__Phantom(_) => {
                unreachable!("phantom dispatch variant")
            }
        }
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCaseGen0::V1(inner), Either::Left(v0)) => {
                inner.serialize(v0, data, pos)
            }
            (MsgValDispatchCaseGen0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.serialize(v1, data, pos)
            }
            (MsgValDispatchCaseGen0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.serialize(v2, data, pos)
            }
            _ => {
                Err(
                    SerializeError::Other(
                        "dispatch branch combinator does not match value".into(),
                    ),
                )
            }
        }
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        match self {
            MsgValDispatchCaseGen0::V1(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Left(v)))
            }
            MsgValDispatchCaseGen0::V2(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgValDispatchCaseGen0::V3(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
            MsgValDispatchCaseGen0::__Phantom(_) => {
                unreachable!("phantom dispatch variant")
            }
        }
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        match (self, v) {
            (MsgValDispatchCaseGen0::V1(inner), Either::Left(v0)) => {
                inner.well_formed(v0)
            }
            (MsgValDispatchCaseGen0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.well_formed(v1)
            }
            (MsgValDispatchCaseGen0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.well_formed(v2)
            }
            _ => false,
        }
    }
}

///Type alias for msg_val combinator
pub type MsgValCombinatorAlias = FixedLen<
    'static,
    Dispatch<'static, u8, MsgValDispatchCase0, 3>,
>;
///Wrapper struct for msg_val combinator
pub struct MsgValCombinator(pub MsgValCombinatorAlias);
impl<I, O> Combinator<I, O> for MsgValCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    MsgValCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <MsgValCombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <MsgValCombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <MsgValCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <MsgValCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <MsgValCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <MsgValCombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <MsgValCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <MsgValCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for msg_val combinator
pub fn msg_val(len: u16, tag: u8) -> MsgValCombinator {
    MsgValCombinator(
        FixedLen(
            Length::from_value(len as usize),
            Dispatch::new(
                RuntimeValue::from_value(tag),
                [
                    (1, MsgValDispatchCase0::V1(msg1())),
                    (2, MsgValDispatchCase0::V2(msg2())),
                    (3, MsgValDispatchCase0::V3(msg3())),
                ],
            ),
        ),
    )
}

///Parse function for msg_val combinator
pub fn parse_msg_val(
    input: &[u8],
    len: u16,
    tag: u8,
) -> Result<
    (usize, <MsgValCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg_val(len, tag);
    <MsgValCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for msg_val combinator
pub fn serialize_msg_val(
    v: <MsgValCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    len: u16,
    tag: u8,
) -> Result<usize, SerializeError> {
    let combinator = msg_val(len, tag);
    <MsgValCombinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for msg_val combinator
pub fn msg_val_len(
    v: <MsgValCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    len: u16,
    tag: u8,
) -> usize {
    let combinator = msg_val(len, tag);
    <MsgValCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

pub enum MsgDispatchCase1_0_0 {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
}

impl<I, O> Combinator<I, O> for MsgDispatchCase1_0_0
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg1Combinator: Combinator<I, O>,
    Msg2Combinator: Combinator<I, O>,
    Msg3Combinator: Combinator<I, O>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<I, O>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::Type<'p>,
            <Msg3Combinator as Combinator<I, O>>::Type<'p>,
        >,
    >
    where
        I: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<I, O>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::SType<'s>,
            <Msg3Combinator as Combinator<I, O>>::SType<'s>,
        >,
    >
    where
        I: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<I, O>>::GType,
        Either<
            <Msg2Combinator as Combinator<I, O>>::GType,
            <Msg3Combinator as Combinator<I, O>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCase1_0_0::V1(inner), Either::Left(v0)) => inner.length(v0),
            (MsgDispatchCase1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.length(v1)
            }
            (MsgDispatchCase1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.length(v2)
            }
            _ => panic!("dispatch branch combinator does not match value"),
        }
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        match self {
            MsgDispatchCase1_0_0::V1(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Left(v)))
            }
            MsgDispatchCase1_0_0::V2(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgDispatchCase1_0_0::V3(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
        }
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCase1_0_0::V1(inner), Either::Left(v0)) => {
                inner.serialize(v0, data, pos)
            }
            (MsgDispatchCase1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.serialize(v1, data, pos)
            }
            (MsgDispatchCase1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.serialize(v2, data, pos)
            }
            _ => {
                Err(
                    SerializeError::Other(
                        "dispatch branch combinator does not match value".into(),
                    ),
                )
            }
        }
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        match self {
            MsgDispatchCase1_0_0::V1(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Left(v)))
            }
            MsgDispatchCase1_0_0::V2(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgDispatchCase1_0_0::V3(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
        }
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCase1_0_0::V1(inner), Either::Left(v0)) => inner.well_formed(v0),
            (MsgDispatchCase1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.well_formed(v1)
            }
            (MsgDispatchCase1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.well_formed(v2)
            }
            _ => false,
        }
    }
}

pub enum MsgDispatchCaseGen1_0_0<'g> {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
    __Phantom(std::marker::PhantomData<&'g ()>),
}

impl<'g, I, O> Combinator<I, O> for MsgDispatchCaseGen1_0_0<'g>
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    Msg1Combinator: Combinator<I, O>,
    Msg2Combinator: Combinator<I, O>,
    Msg3Combinator: Combinator<I, O>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<I, O>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::Type<'p>,
            <Msg3Combinator as Combinator<I, O>>::Type<'p>,
        >,
    >
    where
        I: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<I, O>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<I, O>>::SType<'s>,
            <Msg3Combinator as Combinator<I, O>>::SType<'s>,
        >,
    >
    where
        I: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<I, O>>::GType,
        Either<
            <Msg2Combinator as Combinator<I, O>>::GType,
            <Msg3Combinator as Combinator<I, O>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCaseGen1_0_0::V1(inner), Either::Left(v0)) => inner.length(v0),
            (MsgDispatchCaseGen1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.length(v1)
            }
            (MsgDispatchCaseGen1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.length(v2)
            }
            _ => panic!("dispatch branch combinator does not match value"),
        }
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        match self {
            MsgDispatchCaseGen1_0_0::V1(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Left(v)))
            }
            MsgDispatchCaseGen1_0_0::V2(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgDispatchCaseGen1_0_0::V3(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
            MsgDispatchCaseGen1_0_0::__Phantom(_) => {
                unreachable!("phantom dispatch variant")
            }
        }
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCaseGen1_0_0::V1(inner), Either::Left(v0)) => {
                inner.serialize(v0, data, pos)
            }
            (MsgDispatchCaseGen1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.serialize(v1, data, pos)
            }
            (MsgDispatchCaseGen1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.serialize(v2, data, pos)
            }
            _ => {
                Err(
                    SerializeError::Other(
                        "dispatch branch combinator does not match value".into(),
                    ),
                )
            }
        }
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        match self {
            MsgDispatchCaseGen1_0_0::V1(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Left(v)))
            }
            MsgDispatchCaseGen1_0_0::V2(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Left(v))))
            }
            MsgDispatchCaseGen1_0_0::V3(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, Either::Right(Either::Right(v))))
            }
            MsgDispatchCaseGen1_0_0::__Phantom(_) => {
                unreachable!("phantom dispatch variant")
            }
        }
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        match (self, v) {
            (MsgDispatchCaseGen1_0_0::V1(inner), Either::Left(v0)) => {
                inner.well_formed(v0)
            }
            (MsgDispatchCaseGen1_0_0::V2(inner), Either::Right(Either::Left(v1))) => {
                inner.well_formed(v1)
            }
            (MsgDispatchCaseGen1_0_0::V3(inner), Either::Right(Either::Right(v2))) => {
                inner.well_formed(v2)
            }
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
pub struct MsgDep {}
impl<I, O> DepCombinator<(U8, Refined<U16Le, fn(u16) -> bool>), I, O> for MsgDep
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    (U8, Refined<U16Le, fn(u16) -> bool>): Combinator<I, O>,
    FixedLen<'static, Dispatch<'static, u8, MsgDispatchCase1_0_0, 3>>: Combinator<I, O>,
{
    type Out = FixedLen<'static, Dispatch<'static, u8, MsgDispatchCase1_0_0, 3>>;
    type OutGen<'g> = FixedLen<'g, Dispatch<'g, u8, MsgDispatchCaseGen1_0_0<'g>, 3>>;
    fn dep_snd<'s>(
        &self,
        fst: <(U8, Refined<U16Le, fn(u16) -> bool>) as Combinator<I, O>>::SType<'s>,
    ) -> Self::Out {
        let tag = fst.0;
        let len = fst.1;
        FixedLen(
            Length::from_value(len as usize),
            Dispatch::new(
                RuntimeValue::from_value(tag),
                [
                    (1, MsgDispatchCase1_0_0::V1(msg1())),
                    (2, MsgDispatchCase1_0_0::V2(msg2())),
                    (3, MsgDispatchCase1_0_0::V3(msg3())),
                ],
            ),
        )
    }
    fn dep_snd_gen<'g>(
        &self,
        fst: &'g mut <(U8, Refined<U16Le, fn(u16) -> bool>) as Combinator<I, O>>::GType,
    ) -> Self::OutGen<'g> {
        let tag = &mut fst.0;
        let len = &mut fst.1;
        FixedLen(
            Length::from_u16_mut(len),
            Dispatch::new(
                RuntimeValue::from_mut(tag),
                [
                    (1, MsgDispatchCaseGen1_0_0::V1(msg1())),
                    (2, MsgDispatchCaseGen1_0_0::V2(msg2())),
                    (3, MsgDispatchCaseGen1_0_0::V3(msg3())),
                ],
            ),
        )
    }
}

///Type alias for msg combinator
pub type MsgCombinatorAlias = Pair<(U8, Refined<U16Le, fn(u16) -> bool>), MsgDep>;
///Wrapper struct for msg combinator
pub struct MsgCombinator(pub MsgCombinatorAlias);
impl<I, O> Combinator<I, O> for MsgCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    MsgCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <MsgCombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <MsgCombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <MsgCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <MsgCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <MsgCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut O,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        I: 's,
    {
        <MsgCombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <MsgCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <MsgCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}

///Constructor for msg combinator
pub fn msg() -> MsgCombinator {
    MsgCombinator(
        Pair::new(
            (
                U8,
                Refined {
                    inner: U16Le,
                    predicate: |v: u16| (v as i128 >= 0 && v as i128 <= 8000),
                },
            ),
            MsgDep {},
        ),
    )
}

///Parse function for msg combinator
pub fn parse_msg(
    input: &[u8],
) -> Result<
    (usize, <MsgCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg();
    <MsgCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for msg combinator
pub fn serialize_msg(
    v: <MsgCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg();
    <MsgCombinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for msg combinator
pub fn msg_len(v: <MsgCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg();
    <MsgCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Header {
    pub field0: u16,
    pub field1: u8,
    pub field2: u8,
}

impl From<(u16, (u8, u8))> for Header {
    fn from((v0, (v1, v2)): (u16, (u8, u8))) -> Self {
        Self {
            field0: v0,
            field1: v1,
            field2: v2,
        }
    }
}

impl<'s> From<&'s Header> for (u16, (u8, u8)) {
    fn from(v: &'s Header) -> Self {
        (v.field0, (v.field1, v.field2))
    }
}

pub struct HeaderMapper;
impl Mapper for HeaderMapper {
    type Src<'p> = (u16, (u8, u8));
    type Dst<'p> = Header;
    type SrcBorrow<'s> = (u16, (u8, u8));
    type DstBorrow<'s> = &'s Header;
    type SrcOwned = (u16, (u8, u8));
    type DstOwned = Header;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Record {
    pub field0: u32,
    pub field1: u32,
}

impl From<(u32, u32)> for Record {
    fn from((v0, v1): (u32, u32)) -> Self {
        Self { field0: v0, field1: v1 }
    }
}

impl<'s> From<&'s Record> for (u32, u32) {
    fn from(v: &'s Record) -> Self {
        (v.field0, v.field1)
    }
}

pub struct RecordMapper;
impl Mapper for RecordMapper {
    type Src<'p> = (u32, u32);
    type Dst<'p> = Record;
    type SrcBorrow<'s> = (u32, u32);
    type DstBorrow<'s> = &'s Record;
    type SrcOwned = (u32, u32);
    type DstOwned = Record;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefinedPacket {
    pub field0: Header,
    pub field1: (),
}

impl From<(Header, ())> for RefinedPacket {
    fn from((v0, v1): (Header, ())) -> Self {
        Self { field0: v0, field1: v1 }
    }
}

impl<'s> From<&'s RefinedPacket> for (Header, ()) {
    fn from(v: &'s RefinedPacket) -> Self {
        (v.field0, v.field1)
    }
}

pub struct RefinedPacketMapper;
impl Mapper for RefinedPacketMapper {
    type Src<'p> = (Header, ());
    type Dst<'p> = RefinedPacket;
    type SrcBorrow<'s> = (Header, ());
    type DstBorrow<'s> = &'s RefinedPacket;
    type SrcOwned = (Header, ());
    type DstOwned = RefinedPacket;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg3 {
    pub field0: u16,
    pub field1: u16,
}

impl From<(u16, u16)> for Msg3 {
    fn from((v0, v1): (u16, u16)) -> Self {
        Self { field0: v0, field1: v1 }
    }
}

impl<'s> From<&'s Msg3> for (u16, u16) {
    fn from(v: &'s Msg3) -> Self {
        (v.field0, v.field1)
    }
}

pub struct Msg3Mapper;
impl Mapper for Msg3Mapper {
    type Src<'p> = (u16, u16);
    type Dst<'p> = Msg3;
    type SrcBorrow<'s> = (u16, u16);
    type DstBorrow<'s> = &'s Msg3;
    type SrcOwned = (u16, u16);
    type DstOwned = Msg3;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValValue {
    Case1(Msg1),
    Case2(Msg2),
    Case3(Msg3),
}

impl From<Either<Msg1, Either<Msg2, Msg3>>> for MsgValValue {
    fn from(e: Either<Msg1, Either<Msg2, Msg3>>) -> Self {
        match e {
            Either::Left(v) => MsgValValue::Case1(v),
            Either::Right(Either::Left(v)) => MsgValValue::Case2(v),
            Either::Right(Either::Right(v)) => MsgValValue::Case3(v),
        }
    }
}

impl<'s> From<&'s MsgValValue> for Either<Msg1, Either<Msg2, Msg3>> {
    fn from(e: &'s MsgValValue) -> Self {
        match e {
            MsgValValue::Case1(v) => Either::Left(*v),
            MsgValValue::Case2(v) => Either::Right(Either::Left(*v)),
            MsgValValue::Case3(v) => Either::Right(Either::Right(*v)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg {
    pub tag: u8,
    pub len: u16,
    pub field2: MsgVal,
}

impl From<(u8, (u16, MsgVal))> for Msg {
    fn from((v0, (v1, v2)): (u8, (u16, MsgVal))) -> Self {
        Self {
            tag: v0,
            len: v1,
            field2: v2,
        }
    }
}

impl<'s> From<&'s Msg> for (u8, (u16, MsgVal)) {
    fn from(v: &'s Msg) -> Self {
        (v.tag, (v.len, v.field2))
    }
}

pub struct MsgMapper;
impl Mapper for MsgMapper {
    type Src<'p> = (u8, (u16, MsgVal));
    type Dst<'p> = Msg;
    type SrcBorrow<'s> = (u8, (u16, MsgVal));
    type DstBorrow<'s> = &'s Msg;
    type SrcOwned = (u8, (u16, MsgVal));
    type DstOwned = Msg;
}
