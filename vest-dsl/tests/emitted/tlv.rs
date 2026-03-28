#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
use vest_lib::properties::*;
use vest_lib::errors::*;
use vest_lib::regular::*;
use vest_lib::regular::bytes;
use vest_lib::regular::sequence;
use vest_lib::regular::variant::{self, Either};
use vest_lib::regular::repetition;
use vest_lib::regular::modifier;
use vest_lib::regular::tag;
use vest_lib::regular::uints::*;
use vest_lib::regular::end;
use vest_lib::regular::success;
use vest_lib::regular::fail;
pub type HeaderCombinatorAlias = (tag::Tag<U16Le, u16>, (U8, U8));
pub struct HeaderCombinator(pub HeaderCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for HeaderCombinator
where
    HeaderCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <HeaderCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <HeaderCombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn Header() -> HeaderCombinator {
    HeaderCombinator((tag::Tag::new(U16Le, 51966), (U8, U8)))
}
pub fn parse_Header(
    input: &[u8],
) -> Result<
    (usize, <HeaderCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Header();
    combinator.parse(input)
}
pub fn serialize_Header(
    v: <HeaderCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Header();
    combinator.serialize(v, data, pos)
}
pub fn Header_len(
    v: <HeaderCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Header();
    combinator.length(v)
}
pub type RecordCombinatorAlias = (U32Le, U32Le);
pub struct RecordCombinator(pub RecordCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for RecordCombinator
where
    RecordCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <RecordCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <RecordCombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn Record() -> RecordCombinator {
    RecordCombinator((U32Le, U32Le))
}
pub fn parse_Record(
    input: &[u8],
) -> Result<
    (usize, <RecordCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Record();
    combinator.parse(input)
}
pub fn serialize_Record(
    v: <RecordCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Record();
    combinator.serialize(v, data, pos)
}
pub fn Record_len(
    v: <RecordCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Record();
    combinator.length(v)
}
#[derive(Clone, Copy)]
pub struct RefinedPacketDep1 {}
impl sequence::DepCombinator<modifier::Refined<U16Le, fn(u16) -> bool>, [u8], Vec<u8>>
for RefinedPacketDep1
where
    modifier::Refined<U16Le, fn(u16) -> bool>: Combinator<[u8], Vec<u8>>,
    modifier::FixedLen<
        'static,
        repetition::Repeat<RecordCombinator>,
    >: Combinator<[u8], Vec<u8>>,
{
    type Out = modifier::FixedLen<'static, repetition::Repeat<RecordCombinator>>;
    type OutGen<'g> = modifier::FixedLen<'g, repetition::Repeat<RecordCombinator>>;
    fn dep_snd<'s>(
        &self,
        fst: <modifier::Refined<
            U16Le,
            fn(u16) -> bool,
        > as Combinator<[u8], Vec<u8>>>::SType<'s>,
    ) -> Self::Out {
        let payload_len = fst;
        modifier::FixedLen(
            modifier::Length::from_value(payload_len as usize),
            repetition::Repeat::new(Record()),
        )
    }
    fn dep_snd_gen<'g>(
        &self,
        fst: &'g mut <modifier::Refined<
            U16Le,
            fn(u16) -> bool,
        > as Combinator<[u8], Vec<u8>>>::GType,
    ) -> Self::OutGen<'g> {
        let payload_len = fst;
        modifier::FixedLen(
            modifier::Length::from_u16_mut(payload_len),
            repetition::Repeat::new(Record()),
        )
    }
}
pub type RefinedPacketCombinatorAlias = (
    HeaderCombinator,
    sequence::Pair<modifier::Refined<U16Le, fn(u16) -> bool>, RefinedPacketDep1>,
);
pub struct RefinedPacketCombinator(pub RefinedPacketCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for RefinedPacketCombinator
where
    RefinedPacketCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <RefinedPacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <RefinedPacketCombinatorAlias as Combinator<
        [u8],
        Vec<u8>,
    >>::SType<'s>
    where
        [u8]: 's;
    type GType = <RefinedPacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <RefinedPacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <RefinedPacketCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <RefinedPacketCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::well_formed(&self.0, v)
    }
}
pub fn RefinedPacket() -> RefinedPacketCombinator {
    RefinedPacketCombinator((
        Header(),
        sequence::Pair::new(
            modifier::Refined {
                inner: U16Le,
                predicate: |v: u16| (v as i128 >= 8 && v as i128 <= 10000),
            },
            RefinedPacketDep1 {},
        ),
    ))
}
pub fn parse_RefinedPacket(
    input: &[u8],
) -> Result<
    (usize, <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = RefinedPacket();
    combinator.parse(input)
}
pub fn serialize_RefinedPacket(
    v: <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = RefinedPacket();
    combinator.serialize(v, data, pos)
}
pub fn RefinedPacket_len(
    v: <RefinedPacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = RefinedPacket();
    combinator.length(v)
}
pub type Msg3CombinatorAlias = (U16Le, U16Le);
pub struct Msg3Combinator(pub Msg3CombinatorAlias);
impl Combinator<[u8], Vec<u8>> for Msg3Combinator
where
    Msg3CombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <Msg3CombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <Msg3CombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn msg3() -> Msg3Combinator {
    Msg3Combinator((U16Le, U16Le))
}
pub fn parse_msg3(
    input: &[u8],
) -> Result<
    (usize, <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg3();
    combinator.parse(input)
}
pub fn serialize_msg3(
    v: <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg3();
    combinator.serialize(v, data, pos)
}
pub fn msg3_len(v: <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg3();
    combinator.length(v)
}
pub type Msg1CombinatorAlias = bytes::Fixed<32>;
pub struct Msg1Combinator(pub Msg1CombinatorAlias);
impl Combinator<[u8], Vec<u8>> for Msg1Combinator
where
    Msg1CombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <Msg1CombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <Msg1CombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn msg1() -> Msg1Combinator {
    Msg1Combinator(bytes::Fixed::<32>)
}
pub fn parse_msg1(
    input: &[u8],
) -> Result<
    (usize, <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg1();
    combinator.parse(input)
}
pub fn serialize_msg1(
    v: <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg1();
    combinator.serialize(v, data, pos)
}
pub fn msg1_len(v: <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg1();
    combinator.length(v)
}
pub type Msg2CombinatorAlias = RefinedPacketCombinator;
pub struct Msg2Combinator(pub Msg2CombinatorAlias);
impl Combinator<[u8], Vec<u8>> for Msg2Combinator
where
    Msg2CombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <Msg2CombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <Msg2CombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn msg2() -> Msg2Combinator {
    Msg2Combinator(RefinedPacket())
}
pub fn parse_msg2(
    input: &[u8],
) -> Result<
    (usize, <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg2();
    combinator.parse(input)
}
pub fn serialize_msg2(
    v: <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg2();
    combinator.serialize(v, data, pos)
}
pub fn msg2_len(v: <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg2();
    combinator.length(v)
}
pub enum MsgValDispatchCase0 {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
}
impl Combinator<[u8], Vec<u8>> for MsgValDispatchCase0
where
    Msg1Combinator: Combinator<[u8], Vec<u8>>,
    Msg2Combinator: Combinator<[u8], Vec<u8>>,
    Msg3Combinator: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        >,
    >
    where
        [u8]: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        >,
    >
    where
        [u8]: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::GType,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::GType,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
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
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
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
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
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
        [u8]: 's,
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
impl<'g> Combinator<[u8], Vec<u8>> for MsgValDispatchCaseGen0<'g>
where
    Msg1Combinator: Combinator<[u8], Vec<u8>>,
    Msg2Combinator: Combinator<[u8], Vec<u8>>,
    Msg3Combinator: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        >,
    >
    where
        [u8]: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        >,
    >
    where
        [u8]: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::GType,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::GType,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
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
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
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
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
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
        [u8]: 's,
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
pub type MsgValCombinatorAlias = modifier::FixedLen<
    'static,
    variant::Dispatch<'static, u8, MsgValDispatchCase0, 3>,
>;
pub struct MsgValCombinator(pub MsgValCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for MsgValCombinator
where
    MsgValCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <MsgValCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <MsgValCombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn msg_val(len: u16, tag: u8) -> MsgValCombinator {
    MsgValCombinator(
        modifier::FixedLen(
            modifier::Length::from_value(len as usize),
            variant::Dispatch::new(
                modifier::RuntimeValue::from_value(tag),
                [
                    (1, MsgValDispatchCase0::V1(msg1())),
                    (2, MsgValDispatchCase0::V2(msg2())),
                    (3, MsgValDispatchCase0::V3(msg3())),
                ],
            ),
        ),
    )
}
pub fn parse_msg_val(
    input: &[u8],
    len: u16,
    tag: u8,
) -> Result<
    (usize, <MsgValCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg_val(len, tag);
    combinator.parse(input)
}
pub fn serialize_msg_val(
    v: <MsgValCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    len: u16,
    tag: u8,
) -> Result<usize, SerializeError> {
    let combinator = msg_val(len, tag);
    combinator.serialize(v, data, pos)
}
pub fn msg_val_len(
    v: <MsgValCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    len: u16,
    tag: u8,
) -> usize {
    let combinator = msg_val(len, tag);
    combinator.length(v)
}
pub enum MsgDispatchCase1_0_0 {
    V1(Msg1Combinator),
    V2(Msg2Combinator),
    V3(Msg3Combinator),
}
impl Combinator<[u8], Vec<u8>> for MsgDispatchCase1_0_0
where
    Msg1Combinator: Combinator<[u8], Vec<u8>>,
    Msg2Combinator: Combinator<[u8], Vec<u8>>,
    Msg3Combinator: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        >,
    >
    where
        [u8]: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        >,
    >
    where
        [u8]: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::GType,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::GType,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
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
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
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
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
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
        [u8]: 's,
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
impl<'g> Combinator<[u8], Vec<u8>> for MsgDispatchCaseGen1_0_0<'g>
where
    Msg1Combinator: Combinator<[u8], Vec<u8>>,
    Msg2Combinator: Combinator<[u8], Vec<u8>>,
    Msg3Combinator: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::Type<'p>,
        >,
    >
    where
        [u8]: 'p;
    type SType<'s> = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::SType<'s>,
        >,
    >
    where
        [u8]: 's;
    type GType = Either<
        <Msg1Combinator as Combinator<[u8], Vec<u8>>>::GType,
        Either<
            <Msg2Combinator as Combinator<[u8], Vec<u8>>>::GType,
            <Msg3Combinator as Combinator<[u8], Vec<u8>>>::GType,
        >,
    >;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
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
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
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
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
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
        [u8]: 's,
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
impl sequence::DepCombinator<
    (U8, modifier::Refined<U16Le, fn(u16) -> bool>),
    [u8],
    Vec<u8>,
> for MsgDep
where
    (U8, modifier::Refined<U16Le, fn(u16) -> bool>): Combinator<[u8], Vec<u8>>,
    modifier::FixedLen<
        'static,
        variant::Dispatch<'static, u8, MsgDispatchCase1_0_0, 3>,
    >: Combinator<[u8], Vec<u8>>,
{
    type Out = modifier::FixedLen<
        'static,
        variant::Dispatch<'static, u8, MsgDispatchCase1_0_0, 3>,
    >;
    type OutGen<'g> = modifier::FixedLen<
        'g,
        variant::Dispatch<'g, u8, MsgDispatchCaseGen1_0_0<'g>, 3>,
    >;
    fn dep_snd<'s>(
        &self,
        fst: <(
            U8,
            modifier::Refined<U16Le, fn(u16) -> bool>,
        ) as Combinator<[u8], Vec<u8>>>::SType<'s>,
    ) -> Self::Out {
        let tag = fst.0;
        let len = fst.1;
        modifier::FixedLen(
            modifier::Length::from_value(len as usize),
            variant::Dispatch::new(
                modifier::RuntimeValue::from_value(tag),
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
        fst: &'g mut <(
            U8,
            modifier::Refined<U16Le, fn(u16) -> bool>,
        ) as Combinator<[u8], Vec<u8>>>::GType,
    ) -> Self::OutGen<'g> {
        let tag = &mut fst.0;
        let len = &mut fst.1;
        modifier::FixedLen(
            modifier::Length::from_u16_mut(len),
            variant::Dispatch::new(
                modifier::RuntimeValue::from_mut(tag),
                [
                    (1, MsgDispatchCaseGen1_0_0::V1(msg1())),
                    (2, MsgDispatchCaseGen1_0_0::V2(msg2())),
                    (3, MsgDispatchCaseGen1_0_0::V3(msg3())),
                ],
            ),
        )
    }
}
pub type MsgCombinatorAlias = sequence::Pair<
    (U8, modifier::Refined<U16Le, fn(u16) -> bool>),
    MsgDep,
>;
pub struct MsgCombinator(pub MsgCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for MsgCombinator
where
    MsgCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
    }
    fn serialize<'s>(
        &self,
        v: Self::SType<'s>,
        data: &mut Vec<u8>,
        pos: usize,
    ) -> Result<usize, SerializeError>
    where
        [u8]: 's,
    {
        <MsgCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <MsgCombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn msg() -> MsgCombinator {
    MsgCombinator(
        sequence::Pair::new(
            (
                U8,
                modifier::Refined {
                    inner: U16Le,
                    predicate: |v: u16| (v as i128 >= 0 && v as i128 <= 8000),
                },
            ),
            MsgDep {},
        ),
    )
}
pub fn parse_msg(
    input: &[u8],
) -> Result<
    (usize, <MsgCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = msg();
    combinator.parse(input)
}
pub fn serialize_msg(
    v: <MsgCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg();
    combinator.serialize(v, data, pos)
}
pub fn msg_len(v: <MsgCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>) -> usize {
    let combinator = msg();
    combinator.length(v)
}
