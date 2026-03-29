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
pub struct PacketDep1 {}
impl<I, O> DepCombinator<U16Le, I, O> for PacketDep1
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    U16Le: Combinator<I, O>,
    FixedLen<'static, Repeat<RecordCombinator>>: Combinator<I, O>,
{
    type Out = FixedLen<'static, Repeat<RecordCombinator>>;
    type OutGen<'g> = FixedLen<'g, Repeat<RecordCombinator>>;
    fn dep_snd<'s>(&self, fst: <U16Le as Combinator<I, O>>::SType<'s>) -> Self::Out {
        let payload_len = fst;
        FixedLen(Length::from_value(payload_len as usize), Repeat::new(Record()))
    }
    fn dep_snd_gen<'g>(
        &self,
        fst: &'g mut <U16Le as Combinator<I, O>>::GType,
    ) -> Self::OutGen<'g> {
        let payload_len = fst;
        FixedLen(Length::from_u16_mut(payload_len), Repeat::new(Record()))
    }
}
///Type alias for Packet combinator
pub type PacketCombinatorAlias = (HeaderCombinator, Pair<U16Le, PacketDep1>);
///Wrapper struct for Packet combinator
pub struct PacketCombinator(pub PacketCombinatorAlias);
impl<I, O> Combinator<I, O> for PacketCombinator
where
    I: VestInput + ?Sized,
    O: VestOutput<I>,
    PacketCombinatorAlias: Combinator<I, O>,
{
    type Type<'p> = <PacketCombinatorAlias as Combinator<I, O>>::Type<'p> where I: 'p;
    type SType<'s> = <PacketCombinatorAlias as Combinator<I, O>>::SType<'s> where I: 's;
    type GType = <PacketCombinatorAlias as Combinator<I, O>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        I: 's,
    {
        <PacketCombinatorAlias as Combinator<I, O>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p I) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        I: 'p,
    {
        <PacketCombinatorAlias as Combinator<I, O>>::parse(&self.0, s)
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
        <PacketCombinatorAlias as Combinator<I, O>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <PacketCombinatorAlias as Combinator<I, O>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        I: 's,
    {
        <PacketCombinatorAlias as Combinator<I, O>>::well_formed(&self.0, v)
    }
}
///Constructor for Packet combinator
pub fn Packet() -> PacketCombinator {
    PacketCombinator((Header(), Pair::new(U16Le, PacketDep1 {})))
}
///Parse function for Packet combinator
pub fn parse_Packet(
    input: &[u8],
) -> Result<
    (usize, <PacketCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Packet();
    <PacketCombinator as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}
///Serialize function for Packet combinator
pub fn serialize_Packet(
    v: <PacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Packet();
    <PacketCombinator as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}
///Length function for Packet combinator
pub fn Packet_len(
    v: <PacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Packet();
    <PacketCombinator as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
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
pub struct Packet {
    pub field0: Header,
    pub field1: (),
}
impl From<(Header, ())> for Packet {
    fn from((v0, v1): (Header, ())) -> Self {
        Self { field0: v0, field1: v1 }
    }
}
impl<'s> From<&'s Packet> for (Header, ()) {
    fn from(v: &'s Packet) -> Self {
        (v.field0, v.field1)
    }
}
pub struct PacketMapper;
impl Mapper for PacketMapper {
    type Src<'p> = (Header, ());
    type Dst<'p> = Packet;
    type SrcBorrow<'s> = (Header, ());
    type DstBorrow<'s> = &'s Packet;
    type SrcOwned = (Header, ());
    type DstOwned = Packet;
}
