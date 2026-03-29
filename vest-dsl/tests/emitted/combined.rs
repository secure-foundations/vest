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
pub const HEADERMAGIC_CONST: u16 = 51966;
///Type alias for Header combinator
pub type HeaderCombinatorAlias = Mapped<(Tag<U16Le, u16>, (U8, U8)), HeaderMapper>;
///Wrapper struct for Header combinator
pub struct HeaderCombinator<C = HeaderCombinatorAlias>(pub C);
impl<C> Combinator<[u8], Vec<u8>> for HeaderCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <C as Combinator<[u8], Vec<u8>>>::Type<'p> where [u8]: 'p;
    type SType<'s> = <C as Combinator<[u8], Vec<u8>>>::SType<'s> where [u8]: 's;
    type GType = <C as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <C as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
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
        <C as Combinator<[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <C as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}

///Constructor for Header combinator
pub fn Header() -> HeaderCombinator {
    HeaderCombinator(Mapped::new((Tag::new(U16Le, 51966), (U8, U8)), HeaderMapper))
}

fn Header_gen() -> HeaderCombinator {
    HeaderCombinator(Mapped::new((Tag::new(U16Le, 51966), (U8, U8)), HeaderMapper))
}

///Parse function for Header combinator
pub fn parse_Header<'p>(input: &'p [u8]) -> Result<(usize, Header), ParseError> {
    let combinator = Header();
    <_ as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for Header combinator
pub fn serialize_Header<'s>(
    v: Header,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Header();
    <_ as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for Header combinator
pub fn Header_len<'s>(v: Header) -> usize {
    let combinator = Header();
    <_ as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

///Type alias for Record combinator
pub type RecordCombinatorAlias = Mapped<(U32Le, U32Le), RecordMapper>;
///Wrapper struct for Record combinator
pub struct RecordCombinator<C = RecordCombinatorAlias>(pub C);
impl<C> Combinator<[u8], Vec<u8>> for RecordCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <C as Combinator<[u8], Vec<u8>>>::Type<'p> where [u8]: 'p;
    type SType<'s> = <C as Combinator<[u8], Vec<u8>>>::SType<'s> where [u8]: 's;
    type GType = <C as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <C as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
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
        <C as Combinator<[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <C as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}

///Constructor for Record combinator
pub fn Record() -> RecordCombinator {
    RecordCombinator(Mapped::new((U32Le, U32Le), RecordMapper))
}

fn Record_gen() -> RecordCombinator {
    RecordCombinator(Mapped::new((U32Le, U32Le), RecordMapper))
}

///Parse function for Record combinator
pub fn parse_Record<'p>(input: &'p [u8]) -> Result<(usize, Record), ParseError> {
    let combinator = Record();
    <_ as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for Record combinator
pub fn serialize_Record<'s>(
    v: Record,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Record();
    <_ as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for Record combinator
pub fn Record_len<'s>(v: Record) -> usize {
    let combinator = Record();
    <_ as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

#[derive(Clone, Copy)]
pub struct PacketDep1 {}
impl DepCombinator<U16Le, [u8], Vec<u8>> for PacketDep1 {
    type Out = FixedLen<'static, Repeat<RecordCombinator>>;
    type OutGen<'g> = FixedLen<'g, Repeat<RecordCombinator>>;
    fn dep_snd<'s>(&self, fst: u16) -> Self::Out {
        let fst: u16 = fst;
        let payload_len = fst;
        FixedLen(Length::from_value(payload_len as usize), Repeat::new(Record()))
    }
    fn dep_snd_gen<'g>(&self, fst: &'g mut u16) -> Self::OutGen<'g> {
        let fst: &'g mut u16 = fst;
        let payload_len = fst;
        FixedLen(Length::from_u16_mut(payload_len), Repeat::new(Record()))
    }
}

///Type alias for Packet combinator
pub type PacketCombinatorAlias = Mapped<
    (HeaderCombinator, Pair<U16Le, PacketDep1>),
    PacketMapper,
>;
///Wrapper struct for Packet combinator
pub struct PacketCombinator<C = PacketCombinatorAlias>(pub C);
impl<C> Combinator<[u8], Vec<u8>> for PacketCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <C as Combinator<[u8], Vec<u8>>>::Type<'p> where [u8]: 'p;
    type SType<'s> = <C as Combinator<[u8], Vec<u8>>>::SType<'s> where [u8]: 's;
    type GType = <C as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <C as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
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
        <C as Combinator<[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <C as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <C as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}

///Constructor for Packet combinator
pub fn Packet() -> PacketCombinator {
    PacketCombinator(
        Mapped::new((Header(), Pair::new(U16Le, PacketDep1 {})), PacketMapper),
    )
}

fn Packet_gen() -> PacketCombinator {
    PacketCombinator(
        Mapped::new((Header(), Pair::new(U16Le, PacketDep1 {})), PacketMapper),
    )
}

///Parse function for Packet combinator
pub fn parse_Packet<'p>(input: &'p [u8]) -> Result<(usize, Packet), ParseError> {
    let combinator = Packet();
    <_ as Combinator<[u8], Vec<u8>>>::parse(&combinator, input)
}

///Serialize function for Packet combinator
pub fn serialize_Packet<'s>(
    v: &'s Packet,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Packet();
    <_ as Combinator<[u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

///Length function for Packet combinator
pub fn Packet_len<'s>(v: &'s Packet) -> usize {
    let combinator = Packet();
    <_ as Combinator<[u8], Vec<u8>>>::length(&combinator, v)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
}

impl From<((), (u8, u8))> for Header {
    fn from(src: ((), (u8, u8))) -> Self {
        Self {
            magic: 51966,
            version: src.1.0,
            flags: src.1.1,
        }
    }
}

impl<'s> From<Header> for ((), (u8, u8)) {
    fn from(v: Header) -> Self {
        ((), (v.version, v.flags))
    }
}

pub struct HeaderMapper;
impl Mapper for HeaderMapper {
    type Src<'p> = ((), (u8, u8));
    type Dst<'p> = Header;
    type SrcBorrow<'s> = ((), (u8, u8));
    type DstBorrow<'s> = Header;
    type SrcOwned = ((), (u8, u8));
    type DstOwned = Header;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record {
    pub id: u32,
    pub value: u32,
}

impl From<(u32, u32)> for Record {
    fn from(src: (u32, u32)) -> Self {
        Self { id: src.0, value: src.1 }
    }
}

impl<'s> From<Record> for (u32, u32) {
    fn from(v: Record) -> Self {
        (v.id, v.value)
    }
}

pub struct RecordMapper;
impl Mapper for RecordMapper {
    type Src<'p> = (u32, u32);
    type Dst<'p> = Record;
    type SrcBorrow<'s> = (u32, u32);
    type DstBorrow<'s> = Record;
    type SrcOwned = (u32, u32);
    type DstOwned = Record;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Packet {
    pub header: Header,
    pub field1: u16,
    pub payload: Vec<Record>,
}

impl From<(Header, (u16, Vec<Record>))> for Packet {
    fn from(src: (Header, (u16, Vec<Record>))) -> Self {
        Self {
            header: src.0,
            field1: src.1.0,
            payload: src.1.1,
        }
    }
}

impl<'s> From<&'s Packet> for (Header, (u16, &'s [Record])) {
    fn from(v: &'s Packet) -> Self {
        (v.header, (v.field1, v.payload.as_slice()))
    }
}

pub struct PacketMapper;
impl Mapper for PacketMapper {
    type Src<'p> = (Header, (u16, Vec<Record>));
    type Dst<'p> = Packet;
    type SrcBorrow<'s> = (Header, (u16, &'s [Record]));
    type DstBorrow<'s> = &'s Packet;
    type SrcOwned = (Header, (u16, Vec<Record>));
    type DstOwned = Packet;
}
