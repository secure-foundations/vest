#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_camel_case_types)]
use vest_lib::properties::*;
use vest_lib::errors::*;
use vest_lib::regular::*;
use vest_lib::regular::sequence::{Pair, Preceded, Terminated, DepCombinator};
use vest_lib::regular::variant::{Dispatch, Opt, OptThen, Choice};
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record {
    pub id: u32,
    pub value: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Packet {
    pub header: Header,
    pub payload_len: u16,
    pub payload: Vec<Record>,
}

impl From<((), (u8, u8))> for Header {
    fn from(src: ((), (u8, u8))) -> Self {
        Self {
            magic: HEADERMAGIC_CONST,
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

impl From<(Header, (u16, Vec<Record>))> for Packet {
    fn from(src: (Header, (u16, Vec<Record>))) -> Self {
        Self {
            header: src.0,
            payload_len: src.1.0,
            payload: src.1.1,
        }
    }
}

impl<'s> From<&'s Packet> for (Header, (u16, &'s [Record])) {
    fn from(v: &'s Packet) -> Self {
        (v.header, (v.payload_len, v.payload.as_slice()))
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

pub const HEADERMAGIC_CONST: u16 = 51966;
///Type alias for Header combinator
pub type HeaderCombinatorAlias = Mapped<(Tag<U16Le, u16>, (U8, U8)), HeaderMapper>;
///Wrapper struct for Header combinator
pub struct HeaderCombinator<C = HeaderCombinatorAlias>(pub C);
///Type alias for Record combinator
pub type RecordCombinatorAlias = Mapped<(U32Le, U32Le), RecordMapper>;
///Wrapper struct for Record combinator
pub struct RecordCombinator<C = RecordCombinatorAlias>(pub C);
///Type alias for Packet combinator
pub type PacketCombinatorAlias = Mapped<
    (HeaderCombinator, Pair<U16Le, PacketDep1>),
    PacketMapper,
>;
///Wrapper struct for Packet combinator
pub struct PacketCombinator<C = PacketCombinatorAlias>(pub C);
///Constructor for Header combinator
pub fn Header() -> HeaderCombinator {
    HeaderCombinator(
        Mapped::new((Tag::new(U16Le, HEADERMAGIC_CONST), (U8, U8)), HeaderMapper),
    )
}

///Constructor for Record combinator
pub fn Record() -> RecordCombinator {
    RecordCombinator(Mapped::new((U32Le, U32Le), RecordMapper))
}

///Constructor for Packet combinator
pub fn Packet() -> PacketCombinator {
    PacketCombinator(
        Mapped::new((Header(), Pair::new(U16Le, PacketDep1 {})), PacketMapper),
    )
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

///Parse function for Header combinator
pub fn parse_Header<'p>(input: &'p [u8]) -> Result<(usize, Header), ParseError> {
    let combinator = Header();
    combinator.parse(input)
}

///Serialize function for Header combinator
pub fn serialize_Header<'s>(
    v: Header,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Header();
    combinator.serialize(v, data, pos)
}

///Length function for Header combinator
pub fn Header_len<'s>(v: Header) -> usize {
    let combinator = Header();
    combinator.length(v)
}

///Generate function for Header combinator
pub fn generate_Header(g: &mut GenSt) -> GResult<Header, GenerateError> {
    let mut combinator = Header();
    combinator.generate(g)
}

///Parse function for Record combinator
pub fn parse_Record<'p>(input: &'p [u8]) -> Result<(usize, Record), ParseError> {
    let combinator = Record();
    combinator.parse(input)
}

///Serialize function for Record combinator
pub fn serialize_Record<'s>(
    v: Record,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Record();
    combinator.serialize(v, data, pos)
}

///Length function for Record combinator
pub fn Record_len<'s>(v: Record) -> usize {
    let combinator = Record();
    combinator.length(v)
}

///Generate function for Record combinator
pub fn generate_Record(g: &mut GenSt) -> GResult<Record, GenerateError> {
    let mut combinator = Record();
    combinator.generate(g)
}

///Parse function for Packet combinator
pub fn parse_Packet<'p>(input: &'p [u8]) -> Result<(usize, Packet), ParseError> {
    let combinator = Packet();
    combinator.parse(input)
}

///Serialize function for Packet combinator
pub fn serialize_Packet<'s>(
    v: &'s Packet,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Packet();
    combinator.serialize(v, data, pos)
}

///Length function for Packet combinator
pub fn Packet_len<'s>(v: &'s Packet) -> usize {
    let combinator = Packet();
    combinator.length(v)
}

///Generate function for Packet combinator
pub fn generate_Packet(g: &mut GenSt) -> GResult<Packet, GenerateError> {
    let mut combinator = Packet();
    combinator.generate(g)
}

impl<C> Combinator<[u8], Vec<u8>> for HeaderCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = C::Type<'p>;
    type SType<'s> = C::SType<'s>;
    type GType = C::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        self.0.length(v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        self.0.parse(s)
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
        self.0.serialize(v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.0.generate(g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        self.0.well_formed(v)
    }
}

impl<C> Combinator<[u8], Vec<u8>> for RecordCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = C::Type<'p>;
    type SType<'s> = C::SType<'s>;
    type GType = C::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        self.0.length(v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        self.0.parse(s)
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
        self.0.serialize(v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.0.generate(g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        self.0.well_formed(v)
    }
}

impl<C> Combinator<[u8], Vec<u8>> for PacketCombinator<C>
where
    C: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = C::Type<'p>;
    type SType<'s> = C::SType<'s>;
    type GType = C::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        self.0.length(v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        self.0.parse(s)
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
        self.0.serialize(v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        self.0.generate(g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        self.0.well_formed(v)
    }
}

pub trait RuntimeValParam<'a, T: Copy> {
    fn into_runtime_value(self) -> RuntimeValue<'a, T>;
}

pub trait LengthParam<'a, T: Copy> {
    fn into_length(self) -> Length<'a>;
}

impl<T: Copy> RuntimeValParam<'static, T> for T {
    fn into_runtime_value(self) -> RuntimeValue<'static, T> {
        RuntimeValue::from_value(self)
    }
}

impl<'a, T: Copy> RuntimeValParam<'a, T> for &'a mut T {
    fn into_runtime_value(self) -> RuntimeValue<'a, T> {
        RuntimeValue::from_mut(self)
    }
}

impl LengthParam<'static, u8> for u8 {
    fn into_length(self) -> Length<'static> {
        Length::from_value(self as usize)
    }
}

impl LengthParam<'static, u16> for u16 {
    fn into_length(self) -> Length<'static> {
        Length::from_value(self as usize)
    }
}

impl LengthParam<'static, u24> for u24 {
    fn into_length(self) -> Length<'static> {
        Length::from_value(self.as_u32() as usize)
    }
}

impl LengthParam<'static, u32> for u32 {
    fn into_length(self) -> Length<'static> {
        Length::from_value(self as usize)
    }
}

impl LengthParam<'static, u64> for u64 {
    fn into_length(self) -> Length<'static> {
        Length::from_value(self as usize)
    }
}

impl<'a> LengthParam<'a, u8> for &'a mut u8 {
    fn into_length(self) -> Length<'a> {
        Length::from_u8_mut(self)
    }
}

impl<'a> LengthParam<'a, u16> for &'a mut u16 {
    fn into_length(self) -> Length<'a> {
        Length::from_u16_mut(self)
    }
}

impl<'a> LengthParam<'a, u24> for &'a mut u24 {
    fn into_length(self) -> Length<'a> {
        Length::from_value(self.as_u32() as usize)
    }
}

impl<'a> LengthParam<'a, u32> for &'a mut u32 {
    fn into_length(self) -> Length<'a> {
        Length::from_u32_mut(self)
    }
}

impl<'a> LengthParam<'a, u64> for &'a mut u64 {
    fn into_length(self) -> Length<'a> {
        Length::from_u64_mut(self)
    }
}
