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
pub struct PacketDep1 {}
impl sequence::DepCombinator<U16Le, [u8], Vec<u8>> for PacketDep1
where
    U16Le: Combinator<[u8], Vec<u8>>,
    modifier::FixedLen<
        'static,
        repetition::Repeat<RecordCombinator>,
    >: Combinator<[u8], Vec<u8>>,
{
    type Out = modifier::FixedLen<'static, repetition::Repeat<RecordCombinator>>;
    type OutGen<'g> = modifier::FixedLen<'g, repetition::Repeat<RecordCombinator>>;
    fn dep_snd<'s>(
        &self,
        fst: <U16Le as Combinator<[u8], Vec<u8>>>::SType<'s>,
    ) -> Self::Out {
        let payload_len = fst;
        modifier::FixedLen(
            modifier::Length::from_value(payload_len as usize),
            repetition::Repeat::new(Record()),
        )
    }
    fn dep_snd_gen<'g>(
        &self,
        fst: &'g mut <U16Le as Combinator<[u8], Vec<u8>>>::GType,
    ) -> Self::OutGen<'g> {
        let payload_len = fst;
        modifier::FixedLen(
            modifier::Length::from_u16_mut(payload_len),
            repetition::Repeat::new(Record()),
        )
    }
}
pub type PacketCombinatorAlias = (HeaderCombinator, sequence::Pair<U16Le, PacketDep1>);
pub struct PacketCombinator(pub PacketCombinatorAlias);
impl Combinator<[u8], Vec<u8>> for PacketCombinator
where
    PacketCombinatorAlias: Combinator<[u8], Vec<u8>>,
{
    type Type<'p> = <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::Type<'p>
    where
        [u8]: 'p;
    type SType<'s> = <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::SType<'s>
    where
        [u8]: 's;
    type GType = <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::GType;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::length(&self.0, v)
    }
    fn parse<'p>(&self, s: &'p [u8]) -> Result<(usize, Self::Type<'p>), ParseError>
    where
        [u8]: 'p,
    {
        <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::parse(&self.0, s)
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
        <PacketCombinatorAlias as Combinator<
            [u8],
            Vec<u8>,
        >>::serialize(&self.0, v, data, pos)
    }
    fn generate(&mut self, g: &mut GenSt) -> GResult<Self::GType, GenerateError> {
        <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::generate(&mut self.0, g)
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        <PacketCombinatorAlias as Combinator<[u8], Vec<u8>>>::well_formed(&self.0, v)
    }
}
pub fn Packet() -> PacketCombinator {
    PacketCombinator((Header(), sequence::Pair::new(U16Le, PacketDep1 {})))
}
pub fn parse_Packet(
    input: &[u8],
) -> Result<
    (usize, <PacketCombinator as Combinator<[u8], Vec<u8>>>::Type<'_>),
    ParseError,
> {
    let combinator = Packet();
    combinator.parse(input)
}
pub fn serialize_Packet(
    v: <PacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = Packet();
    combinator.serialize(v, data, pos)
}
pub fn Packet_len(
    v: <PacketCombinator as Combinator<[u8], Vec<u8>>>::SType<'_>,
) -> usize {
    let combinator = Packet();
    combinator.length(v)
}
