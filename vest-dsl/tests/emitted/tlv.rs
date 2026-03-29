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
pub struct RefinedPacket {
    pub header: Header,
    pub payload_len: u16,
    pub payload: Vec<Record>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Msg3 {
    pub x: u16,
    pub y: u16,
}

pub type Msg1<'a> = &'a [u8];
pub type Msg1Owned = Vec<u8>;
pub type Msg2 = RefinedPacket;
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgVal<'a> {
    Ty1(Msg1<'a>),
    Ty2(Msg2),
    Ty3(Msg3),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValOwned {
    Ty1(Msg1Owned),
    Ty2(Msg2),
    Ty3(Msg3),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MsgTy {
    Ty1 = 1,
    Ty2 = 2,
    Ty3 = 3,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg<'a> {
    pub tag: MsgTy,
    pub len: u16,
    pub val: MsgVal<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgOwned {
    pub tag: MsgTy,
    pub len: u16,
    pub val: MsgValOwned,
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

impl From<(Header, (u16, Vec<Record>))> for RefinedPacket {
    fn from(src: (Header, (u16, Vec<Record>))) -> Self {
        Self {
            header: src.0,
            payload_len: src.1.0,
            payload: src.1.1,
        }
    }
}

impl<'s> From<&'s RefinedPacket> for (Header, (u16, &'s [Record])) {
    fn from(v: &'s RefinedPacket) -> Self {
        (v.header, (v.payload_len, v.payload.as_slice()))
    }
}

pub struct RefinedPacketMapper;
impl Mapper for RefinedPacketMapper {
    type Src<'p> = (Header, (u16, Vec<Record>));
    type Dst<'p> = RefinedPacket;
    type SrcBorrow<'s> = (Header, (u16, &'s [Record]));
    type DstBorrow<'s> = &'s RefinedPacket;
    type SrcOwned = (Header, (u16, Vec<Record>));
    type DstOwned = RefinedPacket;
}

impl From<(u16, u16)> for Msg3 {
    fn from(src: (u16, u16)) -> Self {
        Self { x: src.0, y: src.1 }
    }
}

impl<'s> From<Msg3> for (u16, u16) {
    fn from(v: Msg3) -> Self {
        (v.x, v.y)
    }
}

pub struct Msg3Mapper;
impl Mapper for Msg3Mapper {
    type Src<'p> = (u16, u16);
    type Dst<'p> = Msg3;
    type SrcBorrow<'s> = (u16, u16);
    type DstBorrow<'s> = Msg3;
    type SrcOwned = (u16, u16);
    type DstOwned = Msg3;
}

impl From<u8> for MsgTy {
    fn from(src: u8) -> Self {
        match src as i128 {
            1 => Self::Ty1,
            2 => Self::Ty2,
            3 => Self::Ty3,
            _ => unreachable!("validated by combinator"),
        }
    }
}

impl From<MsgTy> for u8 {
    fn from(v: MsgTy) -> Self {
        v as u8
    }
}

pub struct MsgTyMapper;
impl Mapper for MsgTyMapper {
    type Src<'p> = u8;
    type Dst<'p> = MsgTy;
    type SrcBorrow<'s> = u8;
    type DstBorrow<'s> = MsgTy;
    type SrcOwned = u8;
    type DstOwned = MsgTy;
}

impl<'a> From<((MsgTy, u16), MsgVal<'a>)> for Msg<'a> {
    fn from(src: ((MsgTy, u16), MsgVal<'a>)) -> Self {
        Self {
            tag: src.0.0,
            len: src.0.1,
            val: src.1,
        }
    }
}

impl<'s, 'a: 's> From<&'s Msg<'a>> for ((MsgTy, u16), &'s MsgVal<'s>) {
    fn from(v: &'s Msg<'a>) -> Self {
        ((v.tag, v.len), &v.val)
    }
}

impl From<((MsgTy, u16), MsgValOwned)> for MsgOwned {
    fn from(src: ((MsgTy, u16), MsgValOwned)) -> Self {
        Self {
            tag: src.0.0,
            len: src.0.1,
            val: src.1,
        }
    }
}

pub struct MsgMapper;
impl Mapper for MsgMapper {
    type Src<'p> = ((MsgTy, u16), MsgVal<'p>);
    type Dst<'p> = Msg<'p>;
    type SrcBorrow<'s> = ((MsgTy, u16), &'s MsgVal<'s>);
    type DstBorrow<'s> = &'s Msg<'s>;
    type SrcOwned = ((MsgTy, u16), MsgValOwned);
    type DstOwned = MsgOwned;
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
///Type alias for RefinedPacket combinator
pub type RefinedPacketCombinatorAlias = Mapped<
    (HeaderCombinator, Pair<Refined<U16Le, fn(u16) -> bool>, RefinedPacketDep1>),
    RefinedPacketMapper,
>;
///Wrapper struct for RefinedPacket combinator
pub struct RefinedPacketCombinator<C = RefinedPacketCombinatorAlias>(pub C);
///Type alias for msg3 combinator
pub type Msg3CombinatorAlias = Mapped<(U16Le, U16Le), Msg3Mapper>;
///Wrapper struct for msg3 combinator
pub struct Msg3Combinator<C = Msg3CombinatorAlias>(pub C);
///Type alias for msg1 combinator
pub type Msg1CombinatorAlias = Fixed<32>;
///Wrapper struct for msg1 combinator
pub struct Msg1Combinator<C = Msg1CombinatorAlias>(pub C);
///Type alias for msg2 combinator
pub type Msg2CombinatorAlias = RefinedPacketCombinator;
///Wrapper struct for msg2 combinator
pub struct Msg2Combinator<C = Msg2CombinatorAlias>(pub C);
///Type alias for msg_val combinator
pub type MsgValCombinatorAlias<'x> = FixedLen<
    'x,
    Dispatch<'x, MsgTy, MsgValDispatchCase0, 3>,
>;
///Wrapper struct for msg_val combinator
pub struct MsgValCombinator<C = MsgValCombinatorAlias<'static>>(pub C);
///Type alias for msg_ty combinator
pub type MsgTyCombinatorAlias = Mapped<Refined<U8, fn(u8) -> bool>, MsgTyMapper>;
///Wrapper struct for msg_ty combinator
pub struct MsgTyCombinator<C = MsgTyCombinatorAlias>(pub C);
///Type alias for msg combinator
pub type MsgCombinatorAlias = Mapped<
    Pair<(MsgTyCombinator, Refined<U16Le, fn(u16) -> bool>), MsgDep>,
    MsgMapper,
>;
///Wrapper struct for msg combinator
pub struct MsgCombinator<C = MsgCombinatorAlias>(pub C);
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

///Constructor for RefinedPacket combinator
pub fn RefinedPacket() -> RefinedPacketCombinator {
    RefinedPacketCombinator(
        Mapped::new(
            (
                Header(),
                Pair::new(
                    Refined {
                        inner: U16Le,
                        predicate: |v: u16| v as i128 >= 8 && v as i128 <= 10000,
                    },
                    RefinedPacketDep1 {},
                ),
            ),
            RefinedPacketMapper,
        ),
    )
}

///Constructor for msg3 combinator
pub fn msg3() -> Msg3Combinator {
    Msg3Combinator(Mapped::new((U16Le, U16Le), Msg3Mapper))
}

///Constructor for msg1 combinator
pub fn msg1() -> Msg1Combinator {
    Msg1Combinator(Fixed::<32>)
}

///Constructor for msg2 combinator
pub fn msg2() -> Msg2Combinator {
    Msg2Combinator(RefinedPacket())
}

///Constructor for msg_val combinator
pub fn msg_val<'a, LenArg, TagArg>(
    len: LenArg,
    tag: TagArg,
) -> MsgValCombinator<MsgValCombinatorAlias<'a>>
where
    LenArg: LengthParam<'a, u16>,
    TagArg: RuntimeValParam<'a, MsgTy>,
{
    MsgValCombinator(
        FixedLen(
            len.into_length(),
            Dispatch::new(
                tag.into_runtime_value(),
                [
                    (MsgTy::Ty1, MsgValDispatchCase0::V1(msg1())),
                    (MsgTy::Ty2, MsgValDispatchCase0::V2(msg2())),
                    (MsgTy::Ty3, MsgValDispatchCase0::V3(msg3())),
                ],
            ),
        ),
    )
}

///Constructor for msg_ty combinator
pub fn msg_ty() -> MsgTyCombinator {
    MsgTyCombinator(
        Mapped::new(
            Refined {
                inner: U8,
                predicate: |v: u8| (v as i128 == 1 || v as i128 == 2 || v as i128 == 3),
            },
            MsgTyMapper,
        ),
    )
}

///Constructor for msg combinator
pub fn msg() -> MsgCombinator {
    MsgCombinator(
        Mapped::new(
            Pair::new(
                (
                    msg_ty(),
                    Refined {
                        inner: U16Le,
                        predicate: |v: u16| v as i128 >= 0 && v as i128 <= 8000,
                    },
                ),
                MsgDep {},
            ),
            MsgMapper,
        ),
    )
}

#[derive(Clone, Copy)]
pub struct RefinedPacketDep1 {}
impl DepCombinator<Refined<U16Le, fn(u16) -> bool>, [u8], Vec<u8>>
for RefinedPacketDep1 {
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

pub enum MsgValDispatchCase0<
    C0 = Msg1Combinator,
    C1 = Msg2Combinator,
    C2 = Msg3Combinator,
> {
    V1(C0),
    V2(C1),
    V3(C2),
}

impl<C0, C1, C2> Combinator<[u8], Vec<u8>> for MsgValDispatchCase0<C0, C1, C2>
where
    for<'p, 's> C0: Combinator<
        [u8],
        Vec<u8>,
        Type<'p> = Msg1<'p>,
        SType<'s> = Msg1<'s>,
        GType = Msg1Owned,
    >,
    for<'p, 's> C1: Combinator<
        [u8],
        Vec<u8>,
        Type<'p> = Msg2,
        SType<'s> = &'s Msg2,
        GType = Msg2,
    >,
    for<'p, 's> C2: Combinator<
        [u8],
        Vec<u8>,
        Type<'p> = Msg3,
        SType<'s> = Msg3,
        GType = Msg3,
    >,
{
    type Type<'p> = MsgVal<'p>;
    type SType<'s> = &'s MsgVal<'s>;
    type GType = MsgValOwned;
    fn length<'s>(&self, v: Self::SType<'s>) -> usize
    where
        [u8]: 's,
    {
        match (self, v) {
            (MsgValDispatchCase0::V1(inner), MsgVal::Ty1(v0)) => inner.length((*v0)),
            (MsgValDispatchCase0::V2(inner), MsgVal::Ty2(v1)) => inner.length(&(*v1)),
            (MsgValDispatchCase0::V3(inner), MsgVal::Ty3(v2)) => inner.length((*v2)),
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
                Ok((n, MsgVal::Ty1(v)))
            }
            MsgValDispatchCase0::V2(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, MsgVal::Ty2(v)))
            }
            MsgValDispatchCase0::V3(inner) => {
                let (n, v) = inner.parse(s)?;
                Ok((n, MsgVal::Ty3(v)))
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
            (MsgValDispatchCase0::V1(inner), MsgVal::Ty1(v0)) => {
                inner.serialize((*v0), data, pos)
            }
            (MsgValDispatchCase0::V2(inner), MsgVal::Ty2(v1)) => {
                inner.serialize(&(*v1), data, pos)
            }
            (MsgValDispatchCase0::V3(inner), MsgVal::Ty3(v2)) => {
                inner.serialize((*v2), data, pos)
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
                Ok((n, MsgValOwned::Ty1(v)))
            }
            MsgValDispatchCase0::V2(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, MsgValOwned::Ty2(v)))
            }
            MsgValDispatchCase0::V3(inner) => {
                let (n, v) = inner.generate(g)?;
                Ok((n, MsgValOwned::Ty3(v)))
            }
        }
    }
    fn well_formed<'s>(&self, v: Self::SType<'s>) -> bool
    where
        [u8]: 's,
    {
        match (self, v) {
            (MsgValDispatchCase0::V1(inner), MsgVal::Ty1(v0)) => inner.well_formed((*v0)),
            (MsgValDispatchCase0::V2(inner), MsgVal::Ty2(v1)) => {
                inner.well_formed(&(*v1))
            }
            (MsgValDispatchCase0::V3(inner), MsgVal::Ty3(v2)) => inner.well_formed((*v2)),
            _ => false,
        }
    }
}

#[derive(Clone, Copy)]
pub struct MsgDep {}
impl DepCombinator<(MsgTyCombinator, Refined<U16Le, fn(u16) -> bool>), [u8], Vec<u8>>
for MsgDep {
    type Out = MsgValCombinator;
    type OutGen<'g> = MsgValCombinator<MsgValCombinatorAlias<'g>>;
    fn dep_snd<'s>(&self, fst: (MsgTy, u16)) -> Self::Out {
        let fst: (MsgTy, u16) = fst;
        let (tag, len) = fst;
        msg_val(len, tag)
    }
    fn dep_snd_gen<'g>(&self, fst: &'g mut (MsgTy, u16)) -> Self::OutGen<'g> {
        let fst: &'g mut (MsgTy, u16) = fst;
        let (tag, len) = fst;
        msg_val(len, tag)
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

///Parse function for RefinedPacket combinator
pub fn parse_RefinedPacket<'p>(
    input: &'p [u8],
) -> Result<(usize, RefinedPacket), ParseError> {
    let combinator = RefinedPacket();
    combinator.parse(input)
}

///Serialize function for RefinedPacket combinator
pub fn serialize_RefinedPacket<'s>(
    v: &'s RefinedPacket,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = RefinedPacket();
    combinator.serialize(v, data, pos)
}

///Length function for RefinedPacket combinator
pub fn RefinedPacket_len<'s>(v: &'s RefinedPacket) -> usize {
    let combinator = RefinedPacket();
    combinator.length(v)
}

///Generate function for RefinedPacket combinator
pub fn generate_RefinedPacket(g: &mut GenSt) -> GResult<RefinedPacket, GenerateError> {
    let mut combinator = RefinedPacket();
    combinator.generate(g)
}

///Parse function for msg3 combinator
pub fn parse_msg3<'p>(input: &'p [u8]) -> Result<(usize, Msg3), ParseError> {
    let combinator = msg3();
    combinator.parse(input)
}

///Serialize function for msg3 combinator
pub fn serialize_msg3<'s>(
    v: Msg3,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg3();
    combinator.serialize(v, data, pos)
}

///Length function for msg3 combinator
pub fn msg3_len<'s>(v: Msg3) -> usize {
    let combinator = msg3();
    combinator.length(v)
}

///Generate function for msg3 combinator
pub fn generate_msg3(g: &mut GenSt) -> GResult<Msg3, GenerateError> {
    let mut combinator = msg3();
    combinator.generate(g)
}

///Parse function for msg1 combinator
pub fn parse_msg1<'p>(input: &'p [u8]) -> Result<(usize, Msg1<'p>), ParseError> {
    let combinator = msg1();
    combinator.parse(input)
}

///Serialize function for msg1 combinator
pub fn serialize_msg1<'s>(
    v: &'s [u8],
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg1();
    combinator.serialize(v, data, pos)
}

///Length function for msg1 combinator
pub fn msg1_len<'s>(v: &'s [u8]) -> usize {
    let combinator = msg1();
    combinator.length(v)
}

///Generate function for msg1 combinator
pub fn generate_msg1(g: &mut GenSt) -> GResult<Msg1Owned, GenerateError> {
    let mut combinator = msg1();
    combinator.generate(g)
}

///Parse function for msg2 combinator
pub fn parse_msg2<'p>(input: &'p [u8]) -> Result<(usize, Msg2), ParseError> {
    let combinator = msg2();
    combinator.parse(input)
}

///Serialize function for msg2 combinator
pub fn serialize_msg2<'s>(
    v: &'s RefinedPacket,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg2();
    combinator.serialize(v, data, pos)
}

///Length function for msg2 combinator
pub fn msg2_len<'s>(v: &'s RefinedPacket) -> usize {
    let combinator = msg2();
    combinator.length(v)
}

///Generate function for msg2 combinator
pub fn generate_msg2(g: &mut GenSt) -> GResult<Msg2, GenerateError> {
    let mut combinator = msg2();
    combinator.generate(g)
}

///Parse function for msg_val combinator
pub fn parse_msg_val<'p>(
    input: &'p [u8],
    len: u16,
    tag: MsgTy,
) -> Result<(usize, MsgVal<'p>), ParseError> {
    let combinator = msg_val(len, tag);
    combinator.parse(input)
}

///Serialize function for msg_val combinator
pub fn serialize_msg_val<'s>(
    v: &'s MsgVal<'s>,
    data: &mut Vec<u8>,
    pos: usize,
    len: u16,
    tag: MsgTy,
) -> Result<usize, SerializeError> {
    let combinator = msg_val(len, tag);
    combinator.serialize(v, data, pos)
}

///Length function for msg_val combinator
pub fn msg_val_len<'s>(v: &'s MsgVal<'s>, len: u16, tag: MsgTy) -> usize {
    let combinator = msg_val(len, tag);
    combinator.length(v)
}

///Generate function for msg_val combinator
pub fn generate_msg_val<'g>(
    g: &mut GenSt,
    len: &'g mut u16,
    tag: &'g mut MsgTy,
) -> GResult<MsgValOwned, GenerateError> {
    let mut combinator = msg_val(len, tag);
    combinator.generate(g)
}

///Parse function for msg_ty combinator
pub fn parse_msg_ty<'p>(input: &'p [u8]) -> Result<(usize, MsgTy), ParseError> {
    let combinator = msg_ty();
    combinator.parse(input)
}

///Serialize function for msg_ty combinator
pub fn serialize_msg_ty<'s>(
    v: MsgTy,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg_ty();
    combinator.serialize(v, data, pos)
}

///Length function for msg_ty combinator
pub fn msg_ty_len<'s>(v: MsgTy) -> usize {
    let combinator = msg_ty();
    combinator.length(v)
}

///Generate function for msg_ty combinator
pub fn generate_msg_ty(g: &mut GenSt) -> GResult<MsgTy, GenerateError> {
    let mut combinator = msg_ty();
    combinator.generate(g)
}

///Parse function for msg combinator
pub fn parse_msg<'p>(input: &'p [u8]) -> Result<(usize, Msg<'p>), ParseError> {
    let combinator = msg();
    combinator.parse(input)
}

///Serialize function for msg combinator
pub fn serialize_msg<'s>(
    v: &'s Msg<'s>,
    data: &mut Vec<u8>,
    pos: usize,
) -> Result<usize, SerializeError> {
    let combinator = msg();
    combinator.serialize(v, data, pos)
}

///Length function for msg combinator
pub fn msg_len<'s>(v: &'s Msg<'s>) -> usize {
    let combinator = msg();
    combinator.length(v)
}

///Generate function for msg combinator
pub fn generate_msg(g: &mut GenSt) -> GResult<MsgOwned, GenerateError> {
    let mut combinator = msg();
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

impl<C> Combinator<[u8], Vec<u8>> for RefinedPacketCombinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for Msg3Combinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for Msg1Combinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for Msg2Combinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for MsgValCombinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for MsgTyCombinator<C>
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

impl<C> Combinator<[u8], Vec<u8>> for MsgCombinator<C>
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
