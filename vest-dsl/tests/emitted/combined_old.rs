
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest_lib::regular::modifier::*;
use vest_lib::regular::bytes;
use vest_lib::regular::variant::*;
use vest_lib::regular::sequence::*;
use vest_lib::regular::repetition::*;
use vest_lib::regular::disjoint::DisjointFrom;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::utils::*;
use vest_lib::properties::*;
use vest_lib::bitcoin::varint::{BtcVarint, VarInt};
use vest_lib::regular::leb128::*;

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                open spec fn ex_requires(&self) -> bool
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
                fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
                fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
            }
        } // verus!
    };
}
verus!{

pub struct SpecHeader {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
}

pub type SpecHeaderInner = (u16, (u8, u8));


impl SpecFrom<SpecHeader> for SpecHeaderInner {
    open spec fn spec_from(m: SpecHeader) -> SpecHeaderInner {
        (m.magic, (m.version, m.flags))
    }
}

impl SpecFrom<SpecHeaderInner> for SpecHeader {
    open spec fn spec_from(m: SpecHeaderInner) -> SpecHeader {
        let (magic, (version, flags)) = m;
        SpecHeader { magic, version, flags }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Header {
    pub magic: u16,
    pub version: u8,
    pub flags: u8,
}

impl View for Header {
    type V = SpecHeader;

    open spec fn view(&self) -> Self::V {
        SpecHeader {
            magic: self.magic@,
            version: self.version@,
            flags: self.flags@,
        }
    }
}
pub type HeaderInner = (u16, (u8, u8));

pub type HeaderInnerRef<'a> = (&'a u16, (&'a u8, &'a u8));
impl<'a> From<&'a Header> for HeaderInnerRef<'a> {
    fn ex_from(m: &'a Header) -> HeaderInnerRef<'a> {
        (&m.magic, (&m.version, &m.flags))
    }
}

impl From<HeaderInner> for Header {
    fn ex_from(m: HeaderInner) -> Header {
        let (magic, (version, flags)) = m;
        Header { magic, version, flags }
    }
}

pub struct HeaderMapper;
impl View for HeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HeaderMapper {
    type Src = SpecHeaderInner;
    type Dst = SpecHeader;
}
impl SpecIsoProof for HeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HeaderMapper {
    type Src = HeaderInner;
    type Dst = Header;
    type RefSrc = HeaderInnerRef<'a>;
}
pub const HEADERMAGIC_CONST: u16 = 51966;
type SpecHeaderCombinatorAlias1 = (U8, U8);
type SpecHeaderCombinatorAlias2 = (Refined<U16Le, TagPred<u16>>, SpecHeaderCombinatorAlias1);
pub struct SpecHeaderCombinator(pub SpecHeaderCombinatorAlias);

impl SpecCombinator for SpecHeaderCombinator {
    type Type = SpecHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecHeaderCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecHeaderCombinatorAlias = Mapped<SpecHeaderCombinatorAlias2, HeaderMapper>;
type HeaderCombinatorAlias1 = (U8, U8);
type HeaderCombinatorAlias2 = (Refined<U16Le, TagPred<u16>>, HeaderCombinator1);
pub struct HeaderCombinator1(pub HeaderCombinatorAlias1);
impl View for HeaderCombinator1 {
    type V = SpecHeaderCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HeaderCombinator1, HeaderCombinatorAlias1);

pub struct HeaderCombinator2(pub HeaderCombinatorAlias2);
impl View for HeaderCombinator2 {
    type V = SpecHeaderCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HeaderCombinator2, HeaderCombinatorAlias2);

pub struct HeaderCombinator(pub HeaderCombinatorAlias);

impl View for HeaderCombinator {
    type V = SpecHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HeaderCombinator {
    type Type = Header;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type HeaderCombinatorAlias = Mapped<HeaderCombinator2, HeaderMapper>;


pub open spec fn spec_Header() -> SpecHeaderCombinator {
    SpecHeaderCombinator(
    Mapped {
        inner: (Refined { inner: U16Le, predicate: TagPred(HEADERMAGIC_CONST) }, (U8, U8)),
        mapper: HeaderMapper,
    })
}

                
pub fn Header<'a>() -> (o: HeaderCombinator)
    ensures o@ == spec_Header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = HeaderCombinator(
    Mapped {
        inner: HeaderCombinator2((Refined { inner: U16Le, predicate: TagPred(HEADERMAGIC_CONST) }, HeaderCombinator1((U8, U8)))),
        mapper: HeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_Header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_Header<'a>(input: &'a [u8]) -> (res: PResult<<HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_Header().spec_parse(input@) == Some((n as int, v@)),
        spec_Header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_Header().spec_parse(input@) is None,
        spec_Header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = Header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_Header<'a>(v: <HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_Header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_Header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_Header().spec_serialize(v@))
        },
{
    let combinator = Header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn Header_len<'a>(v: <HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_Header().wf(v@),
        spec_Header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_Header().spec_serialize(v@).len(),
{
    let combinator = Header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecRecord {
    pub id: u32,
    pub value: u32,
}

pub type SpecRecordInner = (u32, u32);


impl SpecFrom<SpecRecord> for SpecRecordInner {
    open spec fn spec_from(m: SpecRecord) -> SpecRecordInner {
        (m.id, m.value)
    }
}

impl SpecFrom<SpecRecordInner> for SpecRecord {
    open spec fn spec_from(m: SpecRecordInner) -> SpecRecord {
        let (id, value) = m;
        SpecRecord { id, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Record {
    pub id: u32,
    pub value: u32,
}

impl View for Record {
    type V = SpecRecord;

    open spec fn view(&self) -> Self::V {
        SpecRecord {
            id: self.id@,
            value: self.value@,
        }
    }
}
pub type RecordInner = (u32, u32);

pub type RecordInnerRef<'a> = (&'a u32, &'a u32);
impl<'a> From<&'a Record> for RecordInnerRef<'a> {
    fn ex_from(m: &'a Record) -> RecordInnerRef<'a> {
        (&m.id, &m.value)
    }
}

impl From<RecordInner> for Record {
    fn ex_from(m: RecordInner) -> Record {
        let (id, value) = m;
        Record { id, value }
    }
}

pub struct RecordMapper;
impl View for RecordMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for RecordMapper {
    type Src = SpecRecordInner;
    type Dst = SpecRecord;
}
impl SpecIsoProof for RecordMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for RecordMapper {
    type Src = RecordInner;
    type Dst = Record;
    type RefSrc = RecordInnerRef<'a>;
}
type SpecRecordCombinatorAlias1 = (U32Le, U32Le);
pub struct SpecRecordCombinator(pub SpecRecordCombinatorAlias);

impl SpecCombinator for SpecRecordCombinator {
    type Type = SpecRecord;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecRecordCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecRecordCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecRecordCombinatorAlias = Mapped<SpecRecordCombinatorAlias1, RecordMapper>;
type RecordCombinatorAlias1 = (U32Le, U32Le);
pub struct RecordCombinator1(pub RecordCombinatorAlias1);
impl View for RecordCombinator1 {
    type V = SpecRecordCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(RecordCombinator1, RecordCombinatorAlias1);

pub struct RecordCombinator(pub RecordCombinatorAlias);

impl View for RecordCombinator {
    type V = SpecRecordCombinator;
    open spec fn view(&self) -> Self::V { SpecRecordCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for RecordCombinator {
    type Type = Record;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type RecordCombinatorAlias = Mapped<RecordCombinator1, RecordMapper>;


pub open spec fn spec_Record() -> SpecRecordCombinator {
    SpecRecordCombinator(
    Mapped {
        inner: (U32Le, U32Le),
        mapper: RecordMapper,
    })
}

                
pub fn Record<'a>() -> (o: RecordCombinator)
    ensures o@ == spec_Record(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = RecordCombinator(
    Mapped {
        inner: RecordCombinator1((U32Le, U32Le)),
        mapper: RecordMapper,
    });
    // assert({
    //     &&& combinator@ == spec_Record()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_Record<'a>(input: &'a [u8]) -> (res: PResult<<RecordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_Record().spec_parse(input@) == Some((n as int, v@)),
        spec_Record().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_Record().spec_parse(input@) is None,
        spec_Record().spec_parse(input@) is None ==> res is Err,
{
    let combinator = Record();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_Record<'a>(v: <RecordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_Record().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_Record().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_Record().spec_serialize(v@))
        },
{
    let combinator = Record();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn Record_len<'a>(v: <RecordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_Record().wf(v@),
        spec_Record().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_Record().spec_serialize(v@).len(),
{
    let combinator = Record();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecPacket {
    pub header: SpecHeader,
    pub payload_len: u16,
    pub payload: Seq<SpecRecord>,
}

pub type SpecPacketInner = ((SpecHeader, u16), Seq<SpecRecord>);


impl SpecFrom<SpecPacket> for SpecPacketInner {
    open spec fn spec_from(m: SpecPacket) -> SpecPacketInner {
        ((m.header, m.payload_len), m.payload)
    }
}

impl SpecFrom<SpecPacketInner> for SpecPacket {
    open spec fn spec_from(m: SpecPacketInner) -> SpecPacket {
        let ((header, payload_len), payload) = m;
        SpecPacket { header, payload_len, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Packet {
    pub header: Header,
    pub payload_len: u16,
    pub payload: RepeatResult<Record>,
}

impl View for Packet {
    type V = SpecPacket;

    open spec fn view(&self) -> Self::V {
        SpecPacket {
            header: self.header@,
            payload_len: self.payload_len@,
            payload: self.payload@,
        }
    }
}
pub type PacketInner = ((Header, u16), RepeatResult<Record>);

pub type PacketInnerRef<'a> = ((&'a Header, &'a u16), &'a RepeatResult<Record>);
impl<'a> From<&'a Packet> for PacketInnerRef<'a> {
    fn ex_from(m: &'a Packet) -> PacketInnerRef<'a> {
        ((&m.header, &m.payload_len), &m.payload)
    }
}

impl From<PacketInner> for Packet {
    fn ex_from(m: PacketInner) -> Packet {
        let ((header, payload_len), payload) = m;
        Packet { header, payload_len, payload }
    }
}

pub struct PacketMapper;
impl View for PacketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PacketMapper {
    type Src = SpecPacketInner;
    type Dst = SpecPacket;
}
impl SpecIsoProof for PacketMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PacketMapper {
    type Src = PacketInner;
    type Dst = Packet;
    type RefSrc = PacketInnerRef<'a>;
}

pub struct SpecPacketCombinator(pub SpecPacketCombinatorAlias);

impl SpecCombinator for SpecPacketCombinator {
    type Type = SpecPacket;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPacketCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPacketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>)
    { self.0.lemma_parse_length(s) }
    open spec fn is_productive(&self) -> bool
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>)
    { self.0.lemma_parse_productive(s) }
}
pub type SpecPacketCombinatorAlias = Mapped<SpecPair<(SpecHeaderCombinator, U16Le), AndThen<bytes::Variable, Repeat<SpecRecordCombinator>>>, PacketMapper>;

pub struct PacketCombinator(pub PacketCombinatorAlias);

impl View for PacketCombinator {
    type V = SpecPacketCombinator;
    open spec fn view(&self) -> Self::V { SpecPacketCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PacketCombinator {
    type Type = Packet;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
pub type PacketCombinatorAlias = Mapped<Pair<(HeaderCombinator, U16Le), AndThen<bytes::Variable, Repeat<RecordCombinator>>, PacketCont0>, PacketMapper>;


pub open spec fn spec_Packet() -> SpecPacketCombinator {
    SpecPacketCombinator(
    Mapped {
        inner: Pair::spec_new((spec_Header(), U16Le), |deps| spec_packet_cont0(deps)),
        mapper: PacketMapper,
    })
}

pub open spec fn spec_packet_cont0(deps: (SpecHeader, u16)) -> AndThen<bytes::Variable, Repeat<SpecRecordCombinator>> {
    let (_, payload_len) = deps;
    AndThen(bytes::Variable((usize::spec_from(payload_len)) as usize), Repeat(spec_Record()))
}

impl View for PacketCont0 {
    type V = spec_fn((SpecHeader, u16)) -> AndThen<bytes::Variable, Repeat<SpecRecordCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecHeader, u16)| {
            spec_packet_cont0(deps)
        }
    }
}

                
pub fn Packet<'a>() -> (o: PacketCombinator)
    ensures o@ == spec_Packet(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PacketCombinator(
    Mapped {
        inner: Pair::new((Header(), U16Le), PacketCont0),
        mapper: PacketMapper,
    });
    // assert({
    //     &&& combinator@ == spec_Packet()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_Packet<'a>(input: &'a [u8]) -> (res: PResult<<PacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_Packet().spec_parse(input@) == Some((n as int, v@)),
        spec_Packet().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_Packet().spec_parse(input@) is None,
        spec_Packet().spec_parse(input@) is None ==> res is Err,
{
    let combinator = Packet();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_Packet<'a>(v: <PacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_Packet().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_Packet().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_Packet().spec_serialize(v@))
        },
{
    let combinator = Packet();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn Packet_len<'a>(v: <PacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_Packet().wf(v@),
        spec_Packet().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_Packet().spec_serialize(v@).len(),
{
    let combinator = Packet();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct PacketCont0;
type PacketCont0Type<'a, 'b> = &'b (Header, u16);
type PacketCont0SType<'a, 'x> = (&'x Header, &'x u16);
type PacketCont0Input<'a, 'b, 'x> = POrSType<PacketCont0Type<'a, 'b>, PacketCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PacketCont0Input<'a, 'b, 'x>> for PacketCont0 {
    type Output = AndThen<bytes::Variable, Repeat<RecordCombinator>>;

    open spec fn requires(&self, deps: PacketCont0Input<'a, 'b, 'x>) -> bool {
        &&& ((spec_Header(), U16Le)).wf(deps@)
        }

    open spec fn ensures(&self, deps: PacketCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_packet_cont0(deps@)
    }

    fn apply(&self, deps: PacketCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, payload_len) = deps;
                let payload_len = *payload_len;
                AndThen(bytes::Variable((usize::ex_from(payload_len)) as usize), Repeat::new(Record()))
            }
            POrSType::S(deps) => {
                let (_, payload_len) = deps;
                let payload_len = *payload_len;
                AndThen(bytes::Variable((usize::ex_from(payload_len)) as usize), Repeat::new(Record()))
            }
        }
    }
}
                

}
