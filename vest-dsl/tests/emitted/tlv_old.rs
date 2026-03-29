
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

                

pub struct SpecRefinedPacket {
    pub header: SpecHeader,
    pub payload_len: u16,
    pub payload: Seq<SpecRecord>,
}

pub type SpecRefinedPacketInner = ((SpecHeader, u16), Seq<SpecRecord>);


impl SpecFrom<SpecRefinedPacket> for SpecRefinedPacketInner {
    open spec fn spec_from(m: SpecRefinedPacket) -> SpecRefinedPacketInner {
        ((m.header, m.payload_len), m.payload)
    }
}

impl SpecFrom<SpecRefinedPacketInner> for SpecRefinedPacket {
    open spec fn spec_from(m: SpecRefinedPacketInner) -> SpecRefinedPacket {
        let ((header, payload_len), payload) = m;
        SpecRefinedPacket { header, payload_len, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct RefinedPacket {
    pub header: Header,
    pub payload_len: u16,
    pub payload: RepeatResult<Record>,
}

impl View for RefinedPacket {
    type V = SpecRefinedPacket;

    open spec fn view(&self) -> Self::V {
        SpecRefinedPacket {
            header: self.header@,
            payload_len: self.payload_len@,
            payload: self.payload@,
        }
    }
}
pub type RefinedPacketInner = ((Header, u16), RepeatResult<Record>);

pub type RefinedPacketInnerRef<'a> = ((&'a Header, &'a u16), &'a RepeatResult<Record>);
impl<'a> From<&'a RefinedPacket> for RefinedPacketInnerRef<'a> {
    fn ex_from(m: &'a RefinedPacket) -> RefinedPacketInnerRef<'a> {
        ((&m.header, &m.payload_len), &m.payload)
    }
}

impl From<RefinedPacketInner> for RefinedPacket {
    fn ex_from(m: RefinedPacketInner) -> RefinedPacket {
        let ((header, payload_len), payload) = m;
        RefinedPacket { header, payload_len, payload }
    }
}

pub struct RefinedPacketMapper;
impl View for RefinedPacketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for RefinedPacketMapper {
    type Src = SpecRefinedPacketInner;
    type Dst = SpecRefinedPacket;
}
impl SpecIsoProof for RefinedPacketMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for RefinedPacketMapper {
    type Src = RefinedPacketInner;
    type Dst = RefinedPacket;
    type RefSrc = RefinedPacketInnerRef<'a>;
}

pub struct SpecRefinedPacketCombinator(pub SpecRefinedPacketCombinatorAlias);

impl SpecCombinator for SpecRefinedPacketCombinator {
    type Type = SpecRefinedPacket;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecRefinedPacketCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecRefinedPacketCombinatorAlias::is_prefix_secure() }
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
pub type SpecRefinedPacketCombinatorAlias = Mapped<SpecPair<(SpecHeaderCombinator, Refined<U16Le, Predicate2825674220911311795>), AndThen<bytes::Variable, Repeat<SpecRecordCombinator>>>, RefinedPacketMapper>;
pub struct Predicate2825674220911311795;
impl View for Predicate2825674220911311795 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate2825674220911311795 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 10000)
    }
}
impl SpecPred<u16> for Predicate2825674220911311795 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 10000)
    }
}

pub struct RefinedPacketCombinator(pub RefinedPacketCombinatorAlias);

impl View for RefinedPacketCombinator {
    type V = SpecRefinedPacketCombinator;
    open spec fn view(&self) -> Self::V { SpecRefinedPacketCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for RefinedPacketCombinator {
    type Type = RefinedPacket;
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
pub type RefinedPacketCombinatorAlias = Mapped<Pair<(HeaderCombinator, Refined<U16Le, Predicate2825674220911311795>), AndThen<bytes::Variable, Repeat<RecordCombinator>>, RefinedPacketCont0>, RefinedPacketMapper>;


pub open spec fn spec_RefinedPacket() -> SpecRefinedPacketCombinator {
    SpecRefinedPacketCombinator(
    Mapped {
        inner: Pair::spec_new((spec_Header(), Refined { inner: U16Le, predicate: Predicate2825674220911311795 }), |deps| spec_refined_packet_cont0(deps)),
        mapper: RefinedPacketMapper,
    })
}

pub open spec fn spec_refined_packet_cont0(deps: (SpecHeader, u16)) -> AndThen<bytes::Variable, Repeat<SpecRecordCombinator>> {
    let (_, payload_len) = deps;
    AndThen(bytes::Variable((usize::spec_from(payload_len)) as usize), Repeat(spec_Record()))
}

impl View for RefinedPacketCont0 {
    type V = spec_fn((SpecHeader, u16)) -> AndThen<bytes::Variable, Repeat<SpecRecordCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecHeader, u16)| {
            spec_refined_packet_cont0(deps)
        }
    }
}

                
pub fn RefinedPacket<'a>() -> (o: RefinedPacketCombinator)
    ensures o@ == spec_RefinedPacket(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = RefinedPacketCombinator(
    Mapped {
        inner: Pair::new((Header(), Refined { inner: U16Le, predicate: Predicate2825674220911311795 }), RefinedPacketCont0),
        mapper: RefinedPacketMapper,
    });
    // assert({
    //     &&& combinator@ == spec_RefinedPacket()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_RefinedPacket<'a>(input: &'a [u8]) -> (res: PResult<<RefinedPacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_RefinedPacket().spec_parse(input@) == Some((n as int, v@)),
        spec_RefinedPacket().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_RefinedPacket().spec_parse(input@) is None,
        spec_RefinedPacket().spec_parse(input@) is None ==> res is Err,
{
    let combinator = RefinedPacket();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_RefinedPacket<'a>(v: <RefinedPacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_RefinedPacket().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_RefinedPacket().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_RefinedPacket().spec_serialize(v@))
        },
{
    let combinator = RefinedPacket();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn RefinedPacket_len<'a>(v: <RefinedPacketCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_RefinedPacket().wf(v@),
        spec_RefinedPacket().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_RefinedPacket().spec_serialize(v@).len(),
{
    let combinator = RefinedPacket();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct RefinedPacketCont0;
type RefinedPacketCont0Type<'a, 'b> = &'b (Header, u16);
type RefinedPacketCont0SType<'a, 'x> = (&'x Header, &'x u16);
type RefinedPacketCont0Input<'a, 'b, 'x> = POrSType<RefinedPacketCont0Type<'a, 'b>, RefinedPacketCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<RefinedPacketCont0Input<'a, 'b, 'x>> for RefinedPacketCont0 {
    type Output = AndThen<bytes::Variable, Repeat<RecordCombinator>>;

    open spec fn requires(&self, deps: RefinedPacketCont0Input<'a, 'b, 'x>) -> bool {
        &&& ((spec_Header(), Refined { inner: U16Le, predicate: Predicate2825674220911311795 })).wf(deps@)
        }

    open spec fn ensures(&self, deps: RefinedPacketCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_refined_packet_cont0(deps@)
    }

    fn apply(&self, deps: RefinedPacketCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub struct SpecMsg3 {
    pub x: u16,
    pub y: u16,
}

pub type SpecMsg3Inner = (u16, u16);


impl SpecFrom<SpecMsg3> for SpecMsg3Inner {
    open spec fn spec_from(m: SpecMsg3) -> SpecMsg3Inner {
        (m.x, m.y)
    }
}

impl SpecFrom<SpecMsg3Inner> for SpecMsg3 {
    open spec fn spec_from(m: SpecMsg3Inner) -> SpecMsg3 {
        let (x, y) = m;
        SpecMsg3 { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg3 {
    pub x: u16,
    pub y: u16,
}

impl View for Msg3 {
    type V = SpecMsg3;

    open spec fn view(&self) -> Self::V {
        SpecMsg3 {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type Msg3Inner = (u16, u16);

pub type Msg3InnerRef<'a> = (&'a u16, &'a u16);
impl<'a> From<&'a Msg3> for Msg3InnerRef<'a> {
    fn ex_from(m: &'a Msg3) -> Msg3InnerRef<'a> {
        (&m.x, &m.y)
    }
}

impl From<Msg3Inner> for Msg3 {
    fn ex_from(m: Msg3Inner) -> Msg3 {
        let (x, y) = m;
        Msg3 { x, y }
    }
}

pub struct Msg3Mapper;
impl View for Msg3Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3Mapper {
    type Src = SpecMsg3Inner;
    type Dst = SpecMsg3;
}
impl SpecIsoProof for Msg3Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg3Mapper {
    type Src = Msg3Inner;
    type Dst = Msg3;
    type RefSrc = Msg3InnerRef<'a>;
}
type SpecMsg3CombinatorAlias1 = (U16Le, U16Le);
pub struct SpecMsg3Combinator(pub SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg3Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg3CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg3CombinatorAlias = Mapped<SpecMsg3CombinatorAlias1, Msg3Mapper>;
type Msg3CombinatorAlias1 = (U16Le, U16Le);
pub struct Msg3Combinator1(pub Msg3CombinatorAlias1);
impl View for Msg3Combinator1 {
    type V = SpecMsg3CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3Combinator1, Msg3CombinatorAlias1);

pub struct Msg3Combinator(pub Msg3CombinatorAlias);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3Combinator {
    type Type = Msg3;
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
pub type Msg3CombinatorAlias = Mapped<Msg3Combinator1, Msg3Mapper>;


pub open spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(
    Mapped {
        inner: (U16Le, U16Le),
        mapper: Msg3Mapper,
    })
}

                
pub fn msg3<'a>() -> (o: Msg3Combinator)
    ensures o@ == spec_msg3(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg3Combinator(
    Mapped {
        inner: Msg3Combinator1((U16Le, U16Le)),
        mapper: Msg3Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg3()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg3<'a>(input: &'a [u8]) -> (res: PResult<<Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg3().spec_parse(input@) == Some((n as int, v@)),
        spec_msg3().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg3().spec_parse(input@) is None,
        spec_msg3().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg3<'a>(v: <Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg3().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg3().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg3().spec_serialize(v@))
        },
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg3_len<'a>(v: <Msg3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg3().wf(v@),
        spec_msg3().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg3().spec_serialize(v@).len(),
{
    let combinator = msg3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecMsg1 = Seq<u8>;
pub type Msg1<'a> = &'a [u8];
pub type Msg1Ref<'a> = &'a &'a [u8];


pub struct SpecMsg1Combinator(pub SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg1Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg1CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg1CombinatorAlias = bytes::Fixed<32>;

pub struct Msg1Combinator(pub Msg1CombinatorAlias);

impl View for Msg1Combinator {
    type V = SpecMsg1Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1Combinator {
    type Type = Msg1<'a>;
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
pub type Msg1CombinatorAlias = bytes::Fixed<32>;


pub open spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(bytes::Fixed::<32>)
}

                
pub fn msg1<'a>() -> (o: Msg1Combinator)
    ensures o@ == spec_msg1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg1Combinator(bytes::Fixed::<32>);
    // assert({
    //     &&& combinator@ == spec_msg1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg1<'a>(input: &'a [u8]) -> (res: PResult<<Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg1().spec_parse(input@) == Some((n as int, v@)),
        spec_msg1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg1().spec_parse(input@) is None,
        spec_msg1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg1<'a>(v: <Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg1().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg1().spec_serialize(v@))
        },
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg1_len<'a>(v: <Msg1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg1().wf(v@),
        spec_msg1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg1().spec_serialize(v@).len(),
{
    let combinator = msg1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecMsg2 = SpecRefinedPacket;
pub type Msg2 = RefinedPacket;
pub type Msg2Ref<'a> = &'a RefinedPacket;


pub struct SpecMsg2Combinator(pub SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg2Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsg2CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg2CombinatorAlias = SpecRefinedPacketCombinator;

pub struct Msg2Combinator(pub Msg2CombinatorAlias);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;
    open spec fn view(&self) -> Self::V { SpecMsg2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2Combinator {
    type Type = Msg2;
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
pub type Msg2CombinatorAlias = RefinedPacketCombinator;


pub open spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(spec_RefinedPacket())
}

                
pub fn msg2<'a>() -> (o: Msg2Combinator)
    ensures o@ == spec_msg2(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Msg2Combinator(RefinedPacket());
    // assert({
    //     &&& combinator@ == spec_msg2()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg2<'a>(input: &'a [u8]) -> (res: PResult<<Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg2().spec_parse(input@) == Some((n as int, v@)),
        spec_msg2().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg2().spec_parse(input@) is None,
        spec_msg2().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg2<'a>(v: <Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg2().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg2().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg2().spec_serialize(v@))
        },
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg2_len<'a>(v: <Msg2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg2().wf(v@),
        spec_msg2().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg2().spec_serialize(v@).len(),
{
    let combinator = msg2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecMsgVal {
    Variant0(SpecMsg1),
    Variant1(SpecMsg2),
    Variant2(SpecMsg3),
}

pub type SpecMsgValInner = Either<SpecMsg1, Either<SpecMsg2, SpecMsg3>>;

impl SpecFrom<SpecMsgVal> for SpecMsgValInner {
    open spec fn spec_from(m: SpecMsgVal) -> SpecMsgValInner {
        match m {
            SpecMsgVal::Variant0(m) => Either::Left(m),
            SpecMsgVal::Variant1(m) => Either::Right(Either::Left(m)),
            SpecMsgVal::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecMsgValInner> for SpecMsgVal {
    open spec fn spec_from(m: SpecMsgValInner) -> SpecMsgVal {
        match m {
            Either::Left(m) => SpecMsgVal::Variant0(m),
            Either::Right(Either::Left(m)) => SpecMsgVal::Variant1(m),
            Either::Right(Either::Right(m)) => SpecMsgVal::Variant2(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgVal<'a> {
    Variant0(Msg1<'a>),
    Variant1(Msg2),
    Variant2(Msg3),
}

pub type MsgValInner<'a> = Either<Msg1<'a>, Either<Msg2, Msg3>>;

pub type MsgValInnerRef<'a> = Either<&'a Msg1<'a>, Either<&'a Msg2, &'a Msg3>>;


impl<'a> View for MsgVal<'a> {
    type V = SpecMsgVal;
    open spec fn view(&self) -> Self::V {
        match self {
            MsgVal::Variant0(m) => SpecMsgVal::Variant0(m@),
            MsgVal::Variant1(m) => SpecMsgVal::Variant1(m@),
            MsgVal::Variant2(m) => SpecMsgVal::Variant2(m@),
        }
    }
}


impl<'a> From<&'a MsgVal<'a>> for MsgValInnerRef<'a> {
    fn ex_from(m: &'a MsgVal<'a>) -> MsgValInnerRef<'a> {
        match m {
            MsgVal::Variant0(m) => Either::Left(m),
            MsgVal::Variant1(m) => Either::Right(Either::Left(m)),
            MsgVal::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<MsgValInner<'a>> for MsgVal<'a> {
    fn ex_from(m: MsgValInner<'a>) -> MsgVal<'a> {
        match m {
            Either::Left(m) => MsgVal::Variant0(m),
            Either::Right(Either::Left(m)) => MsgVal::Variant1(m),
            Either::Right(Either::Right(m)) => MsgVal::Variant2(m),
        }
    }
    
}


pub struct MsgValMapper;
impl View for MsgValMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgValMapper {
    type Src = SpecMsgValInner;
    type Dst = SpecMsgVal;
}
impl SpecIsoProof for MsgValMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgValMapper {
    type Src = MsgValInner<'a>;
    type Dst = MsgVal<'a>;
    type RefSrc = MsgValInnerRef<'a>;
}

type SpecMsgValCombinatorAlias1 = Choice<Cond<SpecMsg2Combinator>, Cond<SpecMsg3Combinator>>;
type SpecMsgValCombinatorAlias2 = Choice<Cond<SpecMsg1Combinator>, SpecMsgValCombinatorAlias1>;
pub struct SpecMsgValCombinator(pub SpecMsgValCombinatorAlias);

impl SpecCombinator for SpecMsgValCombinator {
    type Type = SpecMsgVal;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgValCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsgValCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgValCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecMsgValCombinatorAlias2, MsgValMapper>>;
type MsgValCombinatorAlias1 = Choice<Cond<Msg2Combinator>, Cond<Msg3Combinator>>;
type MsgValCombinatorAlias2 = Choice<Cond<Msg1Combinator>, MsgValCombinator1>;
pub struct MsgValCombinator1(pub MsgValCombinatorAlias1);
impl View for MsgValCombinator1 {
    type V = SpecMsgValCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgValCombinator1, MsgValCombinatorAlias1);

pub struct MsgValCombinator2(pub MsgValCombinatorAlias2);
impl View for MsgValCombinator2 {
    type V = SpecMsgValCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgValCombinator2, MsgValCombinatorAlias2);

pub struct MsgValCombinator(pub MsgValCombinatorAlias);

impl View for MsgValCombinator {
    type V = SpecMsgValCombinator;
    open spec fn view(&self) -> Self::V { SpecMsgValCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgValCombinator {
    type Type = MsgVal<'a>;
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
pub type MsgValCombinatorAlias = AndThen<bytes::Variable, Mapped<MsgValCombinator2, MsgValMapper>>;


pub open spec fn spec_msg_val(len: u16, tag: u8) -> SpecMsgValCombinator {
    SpecMsgValCombinator(AndThen(bytes::Variable((usize::spec_from(len)) as usize), Mapped { inner: Choice(Cond { cond: tag == 1, inner: spec_msg1() }, Choice(Cond { cond: tag == 2, inner: spec_msg2() }, Cond { cond: tag == 3, inner: spec_msg3() })), mapper: MsgValMapper }))
}

pub fn msg_val<'a>(len: u16, tag: u8) -> (o: MsgValCombinator)
    requires
        ((len) >= 0 && (len) <= 8000),

    ensures o@ == spec_msg_val(len@, tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MsgValCombinator(AndThen(bytes::Variable((usize::ex_from(len)) as usize), Mapped { inner: MsgValCombinator2(Choice::new(Cond { cond: tag == 1, inner: msg1() }, MsgValCombinator1(Choice::new(Cond { cond: tag == 2, inner: msg2() }, Cond { cond: tag == 3, inner: msg3() })))), mapper: MsgValMapper }));
    // assert({
    //     &&& combinator@ == spec_msg_val(len@, tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg_val<'a>(input: &'a [u8], len: u16, tag: u8) -> (res: PResult<<MsgValCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((len) >= 0 && (len) <= 8000),

    ensures
        res matches Ok((n, v)) ==> spec_msg_val(len@, tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_msg_val(len@, tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg_val(len@, tag@).spec_parse(input@) is None,
        spec_msg_val(len@, tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg_val( len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg_val<'a>(v: <MsgValCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, len: u16, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg_val(len@, tag@).wf(v@),
        ((len) >= 0 && (len) <= 8000),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg_val(len@, tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg_val(len@, tag@).spec_serialize(v@))
        },
{
    let combinator = msg_val( len, tag );
    combinator.serialize(v, data, pos)
}

pub fn msg_val_len<'a>(v: <MsgValCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, len: u16, tag: u8) -> (serialize_len: usize)
    requires
        spec_msg_val(len@, tag@).wf(v@),
        spec_msg_val(len@, tag@).spec_serialize(v@).len() <= usize::MAX,
        ((len) >= 0 && (len) <= 8000),

    ensures
        serialize_len == spec_msg_val(len@, tag@).spec_serialize(v@).len(),
{
    let combinator = msg_val( len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMsg {
    pub tag: u8,
    pub len: u16,
    pub val: SpecMsgVal,
}

pub type SpecMsgInner = ((u8, u16), SpecMsgVal);


impl SpecFrom<SpecMsg> for SpecMsgInner {
    open spec fn spec_from(m: SpecMsg) -> SpecMsgInner {
        ((m.tag, m.len), m.val)
    }
}

impl SpecFrom<SpecMsgInner> for SpecMsg {
    open spec fn spec_from(m: SpecMsgInner) -> SpecMsg {
        let ((tag, len), val) = m;
        SpecMsg { tag, len, val }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg<'a> {
    pub tag: u8,
    pub len: u16,
    pub val: MsgVal<'a>,
}

impl View for Msg<'_> {
    type V = SpecMsg;

    open spec fn view(&self) -> Self::V {
        SpecMsg {
            tag: self.tag@,
            len: self.len@,
            val: self.val@,
        }
    }
}
pub type MsgInner<'a> = ((u8, u16), MsgVal<'a>);

pub type MsgInnerRef<'a> = ((&'a u8, &'a u16), &'a MsgVal<'a>);
impl<'a> From<&'a Msg<'a>> for MsgInnerRef<'a> {
    fn ex_from(m: &'a Msg) -> MsgInnerRef<'a> {
        ((&m.tag, &m.len), &m.val)
    }
}

impl<'a> From<MsgInner<'a>> for Msg<'a> {
    fn ex_from(m: MsgInner) -> Msg {
        let ((tag, len), val) = m;
        Msg { tag, len, val }
    }
}

pub struct MsgMapper;
impl View for MsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgMapper {
    type Src = SpecMsgInner;
    type Dst = SpecMsg;
}
impl SpecIsoProof for MsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgMapper {
    type Src = MsgInner<'a>;
    type Dst = Msg<'a>;
    type RefSrc = MsgInnerRef<'a>;
}

pub struct SpecMsgCombinator(pub SpecMsgCombinatorAlias);

impl SpecCombinator for SpecMsgCombinator {
    type Type = SpecMsg;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgCombinatorAlias = Mapped<SpecPair<SpecPair<U8, Refined<U16Le, Predicate10187121219386167018>>, SpecMsgValCombinator>, MsgMapper>;
pub struct Predicate10187121219386167018;
impl View for Predicate10187121219386167018 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate10187121219386167018 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 8000)
    }
}
impl SpecPred<u16> for Predicate10187121219386167018 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 8000)
    }
}

pub struct MsgCombinator(pub MsgCombinatorAlias);

impl View for MsgCombinator {
    type V = SpecMsgCombinator;
    open spec fn view(&self) -> Self::V { SpecMsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgCombinator {
    type Type = Msg<'a>;
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
pub type MsgCombinatorAlias = Mapped<Pair<Pair<U8, Refined<U16Le, Predicate10187121219386167018>, MsgCont1>, MsgValCombinator, MsgCont0>, MsgMapper>;


pub open spec fn spec_msg() -> SpecMsgCombinator {
    SpecMsgCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(U8, |deps| spec_msg_cont1(deps)), |deps| spec_msg_cont0(deps)),
        mapper: MsgMapper,
    })
}

pub open spec fn spec_msg_cont1(deps: u8) -> Refined<U16Le, Predicate10187121219386167018> {
    let tag = deps;
    Refined { inner: U16Le, predicate: Predicate10187121219386167018 }
}

impl View for MsgCont1 {
    type V = spec_fn(u8) -> Refined<U16Le, Predicate10187121219386167018>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_msg_cont1(deps)
        }
    }
}

pub open spec fn spec_msg_cont0(deps: (u8, u16)) -> SpecMsgValCombinator {
    let (tag, len) = deps;
    spec_msg_val(len, tag)
}

impl View for MsgCont0 {
    type V = spec_fn((u8, u16)) -> SpecMsgValCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, u16)| {
            spec_msg_cont0(deps)
        }
    }
}

                
pub fn msg<'a>() -> (o: MsgCombinator)
    ensures o@ == spec_msg(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MsgCombinator(
    Mapped {
        inner: Pair::new(Pair::new(U8, MsgCont1), MsgCont0),
        mapper: MsgMapper,
    });
    // assert({
    //     &&& combinator@ == spec_msg()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_msg<'a>(input: &'a [u8]) -> (res: PResult<<MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_msg().spec_parse(input@) == Some((n as int, v@)),
        spec_msg().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_msg().spec_parse(input@) is None,
        spec_msg().spec_parse(input@) is None ==> res is Err,
{
    let combinator = msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_msg<'a>(v: <MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_msg().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_msg().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_msg().spec_serialize(v@))
        },
{
    let combinator = msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn msg_len<'a>(v: <MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_msg().wf(v@),
        spec_msg().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_msg().spec_serialize(v@).len(),
{
    let combinator = msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct MsgCont1;
type MsgCont1Type<'a, 'b> = &'b u8;
type MsgCont1SType<'a, 'x> = &'x u8;
type MsgCont1Input<'a, 'b, 'x> = POrSType<MsgCont1Type<'a, 'b>, MsgCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MsgCont1Input<'a, 'b, 'x>> for MsgCont1 {
    type Output = Refined<U16Le, Predicate10187121219386167018>;

    open spec fn requires(&self, deps: MsgCont1Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: MsgCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg_cont1(deps@)
    }

    fn apply(&self, deps: MsgCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                Refined { inner: U16Le, predicate: Predicate10187121219386167018 }
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                Refined { inner: U16Le, predicate: Predicate10187121219386167018 }
            }
        }
    }
}
pub struct MsgCont0;
type MsgCont0Type<'a, 'b> = &'b (u8, u16);
type MsgCont0SType<'a, 'x> = (&'x u8, &'x u16);
type MsgCont0Input<'a, 'b, 'x> = POrSType<MsgCont0Type<'a, 'b>, MsgCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MsgCont0Input<'a, 'b, 'x>> for MsgCont0 {
    type Output = MsgValCombinator;

    open spec fn requires(&self, deps: MsgCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(U8, |deps| spec_msg_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: MsgCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_msg_cont0(deps@)
    }

    fn apply(&self, deps: MsgCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (tag, len) = deps;
                let tag = *tag;
                let len = *len;
                msg_val(len, tag)
            }
            POrSType::S(deps) => {
                let (tag, len) = deps;
                let tag = *tag;
                let len = *len;
                msg_val(len, tag)
            }
        }
    }
}
                

}
