
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
    pub len: u16,
    pub flags: u8,
}

pub type SpecHeaderInner = (u16, u8);


impl SpecFrom<SpecHeader> for SpecHeaderInner {
    open spec fn spec_from(m: SpecHeader) -> SpecHeaderInner {
        (m.len, m.flags)
    }
}

impl SpecFrom<SpecHeaderInner> for SpecHeader {
    open spec fn spec_from(m: SpecHeaderInner) -> SpecHeader {
        let (len, flags) = m;
        SpecHeader { len, flags }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Header {
    pub len: u16,
    pub flags: u8,
}

impl View for Header {
    type V = SpecHeader;

    open spec fn view(&self) -> Self::V {
        SpecHeader {
            len: self.len@,
            flags: self.flags@,
        }
    }
}
pub type HeaderInner = (u16, u8);

pub type HeaderInnerRef<'a> = (&'a u16, &'a u8);
impl<'a> From<&'a Header> for HeaderInnerRef<'a> {
    fn ex_from(m: &'a Header) -> HeaderInnerRef<'a> {
        (&m.len, &m.flags)
    }
}

impl From<HeaderInner> for Header {
    fn ex_from(m: HeaderInner) -> Header {
        let (len, flags) = m;
        Header { len, flags }
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
pub type SpecHeaderCombinatorAlias = Mapped<SpecPair<Refined<U16Le, Predicate12905524399844557818>, U8>, HeaderMapper>;
pub struct Predicate12905524399844557818;
impl View for Predicate12905524399844557818 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate12905524399844557818 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate12905524399844557818 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}

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
pub type HeaderCombinatorAlias = Mapped<Pair<Refined<U16Le, Predicate12905524399844557818>, U8, HeaderCont0>, HeaderMapper>;


pub open spec fn spec_header() -> SpecHeaderCombinator {
    SpecHeaderCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Le, predicate: Predicate12905524399844557818 }, |deps| spec_header_cont0(deps)),
        mapper: HeaderMapper,
    })
}

pub open spec fn spec_header_cont0(deps: u16) -> U8 {
    let len = deps;
    U8
}

impl View for HeaderCont0 {
    type V = spec_fn(u16) -> U8;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_header_cont0(deps)
        }
    }
}

                
pub fn header<'a>() -> (o: HeaderCombinator)
    ensures o@ == spec_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = HeaderCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Le, predicate: Predicate12905524399844557818 }, HeaderCont0),
        mapper: HeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_header<'a>(input: &'a [u8]) -> (res: PResult<<HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_header().spec_parse(input@) == Some((n as int, v@)),
        spec_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_header().spec_parse(input@) is None,
        spec_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_header<'a>(v: <HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_header().spec_serialize(v@))
        },
{
    let combinator = header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn header_len<'a>(v: <HeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_header().wf(v@),
        spec_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_header().spec_serialize(v@).len(),
{
    let combinator = header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct HeaderCont0;
type HeaderCont0Type<'a, 'b> = &'b u16;
type HeaderCont0SType<'a, 'x> = &'x u16;
type HeaderCont0Input<'a, 'b, 'x> = POrSType<HeaderCont0Type<'a, 'b>, HeaderCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HeaderCont0Input<'a, 'b, 'x>> for HeaderCont0 {
    type Output = U8;

    open spec fn requires(&self, deps: HeaderCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Refined { inner: U16Le, predicate: Predicate12905524399844557818 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: HeaderCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_header_cont0(deps@)
    }

    fn apply(&self, deps: HeaderCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = deps;
                let len = *len;
                U8
            }
            POrSType::S(deps) => {
                let len = deps;
                let len = *len;
                U8
            }
        }
    }
}
                
pub type SpecHeaderAlias = SpecHeader;
pub type HeaderAlias = Header;
pub type HeaderAliasRef<'a> = &'a Header;


pub struct SpecHeaderAliasCombinator(pub SpecHeaderAliasCombinatorAlias);

impl SpecCombinator for SpecHeaderAliasCombinator {
    type Type = SpecHeaderAlias;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHeaderAliasCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecHeaderAliasCombinatorAlias::is_prefix_secure() }
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
pub type SpecHeaderAliasCombinatorAlias = SpecHeaderCombinator;

pub struct HeaderAliasCombinator(pub HeaderAliasCombinatorAlias);

impl View for HeaderAliasCombinator {
    type V = SpecHeaderAliasCombinator;
    open spec fn view(&self) -> Self::V { SpecHeaderAliasCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HeaderAliasCombinator {
    type Type = HeaderAlias;
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
pub type HeaderAliasCombinatorAlias = HeaderCombinator;


pub open spec fn spec_header_alias() -> SpecHeaderAliasCombinator {
    SpecHeaderAliasCombinator(spec_header())
}

                
pub fn header_alias<'a>() -> (o: HeaderAliasCombinator)
    ensures o@ == spec_header_alias(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = HeaderAliasCombinator(header());
    // assert({
    //     &&& combinator@ == spec_header_alias()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_header_alias<'a>(input: &'a [u8]) -> (res: PResult<<HeaderAliasCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_header_alias().spec_parse(input@) == Some((n as int, v@)),
        spec_header_alias().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_header_alias().spec_parse(input@) is None,
        spec_header_alias().spec_parse(input@) is None ==> res is Err,
{
    let combinator = header_alias();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_header_alias<'a>(v: <HeaderAliasCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_header_alias().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_header_alias().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_header_alias().spec_serialize(v@))
        },
{
    let combinator = header_alias();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn header_alias_len<'a>(v: <HeaderAliasCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_header_alias().wf(v@),
        spec_header_alias().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_header_alias().spec_serialize(v@).len(),
{
    let combinator = header_alias();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDivide {
    pub chunks: Seq<u8>,
}

pub type SpecDivideInner = Seq<u8>;


impl SpecFrom<SpecDivide> for SpecDivideInner {
    open spec fn spec_from(m: SpecDivide) -> SpecDivideInner {
        m.chunks
    }
}

impl SpecFrom<SpecDivideInner> for SpecDivide {
    open spec fn spec_from(m: SpecDivideInner) -> SpecDivide {
        let chunks = m;
        SpecDivide { chunks }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Divide<'a> {
    pub chunks: &'a [u8],
}

impl View for Divide<'_> {
    type V = SpecDivide;

    open spec fn view(&self) -> Self::V {
        SpecDivide {
            chunks: self.chunks@,
        }
    }
}
pub type DivideInner<'a> = &'a [u8];

pub type DivideInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a Divide<'a>> for DivideInnerRef<'a> {
    fn ex_from(m: &'a Divide) -> DivideInnerRef<'a> {
        &m.chunks
    }
}

impl<'a> From<DivideInner<'a>> for Divide<'a> {
    fn ex_from(m: DivideInner) -> Divide {
        let chunks = m;
        Divide { chunks }
    }
}

pub struct DivideMapper;
impl View for DivideMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DivideMapper {
    type Src = SpecDivideInner;
    type Dst = SpecDivide;
}
impl SpecIsoProof for DivideMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DivideMapper {
    type Src = DivideInner<'a>;
    type Dst = Divide<'a>;
    type RefSrc = DivideInnerRef<'a>;
}

pub struct SpecDivideCombinator(pub SpecDivideCombinatorAlias);

impl SpecCombinator for SpecDivideCombinator {
    type Type = SpecDivide;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDivideCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDivideCombinatorAlias::is_prefix_secure() }
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
pub type SpecDivideCombinatorAlias = Mapped<bytes::Variable, DivideMapper>;

pub struct DivideCombinator(pub DivideCombinatorAlias);

impl View for DivideCombinator {
    type V = SpecDivideCombinator;
    open spec fn view(&self) -> Self::V { SpecDivideCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DivideCombinator {
    type Type = Divide<'a>;
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
pub type DivideCombinatorAlias = Mapped<bytes::Variable, DivideMapper>;


pub open spec fn spec_divide(total: u32) -> SpecDivideCombinator {
    SpecDivideCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(total) / 4)) as usize),
        mapper: DivideMapper,
    })
}

pub fn divide<'a>(total: u32) -> (o: DivideCombinator)

    ensures o@ == spec_divide(total@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DivideCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(total) / 4)) as usize),
        mapper: DivideMapper,
    });
    // assert({
    //     &&& combinator@ == spec_divide(total@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_divide<'a>(input: &'a [u8], total: u32) -> (res: PResult<<DivideCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_divide(total@).spec_parse(input@) == Some((n as int, v@)),
        spec_divide(total@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_divide(total@).spec_parse(input@) is None,
        spec_divide(total@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = divide( total );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_divide<'a>(v: <DivideCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, total: u32) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_divide(total@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_divide(total@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_divide(total@).spec_serialize(v@))
        },
{
    let combinator = divide( total );
    combinator.serialize(v, data, pos)
}

pub fn divide_len<'a>(v: <DivideCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, total: u32) -> (serialize_len: usize)
    requires
        spec_divide(total@).wf(v@),
        spec_divide(total@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_divide(total@).spec_serialize(v@).len(),
{
    let combinator = divide( total );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecFixedChoice {
    Variant0(u16),
    Variant1(u16),
}

pub type SpecFixedChoiceInner = Either<u16, u16>;

impl SpecFrom<SpecFixedChoice> for SpecFixedChoiceInner {
    open spec fn spec_from(m: SpecFixedChoice) -> SpecFixedChoiceInner {
        match m {
            SpecFixedChoice::Variant0(m) => Either::Left(m),
            SpecFixedChoice::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecFixedChoiceInner> for SpecFixedChoice {
    open spec fn spec_from(m: SpecFixedChoiceInner) -> SpecFixedChoice {
        match m {
            Either::Left(m) => SpecFixedChoice::Variant0(m),
            Either::Right(m) => SpecFixedChoice::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixedChoice {
    Variant0(u16),
    Variant1(u16),
}

pub type FixedChoiceInner = Either<u16, u16>;

pub type FixedChoiceInnerRef<'a> = Either<&'a u16, &'a u16>;


impl View for FixedChoice {
    type V = SpecFixedChoice;
    open spec fn view(&self) -> Self::V {
        match self {
            FixedChoice::Variant0(m) => SpecFixedChoice::Variant0(m@),
            FixedChoice::Variant1(m) => SpecFixedChoice::Variant1(m@),
        }
    }
}


impl<'a> From<&'a FixedChoice> for FixedChoiceInnerRef<'a> {
    fn ex_from(m: &'a FixedChoice) -> FixedChoiceInnerRef<'a> {
        match m {
            FixedChoice::Variant0(m) => Either::Left(m),
            FixedChoice::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<FixedChoiceInner> for FixedChoice {
    fn ex_from(m: FixedChoiceInner) -> FixedChoice {
        match m {
            Either::Left(m) => FixedChoice::Variant0(m),
            Either::Right(m) => FixedChoice::Variant1(m),
        }
    }
    
}


pub struct FixedChoiceMapper;
impl View for FixedChoiceMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FixedChoiceMapper {
    type Src = SpecFixedChoiceInner;
    type Dst = SpecFixedChoice;
}
impl SpecIsoProof for FixedChoiceMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FixedChoiceMapper {
    type Src = FixedChoiceInner;
    type Dst = FixedChoice;
    type RefSrc = FixedChoiceInnerRef<'a>;
}

type SpecFixedChoiceCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U16Le>>;
pub struct SpecFixedChoiceCombinator(pub SpecFixedChoiceCombinatorAlias);

impl SpecCombinator for SpecFixedChoiceCombinator {
    type Type = SpecFixedChoice;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFixedChoiceCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecFixedChoiceCombinatorAlias::is_prefix_secure() }
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
pub type SpecFixedChoiceCombinatorAlias = Mapped<SpecFixedChoiceCombinatorAlias1, FixedChoiceMapper>;
type FixedChoiceCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U16Le>>;
pub struct FixedChoiceCombinator1(pub FixedChoiceCombinatorAlias1);
impl View for FixedChoiceCombinator1 {
    type V = SpecFixedChoiceCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FixedChoiceCombinator1, FixedChoiceCombinatorAlias1);

pub struct FixedChoiceCombinator(pub FixedChoiceCombinatorAlias);

impl View for FixedChoiceCombinator {
    type V = SpecFixedChoiceCombinator;
    open spec fn view(&self) -> Self::V { SpecFixedChoiceCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FixedChoiceCombinator {
    type Type = FixedChoice;
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
pub type FixedChoiceCombinatorAlias = Mapped<FixedChoiceCombinator1, FixedChoiceMapper>;


pub open spec fn spec_fixed_choice(tag: u8) -> SpecFixedChoiceCombinator {
    SpecFixedChoiceCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: U16Le }, Cond { cond: !(tag == 0), inner: U16Le }), mapper: FixedChoiceMapper })
}

pub fn fixed_choice<'a>(tag: u8) -> (o: FixedChoiceCombinator)

    ensures o@ == spec_fixed_choice(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = FixedChoiceCombinator(Mapped { inner: FixedChoiceCombinator1(Choice::new(Cond { cond: tag == 0, inner: U16Le }, Cond { cond: !(tag == 0), inner: U16Le })), mapper: FixedChoiceMapper });
    // assert({
    //     &&& combinator@ == spec_fixed_choice(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_fixed_choice<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<FixedChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_fixed_choice(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_fixed_choice(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_fixed_choice(tag@).spec_parse(input@) is None,
        spec_fixed_choice(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = fixed_choice( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_fixed_choice<'a>(v: <FixedChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_fixed_choice(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_fixed_choice(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_fixed_choice(tag@).spec_serialize(v@))
        },
{
    let combinator = fixed_choice( tag );
    combinator.serialize(v, data, pos)
}

pub fn fixed_choice_len<'a>(v: <FixedChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_fixed_choice(tag@).wf(v@),
        spec_fixed_choice(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_fixed_choice(tag@).spec_serialize(v@).len(),
{
    let combinator = fixed_choice( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecSimpleSub {
    pub data: Seq<u8>,
}

pub type SpecSimpleSubInner = Seq<u8>;


impl SpecFrom<SpecSimpleSub> for SpecSimpleSubInner {
    open spec fn spec_from(m: SpecSimpleSub) -> SpecSimpleSubInner {
        m.data
    }
}

impl SpecFrom<SpecSimpleSubInner> for SpecSimpleSub {
    open spec fn spec_from(m: SpecSimpleSubInner) -> SpecSimpleSub {
        let data = m;
        SpecSimpleSub { data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SimpleSub<'a> {
    pub data: &'a [u8],
}

impl View for SimpleSub<'_> {
    type V = SpecSimpleSub;

    open spec fn view(&self) -> Self::V {
        SpecSimpleSub {
            data: self.data@,
        }
    }
}
pub type SimpleSubInner<'a> = &'a [u8];

pub type SimpleSubInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a SimpleSub<'a>> for SimpleSubInnerRef<'a> {
    fn ex_from(m: &'a SimpleSub) -> SimpleSubInnerRef<'a> {
        &m.data
    }
}

impl<'a> From<SimpleSubInner<'a>> for SimpleSub<'a> {
    fn ex_from(m: SimpleSubInner) -> SimpleSub {
        let data = m;
        SimpleSub { data }
    }
}

pub struct SimpleSubMapper;
impl View for SimpleSubMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SimpleSubMapper {
    type Src = SpecSimpleSubInner;
    type Dst = SpecSimpleSub;
}
impl SpecIsoProof for SimpleSubMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SimpleSubMapper {
    type Src = SimpleSubInner<'a>;
    type Dst = SimpleSub<'a>;
    type RefSrc = SimpleSubInnerRef<'a>;
}

pub struct SpecSimpleSubCombinator(pub SpecSimpleSubCombinatorAlias);

impl SpecCombinator for SpecSimpleSubCombinator {
    type Type = SpecSimpleSub;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSimpleSubCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecSimpleSubCombinatorAlias::is_prefix_secure() }
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
pub type SpecSimpleSubCombinatorAlias = Mapped<bytes::Variable, SimpleSubMapper>;

pub struct SimpleSubCombinator(pub SimpleSubCombinatorAlias);

impl View for SimpleSubCombinator {
    type V = SpecSimpleSubCombinator;
    open spec fn view(&self) -> Self::V { SpecSimpleSubCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SimpleSubCombinator {
    type Type = SimpleSub<'a>;
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
pub type SimpleSubCombinatorAlias = Mapped<bytes::Variable, SimpleSubMapper>;


pub open spec fn spec_simple_sub(len: u16) -> SpecSimpleSubCombinator {
    SpecSimpleSubCombinator(
    Mapped {
        inner: bytes::Variable((((usize::spec_from(len) - 3) - 1)) as usize),
        mapper: SimpleSubMapper,
    })
}

pub fn simple_sub<'a>(len: u16) -> (o: SimpleSubCombinator)
    requires
        ((len) >= 4 && (len) <= 65535),

    ensures o@ == spec_simple_sub(len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = SimpleSubCombinator(
    Mapped {
        inner: bytes::Variable((((usize::ex_from(len) - 3) - 1)) as usize),
        mapper: SimpleSubMapper,
    });
    // assert({
    //     &&& combinator@ == spec_simple_sub(len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_simple_sub<'a>(input: &'a [u8], len: u16) -> (res: PResult<<SimpleSubCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((len) >= 4 && (len) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_simple_sub(len@).spec_parse(input@) == Some((n as int, v@)),
        spec_simple_sub(len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_simple_sub(len@).spec_parse(input@) is None,
        spec_simple_sub(len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = simple_sub( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_simple_sub<'a>(v: <SimpleSubCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, len: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_simple_sub(len@).wf(v@),
        ((len) >= 4 && (len) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_simple_sub(len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_simple_sub(len@).spec_serialize(v@))
        },
{
    let combinator = simple_sub( len );
    combinator.serialize(v, data, pos)
}

pub fn simple_sub_len<'a>(v: <SimpleSubCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, len: u16) -> (serialize_len: usize)
    requires
        spec_simple_sub(len@).wf(v@),
        spec_simple_sub(len@).spec_serialize(v@).len() <= usize::MAX,
        ((len) >= 4 && (len) <= 65535),

    ensures
        serialize_len == spec_simple_sub(len@).spec_serialize(v@).len(),
{
    let combinator = simple_sub( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecAliasSize {
    pub bytes: Seq<u8>,
}

pub type SpecAliasSizeInner = Seq<u8>;


impl SpecFrom<SpecAliasSize> for SpecAliasSizeInner {
    open spec fn spec_from(m: SpecAliasSize) -> SpecAliasSizeInner {
        m.bytes
    }
}

impl SpecFrom<SpecAliasSizeInner> for SpecAliasSize {
    open spec fn spec_from(m: SpecAliasSizeInner) -> SpecAliasSize {
        let bytes = m;
        SpecAliasSize { bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct AliasSize<'a> {
    pub bytes: &'a [u8],
}

impl View for AliasSize<'_> {
    type V = SpecAliasSize;

    open spec fn view(&self) -> Self::V {
        SpecAliasSize {
            bytes: self.bytes@,
        }
    }
}
pub type AliasSizeInner<'a> = &'a [u8];

pub type AliasSizeInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a AliasSize<'a>> for AliasSizeInnerRef<'a> {
    fn ex_from(m: &'a AliasSize) -> AliasSizeInnerRef<'a> {
        &m.bytes
    }
}

impl<'a> From<AliasSizeInner<'a>> for AliasSize<'a> {
    fn ex_from(m: AliasSizeInner) -> AliasSize {
        let bytes = m;
        AliasSize { bytes }
    }
}

pub struct AliasSizeMapper;
impl View for AliasSizeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AliasSizeMapper {
    type Src = SpecAliasSizeInner;
    type Dst = SpecAliasSize;
}
impl SpecIsoProof for AliasSizeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for AliasSizeMapper {
    type Src = AliasSizeInner<'a>;
    type Dst = AliasSize<'a>;
    type RefSrc = AliasSizeInnerRef<'a>;
}

pub struct SpecAliasSizeCombinator(pub SpecAliasSizeCombinatorAlias);

impl SpecCombinator for SpecAliasSizeCombinator {
    type Type = SpecAliasSize;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAliasSizeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAliasSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecAliasSizeCombinatorAlias = Mapped<bytes::Fixed<3>, AliasSizeMapper>;

pub struct AliasSizeCombinator(pub AliasSizeCombinatorAlias);

impl View for AliasSizeCombinator {
    type V = SpecAliasSizeCombinator;
    open spec fn view(&self) -> Self::V { SpecAliasSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AliasSizeCombinator {
    type Type = AliasSize<'a>;
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
pub type AliasSizeCombinatorAlias = Mapped<bytes::Fixed<3>, AliasSizeMapper>;


pub open spec fn spec_alias_size() -> SpecAliasSizeCombinator {
    SpecAliasSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: AliasSizeMapper,
    })
}

                
pub fn alias_size<'a>() -> (o: AliasSizeCombinator)
    ensures o@ == spec_alias_size(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AliasSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: AliasSizeMapper,
    });
    // assert({
    //     &&& combinator@ == spec_alias_size()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_alias_size<'a>(input: &'a [u8]) -> (res: PResult<<AliasSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_alias_size().spec_parse(input@) == Some((n as int, v@)),
        spec_alias_size().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_alias_size().spec_parse(input@) is None,
        spec_alias_size().spec_parse(input@) is None ==> res is Err,
{
    let combinator = alias_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_alias_size<'a>(v: <AliasSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_alias_size().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_alias_size().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_alias_size().spec_serialize(v@))
        },
{
    let combinator = alias_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn alias_size_len<'a>(v: <AliasSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_alias_size().wf(v@),
        spec_alias_size().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_alias_size().spec_serialize(v@).len(),
{
    let combinator = alias_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMultiArith {
    pub body: Seq<u8>,
}

pub type SpecMultiArithInner = Seq<u8>;


impl SpecFrom<SpecMultiArith> for SpecMultiArithInner {
    open spec fn spec_from(m: SpecMultiArith) -> SpecMultiArithInner {
        m.body
    }
}

impl SpecFrom<SpecMultiArithInner> for SpecMultiArith {
    open spec fn spec_from(m: SpecMultiArithInner) -> SpecMultiArith {
        let body = m;
        SpecMultiArith { body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MultiArith<'a> {
    pub body: &'a [u8],
}

impl View for MultiArith<'_> {
    type V = SpecMultiArith;

    open spec fn view(&self) -> Self::V {
        SpecMultiArith {
            body: self.body@,
        }
    }
}
pub type MultiArithInner<'a> = &'a [u8];

pub type MultiArithInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a MultiArith<'a>> for MultiArithInnerRef<'a> {
    fn ex_from(m: &'a MultiArith) -> MultiArithInnerRef<'a> {
        &m.body
    }
}

impl<'a> From<MultiArithInner<'a>> for MultiArith<'a> {
    fn ex_from(m: MultiArithInner) -> MultiArith {
        let body = m;
        MultiArith { body }
    }
}

pub struct MultiArithMapper;
impl View for MultiArithMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MultiArithMapper {
    type Src = SpecMultiArithInner;
    type Dst = SpecMultiArith;
}
impl SpecIsoProof for MultiArithMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MultiArithMapper {
    type Src = MultiArithInner<'a>;
    type Dst = MultiArith<'a>;
    type RefSrc = MultiArithInnerRef<'a>;
}

pub struct SpecMultiArithCombinator(pub SpecMultiArithCombinatorAlias);

impl SpecCombinator for SpecMultiArithCombinator {
    type Type = SpecMultiArith;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMultiArithCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMultiArithCombinatorAlias::is_prefix_secure() }
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
pub type SpecMultiArithCombinatorAlias = Mapped<bytes::Variable, MultiArithMapper>;

pub struct MultiArithCombinator(pub MultiArithCombinatorAlias);

impl View for MultiArithCombinator {
    type V = SpecMultiArithCombinator;
    open spec fn view(&self) -> Self::V { SpecMultiArithCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MultiArithCombinator {
    type Type = MultiArith<'a>;
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
pub type MultiArithCombinatorAlias = Mapped<bytes::Variable, MultiArithMapper>;


pub open spec fn spec_multi_arith(total: u32, hdr_len: u8) -> SpecMultiArithCombinator {
    SpecMultiArithCombinator(
    Mapped {
        inner: bytes::Variable((((usize::spec_from(total) - usize::spec_from(hdr_len)) - 8)) as usize),
        mapper: MultiArithMapper,
    })
}

pub fn multi_arith<'a>(total: u32, hdr_len: u8) -> (o: MultiArithCombinator)
    requires
        ((total) >= 263 && (total) <= 4294967295),
        ((hdr_len) >= 0 && (hdr_len) <= 255),

    ensures o@ == spec_multi_arith(total@, hdr_len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MultiArithCombinator(
    Mapped {
        inner: bytes::Variable((((usize::ex_from(total) - usize::ex_from(hdr_len)) - 8)) as usize),
        mapper: MultiArithMapper,
    });
    // assert({
    //     &&& combinator@ == spec_multi_arith(total@, hdr_len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_multi_arith<'a>(input: &'a [u8], total: u32, hdr_len: u8) -> (res: PResult<<MultiArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((total) >= 263 && (total) <= 4294967295),
        ((hdr_len) >= 0 && (hdr_len) <= 255),

    ensures
        res matches Ok((n, v)) ==> spec_multi_arith(total@, hdr_len@).spec_parse(input@) == Some((n as int, v@)),
        spec_multi_arith(total@, hdr_len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_multi_arith(total@, hdr_len@).spec_parse(input@) is None,
        spec_multi_arith(total@, hdr_len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = multi_arith( total, hdr_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_multi_arith<'a>(v: <MultiArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, total: u32, hdr_len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_multi_arith(total@, hdr_len@).wf(v@),
        ((total) >= 263 && (total) <= 4294967295),
        ((hdr_len) >= 0 && (hdr_len) <= 255),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_multi_arith(total@, hdr_len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_multi_arith(total@, hdr_len@).spec_serialize(v@))
        },
{
    let combinator = multi_arith( total, hdr_len );
    combinator.serialize(v, data, pos)
}

pub fn multi_arith_len<'a>(v: <MultiArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, total: u32, hdr_len: u8) -> (serialize_len: usize)
    requires
        spec_multi_arith(total@, hdr_len@).wf(v@),
        spec_multi_arith(total@, hdr_len@).spec_serialize(v@).len() <= usize::MAX,
        ((total) >= 263 && (total) <= 4294967295),
        ((hdr_len) >= 0 && (hdr_len) <= 255),

    ensures
        serialize_len == spec_multi_arith(total@, hdr_len@).spec_serialize(v@).len(),
{
    let combinator = multi_arith( total, hdr_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecSizeArith {
    pub bytes: Seq<u8>,
}

pub type SpecSizeArithInner = Seq<u8>;


impl SpecFrom<SpecSizeArith> for SpecSizeArithInner {
    open spec fn spec_from(m: SpecSizeArith) -> SpecSizeArithInner {
        m.bytes
    }
}

impl SpecFrom<SpecSizeArithInner> for SpecSizeArith {
    open spec fn spec_from(m: SpecSizeArithInner) -> SpecSizeArith {
        let bytes = m;
        SpecSizeArith { bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SizeArith<'a> {
    pub bytes: &'a [u8],
}

impl View for SizeArith<'_> {
    type V = SpecSizeArith;

    open spec fn view(&self) -> Self::V {
        SpecSizeArith {
            bytes: self.bytes@,
        }
    }
}
pub type SizeArithInner<'a> = &'a [u8];

pub type SizeArithInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a SizeArith<'a>> for SizeArithInnerRef<'a> {
    fn ex_from(m: &'a SizeArith) -> SizeArithInnerRef<'a> {
        &m.bytes
    }
}

impl<'a> From<SizeArithInner<'a>> for SizeArith<'a> {
    fn ex_from(m: SizeArithInner) -> SizeArith {
        let bytes = m;
        SizeArith { bytes }
    }
}

pub struct SizeArithMapper;
impl View for SizeArithMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SizeArithMapper {
    type Src = SpecSizeArithInner;
    type Dst = SpecSizeArith;
}
impl SpecIsoProof for SizeArithMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SizeArithMapper {
    type Src = SizeArithInner<'a>;
    type Dst = SizeArith<'a>;
    type RefSrc = SizeArithInnerRef<'a>;
}

pub struct SpecSizeArithCombinator(pub SpecSizeArithCombinatorAlias);

impl SpecCombinator for SpecSizeArithCombinator {
    type Type = SpecSizeArith;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSizeArithCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecSizeArithCombinatorAlias::is_prefix_secure() }
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
pub type SpecSizeArithCombinatorAlias = Mapped<bytes::Fixed<4>, SizeArithMapper>;

pub struct SizeArithCombinator(pub SizeArithCombinatorAlias);

impl View for SizeArithCombinator {
    type V = SpecSizeArithCombinator;
    open spec fn view(&self) -> Self::V { SpecSizeArithCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SizeArithCombinator {
    type Type = SizeArith<'a>;
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
pub type SizeArithCombinatorAlias = Mapped<bytes::Fixed<4>, SizeArithMapper>;


pub open spec fn spec_size_arith() -> SpecSizeArithCombinator {
    SpecSizeArithCombinator(
    Mapped {
        inner: bytes::Fixed::<4>,
        mapper: SizeArithMapper,
    })
}

                
pub fn size_arith<'a>() -> (o: SizeArithCombinator)
    ensures o@ == spec_size_arith(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = SizeArithCombinator(
    Mapped {
        inner: bytes::Fixed::<4>,
        mapper: SizeArithMapper,
    });
    // assert({
    //     &&& combinator@ == spec_size_arith()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_size_arith<'a>(input: &'a [u8]) -> (res: PResult<<SizeArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_size_arith().spec_parse(input@) == Some((n as int, v@)),
        spec_size_arith().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_size_arith().spec_parse(input@) is None,
        spec_size_arith().spec_parse(input@) is None ==> res is Err,
{
    let combinator = size_arith();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_size_arith<'a>(v: <SizeArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_size_arith().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_size_arith().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_size_arith().spec_serialize(v@))
        },
{
    let combinator = size_arith();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn size_arith_len<'a>(v: <SizeArithCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_size_arith().wf(v@),
        spec_size_arith().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_size_arith().spec_serialize(v@).len(),
{
    let combinator = size_arith();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecPayloadWithHeader {
    pub data: Seq<u8>,
}

pub type SpecPayloadWithHeaderInner = Seq<u8>;


impl SpecFrom<SpecPayloadWithHeader> for SpecPayloadWithHeaderInner {
    open spec fn spec_from(m: SpecPayloadWithHeader) -> SpecPayloadWithHeaderInner {
        m.data
    }
}

impl SpecFrom<SpecPayloadWithHeaderInner> for SpecPayloadWithHeader {
    open spec fn spec_from(m: SpecPayloadWithHeaderInner) -> SpecPayloadWithHeader {
        let data = m;
        SpecPayloadWithHeader { data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PayloadWithHeader<'a> {
    pub data: &'a [u8],
}

impl View for PayloadWithHeader<'_> {
    type V = SpecPayloadWithHeader;

    open spec fn view(&self) -> Self::V {
        SpecPayloadWithHeader {
            data: self.data@,
        }
    }
}
pub type PayloadWithHeaderInner<'a> = &'a [u8];

pub type PayloadWithHeaderInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a PayloadWithHeader<'a>> for PayloadWithHeaderInnerRef<'a> {
    fn ex_from(m: &'a PayloadWithHeader) -> PayloadWithHeaderInnerRef<'a> {
        &m.data
    }
}

impl<'a> From<PayloadWithHeaderInner<'a>> for PayloadWithHeader<'a> {
    fn ex_from(m: PayloadWithHeaderInner) -> PayloadWithHeader {
        let data = m;
        PayloadWithHeader { data }
    }
}

pub struct PayloadWithHeaderMapper;
impl View for PayloadWithHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PayloadWithHeaderMapper {
    type Src = SpecPayloadWithHeaderInner;
    type Dst = SpecPayloadWithHeader;
}
impl SpecIsoProof for PayloadWithHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PayloadWithHeaderMapper {
    type Src = PayloadWithHeaderInner<'a>;
    type Dst = PayloadWithHeader<'a>;
    type RefSrc = PayloadWithHeaderInnerRef<'a>;
}

pub struct SpecPayloadWithHeaderCombinator(pub SpecPayloadWithHeaderCombinatorAlias);

impl SpecCombinator for SpecPayloadWithHeaderCombinator {
    type Type = SpecPayloadWithHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPayloadWithHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPayloadWithHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecPayloadWithHeaderCombinatorAlias = Mapped<bytes::Variable, PayloadWithHeaderMapper>;

pub struct PayloadWithHeaderCombinator(pub PayloadWithHeaderCombinatorAlias);

impl View for PayloadWithHeaderCombinator {
    type V = SpecPayloadWithHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecPayloadWithHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PayloadWithHeaderCombinator {
    type Type = PayloadWithHeader<'a>;
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
pub type PayloadWithHeaderCombinatorAlias = Mapped<bytes::Variable, PayloadWithHeaderMapper>;


pub open spec fn spec_payload_with_header(hdr: SpecHeader) -> SpecPayloadWithHeaderCombinator {
    SpecPayloadWithHeaderCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(hdr.len) - 3)) as usize),
        mapper: PayloadWithHeaderMapper,
    })
}

pub fn payload_with_header<'a>(hdr: Header) -> (o: PayloadWithHeaderCombinator)
    requires
        spec_header().wf(hdr@),

    ensures o@ == spec_payload_with_header(hdr@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PayloadWithHeaderCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(hdr.len) - 3)) as usize),
        mapper: PayloadWithHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_payload_with_header(hdr@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_payload_with_header<'a>(input: &'a [u8], hdr: Header) -> (res: PResult<<PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_header().wf(hdr@),

    ensures
        res matches Ok((n, v)) ==> spec_payload_with_header(hdr@).spec_parse(input@) == Some((n as int, v@)),
        spec_payload_with_header(hdr@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_payload_with_header(hdr@).spec_parse(input@) is None,
        spec_payload_with_header(hdr@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = payload_with_header( hdr );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_payload_with_header<'a>(v: <PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, hdr: Header) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_payload_with_header(hdr@).wf(v@),
        spec_header().wf(hdr@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_payload_with_header(hdr@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_payload_with_header(hdr@).spec_serialize(v@))
        },
{
    let combinator = payload_with_header( hdr );
    combinator.serialize(v, data, pos)
}

pub fn payload_with_header_len<'a>(v: <PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, hdr: Header) -> (serialize_len: usize)
    requires
        spec_payload_with_header(hdr@).wf(v@),
        spec_payload_with_header(hdr@).spec_serialize(v@).len() <= usize::MAX,
        spec_header().wf(hdr@),

    ensures
        serialize_len == spec_payload_with_header(hdr@).spec_serialize(v@).len(),
{
    let combinator = payload_with_header( hdr );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMixedConst {
    pub data: Seq<u8>,
}

pub type SpecMixedConstInner = Seq<u8>;


impl SpecFrom<SpecMixedConst> for SpecMixedConstInner {
    open spec fn spec_from(m: SpecMixedConst) -> SpecMixedConstInner {
        m.data
    }
}

impl SpecFrom<SpecMixedConstInner> for SpecMixedConst {
    open spec fn spec_from(m: SpecMixedConstInner) -> SpecMixedConst {
        let data = m;
        SpecMixedConst { data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MixedConst<'a> {
    pub data: &'a [u8],
}

impl View for MixedConst<'_> {
    type V = SpecMixedConst;

    open spec fn view(&self) -> Self::V {
        SpecMixedConst {
            data: self.data@,
        }
    }
}
pub type MixedConstInner<'a> = &'a [u8];

pub type MixedConstInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a MixedConst<'a>> for MixedConstInnerRef<'a> {
    fn ex_from(m: &'a MixedConst) -> MixedConstInnerRef<'a> {
        &m.data
    }
}

impl<'a> From<MixedConstInner<'a>> for MixedConst<'a> {
    fn ex_from(m: MixedConstInner) -> MixedConst {
        let data = m;
        MixedConst { data }
    }
}

pub struct MixedConstMapper;
impl View for MixedConstMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MixedConstMapper {
    type Src = SpecMixedConstInner;
    type Dst = SpecMixedConst;
}
impl SpecIsoProof for MixedConstMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MixedConstMapper {
    type Src = MixedConstInner<'a>;
    type Dst = MixedConst<'a>;
    type RefSrc = MixedConstInnerRef<'a>;
}

pub struct SpecMixedConstCombinator(pub SpecMixedConstCombinatorAlias);

impl SpecCombinator for SpecMixedConstCombinator {
    type Type = SpecMixedConst;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMixedConstCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMixedConstCombinatorAlias::is_prefix_secure() }
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
pub type SpecMixedConstCombinatorAlias = Mapped<bytes::Variable, MixedConstMapper>;

pub struct MixedConstCombinator(pub MixedConstCombinatorAlias);

impl View for MixedConstCombinator {
    type V = SpecMixedConstCombinator;
    open spec fn view(&self) -> Self::V { SpecMixedConstCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MixedConstCombinator {
    type Type = MixedConst<'a>;
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
pub type MixedConstCombinatorAlias = Mapped<bytes::Variable, MixedConstMapper>;


pub open spec fn spec_mixed_const(len: u16) -> SpecMixedConstCombinator {
    SpecMixedConstCombinator(
    Mapped {
        inner: bytes::Variable((((usize::spec_from(len) - 4) + 2)) as usize),
        mapper: MixedConstMapper,
    })
}

pub fn mixed_const<'a>(len: u16) -> (o: MixedConstCombinator)
    requires
        ((len) >= 4 && (len) <= 65535),

    ensures o@ == spec_mixed_const(len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MixedConstCombinator(
    Mapped {
        inner: bytes::Variable((((usize::ex_from(len) - 4) + 2)) as usize),
        mapper: MixedConstMapper,
    });
    // assert({
    //     &&& combinator@ == spec_mixed_const(len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_mixed_const<'a>(input: &'a [u8], len: u16) -> (res: PResult<<MixedConstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((len) >= 4 && (len) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_mixed_const(len@).spec_parse(input@) == Some((n as int, v@)),
        spec_mixed_const(len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mixed_const(len@).spec_parse(input@) is None,
        spec_mixed_const(len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = mixed_const( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mixed_const<'a>(v: <MixedConstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, len: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mixed_const(len@).wf(v@),
        ((len) >= 4 && (len) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mixed_const(len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mixed_const(len@).spec_serialize(v@))
        },
{
    let combinator = mixed_const( len );
    combinator.serialize(v, data, pos)
}

pub fn mixed_const_len<'a>(v: <MixedConstCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, len: u16) -> (serialize_len: usize)
    requires
        spec_mixed_const(len@).wf(v@),
        spec_mixed_const(len@).spec_serialize(v@).len() <= usize::MAX,
        ((len) >= 4 && (len) <= 65535),

    ensures
        serialize_len == spec_mixed_const(len@).spec_serialize(v@).len(),
{
    let combinator = mixed_const( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub type SpecChoiceTag = Seq<u8>;
pub type ChoiceTag<'a> = &'a [u8];
pub type ChoiceTagRef<'a> = &'a &'a [u8];


pub struct SpecChoiceTagCombinator(pub SpecChoiceTagCombinatorAlias);

impl SpecCombinator for SpecChoiceTagCombinator {
    type Type = SpecChoiceTag;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceTagCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceTagCombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceTagCombinatorAlias = bytes::Fixed<2>;

pub struct ChoiceTagCombinator(pub ChoiceTagCombinatorAlias);

impl View for ChoiceTagCombinator {
    type V = SpecChoiceTagCombinator;
    open spec fn view(&self) -> Self::V { SpecChoiceTagCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceTagCombinator {
    type Type = ChoiceTag<'a>;
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
pub type ChoiceTagCombinatorAlias = bytes::Fixed<2>;


pub open spec fn spec_choice_tag() -> SpecChoiceTagCombinator {
    SpecChoiceTagCombinator(bytes::Fixed::<2>)
}

                
pub fn choice_tag<'a>() -> (o: ChoiceTagCombinator)
    ensures o@ == spec_choice_tag(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceTagCombinator(bytes::Fixed::<2>);
    // assert({
    //     &&& combinator@ == spec_choice_tag()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_tag<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_tag().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_tag().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_tag().spec_parse(input@) is None,
        spec_choice_tag().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_tag<'a>(v: <ChoiceTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_tag().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_choice_tag().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_choice_tag().spec_serialize(v@))
        },
{
    let combinator = choice_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn choice_tag_len<'a>(v: <ChoiceTagCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_tag().wf(v@),
        spec_choice_tag().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_tag().spec_serialize(v@).len(),
{
    let combinator = choice_tag();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecNamedSize {
    pub bytes: Seq<u8>,
}

pub type SpecNamedSizeInner = Seq<u8>;


impl SpecFrom<SpecNamedSize> for SpecNamedSizeInner {
    open spec fn spec_from(m: SpecNamedSize) -> SpecNamedSizeInner {
        m.bytes
    }
}

impl SpecFrom<SpecNamedSizeInner> for SpecNamedSize {
    open spec fn spec_from(m: SpecNamedSizeInner) -> SpecNamedSize {
        let bytes = m;
        SpecNamedSize { bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NamedSize<'a> {
    pub bytes: &'a [u8],
}

impl View for NamedSize<'_> {
    type V = SpecNamedSize;

    open spec fn view(&self) -> Self::V {
        SpecNamedSize {
            bytes: self.bytes@,
        }
    }
}
pub type NamedSizeInner<'a> = &'a [u8];

pub type NamedSizeInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a NamedSize<'a>> for NamedSizeInnerRef<'a> {
    fn ex_from(m: &'a NamedSize) -> NamedSizeInnerRef<'a> {
        &m.bytes
    }
}

impl<'a> From<NamedSizeInner<'a>> for NamedSize<'a> {
    fn ex_from(m: NamedSizeInner) -> NamedSize {
        let bytes = m;
        NamedSize { bytes }
    }
}

pub struct NamedSizeMapper;
impl View for NamedSizeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NamedSizeMapper {
    type Src = SpecNamedSizeInner;
    type Dst = SpecNamedSize;
}
impl SpecIsoProof for NamedSizeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NamedSizeMapper {
    type Src = NamedSizeInner<'a>;
    type Dst = NamedSize<'a>;
    type RefSrc = NamedSizeInnerRef<'a>;
}

pub struct SpecNamedSizeCombinator(pub SpecNamedSizeCombinatorAlias);

impl SpecCombinator for SpecNamedSizeCombinator {
    type Type = SpecNamedSize;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNamedSizeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNamedSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecNamedSizeCombinatorAlias = Mapped<bytes::Fixed<3>, NamedSizeMapper>;

pub struct NamedSizeCombinator(pub NamedSizeCombinatorAlias);

impl View for NamedSizeCombinator {
    type V = SpecNamedSizeCombinator;
    open spec fn view(&self) -> Self::V { SpecNamedSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NamedSizeCombinator {
    type Type = NamedSize<'a>;
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
pub type NamedSizeCombinatorAlias = Mapped<bytes::Fixed<3>, NamedSizeMapper>;


pub open spec fn spec_named_size() -> SpecNamedSizeCombinator {
    SpecNamedSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: NamedSizeMapper,
    })
}

                
pub fn named_size<'a>() -> (o: NamedSizeCombinator)
    ensures o@ == spec_named_size(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NamedSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: NamedSizeMapper,
    });
    // assert({
    //     &&& combinator@ == spec_named_size()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_named_size<'a>(input: &'a [u8]) -> (res: PResult<<NamedSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_named_size().spec_parse(input@) == Some((n as int, v@)),
        spec_named_size().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_named_size().spec_parse(input@) is None,
        spec_named_size().spec_parse(input@) is None ==> res is Err,
{
    let combinator = named_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_named_size<'a>(v: <NamedSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_named_size().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_named_size().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_named_size().spec_serialize(v@))
        },
{
    let combinator = named_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn named_size_len<'a>(v: <NamedSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_named_size().wf(v@),
        spec_named_size().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_named_size().spec_serialize(v@).len(),
{
    let combinator = named_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecChoiceFormatSize {
    pub bytes: Seq<u8>,
}

pub type SpecChoiceFormatSizeInner = Seq<u8>;


impl SpecFrom<SpecChoiceFormatSize> for SpecChoiceFormatSizeInner {
    open spec fn spec_from(m: SpecChoiceFormatSize) -> SpecChoiceFormatSizeInner {
        m.bytes
    }
}

impl SpecFrom<SpecChoiceFormatSizeInner> for SpecChoiceFormatSize {
    open spec fn spec_from(m: SpecChoiceFormatSizeInner) -> SpecChoiceFormatSize {
        let bytes = m;
        SpecChoiceFormatSize { bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ChoiceFormatSize<'a> {
    pub bytes: &'a [u8],
}

impl View for ChoiceFormatSize<'_> {
    type V = SpecChoiceFormatSize;

    open spec fn view(&self) -> Self::V {
        SpecChoiceFormatSize {
            bytes: self.bytes@,
        }
    }
}
pub type ChoiceFormatSizeInner<'a> = &'a [u8];

pub type ChoiceFormatSizeInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a ChoiceFormatSize<'a>> for ChoiceFormatSizeInnerRef<'a> {
    fn ex_from(m: &'a ChoiceFormatSize) -> ChoiceFormatSizeInnerRef<'a> {
        &m.bytes
    }
}

impl<'a> From<ChoiceFormatSizeInner<'a>> for ChoiceFormatSize<'a> {
    fn ex_from(m: ChoiceFormatSizeInner) -> ChoiceFormatSize {
        let bytes = m;
        ChoiceFormatSize { bytes }
    }
}

pub struct ChoiceFormatSizeMapper;
impl View for ChoiceFormatSizeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceFormatSizeMapper {
    type Src = SpecChoiceFormatSizeInner;
    type Dst = SpecChoiceFormatSize;
}
impl SpecIsoProof for ChoiceFormatSizeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceFormatSizeMapper {
    type Src = ChoiceFormatSizeInner<'a>;
    type Dst = ChoiceFormatSize<'a>;
    type RefSrc = ChoiceFormatSizeInnerRef<'a>;
}

pub struct SpecChoiceFormatSizeCombinator(pub SpecChoiceFormatSizeCombinatorAlias);

impl SpecCombinator for SpecChoiceFormatSizeCombinator {
    type Type = SpecChoiceFormatSize;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceFormatSizeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceFormatSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceFormatSizeCombinatorAlias = Mapped<bytes::Fixed<2>, ChoiceFormatSizeMapper>;

pub struct ChoiceFormatSizeCombinator(pub ChoiceFormatSizeCombinatorAlias);

impl View for ChoiceFormatSizeCombinator {
    type V = SpecChoiceFormatSizeCombinator;
    open spec fn view(&self) -> Self::V { SpecChoiceFormatSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceFormatSizeCombinator {
    type Type = ChoiceFormatSize<'a>;
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
pub type ChoiceFormatSizeCombinatorAlias = Mapped<bytes::Fixed<2>, ChoiceFormatSizeMapper>;


pub open spec fn spec_choice_format_size() -> SpecChoiceFormatSizeCombinator {
    SpecChoiceFormatSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<2>,
        mapper: ChoiceFormatSizeMapper,
    })
}

                
pub fn choice_format_size<'a>() -> (o: ChoiceFormatSizeCombinator)
    ensures o@ == spec_choice_format_size(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceFormatSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<2>,
        mapper: ChoiceFormatSizeMapper,
    });
    // assert({
    //     &&& combinator@ == spec_choice_format_size()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_format_size<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceFormatSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_format_size().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_format_size().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_format_size().spec_parse(input@) is None,
        spec_choice_format_size().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_format_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_format_size<'a>(v: <ChoiceFormatSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_format_size().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_choice_format_size().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_choice_format_size().spec_serialize(v@))
        },
{
    let combinator = choice_format_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn choice_format_size_len<'a>(v: <ChoiceFormatSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_format_size().wf(v@),
        spec_choice_format_size().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_format_size().spec_serialize(v@).len(),
{
    let combinator = choice_format_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecHeaderBytes = SpecHeader;
pub type HeaderBytes = Header;
pub type HeaderBytesRef<'a> = &'a Header;


pub struct SpecHeaderBytesCombinator(pub SpecHeaderBytesCombinatorAlias);

impl SpecCombinator for SpecHeaderBytesCombinator {
    type Type = SpecHeaderBytes;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHeaderBytesCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecHeaderBytesCombinatorAlias::is_prefix_secure() }
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
pub type SpecHeaderBytesCombinatorAlias = AndThen<bytes::Variable, SpecHeaderCombinator>;

pub struct HeaderBytesCombinator(pub HeaderBytesCombinatorAlias);

impl View for HeaderBytesCombinator {
    type V = SpecHeaderBytesCombinator;
    open spec fn view(&self) -> Self::V { SpecHeaderBytesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HeaderBytesCombinator {
    type Type = HeaderBytes;
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
pub type HeaderBytesCombinatorAlias = AndThen<bytes::Variable, HeaderCombinator>;


pub open spec fn spec_header_bytes() -> SpecHeaderBytesCombinator {
    SpecHeaderBytesCombinator(AndThen(bytes::Variable(3), spec_header()))
}

                
pub fn header_bytes<'a>() -> (o: HeaderBytesCombinator)
    ensures o@ == spec_header_bytes(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = HeaderBytesCombinator(AndThen(bytes::Variable(3), header()));
    // assert({
    //     &&& combinator@ == spec_header_bytes()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_header_bytes<'a>(input: &'a [u8]) -> (res: PResult<<HeaderBytesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_header_bytes().spec_parse(input@) == Some((n as int, v@)),
        spec_header_bytes().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_header_bytes().spec_parse(input@) is None,
        spec_header_bytes().spec_parse(input@) is None ==> res is Err,
{
    let combinator = header_bytes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_header_bytes<'a>(v: <HeaderBytesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_header_bytes().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_header_bytes().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_header_bytes().spec_serialize(v@))
        },
{
    let combinator = header_bytes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn header_bytes_len<'a>(v: <HeaderBytesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_header_bytes().wf(v@),
        spec_header_bytes().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_header_bytes().spec_serialize(v@).len(),
{
    let combinator = header_bytes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMultiply {
    pub items: Seq<u8>,
}

pub type SpecMultiplyInner = Seq<u8>;


impl SpecFrom<SpecMultiply> for SpecMultiplyInner {
    open spec fn spec_from(m: SpecMultiply) -> SpecMultiplyInner {
        m.items
    }
}

impl SpecFrom<SpecMultiplyInner> for SpecMultiply {
    open spec fn spec_from(m: SpecMultiplyInner) -> SpecMultiply {
        let items = m;
        SpecMultiply { items }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Multiply<'a> {
    pub items: &'a [u8],
}

impl View for Multiply<'_> {
    type V = SpecMultiply;

    open spec fn view(&self) -> Self::V {
        SpecMultiply {
            items: self.items@,
        }
    }
}
pub type MultiplyInner<'a> = &'a [u8];

pub type MultiplyInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a Multiply<'a>> for MultiplyInnerRef<'a> {
    fn ex_from(m: &'a Multiply) -> MultiplyInnerRef<'a> {
        &m.items
    }
}

impl<'a> From<MultiplyInner<'a>> for Multiply<'a> {
    fn ex_from(m: MultiplyInner) -> Multiply {
        let items = m;
        Multiply { items }
    }
}

pub struct MultiplyMapper;
impl View for MultiplyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MultiplyMapper {
    type Src = SpecMultiplyInner;
    type Dst = SpecMultiply;
}
impl SpecIsoProof for MultiplyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MultiplyMapper {
    type Src = MultiplyInner<'a>;
    type Dst = Multiply<'a>;
    type RefSrc = MultiplyInnerRef<'a>;
}

pub struct SpecMultiplyCombinator(pub SpecMultiplyCombinatorAlias);

impl SpecCombinator for SpecMultiplyCombinator {
    type Type = SpecMultiply;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMultiplyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecMultiplyCombinatorAlias::is_prefix_secure() }
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
pub type SpecMultiplyCombinatorAlias = Mapped<bytes::Variable, MultiplyMapper>;

pub struct MultiplyCombinator(pub MultiplyCombinatorAlias);

impl View for MultiplyCombinator {
    type V = SpecMultiplyCombinator;
    open spec fn view(&self) -> Self::V { SpecMultiplyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MultiplyCombinator {
    type Type = Multiply<'a>;
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
pub type MultiplyCombinatorAlias = Mapped<bytes::Variable, MultiplyMapper>;


pub open spec fn spec_multiply(count: u16, size: u8) -> SpecMultiplyCombinator {
    SpecMultiplyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(count) * usize::spec_from(size))) as usize),
        mapper: MultiplyMapper,
    })
}

pub fn multiply<'a>(count: u16, size: u8) -> (o: MultiplyCombinator)
    requires
        ((size) == 1),

    ensures o@ == spec_multiply(count@, size@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MultiplyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(count) * usize::ex_from(size))) as usize),
        mapper: MultiplyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_multiply(count@, size@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_multiply<'a>(input: &'a [u8], count: u16, size: u8) -> (res: PResult<<MultiplyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((size) == 1),

    ensures
        res matches Ok((n, v)) ==> spec_multiply(count@, size@).spec_parse(input@) == Some((n as int, v@)),
        spec_multiply(count@, size@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_multiply(count@, size@).spec_parse(input@) is None,
        spec_multiply(count@, size@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = multiply( count, size );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_multiply<'a>(v: <MultiplyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, count: u16, size: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_multiply(count@, size@).wf(v@),
        ((size) == 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_multiply(count@, size@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_multiply(count@, size@).spec_serialize(v@))
        },
{
    let combinator = multiply( count, size );
    combinator.serialize(v, data, pos)
}

pub fn multiply_len<'a>(v: <MultiplyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, count: u16, size: u8) -> (serialize_len: usize)
    requires
        spec_multiply(count@, size@).wf(v@),
        spec_multiply(count@, size@).spec_serialize(v@).len() <= usize::MAX,
        ((size) == 1),

    ensures
        serialize_len == spec_multiply(count@, size@).spec_serialize(v@).len(),
{
    let combinator = multiply( count, size );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecChoiceArraysFoldedBody {
    Variant0(u8),
    Variant1(u16),
}

pub type SpecChoiceArraysFoldedBodyInner = Either<u8, u16>;

impl SpecFrom<SpecChoiceArraysFoldedBody> for SpecChoiceArraysFoldedBodyInner {
    open spec fn spec_from(m: SpecChoiceArraysFoldedBody) -> SpecChoiceArraysFoldedBodyInner {
        match m {
            SpecChoiceArraysFoldedBody::Variant0(m) => Either::Left(m),
            SpecChoiceArraysFoldedBody::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecChoiceArraysFoldedBodyInner> for SpecChoiceArraysFoldedBody {
    open spec fn spec_from(m: SpecChoiceArraysFoldedBodyInner) -> SpecChoiceArraysFoldedBody {
        match m {
            Either::Left(m) => SpecChoiceArraysFoldedBody::Variant0(m),
            Either::Right(m) => SpecChoiceArraysFoldedBody::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceArraysFoldedBody {
    Variant0(u8),
    Variant1(u16),
}

pub type ChoiceArraysFoldedBodyInner = Either<u8, u16>;

pub type ChoiceArraysFoldedBodyInnerRef<'a> = Either<&'a u8, &'a u16>;


impl View for ChoiceArraysFoldedBody {
    type V = SpecChoiceArraysFoldedBody;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceArraysFoldedBody::Variant0(m) => SpecChoiceArraysFoldedBody::Variant0(m@),
            ChoiceArraysFoldedBody::Variant1(m) => SpecChoiceArraysFoldedBody::Variant1(m@),
        }
    }
}


impl<'a> From<&'a ChoiceArraysFoldedBody> for ChoiceArraysFoldedBodyInnerRef<'a> {
    fn ex_from(m: &'a ChoiceArraysFoldedBody) -> ChoiceArraysFoldedBodyInnerRef<'a> {
        match m {
            ChoiceArraysFoldedBody::Variant0(m) => Either::Left(m),
            ChoiceArraysFoldedBody::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<ChoiceArraysFoldedBodyInner> for ChoiceArraysFoldedBody {
    fn ex_from(m: ChoiceArraysFoldedBodyInner) -> ChoiceArraysFoldedBody {
        match m {
            Either::Left(m) => ChoiceArraysFoldedBody::Variant0(m),
            Either::Right(m) => ChoiceArraysFoldedBody::Variant1(m),
        }
    }
    
}


pub struct ChoiceArraysFoldedBodyMapper;
impl View for ChoiceArraysFoldedBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceArraysFoldedBodyMapper {
    type Src = SpecChoiceArraysFoldedBodyInner;
    type Dst = SpecChoiceArraysFoldedBody;
}
impl SpecIsoProof for ChoiceArraysFoldedBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceArraysFoldedBodyMapper {
    type Src = ChoiceArraysFoldedBodyInner;
    type Dst = ChoiceArraysFoldedBody;
    type RefSrc = ChoiceArraysFoldedBodyInnerRef<'a>;
}

type SpecChoiceArraysFoldedBodyCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct SpecChoiceArraysFoldedBodyCombinator(pub SpecChoiceArraysFoldedBodyCombinatorAlias);

impl SpecCombinator for SpecChoiceArraysFoldedBodyCombinator {
    type Type = SpecChoiceArraysFoldedBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceArraysFoldedBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceArraysFoldedBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceArraysFoldedBodyCombinatorAlias = Mapped<SpecChoiceArraysFoldedBodyCombinatorAlias1, ChoiceArraysFoldedBodyMapper>;
type ChoiceArraysFoldedBodyCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct ChoiceArraysFoldedBodyCombinator1(pub ChoiceArraysFoldedBodyCombinatorAlias1);
impl View for ChoiceArraysFoldedBodyCombinator1 {
    type V = SpecChoiceArraysFoldedBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceArraysFoldedBodyCombinator1, ChoiceArraysFoldedBodyCombinatorAlias1);

pub struct ChoiceArraysFoldedBodyCombinator(pub ChoiceArraysFoldedBodyCombinatorAlias);

impl View for ChoiceArraysFoldedBodyCombinator {
    type V = SpecChoiceArraysFoldedBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecChoiceArraysFoldedBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceArraysFoldedBodyCombinator {
    type Type = ChoiceArraysFoldedBody;
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
pub type ChoiceArraysFoldedBodyCombinatorAlias = Mapped<ChoiceArraysFoldedBodyCombinator1, ChoiceArraysFoldedBodyMapper>;


pub open spec fn spec_choice_arrays_folded_body(tag: SpecChoiceTag) -> SpecChoiceArraysFoldedBodyCombinator {
    SpecChoiceArraysFoldedBodyCombinator(Mapped { inner: Choice(Cond { cond: tag == seq![0u8, 0u8], inner: U8 }, Cond { cond: tag == seq![1u8, 1u8], inner: U16Le }), mapper: ChoiceArraysFoldedBodyMapper })
}

pub fn choice_arrays_folded_body<'a>(tag: ChoiceTag) -> (o: ChoiceArraysFoldedBodyCombinator)

    ensures o@ == spec_choice_arrays_folded_body(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceArraysFoldedBodyCombinator(Mapped { inner: ChoiceArraysFoldedBodyCombinator1(Choice::new(Cond { cond: compare_slice(tag, [0u8, 0u8].as_slice()), inner: U8 }, Cond { cond: compare_slice(tag, [1u8, 1u8].as_slice()), inner: U16Le })), mapper: ChoiceArraysFoldedBodyMapper });
    // assert({
    //     &&& combinator@ == spec_choice_arrays_folded_body(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_arrays_folded_body<'a>(input: &'a [u8], tag: ChoiceTag) -> (res: PResult<<ChoiceArraysFoldedBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_choice_arrays_folded_body(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_choice_arrays_folded_body(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_arrays_folded_body(tag@).spec_parse(input@) is None,
        spec_choice_arrays_folded_body(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_arrays_folded_body( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_arrays_folded_body<'a>(v: <ChoiceArraysFoldedBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: ChoiceTag) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_arrays_folded_body(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_choice_arrays_folded_body(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_choice_arrays_folded_body(tag@).spec_serialize(v@))
        },
{
    let combinator = choice_arrays_folded_body( tag );
    combinator.serialize(v, data, pos)
}

pub fn choice_arrays_folded_body_len<'a>(v: <ChoiceArraysFoldedBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: ChoiceTag) -> (serialize_len: usize)
    requires
        spec_choice_arrays_folded_body(tag@).wf(v@),
        spec_choice_arrays_folded_body(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_choice_arrays_folded_body(tag@).spec_serialize(v@).len(),
{
    let combinator = choice_arrays_folded_body( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecChoiceArraysFolded {
    pub tag: SpecChoiceTag,
    pub body: SpecChoiceArraysFoldedBody,
}

pub type SpecChoiceArraysFoldedInner = (SpecChoiceTag, SpecChoiceArraysFoldedBody);


impl SpecFrom<SpecChoiceArraysFolded> for SpecChoiceArraysFoldedInner {
    open spec fn spec_from(m: SpecChoiceArraysFolded) -> SpecChoiceArraysFoldedInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecChoiceArraysFoldedInner> for SpecChoiceArraysFolded {
    open spec fn spec_from(m: SpecChoiceArraysFoldedInner) -> SpecChoiceArraysFolded {
        let (tag, body) = m;
        SpecChoiceArraysFolded { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ChoiceArraysFolded<'a> {
    pub tag: ChoiceTag<'a>,
    pub body: ChoiceArraysFoldedBody,
}

impl View for ChoiceArraysFolded<'_> {
    type V = SpecChoiceArraysFolded;

    open spec fn view(&self) -> Self::V {
        SpecChoiceArraysFolded {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type ChoiceArraysFoldedInner<'a> = (ChoiceTag<'a>, ChoiceArraysFoldedBody);

pub type ChoiceArraysFoldedInnerRef<'a> = (&'a ChoiceTag<'a>, &'a ChoiceArraysFoldedBody);
impl<'a> From<&'a ChoiceArraysFolded<'a>> for ChoiceArraysFoldedInnerRef<'a> {
    fn ex_from(m: &'a ChoiceArraysFolded) -> ChoiceArraysFoldedInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl<'a> From<ChoiceArraysFoldedInner<'a>> for ChoiceArraysFolded<'a> {
    fn ex_from(m: ChoiceArraysFoldedInner) -> ChoiceArraysFolded {
        let (tag, body) = m;
        ChoiceArraysFolded { tag, body }
    }
}

pub struct ChoiceArraysFoldedMapper;
impl View for ChoiceArraysFoldedMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceArraysFoldedMapper {
    type Src = SpecChoiceArraysFoldedInner;
    type Dst = SpecChoiceArraysFolded;
}
impl SpecIsoProof for ChoiceArraysFoldedMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceArraysFoldedMapper {
    type Src = ChoiceArraysFoldedInner<'a>;
    type Dst = ChoiceArraysFolded<'a>;
    type RefSrc = ChoiceArraysFoldedInnerRef<'a>;
}

pub struct SpecChoiceArraysFoldedCombinator(pub SpecChoiceArraysFoldedCombinatorAlias);

impl SpecCombinator for SpecChoiceArraysFoldedCombinator {
    type Type = SpecChoiceArraysFolded;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceArraysFoldedCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceArraysFoldedCombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceArraysFoldedCombinatorAlias = Mapped<SpecPair<SpecChoiceTagCombinator, SpecChoiceArraysFoldedBodyCombinator>, ChoiceArraysFoldedMapper>;

pub struct ChoiceArraysFoldedCombinator(pub ChoiceArraysFoldedCombinatorAlias);

impl View for ChoiceArraysFoldedCombinator {
    type V = SpecChoiceArraysFoldedCombinator;
    open spec fn view(&self) -> Self::V { SpecChoiceArraysFoldedCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceArraysFoldedCombinator {
    type Type = ChoiceArraysFolded<'a>;
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
pub type ChoiceArraysFoldedCombinatorAlias = Mapped<Pair<ChoiceTagCombinator, ChoiceArraysFoldedBodyCombinator, ChoiceArraysFoldedCont0>, ChoiceArraysFoldedMapper>;


pub open spec fn spec_choice_arrays_folded() -> SpecChoiceArraysFoldedCombinator {
    SpecChoiceArraysFoldedCombinator(
    Mapped {
        inner: Pair::spec_new(spec_choice_tag(), |deps| spec_choice_arrays_folded_cont0(deps)),
        mapper: ChoiceArraysFoldedMapper,
    })
}

pub open spec fn spec_choice_arrays_folded_cont0(deps: SpecChoiceTag) -> SpecChoiceArraysFoldedBodyCombinator {
    let tag = deps;
    spec_choice_arrays_folded_body(tag)
}

impl View for ChoiceArraysFoldedCont0 {
    type V = spec_fn(SpecChoiceTag) -> SpecChoiceArraysFoldedBodyCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecChoiceTag| {
            spec_choice_arrays_folded_cont0(deps)
        }
    }
}

                
pub fn choice_arrays_folded<'a>() -> (o: ChoiceArraysFoldedCombinator)
    ensures o@ == spec_choice_arrays_folded(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceArraysFoldedCombinator(
    Mapped {
        inner: Pair::new(choice_tag(), ChoiceArraysFoldedCont0),
        mapper: ChoiceArraysFoldedMapper,
    });
    // assert({
    //     &&& combinator@ == spec_choice_arrays_folded()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_arrays_folded<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceArraysFoldedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_arrays_folded().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_arrays_folded().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_arrays_folded().spec_parse(input@) is None,
        spec_choice_arrays_folded().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_arrays_folded();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_arrays_folded<'a>(v: <ChoiceArraysFoldedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_arrays_folded().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_choice_arrays_folded().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_choice_arrays_folded().spec_serialize(v@))
        },
{
    let combinator = choice_arrays_folded();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn choice_arrays_folded_len<'a>(v: <ChoiceArraysFoldedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_arrays_folded().wf(v@),
        spec_choice_arrays_folded().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_arrays_folded().spec_serialize(v@).len(),
{
    let combinator = choice_arrays_folded();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct ChoiceArraysFoldedCont0;
type ChoiceArraysFoldedCont0Type<'a, 'b> = &'b ChoiceTag<'a>;
type ChoiceArraysFoldedCont0SType<'a, 'x> = &'x ChoiceTag<'a>;
type ChoiceArraysFoldedCont0Input<'a, 'b, 'x> = POrSType<ChoiceArraysFoldedCont0Type<'a, 'b>, ChoiceArraysFoldedCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ChoiceArraysFoldedCont0Input<'a, 'b, 'x>> for ChoiceArraysFoldedCont0 {
    type Output = ChoiceArraysFoldedBodyCombinator;

    open spec fn requires(&self, deps: ChoiceArraysFoldedCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_choice_tag()).wf(deps@)
        }

    open spec fn ensures(&self, deps: ChoiceArraysFoldedCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_choice_arrays_folded_cont0(deps@)
    }

    fn apply(&self, deps: ChoiceArraysFoldedCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                choice_arrays_folded_body(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                choice_arrays_folded_body(tag)
            }
        }
    }
}
                

pub struct SpecParenExpr {
    pub data: Seq<u8>,
}

pub type SpecParenExprInner = Seq<u8>;


impl SpecFrom<SpecParenExpr> for SpecParenExprInner {
    open spec fn spec_from(m: SpecParenExpr) -> SpecParenExprInner {
        m.data
    }
}

impl SpecFrom<SpecParenExprInner> for SpecParenExpr {
    open spec fn spec_from(m: SpecParenExprInner) -> SpecParenExpr {
        let data = m;
        SpecParenExpr { data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParenExpr<'a> {
    pub data: &'a [u8],
}

impl View for ParenExpr<'_> {
    type V = SpecParenExpr;

    open spec fn view(&self) -> Self::V {
        SpecParenExpr {
            data: self.data@,
        }
    }
}
pub type ParenExprInner<'a> = &'a [u8];

pub type ParenExprInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a ParenExpr<'a>> for ParenExprInnerRef<'a> {
    fn ex_from(m: &'a ParenExpr) -> ParenExprInnerRef<'a> {
        &m.data
    }
}

impl<'a> From<ParenExprInner<'a>> for ParenExpr<'a> {
    fn ex_from(m: ParenExprInner) -> ParenExpr {
        let data = m;
        ParenExpr { data }
    }
}

pub struct ParenExprMapper;
impl View for ParenExprMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParenExprMapper {
    type Src = SpecParenExprInner;
    type Dst = SpecParenExpr;
}
impl SpecIsoProof for ParenExprMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParenExprMapper {
    type Src = ParenExprInner<'a>;
    type Dst = ParenExpr<'a>;
    type RefSrc = ParenExprInnerRef<'a>;
}

pub struct SpecParenExprCombinator(pub SpecParenExprCombinatorAlias);

impl SpecCombinator for SpecParenExprCombinator {
    type Type = SpecParenExpr;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParenExprCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecParenExprCombinatorAlias::is_prefix_secure() }
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
pub type SpecParenExprCombinatorAlias = Mapped<bytes::Variable, ParenExprMapper>;

pub struct ParenExprCombinator(pub ParenExprCombinatorAlias);

impl View for ParenExprCombinator {
    type V = SpecParenExprCombinator;
    open spec fn view(&self) -> Self::V { SpecParenExprCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParenExprCombinator {
    type Type = ParenExpr<'a>;
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
pub type ParenExprCombinatorAlias = Mapped<bytes::Variable, ParenExprMapper>;


pub open spec fn spec_paren_expr(a: u16, b: u8, c: u8) -> SpecParenExprCombinator {
    SpecParenExprCombinator(
    Mapped {
        inner: bytes::Variable((((usize::spec_from(a) - usize::spec_from(b)) * usize::spec_from(c))) as usize),
        mapper: ParenExprMapper,
    })
}

pub fn paren_expr<'a>(a: u16, b: u8, c: u8) -> (o: ParenExprCombinator)
    requires
        ((a) >= 255 && (a) <= 65535),
        ((b) >= 0 && (b) <= 255),
        ((c) == 1),

    ensures o@ == spec_paren_expr(a@, b@, c@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ParenExprCombinator(
    Mapped {
        inner: bytes::Variable((((usize::ex_from(a) - usize::ex_from(b)) * usize::ex_from(c))) as usize),
        mapper: ParenExprMapper,
    });
    // assert({
    //     &&& combinator@ == spec_paren_expr(a@, b@, c@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_paren_expr<'a>(input: &'a [u8], a: u16, b: u8, c: u8) -> (res: PResult<<ParenExprCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((a) >= 255 && (a) <= 65535),
        ((b) >= 0 && (b) <= 255),
        ((c) == 1),

    ensures
        res matches Ok((n, v)) ==> spec_paren_expr(a@, b@, c@).spec_parse(input@) == Some((n as int, v@)),
        spec_paren_expr(a@, b@, c@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_paren_expr(a@, b@, c@).spec_parse(input@) is None,
        spec_paren_expr(a@, b@, c@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = paren_expr( a, b, c );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_paren_expr<'a>(v: <ParenExprCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, a: u16, b: u8, c: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_paren_expr(a@, b@, c@).wf(v@),
        ((a) >= 255 && (a) <= 65535),
        ((b) >= 0 && (b) <= 255),
        ((c) == 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_paren_expr(a@, b@, c@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_paren_expr(a@, b@, c@).spec_serialize(v@))
        },
{
    let combinator = paren_expr( a, b, c );
    combinator.serialize(v, data, pos)
}

pub fn paren_expr_len<'a>(v: <ParenExprCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, a: u16, b: u8, c: u8) -> (serialize_len: usize)
    requires
        spec_paren_expr(a@, b@, c@).wf(v@),
        spec_paren_expr(a@, b@, c@).spec_serialize(v@).len() <= usize::MAX,
        ((a) >= 255 && (a) <= 65535),
        ((b) >= 0 && (b) <= 255),
        ((c) == 1),

    ensures
        serialize_len == spec_paren_expr(a@, b@, c@).spec_serialize(v@).len(),
{
    let combinator = paren_expr( a, b, c );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecReinterpretSize {
    pub bytes: Seq<u8>,
}

pub type SpecReinterpretSizeInner = Seq<u8>;


impl SpecFrom<SpecReinterpretSize> for SpecReinterpretSizeInner {
    open spec fn spec_from(m: SpecReinterpretSize) -> SpecReinterpretSizeInner {
        m.bytes
    }
}

impl SpecFrom<SpecReinterpretSizeInner> for SpecReinterpretSize {
    open spec fn spec_from(m: SpecReinterpretSizeInner) -> SpecReinterpretSize {
        let bytes = m;
        SpecReinterpretSize { bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ReinterpretSize<'a> {
    pub bytes: &'a [u8],
}

impl View for ReinterpretSize<'_> {
    type V = SpecReinterpretSize;

    open spec fn view(&self) -> Self::V {
        SpecReinterpretSize {
            bytes: self.bytes@,
        }
    }
}
pub type ReinterpretSizeInner<'a> = &'a [u8];

pub type ReinterpretSizeInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a ReinterpretSize<'a>> for ReinterpretSizeInnerRef<'a> {
    fn ex_from(m: &'a ReinterpretSize) -> ReinterpretSizeInnerRef<'a> {
        &m.bytes
    }
}

impl<'a> From<ReinterpretSizeInner<'a>> for ReinterpretSize<'a> {
    fn ex_from(m: ReinterpretSizeInner) -> ReinterpretSize {
        let bytes = m;
        ReinterpretSize { bytes }
    }
}

pub struct ReinterpretSizeMapper;
impl View for ReinterpretSizeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ReinterpretSizeMapper {
    type Src = SpecReinterpretSizeInner;
    type Dst = SpecReinterpretSize;
}
impl SpecIsoProof for ReinterpretSizeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ReinterpretSizeMapper {
    type Src = ReinterpretSizeInner<'a>;
    type Dst = ReinterpretSize<'a>;
    type RefSrc = ReinterpretSizeInnerRef<'a>;
}

pub struct SpecReinterpretSizeCombinator(pub SpecReinterpretSizeCombinatorAlias);

impl SpecCombinator for SpecReinterpretSizeCombinator {
    type Type = SpecReinterpretSize;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecReinterpretSizeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecReinterpretSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecReinterpretSizeCombinatorAlias = Mapped<bytes::Fixed<3>, ReinterpretSizeMapper>;

pub struct ReinterpretSizeCombinator(pub ReinterpretSizeCombinatorAlias);

impl View for ReinterpretSizeCombinator {
    type V = SpecReinterpretSizeCombinator;
    open spec fn view(&self) -> Self::V { SpecReinterpretSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ReinterpretSizeCombinator {
    type Type = ReinterpretSize<'a>;
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
pub type ReinterpretSizeCombinatorAlias = Mapped<bytes::Fixed<3>, ReinterpretSizeMapper>;


pub open spec fn spec_reinterpret_size() -> SpecReinterpretSizeCombinator {
    SpecReinterpretSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: ReinterpretSizeMapper,
    })
}

                
pub fn reinterpret_size<'a>() -> (o: ReinterpretSizeCombinator)
    ensures o@ == spec_reinterpret_size(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ReinterpretSizeCombinator(
    Mapped {
        inner: bytes::Fixed::<3>,
        mapper: ReinterpretSizeMapper,
    });
    // assert({
    //     &&& combinator@ == spec_reinterpret_size()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_reinterpret_size<'a>(input: &'a [u8]) -> (res: PResult<<ReinterpretSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_reinterpret_size().spec_parse(input@) == Some((n as int, v@)),
        spec_reinterpret_size().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_reinterpret_size().spec_parse(input@) is None,
        spec_reinterpret_size().spec_parse(input@) is None ==> res is Err,
{
    let combinator = reinterpret_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_reinterpret_size<'a>(v: <ReinterpretSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_reinterpret_size().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_reinterpret_size().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_reinterpret_size().spec_serialize(v@))
        },
{
    let combinator = reinterpret_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn reinterpret_size_len<'a>(v: <ReinterpretSizeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_reinterpret_size().wf(v@),
        spec_reinterpret_size().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_reinterpret_size().spec_serialize(v@).len(),
{
    let combinator = reinterpret_size();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecPrimitiveSizes {
    pub byte: Seq<u8>,
    pub word: Seq<u8>,
}

pub type SpecPrimitiveSizesInner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecPrimitiveSizes> for SpecPrimitiveSizesInner {
    open spec fn spec_from(m: SpecPrimitiveSizes) -> SpecPrimitiveSizesInner {
        (m.byte, m.word)
    }
}

impl SpecFrom<SpecPrimitiveSizesInner> for SpecPrimitiveSizes {
    open spec fn spec_from(m: SpecPrimitiveSizesInner) -> SpecPrimitiveSizes {
        let (byte, word) = m;
        SpecPrimitiveSizes { byte, word }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PrimitiveSizes<'a> {
    pub byte: &'a [u8],
    pub word: &'a [u8],
}

impl View for PrimitiveSizes<'_> {
    type V = SpecPrimitiveSizes;

    open spec fn view(&self) -> Self::V {
        SpecPrimitiveSizes {
            byte: self.byte@,
            word: self.word@,
        }
    }
}
pub type PrimitiveSizesInner<'a> = (&'a [u8], &'a [u8]);

pub type PrimitiveSizesInnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a PrimitiveSizes<'a>> for PrimitiveSizesInnerRef<'a> {
    fn ex_from(m: &'a PrimitiveSizes) -> PrimitiveSizesInnerRef<'a> {
        (&m.byte, &m.word)
    }
}

impl<'a> From<PrimitiveSizesInner<'a>> for PrimitiveSizes<'a> {
    fn ex_from(m: PrimitiveSizesInner) -> PrimitiveSizes {
        let (byte, word) = m;
        PrimitiveSizes { byte, word }
    }
}

pub struct PrimitiveSizesMapper;
impl View for PrimitiveSizesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PrimitiveSizesMapper {
    type Src = SpecPrimitiveSizesInner;
    type Dst = SpecPrimitiveSizes;
}
impl SpecIsoProof for PrimitiveSizesMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PrimitiveSizesMapper {
    type Src = PrimitiveSizesInner<'a>;
    type Dst = PrimitiveSizes<'a>;
    type RefSrc = PrimitiveSizesInnerRef<'a>;
}
type SpecPrimitiveSizesCombinatorAlias1 = (bytes::Fixed<1>, bytes::Fixed<2>);
pub struct SpecPrimitiveSizesCombinator(pub SpecPrimitiveSizesCombinatorAlias);

impl SpecCombinator for SpecPrimitiveSizesCombinator {
    type Type = SpecPrimitiveSizes;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPrimitiveSizesCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPrimitiveSizesCombinatorAlias::is_prefix_secure() }
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
pub type SpecPrimitiveSizesCombinatorAlias = Mapped<SpecPrimitiveSizesCombinatorAlias1, PrimitiveSizesMapper>;
type PrimitiveSizesCombinatorAlias1 = (bytes::Fixed<1>, bytes::Fixed<2>);
pub struct PrimitiveSizesCombinator1(pub PrimitiveSizesCombinatorAlias1);
impl View for PrimitiveSizesCombinator1 {
    type V = SpecPrimitiveSizesCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PrimitiveSizesCombinator1, PrimitiveSizesCombinatorAlias1);

pub struct PrimitiveSizesCombinator(pub PrimitiveSizesCombinatorAlias);

impl View for PrimitiveSizesCombinator {
    type V = SpecPrimitiveSizesCombinator;
    open spec fn view(&self) -> Self::V { SpecPrimitiveSizesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PrimitiveSizesCombinator {
    type Type = PrimitiveSizes<'a>;
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
pub type PrimitiveSizesCombinatorAlias = Mapped<PrimitiveSizesCombinator1, PrimitiveSizesMapper>;


pub open spec fn spec_primitive_sizes() -> SpecPrimitiveSizesCombinator {
    SpecPrimitiveSizesCombinator(
    Mapped {
        inner: (bytes::Fixed::<1>, bytes::Fixed::<2>),
        mapper: PrimitiveSizesMapper,
    })
}

                
pub fn primitive_sizes<'a>() -> (o: PrimitiveSizesCombinator)
    ensures o@ == spec_primitive_sizes(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PrimitiveSizesCombinator(
    Mapped {
        inner: PrimitiveSizesCombinator1((bytes::Fixed::<1>, bytes::Fixed::<2>)),
        mapper: PrimitiveSizesMapper,
    });
    // assert({
    //     &&& combinator@ == spec_primitive_sizes()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_primitive_sizes<'a>(input: &'a [u8]) -> (res: PResult<<PrimitiveSizesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_primitive_sizes().spec_parse(input@) == Some((n as int, v@)),
        spec_primitive_sizes().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_primitive_sizes().spec_parse(input@) is None,
        spec_primitive_sizes().spec_parse(input@) is None ==> res is Err,
{
    let combinator = primitive_sizes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_primitive_sizes<'a>(v: <PrimitiveSizesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_primitive_sizes().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_primitive_sizes().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_primitive_sizes().spec_serialize(v@))
        },
{
    let combinator = primitive_sizes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn primitive_sizes_len<'a>(v: <PrimitiveSizesCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_primitive_sizes().wf(v@),
        spec_primitive_sizes().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_primitive_sizes().spec_serialize(v@).len(),
{
    let combinator = primitive_sizes();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
