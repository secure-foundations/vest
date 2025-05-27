#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vstd::prelude::*;
use vest::regular::modifier::*;
use vest::regular::bytes;
use vest::regular::variant::*;
use vest::regular::sequence::*;
use vest::regular::repetition::*;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::utils::*;
use vest::properties::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::leb128::*;
verus!{
pub type SpecA = Seq<u8>;
pub type A<'a> = &'a [u8];
pub type ARef<'a> = &'a &'a [u8];

pub const A_0_FRONT_CONST: u8 = 1;

pub const A_1_FRONT_CONST: u8 = 2;

pub const A_0_BACK_CONST: u8 = 3;

pub struct SpecACombinator(SpecACombinatorAlias);

impl SpecCombinator for SpecACombinator {
    type Type = SpecA;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecACombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecACombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecACombinatorAlias = Terminated<Preceded<Tag<U8, u8>, Preceded<Tag<U8, u8>, bytes::Fixed<10>>>, Tag<U8, u8>>;



pub struct ACombinator(ACombinatorAlias);

impl View for ACombinator {
    type V = SpecACombinator;
    closed spec fn view(&self) -> Self::V { SpecACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ACombinator {
    type Type = A<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ACombinatorAlias = Terminated<Preceded<Tag<U8, u8>, Preceded<Tag<U8, u8>, bytes::Fixed<10>>>, Tag<U8, u8>>;


pub closed spec fn spec_a() -> SpecACombinator {
    SpecACombinator(Terminated(Preceded(Tag::spec_new(U8, A_0_FRONT_CONST), Preceded(Tag::spec_new(U8, A_1_FRONT_CONST), bytes::Fixed::<10>)), Tag::spec_new(U8, A_0_BACK_CONST)))
}

                
pub fn a() -> (o: ACombinator)
    ensures o@ == spec_a(),
{
    ACombinator(Terminated(Preceded(Tag::new(U8, A_0_FRONT_CONST), Preceded(Tag::new(U8, A_1_FRONT_CONST), bytes::Fixed::<10>)), Tag::new(U8, A_0_BACK_CONST)))
}

                

pub struct SpecB {
    pub x: Seq<u8>,
    pub y: SpecA,
}

pub type SpecBInner = (Seq<u8>, SpecA);


impl SpecFrom<SpecB> for SpecBInner {
    open spec fn spec_from(m: SpecB) -> SpecBInner {
        (m.x, m.y)
    }
}

impl SpecFrom<SpecBInner> for SpecB {
    open spec fn spec_from(m: SpecBInner) -> SpecB {
        let (x, y) = m;
        SpecB { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct B<'a> {
    pub x: &'a [u8],
    pub y: A<'a>,
}

impl View for B<'_> {
    type V = SpecB;

    open spec fn view(&self) -> Self::V {
        SpecB {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type BInner<'a> = (&'a [u8], A<'a>);

pub type BInnerRef<'a> = (&'a &'a [u8], &'a A<'a>);
impl<'a> From<&'a B<'a>> for BInnerRef<'a> {
    fn ex_from(m: &'a B) -> BInnerRef<'a> {
        (&m.x, &m.y)
    }
}

impl<'a> From<BInner<'a>> for B<'a> {
    fn ex_from(m: BInner) -> B {
        let (x, y) = m;
        B { x, y }
    }
}

pub struct BMapper;
impl View for BMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BMapper {
    type Src = SpecBInner;
    type Dst = SpecB;
}
impl SpecIsoProof for BMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for BMapper {
    type Src = BInner<'a>;
    type Dst = B<'a>;
    type RefSrc = BInnerRef<'a>;
}
pub spec const SPEC_BY_0_FRONT_CONST: Seq<u8> = seq![1, 2, 3];
pub const BY_0_BACK_CONST: u8 = 1;

pub struct SpecBCombinator(SpecBCombinatorAlias);

impl SpecCombinator for SpecBCombinator {
    type Type = SpecB;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecBCombinatorAlias = Mapped<(bytes::Fixed<10>, Terminated<Preceded<Tag<bytes::Fixed<3>, Seq<u8>>, SpecACombinator>, Tag<U8, u8>>), BMapper>;
pub exec static BY_0_FRONT_CONST: [u8; 3]
    ensures BY_0_FRONT_CONST@ == SPEC_BY_0_FRONT_CONST,
{
    let arr: [u8; 3] = [1, 2, 3];
    assert(arr@ == SPEC_BY_0_FRONT_CONST);
    arr
}


pub struct BCombinator(BCombinatorAlias);

impl View for BCombinator {
    type V = SpecBCombinator;
    closed spec fn view(&self) -> Self::V { SpecBCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for BCombinator {
    type Type = B<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type BCombinatorAlias = Mapped<(bytes::Fixed<10>, Terminated<Preceded<Tag<bytes::Fixed<3>, [u8; 3]>, ACombinator>, Tag<U8, u8>>), BMapper>;


pub closed spec fn spec_b() -> SpecBCombinator {
    SpecBCombinator(
    Mapped {
        inner: (bytes::Fixed::<10>, Terminated(Preceded(Tag::spec_new(bytes::Fixed::<3>, SPEC_BY_0_FRONT_CONST), spec_a()), Tag::spec_new(U8, BY_0_BACK_CONST))),
        mapper: BMapper,
    })
}

                
pub fn b() -> (o: BCombinator)
    ensures o@ == spec_b(),
{
    BCombinator(
    Mapped {
        inner: (bytes::Fixed::<10>, Terminated(Preceded(Tag::new(bytes::Fixed::<3>, BY_0_FRONT_CONST), a()), Tag::new(U8, BY_0_BACK_CONST))),
        mapper: BMapper,
    })
}

                

pub struct SpecMsg {
    pub a: u8,
    pub b: Seq<u8>,
}

pub type SpecMsgInner = (u8, Seq<u8>);


impl SpecFrom<SpecMsg> for SpecMsgInner {
    open spec fn spec_from(m: SpecMsg) -> SpecMsgInner {
        (m.a, m.b)
    }
}

impl SpecFrom<SpecMsgInner> for SpecMsg {
    open spec fn spec_from(m: SpecMsgInner) -> SpecMsg {
        let (a, b) = m;
        SpecMsg { a, b }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg<'a> {
    pub a: u8,
    pub b: &'a [u8],
}

impl View for Msg<'_> {
    type V = SpecMsg;

    open spec fn view(&self) -> Self::V {
        SpecMsg {
            a: self.a@,
            b: self.b@,
        }
    }
}
pub type MsgInner<'a> = (u8, &'a [u8]);

pub type MsgInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a Msg<'a>> for MsgInnerRef<'a> {
    fn ex_from(m: &'a Msg) -> MsgInnerRef<'a> {
        (&m.a, &m.b)
    }
}

impl<'a> From<MsgInner<'a>> for Msg<'a> {
    fn ex_from(m: MsgInner) -> Msg {
        let (a, b) = m;
        Msg { a, b }
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
pub const MSGA_CONST: u8 = 1;
pub spec const SPEC_MSGB_CONST: Seq<u8> = seq![1, 2];
pub struct SpecMsgCombinator(SpecMsgCombinatorAlias);

impl SpecCombinator for SpecMsgCombinator {
    type Type = SpecMsg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecMsgCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, Refined<bytes::Fixed<2>, TagPred<Seq<u8>>>), MsgMapper>;
pub exec static MSGB_CONST: [u8; 2]
    ensures MSGB_CONST@ == SPEC_MSGB_CONST,
{
    let arr: [u8; 2] = [1, 2];
    assert(arr@ == SPEC_MSGB_CONST);
    arr
}

pub struct MsgCombinator(MsgCombinatorAlias);

impl View for MsgCombinator {
    type V = SpecMsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgCombinator {
    type Type = Msg<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MsgCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, Refined<bytes::Fixed<2>, TagPred<[u8; 2]>>), MsgMapper>;


pub closed spec fn spec_msg() -> SpecMsgCombinator {
    SpecMsgCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(MSGA_CONST) }, Refined { inner: bytes::Fixed::<2>, predicate: TagPred(SPEC_MSGB_CONST) }),
        mapper: MsgMapper,
    })
}

                
pub fn msg() -> (o: MsgCombinator)
    ensures o@ == spec_msg(),
{
    MsgCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(MSGA_CONST) }, Refined { inner: bytes::Fixed::<2>, predicate: TagPred(MSGB_CONST) }),
        mapper: MsgMapper,
    })
}

                
pub type SpecOptmsg = Option<SpecMsg>;
pub type Optmsg<'a> = Optional<Msg<'a>>;
pub type OptmsgRef<'a> = &'a Optional<Msg<'a>>;


pub struct SpecOptmsgCombinator(SpecOptmsgCombinatorAlias);

impl SpecCombinator for SpecOptmsgCombinator {
    type Type = SpecOptmsg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOptmsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOptmsgCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
    proof fn lemma_parse_length(&self, s: Seq<u8>) 
    { self.0.lemma_parse_length(s) }
    closed spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecOptmsgCombinatorAlias = Opt<SpecMsgCombinator>;

pub struct OptmsgCombinator(OptmsgCombinatorAlias);

impl View for OptmsgCombinator {
    type V = SpecOptmsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecOptmsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OptmsgCombinator {
    type Type = Optmsg<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OptmsgCombinatorAlias = Opt<MsgCombinator>;


pub closed spec fn spec_optmsg() -> SpecOptmsgCombinator {
    SpecOptmsgCombinator(Opt(spec_msg()))
}

                
pub fn optmsg() -> (o: OptmsgCombinator)
    ensures o@ == spec_optmsg(),
{
    OptmsgCombinator(Opt::new(msg()))
}

                

}
