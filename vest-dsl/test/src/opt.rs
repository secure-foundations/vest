#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vstd::prelude::*;
use vest::properties::*;
use vest::utils::*;
use vest::regular::map::*;
use vest::regular::tag::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::uints::*;
use vest::regular::tail::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::depend::*;
use vest::regular::and_then::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::repeat_n::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
verus!{
pub type SpecOptmsg = Option<SpecMsg>;
pub type Optmsg<'a> = Optional<Msg<'a>>;


pub struct SpecOptmsgCombinator(SpecOptmsgCombinatorAlias);

impl SpecCombinator for SpecOptmsgCombinator {
    type Type = SpecOptmsg;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
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

pub struct OptmsgCombinator<'a>(OptmsgCombinatorAlias<'a>);

impl<'a> View for OptmsgCombinator<'a> {
    type V = SpecOptmsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecOptmsgCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OptmsgCombinator<'a> {
    type Type = Optmsg<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OptmsgCombinatorAlias<'a> = Opt<MsgCombinator<'a>>;


pub closed spec fn spec_optmsg() -> SpecOptmsgCombinator {
    SpecOptmsgCombinator(Opt(spec_msg()))
}

                
pub fn optmsg<'a>() -> (o: OptmsgCombinator<'a>)
    ensures o@ == spec_optmsg(),
{
    OptmsgCombinator(Opt::new(msg()))
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
impl<'a> From<Msg<'a>> for MsgInner<'a> {
    fn ex_from(m: Msg) -> MsgInner {
        (m.a, m.b)
    }
}
impl<'a> From<MsgInner<'a>> for Msg<'a> {
    fn ex_from(m: MsgInner) -> Msg {
        let (a, b) = m;
        Msg { a, b }
    }
}

pub struct MsgMapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgMapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgMapper(PhantomData)
    }
}
impl View for MsgMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgMapper<'_> {
    type Src = SpecMsgInner;
    type Dst = SpecMsg;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgMapper<'a> {
    type Src = MsgInner<'a>;
    type Dst = Msg<'a>;
}
pub const MSG_A: u8 = 1;
pub spec const SPEC_MSG_B: Seq<u8> = seq![1, 2];
pub struct SpecMsgCombinator(SpecMsgCombinatorAlias);

impl SpecCombinator for SpecMsgCombinator {
    type Type = SpecMsg;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
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
pub type SpecMsgCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, Refined<BytesN<2>, BytesPredicate8108826520007174880<'static>>), MsgMapper<'static>>;
pub exec const MSG_B: [u8; 2]
    ensures MSG_B@ == SPEC_MSG_B,
{
    let arr: [u8; 2] = [1, 2];
    assert(arr@ == SPEC_MSG_B);
    arr
}

pub struct BytesPredicate8108826520007174880<'a>(PhantomData<&'a ()>);
impl<'a> BytesPredicate8108826520007174880<'a> {
    pub closed spec fn spec_new() -> Self {
        BytesPredicate8108826520007174880(PhantomData)
    }
    pub fn new() -> Self {
        BytesPredicate8108826520007174880(PhantomData)
    }
}
impl View for BytesPredicate8108826520007174880<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecPred for BytesPredicate8108826520007174880<'_> {
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        i == &SPEC_MSG_B
    }
}
impl<'a> Pred for BytesPredicate8108826520007174880<'a> {
    type Input = &'a [u8];

    fn apply(&self, i: &Self::Input) -> bool {
        compare_slice(i, MSG_B.as_slice())
    }
}

pub struct MsgCombinator<'a>(MsgCombinatorAlias<'a>);

impl<'a> View for MsgCombinator<'a> {
    type V = SpecMsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgCombinator<'a> {
    type Type = Msg<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MsgCombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, Refined<BytesN<2>, BytesPredicate8108826520007174880<'a>>), MsgMapper<'a>>;


pub closed spec fn spec_msg() -> SpecMsgCombinator {
    SpecMsgCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(MSG_A) }, Refined { inner: BytesN::<2>, predicate: BytesPredicate8108826520007174880::spec_new() }),
        mapper: MsgMapper::spec_new(),
    })
}

                
pub fn msg<'a>() -> (o: MsgCombinator<'a>)
    ensures o@ == spec_msg(),
{
    MsgCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(MSG_A) }, Refined { inner: BytesN::<2>, predicate: BytesPredicate8108826520007174880::new() }),
        mapper: MsgMapper::new(),
    })
}

                

}
