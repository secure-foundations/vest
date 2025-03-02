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
pub type SpecContentType = u8;
pub type ContentType = u8;


pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type Type = SpecContentType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecContentTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecContentTypeCombinatorAlias = U8;

pub struct ContentTypeCombinator(ContentTypeCombinatorAlias);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecContentTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ContentTypeCombinator {
    type Type = ContentType;
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
pub type ContentTypeCombinatorAlias = U8;


pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(U8)
}

                
pub fn content_type() -> (o: ContentTypeCombinator)
    ensures o@ == spec_content_type(),
{
    ContentTypeCombinator(U8)
}

                
pub type SpecContent0 = Seq<u8>;
pub type Content0<'a> = &'a [u8];


pub struct SpecContent0Combinator(SpecContent0CombinatorAlias);

impl SpecCombinator for SpecContent0Combinator {
    type Type = SpecContent0;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecContent0Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecContent0CombinatorAlias::is_prefix_secure() }
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
pub type SpecContent0CombinatorAlias = bytes::Variable;

pub struct Content0Combinator(Content0CombinatorAlias);

impl View for Content0Combinator {
    type V = SpecContent0Combinator;
    closed spec fn view(&self) -> Self::V { SpecContent0Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Content0Combinator {
    type Type = Content0<'a>;
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
pub type Content0CombinatorAlias = bytes::Variable;


pub closed spec fn spec_content_0(num: u24) -> SpecContent0Combinator {
    SpecContent0Combinator(bytes::Variable(num.spec_into()))
}

pub fn content_0<'a>(num: u24) -> (o: Content0Combinator)
    ensures o@ == spec_content_0(num@),
{
    Content0Combinator(bytes::Variable(num.ex_into()))
}


pub enum SpecMsgCF4 {
    C0(SpecContent0),
    C1(u16),
    C2(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecMsgCF4Inner = Either<SpecContent0, Either<u16, Either<u32, Seq<u8>>>>;



impl SpecFrom<SpecMsgCF4> for SpecMsgCF4Inner {
    open spec fn spec_from(m: SpecMsgCF4) -> SpecMsgCF4Inner {
        match m {
            SpecMsgCF4::C0(m) => Either::Left(m),
            SpecMsgCF4::C1(m) => Either::Right(Either::Left(m)),
            SpecMsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecMsgCF4Inner> for SpecMsgCF4 {
    open spec fn spec_from(m: SpecMsgCF4Inner) -> SpecMsgCF4 {
        match m {
            Either::Left(m) => SpecMsgCF4::C0(m),
            Either::Right(Either::Left(m)) => SpecMsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecMsgCF4::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgCF4<'a> {
    C0(Content0<'a>),
    C1(u16),
    C2(u32),
    Unrecognized(&'a [u8]),
}

pub type MsgCF4Inner<'a> = Either<Content0<'a>, Either<u16, Either<u32, &'a [u8]>>>;


impl<'a> View for MsgCF4<'a> {
    type V = SpecMsgCF4;
    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}


impl<'a> From<MsgCF4<'a>> for MsgCF4Inner<'a> {
    fn ex_from(m: MsgCF4<'a>) -> MsgCF4Inner<'a> {
        match m {
            MsgCF4::C0(m) => Either::Left(m),
            MsgCF4::C1(m) => Either::Right(Either::Left(m)),
            MsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            MsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<MsgCF4Inner<'a>> for MsgCF4<'a> {
    fn ex_from(m: MsgCF4Inner<'a>) -> MsgCF4<'a> {
        match m {
            Either::Left(m) => MsgCF4::C0(m),
            Either::Right(Either::Left(m)) => MsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => MsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => MsgCF4::Unrecognized(m),
        }
    }
    
}


pub struct MsgCF4Mapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgCF4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgCF4Mapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgCF4Mapper(PhantomData)
    }
}
impl View for MsgCF4Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgCF4Mapper<'_> {
    type Src = SpecMsgCF4Inner;
    type Dst = SpecMsgCF4;
}
impl SpecIsoProof for MsgCF4Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgCF4Mapper<'a> {
    type Src = MsgCF4Inner<'a>;
    type Dst = MsgCF4<'a>;
}


pub struct SpecMsgCF4Combinator(SpecMsgCF4CombinatorAlias);

impl SpecCombinator for SpecMsgCF4Combinator {
    type Type = SpecMsgCF4;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgCF4Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsgCF4CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgCF4CombinatorAlias = AndThen<bytes::Variable, Mapped<Choice<Cond<SpecContent0Combinator>, Choice<Cond<U16Be>, Choice<Cond<U32Be>, Cond<bytes::Tail>>>>, MsgCF4Mapper<'static>>>;

pub struct MsgCF4Combinator<'a>(MsgCF4CombinatorAlias<'a>);

impl<'a> View for MsgCF4Combinator<'a> {
    type V = SpecMsgCF4Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCF4Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgCF4Combinator<'a> {
    type Type = MsgCF4<'a>;
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
pub type MsgCF4CombinatorAlias<'a> = AndThen<bytes::Variable, Mapped<Choice<Cond<Content0Combinator>, Choice<Cond<U16Be>, Choice<Cond<U32Be>, Cond<bytes::Tail>>>>, MsgCF4Mapper<'a>>>;


pub closed spec fn spec_msg_c_f4(f3: u24, f2: SpecContentType) -> SpecMsgCF4Combinator {
    SpecMsgCF4Combinator(AndThen(bytes::Variable(f3.spec_into()), Mapped { inner: Choice(Cond { cond: f2 == 0, inner: spec_content_0(f3) }, Choice(Cond { cond: f2 == 1, inner: U16Be }, Choice(Cond { cond: f2 == 2, inner: U32Be }, Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: bytes::Tail }))), mapper: MsgCF4Mapper::spec_new() }))
}

pub fn msg_c_f4<'a>(f3: u24, f2: ContentType) -> (o: MsgCF4Combinator<'a>)
    ensures o@ == spec_msg_c_f4(f3@, f2@),
{
    MsgCF4Combinator(AndThen(bytes::Variable(f3.ex_into()), Mapped { inner: Choice::new(Cond { cond: f2 == 0, inner: content_0(f3) }, Choice::new(Cond { cond: f2 == 1, inner: U16Be }, Choice::new(Cond { cond: f2 == 2, inner: U32Be }, Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: bytes::Tail }))), mapper: MsgCF4Mapper::new() }))
}


pub struct SpecMsgC {
    pub f2: SpecContentType,
    pub f3: u24,
    pub f4: SpecMsgCF4,
}

pub type SpecMsgCInner = ((SpecContentType, u24), SpecMsgCF4);
impl SpecFrom<SpecMsgC> for SpecMsgCInner {
    open spec fn spec_from(m: SpecMsgC) -> SpecMsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}
impl SpecFrom<SpecMsgCInner> for SpecMsgC {
    open spec fn spec_from(m: SpecMsgCInner) -> SpecMsgC {
        let ((f2, f3), f4) = m;
        SpecMsgC { f2, f3, f4 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MsgC<'a> {
    pub f2: ContentType,
    pub f3: u24,
    pub f4: MsgCF4<'a>,
}

impl View for MsgC<'_> {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC {
            f2: self.f2@,
            f3: self.f3@,
            f4: self.f4@,
        }
    }
}
pub type MsgCInner<'a> = ((ContentType, u24), MsgCF4<'a>);
impl<'a> From<MsgC<'a>> for MsgCInner<'a> {
    fn ex_from(m: MsgC) -> MsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}
impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner) -> MsgC {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgCMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgCMapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgCMapper(PhantomData)
    }
}
impl View for MsgCMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgCMapper<'_> {
    type Src = SpecMsgCInner;
    type Dst = SpecMsgC;
}
impl SpecIsoProof for MsgCMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgCMapper<'a> {
    type Src = MsgCInner<'a>;
    type Dst = MsgC<'a>;
}

pub struct SpecMsgCCombinator(SpecMsgCCombinatorAlias);

impl SpecCombinator for SpecMsgCCombinator {
    type Type = SpecMsgC;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgCCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsgCCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgCCombinatorAlias = Mapped<SpecPair<SpecPair<SpecContentTypeCombinator, U24Be>, SpecMsgCF4Combinator>, MsgCMapper<'static>>;

pub struct MsgCCombinator<'a>(MsgCCombinatorAlias<'a>);

impl<'a> View for MsgCCombinator<'a> {
    type V = SpecMsgCCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgCCombinator<'a> {
    type Type = MsgC<'a>;
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
pub type MsgCCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, Pair<&'a [u8], Vec<u8>, ContentTypeCombinator, U24Be, MsgCCont1<'a>>, MsgCF4Combinator<'a>, MsgCCont0<'a>>, MsgCMapper<'a>>;


pub closed spec fn spec_msg_c() -> SpecMsgCCombinator {
    SpecMsgCCombinator(
    Mapped {
        inner: SpecPair { fst: SpecPair { fst: spec_content_type(), snd: |deps| spec_msg_c_cont1(deps) }, snd: |deps| spec_msg_c_cont0(deps) },
        mapper: MsgCMapper::spec_new(),
    })
}

pub open spec fn spec_msg_c_cont1(deps: SpecContentType) -> U24Be {
    let f2 = deps;
    U24Be
}
pub open spec fn spec_msg_c_cont0(deps: (SpecContentType, u24)) -> SpecMsgCF4Combinator {
    let (f2, f3) = deps;
    spec_msg_c_f4(f3, f2)
}
                
pub fn msg_c<'a>() -> (o: MsgCCombinator<'a>)
    ensures o@ == spec_msg_c(),
{
    MsgCCombinator(
    Mapped {
        inner: Pair { fst: Pair { fst: content_type(), snd: MsgCCont1::new(), spec_snd: Ghost(|deps| spec_msg_c_cont1(deps)) }, snd: MsgCCont0::new(), spec_snd: Ghost(|deps| spec_msg_c_cont0(deps)) },
        mapper: MsgCMapper::new(),
    })
}

pub struct MsgCCont1<'a>(PhantomData<&'a ()>);
impl<'a> MsgCCont1<'a> {
    pub fn new() -> Self {
        MsgCCont1(PhantomData)
    }
}
impl<'a> Continuation<&ContentType> for MsgCCont1<'a> {
    type Output = U24Be;

    open spec fn requires(&self, deps: &ContentType) -> bool { true }

    open spec fn ensures(&self, deps: &ContentType, o: Self::Output) -> bool {
        o@ == spec_msg_c_cont1(deps@)
    }

    fn apply(&self, deps: &ContentType) -> Self::Output {
        let f2 = *deps;
        U24Be
    }
}
pub struct MsgCCont0<'a>(PhantomData<&'a ()>);
impl<'a> MsgCCont0<'a> {
    pub fn new() -> Self {
        MsgCCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ContentType, u24)> for MsgCCont0<'a> {
    type Output = MsgCF4Combinator<'a>;

    open spec fn requires(&self, deps: &(ContentType, u24)) -> bool { true }

    open spec fn ensures(&self, deps: &(ContentType, u24), o: Self::Output) -> bool {
        o@ == spec_msg_c_cont0(deps@)
    }

    fn apply(&self, deps: &(ContentType, u24)) -> Self::Output {
        let (f2, f3) = *deps;
        msg_c_f4(f3, f2)
    }
}
                
pub type SpecF5 = Seq<u8>;
pub type F5<'a> = &'a [u8];

pub spec const SPEC_F5_CONST: Seq<u8> = seq![1; 5];pub type SpecF5Combinator = Refined<bytes::Fixed<5>, TagPred<Seq<u8>>>;
pub exec static F5_CONST: [u8; 5]
    ensures F5_CONST@ == SPEC_F5_CONST,
{
    let arr: [u8; 5] = [1; 5];
    assert(arr@ == SPEC_F5_CONST);
    arr
}
pub type F5Combinator<'a> = Refined<bytes::Fixed<5>, TagPred<&'a [u8]>>;


pub closed spec fn spec_F5() -> SpecF5Combinator {
    Refined { inner: bytes::Fixed::<5>, predicate: TagPred(SPEC_F5_CONST) }
}

pub fn F5<'a>() -> (o: F5Combinator<'a>)
    ensures o@ == spec_F5(),
{
    Refined { inner: bytes::Fixed::<5>, predicate: TagPred(F5_CONST.as_slice()) }
}


pub struct SpecMsgD {
    pub f1: Seq<u8>,
    pub f2: u16,
    pub c: SpecF5,
}

pub type SpecMsgDInner = (Seq<u8>, (u16, SpecF5));
impl SpecFrom<SpecMsgD> for SpecMsgDInner {
    open spec fn spec_from(m: SpecMsgD) -> SpecMsgDInner {
        (m.f1, (m.f2, m.c))
    }
}
impl SpecFrom<SpecMsgDInner> for SpecMsgD {
    open spec fn spec_from(m: SpecMsgDInner) -> SpecMsgD {
        let (f1, (f2, c)) = m;
        SpecMsgD { f1, f2, c }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MsgD<'a> {
    pub f1: &'a [u8],
    pub f2: u16,
    pub c: F5<'a>,
}

impl View for MsgD<'_> {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD {
            f1: self.f1@,
            f2: self.f2@,
            c: self.c@,
        }
    }
}
pub type MsgDInner<'a> = (&'a [u8], (u16, F5<'a>));
impl<'a> From<MsgD<'a>> for MsgDInner<'a> {
    fn ex_from(m: MsgD) -> MsgDInner {
        (m.f1, (m.f2, m.c))
    }
}
impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner) -> MsgD {
        let (f1, (f2, c)) = m;
        MsgD { f1, f2, c }
    }
}

pub struct MsgDMapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgDMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgDMapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgDMapper(PhantomData)
    }
}
impl View for MsgDMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgDMapper<'_> {
    type Src = SpecMsgDInner;
    type Dst = SpecMsgD;
}
impl SpecIsoProof for MsgDMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgDMapper<'a> {
    type Src = MsgDInner<'a>;
    type Dst = MsgD<'a>;
}
pub spec const SPEC_MSGDF1_CONST: Seq<u8> = seq![1; 4];pub const MSGDF2_CONST: u16 = 4660;

pub struct SpecMsgDCombinator(SpecMsgDCombinatorAlias);

impl SpecCombinator for SpecMsgDCombinator {
    type Type = SpecMsgD;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgDCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsgDCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgDCombinatorAlias = Mapped<(Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>, (Refined<U16Be, TagPred<u16>>, SpecF5Combinator)), MsgDMapper<'static>>;
pub exec static MSGDF1_CONST: [u8; 4]
    ensures MSGDF1_CONST@ == SPEC_MSGDF1_CONST,
{
    let arr: [u8; 4] = [1; 4];
    assert(arr@ == SPEC_MSGDF1_CONST);
    arr
}

pub struct MsgDCombinator<'a>(MsgDCombinatorAlias<'a>);

impl<'a> View for MsgDCombinator<'a> {
    type V = SpecMsgDCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgDCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgDCombinator<'a> {
    type Type = MsgD<'a>;
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
pub type MsgDCombinatorAlias<'a> = Mapped<(Refined<bytes::Fixed<4>, TagPred<&'a [u8]>>, (Refined<U16Be, TagPred<u16>>, F5Combinator<'a>)), MsgDMapper<'a>>;


pub closed spec fn spec_msg_d() -> SpecMsgDCombinator {
    SpecMsgDCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MSGDF1_CONST) }, (Refined { inner: U16Be, predicate: TagPred(MSGDF2_CONST) }, spec_F5())),
        mapper: MsgDMapper::spec_new(),
    })
}

                
pub fn msg_d<'a>() -> (o: MsgDCombinator<'a>)
    ensures o@ == spec_msg_d(),
{
    MsgDCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MSGDF1_CONST.as_slice()) }, (Refined { inner: U16Be, predicate: TagPred(MSGDF2_CONST) }, F5())),
        mapper: MsgDMapper::new(),
    })
}

                

pub struct SpecMsgB {
    pub f1: SpecMsgD,
}

pub type SpecMsgBInner = SpecMsgD;
impl SpecFrom<SpecMsgB> for SpecMsgBInner {
    open spec fn spec_from(m: SpecMsgB) -> SpecMsgBInner {
        m.f1
    }
}
impl SpecFrom<SpecMsgBInner> for SpecMsgB {
    open spec fn spec_from(m: SpecMsgBInner) -> SpecMsgB {
        let f1 = m;
        SpecMsgB { f1 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MsgB<'a> {
    pub f1: MsgD<'a>,
}

impl View for MsgB<'_> {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB {
            f1: self.f1@,
        }
    }
}
pub type MsgBInner<'a> = MsgD<'a>;
impl<'a> From<MsgB<'a>> for MsgBInner<'a> {
    fn ex_from(m: MsgB) -> MsgBInner {
        m.f1
    }
}
impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner) -> MsgB {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgBMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgBMapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgBMapper(PhantomData)
    }
}
impl View for MsgBMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgBMapper<'_> {
    type Src = SpecMsgBInner;
    type Dst = SpecMsgB;
}
impl SpecIsoProof for MsgBMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgBMapper<'a> {
    type Src = MsgBInner<'a>;
    type Dst = MsgB<'a>;
}

pub struct SpecMsgBCombinator(SpecMsgBCombinatorAlias);

impl SpecCombinator for SpecMsgBCombinator {
    type Type = SpecMsgB;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgBCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsgBCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgBCombinatorAlias = Mapped<SpecMsgDCombinator, MsgBMapper<'static>>;

pub struct MsgBCombinator<'a>(MsgBCombinatorAlias<'a>);

impl<'a> View for MsgBCombinator<'a> {
    type V = SpecMsgBCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgBCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgBCombinator<'a> {
    type Type = MsgB<'a>;
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
pub type MsgBCombinatorAlias<'a> = Mapped<MsgDCombinator<'a>, MsgBMapper<'a>>;


pub closed spec fn spec_msg_b() -> SpecMsgBCombinator {
    SpecMsgBCombinator(
    Mapped {
        inner: spec_msg_d(),
        mapper: MsgBMapper::spec_new(),
    })
}

                
pub fn msg_b<'a>() -> (o: MsgBCombinator<'a>)
    ensures o@ == spec_msg_b(),
{
    MsgBCombinator(
    Mapped {
        inner: msg_d(),
        mapper: MsgBMapper::new(),
    })
}

                

pub struct SpecMsgA {
    pub f1: SpecMsgB,
    pub f2: Seq<u8>,
}

pub type SpecMsgAInner = (SpecMsgB, Seq<u8>);
impl SpecFrom<SpecMsgA> for SpecMsgAInner {
    open spec fn spec_from(m: SpecMsgA) -> SpecMsgAInner {
        (m.f1, m.f2)
    }
}
impl SpecFrom<SpecMsgAInner> for SpecMsgA {
    open spec fn spec_from(m: SpecMsgAInner) -> SpecMsgA {
        let (f1, f2) = m;
        SpecMsgA { f1, f2 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MsgA<'a> {
    pub f1: MsgB<'a>,
    pub f2: &'a [u8],
}

impl View for MsgA<'_> {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA {
            f1: self.f1@,
            f2: self.f2@,
        }
    }
}
pub type MsgAInner<'a> = (MsgB<'a>, &'a [u8]);
impl<'a> From<MsgA<'a>> for MsgAInner<'a> {
    fn ex_from(m: MsgA) -> MsgAInner {
        (m.f1, m.f2)
    }
}
impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner) -> MsgA {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper<'a>(PhantomData<&'a ()>);
impl<'a> MsgAMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgAMapper(PhantomData)
    }
    pub fn new() -> Self {
        MsgAMapper(PhantomData)
    }
}
impl View for MsgAMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgAMapper<'_> {
    type Src = SpecMsgAInner;
    type Dst = SpecMsgA;
}
impl SpecIsoProof for MsgAMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for MsgAMapper<'a> {
    type Src = MsgAInner<'a>;
    type Dst = MsgA<'a>;
}

pub struct SpecMsgACombinator(SpecMsgACombinatorAlias);

impl SpecCombinator for SpecMsgACombinator {
    type Type = SpecMsgA;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsgACombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsgACombinatorAlias::is_prefix_secure() }
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
pub type SpecMsgACombinatorAlias = Mapped<(SpecMsgBCombinator, bytes::Tail), MsgAMapper<'static>>;

pub struct MsgACombinator<'a>(MsgACombinatorAlias<'a>);

impl<'a> View for MsgACombinator<'a> {
    type V = SpecMsgACombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgACombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgACombinator<'a> {
    type Type = MsgA<'a>;
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
pub type MsgACombinatorAlias<'a> = Mapped<(MsgBCombinator<'a>, bytes::Tail), MsgAMapper<'a>>;


pub closed spec fn spec_msg_a() -> SpecMsgACombinator {
    SpecMsgACombinator(
    Mapped {
        inner: (spec_msg_b(), bytes::Tail),
        mapper: MsgAMapper::spec_new(),
    })
}

                
pub fn msg_a<'a>() -> (o: MsgACombinator<'a>)
    ensures o@ == spec_msg_a(),
{
    MsgACombinator(
    Mapped {
        inner: (msg_b(), bytes::Tail),
        mapper: MsgAMapper::new(),
    })
}

                

}
