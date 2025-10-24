
#![allow(warnings)]
#![allow(unused)]
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

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                closed spec fn ex_requires(&self) -> bool
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
pub mod ContentType {
    use super::*;
    pub spec const SPEC_C0: u8 = 0;
    pub spec const SPEC_C1: u8 = 1;
    pub spec const SPEC_C2: u8 = 2;
    pub exec const C0: u8 ensures C0 == SPEC_C0 { 0 }
    pub exec const C1: u8 ensures C1 == SPEC_C1 { 1 }
    pub exec const C2: u8 ensures C2 == SPEC_C2 { 2 }
}


pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type Type = u8;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ContentTypeCombinator {
    type Type = u8;
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
pub type Content0Ref<'a> = &'a &'a [u8];


pub struct SpecContent0Combinator(SpecContent0CombinatorAlias);

impl SpecCombinator for SpecContent0Combinator {
    type Type = SpecContent0;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Content0Combinator {
    type Type = Content0<'a>;
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

pub type MsgCF4InnerRef<'a> = Either<&'a Content0<'a>, Either<&'a u16, Either<&'a u32, &'a &'a [u8]>>>;


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


impl<'a> From<&'a MsgCF4<'a>> for MsgCF4InnerRef<'a> {
    fn ex_from(m: &'a MsgCF4<'a>) -> MsgCF4InnerRef<'a> {
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


pub struct MsgCF4Mapper;
impl View for MsgCF4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgCF4Mapper {
    type Src = SpecMsgCF4Inner;
    type Dst = SpecMsgCF4;
}
impl SpecIsoProof for MsgCF4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgCF4Mapper {
    type Src = MsgCF4Inner<'a>;
    type Dst = MsgCF4<'a>;
    type RefSrc = MsgCF4InnerRef<'a>;
}

type SpecMsgCF4CombinatorAlias1 = Choice<Cond<U32Be>, Cond<bytes::Tail>>;
type SpecMsgCF4CombinatorAlias2 = Choice<Cond<U16Be>, SpecMsgCF4CombinatorAlias1>;
type SpecMsgCF4CombinatorAlias3 = Choice<Cond<SpecContent0Combinator>, SpecMsgCF4CombinatorAlias2>;
pub struct SpecMsgCF4Combinator(SpecMsgCF4CombinatorAlias);

impl SpecCombinator for SpecMsgCF4Combinator {
    type Type = SpecMsgCF4;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsgCF4CombinatorAlias = AndThen<bytes::Variable, Mapped<SpecMsgCF4CombinatorAlias3, MsgCF4Mapper>>;
type MsgCF4CombinatorAlias1 = Choice<Cond<U32Be>, Cond<bytes::Tail>>;
type MsgCF4CombinatorAlias2 = Choice<Cond<U16Be>, MsgCF4Combinator1>;
type MsgCF4CombinatorAlias3 = Choice<Cond<Content0Combinator>, MsgCF4Combinator2>;
struct MsgCF4Combinator1(MsgCF4CombinatorAlias1);
impl View for MsgCF4Combinator1 {
    type V = SpecMsgCF4CombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgCF4Combinator1, MsgCF4CombinatorAlias1);

struct MsgCF4Combinator2(MsgCF4CombinatorAlias2);
impl View for MsgCF4Combinator2 {
    type V = SpecMsgCF4CombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgCF4Combinator2, MsgCF4CombinatorAlias2);

struct MsgCF4Combinator3(MsgCF4CombinatorAlias3);
impl View for MsgCF4Combinator3 {
    type V = SpecMsgCF4CombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgCF4Combinator3, MsgCF4CombinatorAlias3);

pub struct MsgCF4Combinator(MsgCF4CombinatorAlias);

impl View for MsgCF4Combinator {
    type V = SpecMsgCF4Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCF4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgCF4Combinator {
    type Type = MsgCF4<'a>;
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
pub type MsgCF4CombinatorAlias = AndThen<bytes::Variable, Mapped<MsgCF4Combinator3, MsgCF4Mapper>>;


pub closed spec fn spec_msg_c_f4(f2: u8, f3: u24) -> SpecMsgCF4Combinator {
    SpecMsgCF4Combinator(AndThen(bytes::Variable(f3.spec_into()), Mapped { inner: Choice(Cond { cond: f2 == ContentType::SPEC_C0, inner: spec_content_0(f3) }, Choice(Cond { cond: f2 == ContentType::SPEC_C1, inner: U16Be }, Choice(Cond { cond: f2 == ContentType::SPEC_C2, inner: U32Be }, Cond { cond: !(f2 == ContentType::SPEC_C0 || f2 == ContentType::SPEC_C1 || f2 == ContentType::SPEC_C2), inner: bytes::Tail }))), mapper: MsgCF4Mapper }))
}

pub fn msg_c_f4<'a>(f2: u8, f3: u24) -> (o: MsgCF4Combinator)
    ensures o@ == spec_msg_c_f4(f2@, f3@),
{
    MsgCF4Combinator(AndThen(bytes::Variable(f3.ex_into()), Mapped { inner: MsgCF4Combinator3(Choice::new(Cond { cond: f2 == ContentType::C0, inner: content_0(f3) }, MsgCF4Combinator2(Choice::new(Cond { cond: f2 == ContentType::C1, inner: U16Be }, MsgCF4Combinator1(Choice::new(Cond { cond: f2 == ContentType::C2, inner: U32Be }, Cond { cond: !(f2 == ContentType::C0 || f2 == ContentType::C1 || f2 == ContentType::C2), inner: bytes::Tail })))))), mapper: MsgCF4Mapper }))
}


pub struct SpecMsgC {
    pub f2: u8,
    pub f3: u24,
    pub f4: SpecMsgCF4,
}

pub type SpecMsgCInner = ((u8, u24), SpecMsgCF4);


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
    pub f2: u8,
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
pub type MsgCInner<'a> = ((u8, u24), MsgCF4<'a>);

pub type MsgCInnerRef<'a> = ((&'a u8, &'a u24), &'a MsgCF4<'a>);
impl<'a> From<&'a MsgC<'a>> for MsgCInnerRef<'a> {
    fn ex_from(m: &'a MsgC) -> MsgCInnerRef<'a> {
        ((&m.f2, &m.f3), &m.f4)
    }
}

impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner) -> MsgC {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper;
impl View for MsgCMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgCMapper {
    type Src = SpecMsgCInner;
    type Dst = SpecMsgC;
}
impl SpecIsoProof for MsgCMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgCMapper {
    type Src = MsgCInner<'a>;
    type Dst = MsgC<'a>;
    type RefSrc = MsgCInnerRef<'a>;
}

pub struct SpecMsgCCombinator(SpecMsgCCombinatorAlias);

impl SpecCombinator for SpecMsgCCombinator {
    type Type = SpecMsgC;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsgCCombinatorAlias = Mapped<SpecPair<SpecPair<SpecContentTypeCombinator, U24Be>, SpecMsgCF4Combinator>, MsgCMapper>;

pub struct MsgCCombinator(MsgCCombinatorAlias);

impl View for MsgCCombinator {
    type V = SpecMsgCCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgCCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgCCombinator {
    type Type = MsgC<'a>;
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
pub type MsgCCombinatorAlias = Mapped<Pair<Pair<ContentTypeCombinator, U24Be, MsgCCont1>, MsgCF4Combinator, MsgCCont0>, MsgCMapper>;


pub closed spec fn spec_msg_c() -> SpecMsgCCombinator {
    SpecMsgCCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_content_type(), |deps| spec_msg_c_cont1(deps)), |deps| spec_msg_c_cont0(deps)),
        mapper: MsgCMapper,
    })
}

pub open spec fn spec_msg_c_cont1(deps: u8) -> U24Be {
    let f2 = deps;
    U24Be
}

impl View for MsgCCont1 {
    type V = spec_fn(u8) -> U24Be;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_msg_c_cont1(deps)
        }
    }
}

pub open spec fn spec_msg_c_cont0(deps: (u8, u24)) -> SpecMsgCF4Combinator {
    let (f2, f3) = deps;
    spec_msg_c_f4(f2, f3)
}

impl View for MsgCCont0 {
    type V = spec_fn((u8, u24)) -> SpecMsgCF4Combinator;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, u24)| {
            spec_msg_c_cont0(deps)
        }
    }
}

                
pub fn msg_c() -> (o: MsgCCombinator)
    ensures o@ == spec_msg_c(),
{
    MsgCCombinator(
    Mapped {
        inner: Pair::new(Pair::new(content_type(), MsgCCont1), MsgCCont0),
        mapper: MsgCMapper,
    })
}

pub struct MsgCCont1;
type MsgCCont1Type<'a, 'b> = &'b u8;
type MsgCCont1SType<'a, 'x> = &'x u8;
type MsgCCont1Input<'a, 'b, 'x> = POrSType<MsgCCont1Type<'a, 'b>, MsgCCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MsgCCont1Input<'a, 'b, 'x>> for MsgCCont1 {
    type Output = U24Be;

    open spec fn requires(&self, deps: MsgCCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MsgCCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg_c_cont1(deps@)
    }

    fn apply(&self, deps: MsgCCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let f2 = *deps;
                U24Be
            }
            POrSType::S(deps) => {
                let f2 = deps;
                let f2 = *f2;
                U24Be
            }
        }
    }
}
pub struct MsgCCont0;
type MsgCCont0Type<'a, 'b> = &'b (u8, u24);
type MsgCCont0SType<'a, 'x> = (&'x u8, &'x u24);
type MsgCCont0Input<'a, 'b, 'x> = POrSType<MsgCCont0Type<'a, 'b>, MsgCCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MsgCCont0Input<'a, 'b, 'x>> for MsgCCont0 {
    type Output = MsgCF4Combinator;

    open spec fn requires(&self, deps: MsgCCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MsgCCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg_c_cont0(deps@)
    }

    fn apply(&self, deps: MsgCCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (f2, f3) = *deps;
                msg_c_f4(f2, f3)
            }
            POrSType::S(deps) => {
                let (f2, f3) = deps;
                let (f2, f3) = (*f2, *f3);
                msg_c_f4(f2, f3)
            }
        }
    }
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

pub type MsgDInnerRef<'a> = (&'a &'a [u8], (&'a u16, &'a F5<'a>));
impl<'a> From<&'a MsgD<'a>> for MsgDInnerRef<'a> {
    fn ex_from(m: &'a MsgD) -> MsgDInnerRef<'a> {
        (&m.f1, (&m.f2, &m.c))
    }
}

impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner) -> MsgD {
        let (f1, (f2, c)) = m;
        MsgD { f1, f2, c }
    }
}

pub struct MsgDMapper;
impl View for MsgDMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgDMapper {
    type Src = SpecMsgDInner;
    type Dst = SpecMsgD;
}
impl SpecIsoProof for MsgDMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgDMapper {
    type Src = MsgDInner<'a>;
    type Dst = MsgD<'a>;
    type RefSrc = MsgDInnerRef<'a>;
}
pub spec const SPEC_MSGDF1_CONST: Seq<u8> = seq![1; 4];pub const MSGDF2_CONST: u16 = 4660;
type SpecMsgDCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, SpecF5Combinator);
type SpecMsgDCombinatorAlias2 = (Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>, SpecMsgDCombinatorAlias1);
pub struct SpecMsgDCombinator(SpecMsgDCombinatorAlias);

impl SpecCombinator for SpecMsgDCombinator {
    type Type = SpecMsgD;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsgDCombinatorAlias = Mapped<SpecMsgDCombinatorAlias2, MsgDMapper>;
pub exec static MSGDF1_CONST: [u8; 4]
    ensures MSGDF1_CONST@ == SPEC_MSGDF1_CONST,
{
    let arr: [u8; 4] = [1; 4];
    assert(arr@ == SPEC_MSGDF1_CONST);
    arr
}
type MsgDCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, F5Combinator);
type MsgDCombinatorAlias2 = (Refined<bytes::Fixed<4>, TagPred<[u8; 4]>>, MsgDCombinator1);
struct MsgDCombinator1(MsgDCombinatorAlias1);
impl View for MsgDCombinator1 {
    type V = SpecMsgDCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgDCombinator1, MsgDCombinatorAlias1);

struct MsgDCombinator2(MsgDCombinatorAlias2);
impl View for MsgDCombinator2 {
    type V = SpecMsgDCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgDCombinator2, MsgDCombinatorAlias2);

pub struct MsgDCombinator(MsgDCombinatorAlias);

impl View for MsgDCombinator {
    type V = SpecMsgDCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgDCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgDCombinator {
    type Type = MsgD<'a>;
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
pub type MsgDCombinatorAlias = Mapped<MsgDCombinator2, MsgDMapper>;


pub closed spec fn spec_msg_d() -> SpecMsgDCombinator {
    SpecMsgDCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MSGDF1_CONST) }, (Refined { inner: U16Be, predicate: TagPred(MSGDF2_CONST) }, spec_F5())),
        mapper: MsgDMapper,
    })
}

                
pub fn msg_d() -> (o: MsgDCombinator)
    ensures o@ == spec_msg_d(),
{
    MsgDCombinator(
    Mapped {
        inner: MsgDCombinator2((Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MSGDF1_CONST) }, MsgDCombinator1((Refined { inner: U16Be, predicate: TagPred(MSGDF2_CONST) }, F5())))),
        mapper: MsgDMapper,
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

pub type MsgBInnerRef<'a> = &'a MsgD<'a>;
impl<'a> From<&'a MsgB<'a>> for MsgBInnerRef<'a> {
    fn ex_from(m: &'a MsgB) -> MsgBInnerRef<'a> {
        &m.f1
    }
}

impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner) -> MsgB {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper;
impl View for MsgBMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgBMapper {
    type Src = SpecMsgBInner;
    type Dst = SpecMsgB;
}
impl SpecIsoProof for MsgBMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgBMapper {
    type Src = MsgBInner<'a>;
    type Dst = MsgB<'a>;
    type RefSrc = MsgBInnerRef<'a>;
}

pub struct SpecMsgBCombinator(SpecMsgBCombinatorAlias);

impl SpecCombinator for SpecMsgBCombinator {
    type Type = SpecMsgB;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsgBCombinatorAlias = Mapped<SpecMsgDCombinator, MsgBMapper>;

pub struct MsgBCombinator(MsgBCombinatorAlias);

impl View for MsgBCombinator {
    type V = SpecMsgBCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgBCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgBCombinator {
    type Type = MsgB<'a>;
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
pub type MsgBCombinatorAlias = Mapped<MsgDCombinator, MsgBMapper>;


pub closed spec fn spec_msg_b() -> SpecMsgBCombinator {
    SpecMsgBCombinator(
    Mapped {
        inner: spec_msg_d(),
        mapper: MsgBMapper,
    })
}

                
pub fn msg_b() -> (o: MsgBCombinator)
    ensures o@ == spec_msg_b(),
{
    MsgBCombinator(
    Mapped {
        inner: msg_d(),
        mapper: MsgBMapper,
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

pub type MsgAInnerRef<'a> = (&'a MsgB<'a>, &'a &'a [u8]);
impl<'a> From<&'a MsgA<'a>> for MsgAInnerRef<'a> {
    fn ex_from(m: &'a MsgA) -> MsgAInnerRef<'a> {
        (&m.f1, &m.f2)
    }
}

impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner) -> MsgA {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper;
impl View for MsgAMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MsgAMapper {
    type Src = SpecMsgAInner;
    type Dst = SpecMsgA;
}
impl SpecIsoProof for MsgAMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MsgAMapper {
    type Src = MsgAInner<'a>;
    type Dst = MsgA<'a>;
    type RefSrc = MsgAInnerRef<'a>;
}
type SpecMsgACombinatorAlias1 = (SpecMsgBCombinator, bytes::Tail);
pub struct SpecMsgACombinator(SpecMsgACombinatorAlias);

impl SpecCombinator for SpecMsgACombinator {
    type Type = SpecMsgA;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsgACombinatorAlias = Mapped<SpecMsgACombinatorAlias1, MsgAMapper>;
type MsgACombinatorAlias1 = (MsgBCombinator, bytes::Tail);
struct MsgACombinator1(MsgACombinatorAlias1);
impl View for MsgACombinator1 {
    type V = SpecMsgACombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MsgACombinator1, MsgACombinatorAlias1);

pub struct MsgACombinator(MsgACombinatorAlias);

impl View for MsgACombinator {
    type V = SpecMsgACombinator;
    closed spec fn view(&self) -> Self::V { SpecMsgACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MsgACombinator {
    type Type = MsgA<'a>;
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
pub type MsgACombinatorAlias = Mapped<MsgACombinator1, MsgAMapper>;


pub closed spec fn spec_msg_a() -> SpecMsgACombinator {
    SpecMsgACombinator(
    Mapped {
        inner: (spec_msg_b(), bytes::Tail),
        mapper: MsgAMapper,
    })
}

                
pub fn msg_a() -> (o: MsgACombinator)
    ensures o@ == spec_msg_a(),
{
    MsgACombinator(
    Mapped {
        inner: MsgACombinator1((msg_b(), bytes::Tail)),
        mapper: MsgAMapper,
    })
}

                
pub type SpecF5 = Seq<u8>;
pub type F5<'a> = &'a [u8];
pub type F5Ref<'a> = &'a &'a [u8];

pub spec const SPEC_F5_CONST: Seq<u8> = seq![1; 5];pub type SpecF5Combinator = Refined<bytes::Fixed<5>, TagPred<Seq<u8>>>;
pub exec static F5_CONST: [u8; 5]
    ensures F5_CONST@ == SPEC_F5_CONST,
{
    let arr: [u8; 5] = [1; 5];
    assert(arr@ == SPEC_F5_CONST);
    arr
}
pub type F5Combinator = Refined<bytes::Fixed<5>, TagPred<[u8; 5]>>;


pub closed spec fn spec_F5() -> SpecF5Combinator {
    Refined { inner: bytes::Fixed::<5>, predicate: TagPred(SPEC_F5_CONST) }
}

pub fn F5() -> (o: F5Combinator)
    ensures o@ == spec_F5(),
{
    Refined { inner: bytes::Fixed::<5>, predicate: TagPred(F5_CONST) }
}


}
