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
pub type SpecRepeatFix = Seq<u16>;
pub type RepeatFix = RepeatResult<u16>;


pub struct SpecRepeatFixCombinator(SpecRepeatFixCombinatorAlias);

impl SpecCombinator for SpecRepeatFixCombinator {
    type Type = SpecRepeatFix;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecRepeatFixCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecRepeatFixCombinatorAlias::is_prefix_secure() }
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
pub type SpecRepeatFixCombinatorAlias = RepeatN<U16Le>;

pub struct RepeatFixCombinator(RepeatFixCombinatorAlias);

impl View for RepeatFixCombinator {
    type V = SpecRepeatFixCombinator;
    closed spec fn view(&self) -> Self::V { SpecRepeatFixCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for RepeatFixCombinator {
    type Type = RepeatFix;
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
pub type RepeatFixCombinatorAlias = RepeatN<U16Le>;


pub closed spec fn spec_repeat_fix() -> SpecRepeatFixCombinator {
    SpecRepeatFixCombinator(RepeatN(U16Le, 32))
}

                
pub fn repeat_fix() -> (o: RepeatFixCombinator)
    ensures o@ == spec_repeat_fix(),
{
    RepeatFixCombinator(RepeatN(U16Le, 32))
}

                

pub struct SpecOpaqueU16 {
    pub l: u16,
    pub data: Seq<u8>,
}

pub type SpecOpaqueU16Inner = (u16, Seq<u8>);
impl SpecFrom<SpecOpaqueU16> for SpecOpaqueU16Inner {
    open spec fn spec_from(m: SpecOpaqueU16) -> SpecOpaqueU16Inner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaqueU16Inner> for SpecOpaqueU16 {
    open spec fn spec_from(m: SpecOpaqueU16Inner) -> SpecOpaqueU16 {
        let (l, data) = m;
        SpecOpaqueU16 { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OpaqueU16<'a> {
    pub l: u16,
    pub data: &'a [u8],
}

impl View for OpaqueU16<'_> {
    type V = SpecOpaqueU16;

    open spec fn view(&self) -> Self::V {
        SpecOpaqueU16 {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type OpaqueU16Inner<'a> = (u16, &'a [u8]);
impl<'a> From<OpaqueU16<'a>> for OpaqueU16Inner<'a> {
    fn ex_from(m: OpaqueU16) -> OpaqueU16Inner {
        (m.l, m.data)
    }
}
impl<'a> From<OpaqueU16Inner<'a>> for OpaqueU16<'a> {
    fn ex_from(m: OpaqueU16Inner) -> OpaqueU16 {
        let (l, data) = m;
        OpaqueU16 { l, data }
    }
}

pub struct OpaqueU16Mapper<'a>(PhantomData<&'a ()>);
impl<'a> OpaqueU16Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OpaqueU16Mapper(PhantomData)
    }
    pub fn new() -> Self {
        OpaqueU16Mapper(PhantomData)
    }
}
impl View for OpaqueU16Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OpaqueU16Mapper<'_> {
    type Src = SpecOpaqueU16Inner;
    type Dst = SpecOpaqueU16;
}
impl SpecIsoProof for OpaqueU16Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OpaqueU16Mapper<'a> {
    type Src = OpaqueU16Inner<'a>;
    type Dst = OpaqueU16<'a>;
}

pub struct SpecOpaqueU16Combinator(SpecOpaqueU16CombinatorAlias);

impl SpecCombinator for SpecOpaqueU16Combinator {
    type Type = SpecOpaqueU16;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaqueU16Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaqueU16CombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaqueU16CombinatorAlias = Mapped<SpecPair<Refined<U16Le, Predicate17626095872143391426>, bytes::Variable>, OpaqueU16Mapper<'static>>;
pub struct Predicate17626095872143391426;
impl View for Predicate17626095872143391426 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17626095872143391426 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}
impl SpecPred for Predicate17626095872143391426 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}

pub struct OpaqueU16Combinator<'a>(OpaqueU16CombinatorAlias<'a>);

impl<'a> View for OpaqueU16Combinator<'a> {
    type V = SpecOpaqueU16Combinator;
    closed spec fn view(&self) -> Self::V { SpecOpaqueU16Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OpaqueU16Combinator<'a> {
    type Type = OpaqueU16<'a>;
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
pub type OpaqueU16CombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, Refined<U16Le, Predicate17626095872143391426>, bytes::Variable, OpaqueU16Cont0<'a>>, OpaqueU16Mapper<'a>>;


pub closed spec fn spec_opaque_u16() -> SpecOpaqueU16Combinator {
    SpecOpaqueU16Combinator(
    Mapped {
        inner: SpecPair { fst: Refined { inner: U16Le, predicate: Predicate17626095872143391426 }, snd: |deps| spec_opaque_u16_cont0(deps) },
        mapper: OpaqueU16Mapper::spec_new(),
    })
}

pub open spec fn spec_opaque_u16_cont0(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}
                
pub fn opaque_u16<'a>() -> (o: OpaqueU16Combinator<'a>)
    ensures o@ == spec_opaque_u16(),
{
    OpaqueU16Combinator(
    Mapped {
        inner: Pair { fst: Refined { inner: U16Le, predicate: Predicate17626095872143391426 }, snd: OpaqueU16Cont0::new(), spec_snd: Ghost(|deps| spec_opaque_u16_cont0(deps)) },
        mapper: OpaqueU16Mapper::new(),
    })
}

pub struct OpaqueU16Cont0<'a>(PhantomData<&'a ()>);
impl<'a> OpaqueU16Cont0<'a> {
    pub fn new() -> Self {
        OpaqueU16Cont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for OpaqueU16Cont0<'a> {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_opaque_u16_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        bytes::Variable(l.ex_into())
    }
}
                
pub type SpecResponderId = SpecOpaqueU16;
pub type ResponderId<'a> = OpaqueU16<'a>;


pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type Type = SpecResponderId;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecResponderIdCombinatorAlias = SpecOpaqueU16Combinator;

pub struct ResponderIdCombinator<'a>(ResponderIdCombinatorAlias<'a>);

impl<'a> View for ResponderIdCombinator<'a> {
    type V = SpecResponderIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdCombinator<'a> {
    type Type = ResponderId<'a>;
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
pub type ResponderIdCombinatorAlias<'a> = OpaqueU16Combinator<'a>;


pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_u16())
}

                
pub fn responder_id<'a>() -> (o: ResponderIdCombinator<'a>)
    ensures o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_u16())
}

                

pub struct SpecResponderIdList {
    pub l: u16,
    pub list: Seq<SpecResponderId>,
}

pub type SpecResponderIdListInner = (u16, Seq<SpecResponderId>);
impl SpecFrom<SpecResponderIdList> for SpecResponderIdListInner {
    open spec fn spec_from(m: SpecResponderIdList) -> SpecResponderIdListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecResponderIdListInner> for SpecResponderIdList {
    open spec fn spec_from(m: SpecResponderIdListInner) -> SpecResponderIdList {
        let (l, list) = m;
        SpecResponderIdList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ResponderIdList<'a> {
    pub l: u16,
    pub list: RepeatResult<ResponderId<'a>>,
}

impl View for ResponderIdList<'_> {
    type V = SpecResponderIdList;

    open spec fn view(&self) -> Self::V {
        SpecResponderIdList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ResponderIdListInner<'a> = (u16, RepeatResult<ResponderId<'a>>);
impl<'a> From<ResponderIdList<'a>> for ResponderIdListInner<'a> {
    fn ex_from(m: ResponderIdList) -> ResponderIdListInner {
        (m.l, m.list)
    }
}
impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner) -> ResponderIdList {
        let (l, list) = m;
        ResponderIdList { l, list }
    }
}

pub struct ResponderIdListMapper<'a>(PhantomData<&'a ()>);
impl<'a> ResponderIdListMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ResponderIdListMapper(PhantomData)
    }
    pub fn new() -> Self {
        ResponderIdListMapper(PhantomData)
    }
}
impl View for ResponderIdListMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResponderIdListMapper<'_> {
    type Src = SpecResponderIdListInner;
    type Dst = SpecResponderIdList;
}
impl SpecIsoProof for ResponderIdListMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ResponderIdListMapper<'a> {
    type Src = ResponderIdListInner<'a>;
    type Dst = ResponderIdList<'a>;
}

pub struct SpecResponderIdListCombinator(SpecResponderIdListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListCombinator {
    type Type = SpecResponderIdList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListCombinatorAlias::is_prefix_secure() }
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
pub type SpecResponderIdListCombinatorAlias = Mapped<SpecPair<Refined<U16Le, Predicate2984462868727922620>, AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>>>, ResponderIdListMapper<'static>>;
pub struct Predicate2984462868727922620;
impl View for Predicate2984462868727922620 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate2984462868727922620 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65535)
    }
}
impl SpecPred for Predicate2984462868727922620 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65535)
    }
}

pub struct ResponderIdListCombinator<'a>(ResponderIdListCombinatorAlias<'a>);

impl<'a> View for ResponderIdListCombinator<'a> {
    type V = SpecResponderIdListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdListCombinator<'a> {
    type Type = ResponderIdList<'a>;
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
pub type ResponderIdListCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, Refined<U16Le, Predicate2984462868727922620>, AndThen<bytes::Variable, Repeat<ResponderIdCombinator<'a>>>, ResponderIdListCont0<'a>>, ResponderIdListMapper<'a>>;


pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: SpecPair { fst: Refined { inner: U16Le, predicate: Predicate2984462868727922620 }, snd: |deps| spec_responder_id_list_cont0(deps) },
        mapper: ResponderIdListMapper::spec_new(),
    })
}

pub open spec fn spec_responder_id_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_responder_id()))
}
                
pub fn responder_id_list<'a>() -> (o: ResponderIdListCombinator<'a>)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Pair { fst: Refined { inner: U16Le, predicate: Predicate2984462868727922620 }, snd: ResponderIdListCont0::new(), spec_snd: Ghost(|deps| spec_responder_id_list_cont0(deps)) },
        mapper: ResponderIdListMapper::new(),
    })
}

pub struct ResponderIdListCont0<'a>(PhantomData<&'a ()>);
impl<'a> ResponderIdListCont0<'a> {
    pub fn new() -> Self {
        ResponderIdListCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for ResponderIdListCont0<'a> {
    type Output = AndThen<bytes::Variable, Repeat<ResponderIdCombinator<'a>>>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id()))
    }
}
                

pub struct SpecRepeatDyn {
    pub l: VarInt,
    pub data: Seq<SpecResponderIdList>,
}

pub type SpecRepeatDynInner = (VarInt, Seq<SpecResponderIdList>);
impl SpecFrom<SpecRepeatDyn> for SpecRepeatDynInner {
    open spec fn spec_from(m: SpecRepeatDyn) -> SpecRepeatDynInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecRepeatDynInner> for SpecRepeatDyn {
    open spec fn spec_from(m: SpecRepeatDynInner) -> SpecRepeatDyn {
        let (l, data) = m;
        SpecRepeatDyn { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct RepeatDyn<'a> {
    pub l: VarInt,
    pub data: RepeatResult<ResponderIdList<'a>>,
}

impl View for RepeatDyn<'_> {
    type V = SpecRepeatDyn;

    open spec fn view(&self) -> Self::V {
        SpecRepeatDyn {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type RepeatDynInner<'a> = (VarInt, RepeatResult<ResponderIdList<'a>>);
impl<'a> From<RepeatDyn<'a>> for RepeatDynInner<'a> {
    fn ex_from(m: RepeatDyn) -> RepeatDynInner {
        (m.l, m.data)
    }
}
impl<'a> From<RepeatDynInner<'a>> for RepeatDyn<'a> {
    fn ex_from(m: RepeatDynInner) -> RepeatDyn {
        let (l, data) = m;
        RepeatDyn { l, data }
    }
}

pub struct RepeatDynMapper<'a>(PhantomData<&'a ()>);
impl<'a> RepeatDynMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        RepeatDynMapper(PhantomData)
    }
    pub fn new() -> Self {
        RepeatDynMapper(PhantomData)
    }
}
impl View for RepeatDynMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for RepeatDynMapper<'_> {
    type Src = SpecRepeatDynInner;
    type Dst = SpecRepeatDyn;
}
impl SpecIsoProof for RepeatDynMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for RepeatDynMapper<'a> {
    type Src = RepeatDynInner<'a>;
    type Dst = RepeatDyn<'a>;
}

pub struct SpecRepeatDynCombinator(SpecRepeatDynCombinatorAlias);

impl SpecCombinator for SpecRepeatDynCombinator {
    type Type = SpecRepeatDyn;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecRepeatDynCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecRepeatDynCombinatorAlias::is_prefix_secure() }
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
pub type SpecRepeatDynCombinatorAlias = Mapped<SpecPair<BtcVarint, RepeatN<SpecResponderIdListCombinator>>, RepeatDynMapper<'static>>;

pub struct RepeatDynCombinator<'a>(RepeatDynCombinatorAlias<'a>);

impl<'a> View for RepeatDynCombinator<'a> {
    type V = SpecRepeatDynCombinator;
    closed spec fn view(&self) -> Self::V { SpecRepeatDynCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for RepeatDynCombinator<'a> {
    type Type = RepeatDyn<'a>;
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
pub type RepeatDynCombinatorAlias<'a> = Mapped<Pair<&'a [u8], Vec<u8>, BtcVarint, RepeatN<ResponderIdListCombinator<'a>>, RepeatDynCont0<'a>>, RepeatDynMapper<'a>>;


pub closed spec fn spec_repeat_dyn() -> SpecRepeatDynCombinator {
    SpecRepeatDynCombinator(
    Mapped {
        inner: SpecPair { fst: BtcVarint, snd: |deps| spec_repeat_dyn_cont0(deps) },
        mapper: RepeatDynMapper::spec_new(),
    })
}

pub open spec fn spec_repeat_dyn_cont0(deps: VarInt) -> RepeatN<SpecResponderIdListCombinator> {
    let l = deps;
    RepeatN(spec_responder_id_list(), l.spec_into())
}
                
pub fn repeat_dyn<'a>() -> (o: RepeatDynCombinator<'a>)
    ensures o@ == spec_repeat_dyn(),
{
    RepeatDynCombinator(
    Mapped {
        inner: Pair { fst: BtcVarint, snd: RepeatDynCont0::new(), spec_snd: Ghost(|deps| spec_repeat_dyn_cont0(deps)) },
        mapper: RepeatDynMapper::new(),
    })
}

pub struct RepeatDynCont0<'a>(PhantomData<&'a ()>);
impl<'a> RepeatDynCont0<'a> {
    pub fn new() -> Self {
        RepeatDynCont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for RepeatDynCont0<'a> {
    type Output = RepeatN<ResponderIdListCombinator<'a>>;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_repeat_dyn_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let l = *deps;
        RepeatN(responder_id_list(), l.ex_into())
    }
}
                

}
