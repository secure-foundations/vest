
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

pub type OpaqueU16InnerRef<'a> = (&'a u16, &'a &'a [u8]);
impl<'a> From<&'a OpaqueU16<'a>> for OpaqueU16InnerRef<'a> {
    fn ex_from(m: &'a OpaqueU16) -> OpaqueU16InnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<OpaqueU16Inner<'a>> for OpaqueU16<'a> {
    fn ex_from(m: OpaqueU16Inner) -> OpaqueU16 {
        let (l, data) = m;
        OpaqueU16 { l, data }
    }
}

pub struct OpaqueU16Mapper;
impl View for OpaqueU16Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OpaqueU16Mapper {
    type Src = SpecOpaqueU16Inner;
    type Dst = SpecOpaqueU16;
}
impl SpecIsoProof for OpaqueU16Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OpaqueU16Mapper {
    type Src = OpaqueU16Inner<'a>;
    type Dst = OpaqueU16<'a>;
    type RefSrc = OpaqueU16InnerRef<'a>;
}

pub struct SpecOpaqueU16Combinator(SpecOpaqueU16CombinatorAlias);

impl SpecCombinator for SpecOpaqueU16Combinator {
    type Type = SpecOpaqueU16;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecOpaqueU16CombinatorAlias = Mapped<SpecPair<Refined<U16Le, Predicate17626095872143391426>, bytes::Variable>, OpaqueU16Mapper>;
pub struct Predicate17626095872143391426;
impl View for Predicate17626095872143391426 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate17626095872143391426 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate17626095872143391426 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}

pub struct OpaqueU16Combinator(OpaqueU16CombinatorAlias);

impl View for OpaqueU16Combinator {
    type V = SpecOpaqueU16Combinator;
    closed spec fn view(&self) -> Self::V { SpecOpaqueU16Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OpaqueU16Combinator {
    type Type = OpaqueU16<'a>;
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
pub type OpaqueU16CombinatorAlias = Mapped<Pair<Refined<U16Le, Predicate17626095872143391426>, bytes::Variable, OpaqueU16Cont0>, OpaqueU16Mapper>;


pub closed spec fn spec_opaque_u16() -> SpecOpaqueU16Combinator {
    SpecOpaqueU16Combinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Le, predicate: Predicate17626095872143391426 }, |deps| spec_opaque_u16_cont0(deps)),
        mapper: OpaqueU16Mapper,
    })
}

pub open spec fn spec_opaque_u16_cont0(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for OpaqueU16Cont0 {
    type V = spec_fn(u16) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_opaque_u16_cont0(deps)
        }
    }
}

                
pub fn opaque_u16() -> (o: OpaqueU16Combinator)
    ensures o@ == spec_opaque_u16(),
{
    OpaqueU16Combinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Le, predicate: Predicate17626095872143391426 }, OpaqueU16Cont0),
        mapper: OpaqueU16Mapper,
    })
}

pub struct OpaqueU16Cont0;
type OpaqueU16Cont0Type<'a, 'b> = &'b u16;
type OpaqueU16Cont0SType<'a, 'x> = &'x u16;
type OpaqueU16Cont0Input<'a, 'b, 'x> = POrSType<OpaqueU16Cont0Type<'a, 'b>, OpaqueU16Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<OpaqueU16Cont0Input<'a, 'b, 'x>> for OpaqueU16Cont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: OpaqueU16Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: OpaqueU16Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque_u16_cont0(deps@)
    }

    fn apply(&self, deps: OpaqueU16Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                bytes::Variable(l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                bytes::Variable(l.ex_into())
            }
        }
    }
}
                
pub type SpecResponderId = SpecOpaqueU16;
pub type ResponderId<'a> = OpaqueU16<'a>;
pub type ResponderIdRef<'a> = &'a OpaqueU16<'a>;


pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type Type = SpecResponderId;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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

pub struct ResponderIdCombinator(ResponderIdCombinatorAlias);

impl View for ResponderIdCombinator {
    type V = SpecResponderIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdCombinator {
    type Type = ResponderId<'a>;
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
pub type ResponderIdCombinatorAlias = OpaqueU16Combinator;


pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_u16())
}

                
pub fn responder_id() -> (o: ResponderIdCombinator)
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

pub type ResponderIdListInnerRef<'a> = (&'a u16, &'a RepeatResult<ResponderId<'a>>);
impl<'a> From<&'a ResponderIdList<'a>> for ResponderIdListInnerRef<'a> {
    fn ex_from(m: &'a ResponderIdList) -> ResponderIdListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner) -> ResponderIdList {
        let (l, list) = m;
        ResponderIdList { l, list }
    }
}

pub struct ResponderIdListMapper;
impl View for ResponderIdListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResponderIdListMapper {
    type Src = SpecResponderIdListInner;
    type Dst = SpecResponderIdList;
}
impl SpecIsoProof for ResponderIdListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ResponderIdListMapper {
    type Src = ResponderIdListInner<'a>;
    type Dst = ResponderIdList<'a>;
    type RefSrc = ResponderIdListInnerRef<'a>;
}

pub struct SpecResponderIdListCombinator(SpecResponderIdListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListCombinator {
    type Type = SpecResponderIdList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecResponderIdListCombinatorAlias = Mapped<SpecPair<Refined<U16Le, Predicate2984462868727922620>, AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>>>, ResponderIdListMapper>;
pub struct Predicate2984462868727922620;
impl View for Predicate2984462868727922620 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate2984462868727922620 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate2984462868727922620 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65535)
    }
}

pub struct ResponderIdListCombinator(ResponderIdListCombinatorAlias);

impl View for ResponderIdListCombinator {
    type V = SpecResponderIdListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdListCombinator {
    type Type = ResponderIdList<'a>;
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
pub type ResponderIdListCombinatorAlias = Mapped<Pair<Refined<U16Le, Predicate2984462868727922620>, AndThen<bytes::Variable, Repeat<ResponderIdCombinator>>, ResponderIdListCont0>, ResponderIdListMapper>;


pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Le, predicate: Predicate2984462868727922620 }, |deps| spec_responder_id_list_cont0(deps)),
        mapper: ResponderIdListMapper,
    })
}

pub open spec fn spec_responder_id_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_responder_id()))
}

impl View for ResponderIdListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_responder_id_list_cont0(deps)
        }
    }
}

                
pub fn responder_id_list() -> (o: ResponderIdListCombinator)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Le, predicate: Predicate2984462868727922620 }, ResponderIdListCont0),
        mapper: ResponderIdListMapper,
    })
}

pub struct ResponderIdListCont0;
type ResponderIdListCont0Type<'a, 'b> = &'b u16;
type ResponderIdListCont0SType<'a, 'x> = &'x u16;
type ResponderIdListCont0Input<'a, 'b, 'x> = POrSType<ResponderIdListCont0Type<'a, 'b>, ResponderIdListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ResponderIdListCont0Input<'a, 'b, 'x>> for ResponderIdListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ResponderIdCombinator>>;

    open spec fn requires(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont0(deps@)
    }

    fn apply(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id()))
            }
        }
    }
}
                
pub type SpecRepeatFix = Seq<u16>;
pub type RepeatFix = RepeatResult<u16>;
pub type RepeatFixRef<'a> = &'a RepeatResult<u16>;


pub struct SpecRepeatFixCombinator(SpecRepeatFixCombinatorAlias);

impl SpecCombinator for SpecRepeatFixCombinator {
    type Type = SpecRepeatFix;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for RepeatFixCombinator {
    type Type = RepeatFix;
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
pub type RepeatFixCombinatorAlias = RepeatN<U16Le>;


pub closed spec fn spec_repeat_fix() -> SpecRepeatFixCombinator {
    SpecRepeatFixCombinator(RepeatN(U16Le, 32))
}

                
pub fn repeat_fix() -> (o: RepeatFixCombinator)
    ensures o@ == spec_repeat_fix(),
{
    RepeatFixCombinator(RepeatN(U16Le, 32))
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

pub type RepeatDynInnerRef<'a> = (&'a VarInt, &'a RepeatResult<ResponderIdList<'a>>);
impl<'a> From<&'a RepeatDyn<'a>> for RepeatDynInnerRef<'a> {
    fn ex_from(m: &'a RepeatDyn) -> RepeatDynInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<RepeatDynInner<'a>> for RepeatDyn<'a> {
    fn ex_from(m: RepeatDynInner) -> RepeatDyn {
        let (l, data) = m;
        RepeatDyn { l, data }
    }
}

pub struct RepeatDynMapper;
impl View for RepeatDynMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for RepeatDynMapper {
    type Src = SpecRepeatDynInner;
    type Dst = SpecRepeatDyn;
}
impl SpecIsoProof for RepeatDynMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for RepeatDynMapper {
    type Src = RepeatDynInner<'a>;
    type Dst = RepeatDyn<'a>;
    type RefSrc = RepeatDynInnerRef<'a>;
}

pub struct SpecRepeatDynCombinator(SpecRepeatDynCombinatorAlias);

impl SpecCombinator for SpecRepeatDynCombinator {
    type Type = SpecRepeatDyn;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecRepeatDynCombinatorAlias = Mapped<SpecPair<BtcVarint, RepeatN<SpecResponderIdListCombinator>>, RepeatDynMapper>;

pub struct RepeatDynCombinator(RepeatDynCombinatorAlias);

impl View for RepeatDynCombinator {
    type V = SpecRepeatDynCombinator;
    closed spec fn view(&self) -> Self::V { SpecRepeatDynCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for RepeatDynCombinator {
    type Type = RepeatDyn<'a>;
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
pub type RepeatDynCombinatorAlias = Mapped<Pair<BtcVarint, RepeatN<ResponderIdListCombinator>, RepeatDynCont0>, RepeatDynMapper>;


pub closed spec fn spec_repeat_dyn() -> SpecRepeatDynCombinator {
    SpecRepeatDynCombinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_repeat_dyn_cont0(deps)),
        mapper: RepeatDynMapper,
    })
}

pub open spec fn spec_repeat_dyn_cont0(deps: VarInt) -> RepeatN<SpecResponderIdListCombinator> {
    let l = deps;
    RepeatN(spec_responder_id_list(), l.spec_into())
}

impl View for RepeatDynCont0 {
    type V = spec_fn(VarInt) -> RepeatN<SpecResponderIdListCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_repeat_dyn_cont0(deps)
        }
    }
}

                
pub fn repeat_dyn() -> (o: RepeatDynCombinator)
    ensures o@ == spec_repeat_dyn(),
{
    RepeatDynCombinator(
    Mapped {
        inner: Pair::new(BtcVarint, RepeatDynCont0),
        mapper: RepeatDynMapper,
    })
}

pub struct RepeatDynCont0;
type RepeatDynCont0Type<'a, 'b> = &'b VarInt;
type RepeatDynCont0SType<'a, 'x> = &'x VarInt;
type RepeatDynCont0Input<'a, 'b, 'x> = POrSType<RepeatDynCont0Type<'a, 'b>, RepeatDynCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<RepeatDynCont0Input<'a, 'b, 'x>> for RepeatDynCont0 {
    type Output = RepeatN<ResponderIdListCombinator>;

    open spec fn requires(&self, deps: RepeatDynCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: RepeatDynCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_repeat_dyn_cont0(deps@)
    }

    fn apply(&self, deps: RepeatDynCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(responder_id_list(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(responder_id_list(), l.ex_into())
            }
        }
    }
}
                

}
