#![allow(unused_imports)]
use std::marker::PhantomData;
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

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

pub type OpaqueU16Inner<'a> = (u16, &'a [u8]);

impl View for OpaqueU16<'_> {
    type V = SpecOpaqueU16;

    open spec fn view(&self) -> Self::V {
        SpecOpaqueU16 { l: self.l@, data: self.data@ }
    }
}

impl<'a> From<OpaqueU16<'a>> for OpaqueU16Inner<'a> {
    fn ex_from(m: OpaqueU16<'a>) -> OpaqueU16Inner<'a> {
        (m.l, m.data)
    }
}

impl<'a> From<OpaqueU16Inner<'a>> for OpaqueU16<'a> {
    fn ex_from(m: OpaqueU16Inner<'a>) -> OpaqueU16<'a> {
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

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for OpaqueU16Mapper<'a> {
    type Src = OpaqueU16Inner<'a>;

    type Dst = OpaqueU16<'a>;
}

impl SpecPred for Predicate11955646336730306823 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecOpaqueU16Combinator(SpecOpaqueU16CombinatorAlias);

impl SpecCombinator for SpecOpaqueU16Combinator {
    type SpecResult = SpecOpaqueU16;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecOpaqueU16Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecOpaqueU16CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecOpaqueU16CombinatorAlias = Mapped<
    SpecDepend<Refined<U16Le, Predicate11955646336730306823>, Bytes>,
    OpaqueU16Mapper<'static>,
>;

pub struct Predicate11955646336730306823;

impl View for Predicate11955646336730306823 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate11955646336730306823 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct OpaqueU16Combinator<'a>(OpaqueU16CombinatorAlias<'a>);

impl<'a> View for OpaqueU16Combinator<'a> {
    type V = SpecOpaqueU16Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecOpaqueU16Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for OpaqueU16Combinator<'a> {
    type Result = OpaqueU16<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type OpaqueU16CombinatorAlias<'a> = Mapped<
    Depend<
        &'a [u8],
        Vec<u8>,
        Refined<U16Le, Predicate11955646336730306823>,
        Bytes,
        OpaqueU16Cont<'a>,
    >,
    OpaqueU16Mapper<'a>,
>;

pub closed spec fn spec_opaque_u16() -> SpecOpaqueU16Combinator {
    SpecOpaqueU16Combinator(
        Mapped {
            inner: SpecDepend {
                fst: Refined { inner: U16Le, predicate: Predicate11955646336730306823 },
                snd: |deps| spec_opaque_u16_cont(deps),
            },
            mapper: OpaqueU16Mapper::spec_new(),
        },
    )
}

pub open spec fn spec_opaque_u16_cont(deps: u16) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

pub fn opaque_u16<'a>() -> (o: OpaqueU16Combinator<'a>)
    ensures
        o@ == spec_opaque_u16(),
{
    OpaqueU16Combinator(
        Mapped {
            inner: Depend {
                fst: Refined { inner: U16Le, predicate: Predicate11955646336730306823 },
                snd: OpaqueU16Cont::new(),
                spec_snd: Ghost(|deps| spec_opaque_u16_cont(deps)),
            },
            mapper: OpaqueU16Mapper::new(),
        },
    )
}

pub struct OpaqueU16Cont<'a>(PhantomData<&'a ()>);

impl<'a> OpaqueU16Cont<'a> {
    pub fn new() -> Self {
        OpaqueU16Cont(PhantomData)
    }
}

impl<'a> Continuation<u16> for OpaqueU16Cont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_opaque_u16_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}

pub type SpecResponderId = SpecOpaqueU16;

pub type ResponderId<'a> = OpaqueU16<'a>;

pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type SpecResult = SpecResponderId;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecResponderIdCombinatorAlias = SpecOpaqueU16Combinator;

pub struct ResponderIdCombinator<'a>(ResponderIdCombinatorAlias<'a>);

impl<'a> View for ResponderIdCombinator<'a> {
    type V = SpecResponderIdCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdCombinator<'a> {
    type Result = ResponderId<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdCombinatorAlias<'a> = OpaqueU16Combinator<'a>;

pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_u16())
}

pub fn responder_id<'a>() -> (o: ResponderIdCombinator<'a>)
    ensures
        o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_u16())
}

pub type SpecResponderIdListList = Seq<SpecResponderId>;

pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;

pub struct SpecResponderIdListListCombinator(SpecResponderIdListListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListListCombinator {
    type SpecResult = SpecResponderIdListList;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecResponderIdListListCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdListListCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecResponderIdListListCombinatorAlias = AndThen<Bytes, Repeat<SpecResponderIdCombinator>>;

pub struct ResponderIdListListCombinator<'a>(ResponderIdListListCombinatorAlias<'a>);

impl<'a> View for ResponderIdListListCombinator<'a> {
    type V = SpecResponderIdListListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListListCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdListListCombinator<'a> {
    type Result = ResponderIdListList<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<ResponderIdCombinator<'a>>>;

pub closed spec fn spec_responder_id_list_list(l: u16) -> SpecResponderIdListListCombinator {
    SpecResponderIdListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id())))
}

pub fn responder_id_list_list<'a>(l: u16) -> (o: ResponderIdListListCombinator<'a>)
    ensures
        o@ == spec_responder_id_list_list(l@),
{
    ResponderIdListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(responder_id())))
}

pub struct SpecResponderIdList {
    pub l: u16,
    pub list: SpecResponderIdListList,
}

pub type SpecResponderIdListInner = (u16, SpecResponderIdListList);

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
    pub list: ResponderIdListList<'a>,
}

pub type ResponderIdListInner<'a> = (u16, ResponderIdListList<'a>);

impl View for ResponderIdList<'_> {
    type V = SpecResponderIdList;

    open spec fn view(&self) -> Self::V {
        SpecResponderIdList { l: self.l@, list: self.list@ }
    }
}

impl<'a> From<ResponderIdList<'a>> for ResponderIdListInner<'a> {
    fn ex_from(m: ResponderIdList<'a>) -> ResponderIdListInner<'a> {
        (m.l, m.list)
    }
}

impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner<'a>) -> ResponderIdList<'a> {
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

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for ResponderIdListMapper<'a> {
    type Src = ResponderIdListInner<'a>;

    type Dst = ResponderIdList<'a>;
}

impl SpecPred for Predicate6556550293019859977 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecResponderIdListCombinator(SpecResponderIdListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListCombinator {
    type SpecResult = SpecResponderIdList;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdListCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecResponderIdListCombinatorAlias = Mapped<
    SpecDepend<Refined<U16Le, Predicate6556550293019859977>, SpecResponderIdListListCombinator>,
    ResponderIdListMapper<'static>,
>;

pub struct Predicate6556550293019859977;

impl View for Predicate6556550293019859977 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate6556550293019859977 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct ResponderIdListCombinator<'a>(ResponderIdListCombinatorAlias<'a>);

impl<'a> View for ResponderIdListCombinator<'a> {
    type V = SpecResponderIdListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdListCombinator<'a> {
    type Result = ResponderIdList<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdListCombinatorAlias<'a> = Mapped<
    Depend<
        &'a [u8],
        Vec<u8>,
        Refined<U16Le, Predicate6556550293019859977>,
        ResponderIdListListCombinator<'a>,
        ResponderIdListCont<'a>,
    >,
    ResponderIdListMapper<'a>,
>;

pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
        Mapped {
            inner: SpecDepend {
                fst: Refined { inner: U16Le, predicate: Predicate6556550293019859977 },
                snd: |deps| spec_responder_id_list_cont(deps),
            },
            mapper: ResponderIdListMapper::spec_new(),
        },
    )
}

pub open spec fn spec_responder_id_list_cont(deps: u16) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}

pub fn responder_id_list<'a>() -> (o: ResponderIdListCombinator<'a>)
    ensures
        o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
        Mapped {
            inner: Depend {
                fst: Refined { inner: U16Le, predicate: Predicate6556550293019859977 },
                snd: ResponderIdListCont::new(),
                spec_snd: Ghost(|deps| spec_responder_id_list_cont(deps)),
            },
            mapper: ResponderIdListMapper::new(),
        },
    )
}

pub struct ResponderIdListCont<'a>(PhantomData<&'a ()>);

impl<'a> ResponderIdListCont<'a> {
    pub fn new() -> Self {
        ResponderIdListCont(PhantomData)
    }
}

impl<'a> Continuation<u16> for ResponderIdListCont<'a> {
    type Output = ResponderIdListListCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        responder_id_list_list(l)
    }
}

} // verus!
