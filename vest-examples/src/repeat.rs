#![allow(unused_imports)]
use std::marker::PhantomData;

use vest::properties::*;
use vest::regular::bytes;
use vest::regular::modifier::*;
use vest::regular::repetition::*;
use vest::regular::sequence::*;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::regular::variant::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

// Format for:
// ```vest
// opaque_u16_1 = {
//   @l: u16 | { 1..0xffff },
//   data: [u8; @l],
// }
//
// responder_id = opaque_u16_1
//
// responder_id_list = {
//   @l: u16 | { 0..0xffff },
//   list: [u8; @l] >>= Vec<responder_id>,
// }
// ```
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

#[derive(Debug, PartialEq, Eq)]
pub struct OpaqueU16<'a> {
    pub l: u16,
    pub data: &'a [u8],
}

pub type OpaqueU16Ref<'a> = &'a OpaqueU16<'a>;

pub type OpaqueU16Inner<'a> = (u16, &'a [u8]);

pub type OpaqueU16InnerRef<'a> = (&'a u16, &'a &'a [u8]);

impl View for OpaqueU16<'_> {
    type V = SpecOpaqueU16;

    open spec fn view(&self) -> Self::V {
        SpecOpaqueU16 { l: self.l@, data: self.data@ }
    }
}

impl<'a> From<OpaqueU16Ref<'a>> for OpaqueU16InnerRef<'a> {
    fn ex_from(m: OpaqueU16Ref<'a>) -> OpaqueU16InnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<OpaqueU16Inner<'a>> for OpaqueU16<'a> {
    fn ex_from(m: OpaqueU16Inner<'a>) -> OpaqueU16<'a> {
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso<'a> for OpaqueU16Mapper {
    type Src = OpaqueU16Inner<'a>;

    type Dst = OpaqueU16<'a>;

    type RefSrc = OpaqueU16InnerRef<'a>;
}

impl SpecPred<u16> for Predicate11955646336730306823 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
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
    type Type = SpecOpaqueU16;

    closed spec fn requires(&self) -> bool {
        self.0.requires()
    }

    closed spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl SecureSpecCombinator for SpecOpaqueU16Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecOpaqueU16CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.0.lemma_parse_length(s)
    }

    closed spec fn is_productive(&self) -> bool {
        self.0.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.0.lemma_parse_productive(s)
    }
}

pub type SpecOpaqueU16CombinatorAlias = Mapped<
    SpecPair<Refined<U16Le, Predicate11955646336730306823>, bytes::Variable>,
    OpaqueU16Mapper,
>;

pub struct Predicate11955646336730306823;

impl View for Predicate11955646336730306823 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred<u16> for Predicate11955646336730306823 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct OpaqueU16Combinator(OpaqueU16CombinatorAlias);

impl View for OpaqueU16Combinator {
    type V = SpecOpaqueU16Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecOpaqueU16Combinator(self.0@)
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OpaqueU16Combinator {
    type Type = OpaqueU16<'a>;

    type SType = OpaqueU16Ref<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn ex_requires(&self) -> bool {
        <_ as Combinator<&'a [u8], Vec<u8>>>::ex_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::parse(&self.0, s)
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type OpaqueU16CombinatorAlias = Mapped<
    Pair<Refined<U16Le, Predicate11955646336730306823>, bytes::Variable, OpaqueU16Cont>,
    OpaqueU16Mapper,
>;

pub closed spec fn spec_opaque_u16() -> SpecOpaqueU16Combinator {
    SpecOpaqueU16Combinator(
        Mapped {
            inner: Pair::spec_new(
                Refined { inner: U16Le, predicate: Predicate11955646336730306823 },
                |deps| spec_opaque_u16_cont(deps),
            ),
            mapper: OpaqueU16Mapper,
        },
    )
}

pub open spec fn spec_opaque_u16_cont(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

pub fn opaque_u16() -> (o: OpaqueU16Combinator)
    ensures
        o@ == spec_opaque_u16(),
{
    OpaqueU16Combinator(
        Mapped {
            inner: Pair::new(
                Refined { inner: U16Le, predicate: Predicate11955646336730306823 },
                OpaqueU16Cont,
            ),
            mapper: OpaqueU16Mapper,
        },
    )
}

pub struct OpaqueU16Cont;

impl View for OpaqueU16Cont {
    type V = spec_fn(u16) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps| spec_opaque_u16_cont(deps)
    }
}

impl<'a> Continuation<POrSType<&'a u16, &u16>> for OpaqueU16Cont {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: POrSType<&'a u16, &u16>) -> bool {
        true
    }

    open spec fn ensures(&self, deps: POrSType<&'a u16, &u16>, o: Self::Output) -> bool {
        o@ == spec_opaque_u16_cont(deps@)
    }

    fn apply(&self, deps: POrSType<&'a u16, &u16>) -> Self::Output {
        let deps = match deps {
            POrSType::P(deps) => deps,
            POrSType::S(deps) => deps,
        };
        let l = *deps;
        bytes::Variable(l.ex_into())
    }
}

pub type SpecResponderId = SpecOpaqueU16;

pub type ResponderId<'a> = OpaqueU16<'a>;

pub type ResponderIdRef<'a> = OpaqueU16Ref<'a>;

pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type Type = SpecResponderId;

    closed spec fn requires(&self) -> bool {
        self.0.requires()
    }

    closed spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.0.lemma_parse_length(s)
    }

    closed spec fn is_productive(&self) -> bool {
        self.0.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.0.lemma_parse_productive(s)
    }
}

pub type SpecResponderIdCombinatorAlias = SpecOpaqueU16Combinator;

pub struct ResponderIdCombinator(ResponderIdCombinatorAlias);

impl View for ResponderIdCombinator {
    type V = SpecResponderIdCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdCombinator(self.0@)
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdCombinator {
    type Type = ResponderId<'a>;

    type SType = ResponderIdRef<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn ex_requires(&self) -> bool {
        <_ as Combinator<&'a [u8], Vec<u8>>>::ex_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::parse(&self.0, s)
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdCombinatorAlias = OpaqueU16Combinator;

pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_u16())
}

pub fn responder_id<'a>() -> (o: ResponderIdCombinator)
    ensures
        o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_u16())
}

pub type SpecResponderIdListList = Seq<SpecResponderId>;

pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;

pub type ResponderIdListListRef<'a> = &'a RepeatResult<ResponderId<'a>>;

pub struct SpecResponderIdListListCombinator(SpecResponderIdListListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListListCombinator {
    type Type = SpecResponderIdListList;

    closed spec fn requires(&self) -> bool {
        self.0.requires()
    }

    closed spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl SecureSpecCombinator for SpecResponderIdListListCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdListListCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.0.lemma_parse_length(s)
    }

    closed spec fn is_productive(&self) -> bool {
        self.0.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.0.lemma_parse_productive(s)
    }
}

pub type SpecResponderIdListListCombinatorAlias = AndThen<
    bytes::Variable,
    Repeat<SpecResponderIdCombinator>,
>;

pub struct ResponderIdListListCombinator(ResponderIdListListCombinatorAlias);

impl<'a> View for ResponderIdListListCombinator {
    type V = SpecResponderIdListListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListListCombinator(self.0@)
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdListListCombinator {
    type Type = ResponderIdListList<'a>;

    type SType = ResponderIdListListRef<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn ex_requires(&self) -> bool {
        <_ as Combinator<&'a [u8], Vec<u8>>>::ex_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::parse(&self.0, s)
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdListListCombinatorAlias = AndThen<
    bytes::Variable,
    Repeat<ResponderIdCombinator>,
>;

pub closed spec fn spec_responder_id_list_list(l: u16) -> SpecResponderIdListListCombinator {
    SpecResponderIdListListCombinator(
        AndThen(bytes::Variable(l.spec_into()), Repeat(spec_responder_id())),
    )
}

pub fn responder_id_list_list<'a>(l: u16) -> (o: ResponderIdListListCombinator)
    ensures
        o@ == spec_responder_id_list_list(l@),
{
    ResponderIdListListCombinator(
        AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id())),
    )
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

#[derive(Debug, PartialEq, Eq)]
pub struct ResponderIdList<'a> {
    pub l: u16,
    pub list: ResponderIdListList<'a>,
}

pub type ResponderIdListRef<'a> = &'a ResponderIdList<'a>;

pub type ResponderIdListInner<'a> = (u16, ResponderIdListList<'a>);

pub type ResponderIdListInnerRef<'a> = (&'a u16, ResponderIdListListRef<'a>);

impl View for ResponderIdList<'_> {
    type V = SpecResponderIdList;

    open spec fn view(&self) -> Self::V {
        SpecResponderIdList { l: self.l@, list: self.list@ }
    }
}

impl<'a> From<ResponderIdListRef<'a>> for ResponderIdListInnerRef<'a> {
    fn ex_from(m: ResponderIdListRef<'a>) -> ResponderIdListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner<'a>) -> ResponderIdList<'a> {
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso<'a> for ResponderIdListMapper {
    type Src = ResponderIdListInner<'a>;

    type Dst = ResponderIdList<'a>;

    type RefSrc = ResponderIdListInnerRef<'a>;
}

impl SpecPred<u16> for Predicate6556550293019859977 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
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
    type Type = SpecResponderIdList;

    closed spec fn requires(&self) -> bool {
        self.0.requires()
    }

    closed spec fn wf(&self, v: Self::Type) -> bool {
        self.0.wf(v)
    }

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        self.0.spec_serialize(v)
    }
}

impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecResponderIdListCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.0.lemma_parse_length(s)
    }

    closed spec fn is_productive(&self) -> bool {
        self.0.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.0.lemma_parse_productive(s)
    }
}

pub type SpecResponderIdListCombinatorAlias = Mapped<
    SpecPair<Refined<U16Le, Predicate6556550293019859977>, SpecResponderIdListListCombinator>,
    ResponderIdListMapper,
>;

pub struct Predicate6556550293019859977;

impl View for Predicate6556550293019859977 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred<u16> for Predicate6556550293019859977 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct ResponderIdListCombinator(ResponderIdListCombinatorAlias);

impl View for ResponderIdListCombinator {
    type V = SpecResponderIdListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListCombinator(self.0@)
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdListCombinator {
    type Type = ResponderIdList<'a>;

    type SType = ResponderIdListRef<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&'a [u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn ex_requires(&self) -> bool {
        <_ as Combinator<&'a [u8], Vec<u8>>>::ex_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::parse(&self.0, s)
    }

    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ResponderIdListCombinatorAlias = Mapped<
    Pair<
        Refined<U16Le, Predicate6556550293019859977>,
        ResponderIdListListCombinator,
        ResponderIdListCont,
    >,
    ResponderIdListMapper,
>;

pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
        Mapped {
            inner: SpecPair::spec_new(
                Refined { inner: U16Le, predicate: Predicate6556550293019859977 },
                |deps| spec_responder_id_list_cont(deps),
            ),
            mapper: ResponderIdListMapper,
        },
    )
}

pub open spec fn spec_responder_id_list_cont(deps: u16) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}

pub fn responder_id_list() -> (o: ResponderIdListCombinator)
    ensures
        o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
        Mapped {
            inner: Pair::new(
                Refined { inner: U16Le, predicate: Predicate6556550293019859977 },
                ResponderIdListCont,
            ),
            mapper: ResponderIdListMapper,
        },
    )
}

pub struct ResponderIdListCont;

impl View for ResponderIdListCont {
    type V = spec_fn(u16) -> SpecResponderIdListListCombinator;

    open spec fn view(&self) -> Self::V {
        |deps| spec_responder_id_list_cont(deps)
    }
}

impl<'a> Continuation<POrSType<&'a u16, &u16>> for ResponderIdListCont {
    type Output = ResponderIdListListCombinator;

    open spec fn requires(&self, deps: POrSType<&'a u16, &u16>) -> bool {
        true
    }

    open spec fn ensures(&self, deps: POrSType<&'a u16, &u16>, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont(deps@)
    }

    fn apply(&self, deps: POrSType<&'a u16, &u16>) -> Self::Output {
        let deps = match deps {
            POrSType::P(deps) => deps,
            POrSType::S(deps) => deps,
        };
        let l = *deps;
        responder_id_list_list(l)
    }
}

// fn test_comb(ibuf: &[u8], obuf: &mut Vec<u8>) {
//     if let Ok((n, v)) = responder_id_list().parse(ibuf) {
//         let len = responder_id_list().serialize(&v, obuf, 0);
//     }
// }
} // verus!
