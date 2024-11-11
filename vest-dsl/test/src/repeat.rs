#![allow(unused_imports)]
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

pub struct SpecOpaqueU161 {
    pub l: u16,
    pub data: Seq<u8>,
}

pub type SpecOpaqueU161Inner = (u16, Seq<u8>);

impl SpecFrom<SpecOpaqueU161> for SpecOpaqueU161Inner {
    open spec fn spec_from(m: SpecOpaqueU161) -> SpecOpaqueU161Inner {
        (m.l, m.data)
    }
}

impl SpecFrom<SpecOpaqueU161Inner> for SpecOpaqueU161 {
    open spec fn spec_from(m: SpecOpaqueU161Inner) -> SpecOpaqueU161 {
        let (l, data) = m;
        SpecOpaqueU161 { l, data }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueU161<'a> {
    pub l: u16,
    pub data: &'a [u8],
}

pub type OpaqueU161Inner<'a> = (u16, &'a [u8]);

impl View for OpaqueU161<'_> {
    type V = SpecOpaqueU161;

    open spec fn view(&self) -> Self::V {
        SpecOpaqueU161 { l: self.l@, data: self.data@ }
    }
}

impl<'a> From<OpaqueU161<'a>> for OpaqueU161Inner<'a> {
    fn ex_from(m: OpaqueU161<'a>) -> OpaqueU161Inner<'a> {
        (m.l, m.data)
    }
}

impl<'a> From<OpaqueU161Inner<'a>> for OpaqueU161<'a> {
    fn ex_from(m: OpaqueU161Inner<'a>) -> OpaqueU161<'a> {
        let (l, data) = m;
        OpaqueU161 { l, data }
    }
}

pub struct OpaqueU161Mapper;

impl View for OpaqueU161Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for OpaqueU161Mapper {
    type Src = SpecOpaqueU161Inner;

    type Dst = SpecOpaqueU161;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for OpaqueU161Mapper {
    type Src<'a> = OpaqueU161Inner<'a>;

    type Dst<'a> = OpaqueU161<'a>;

    type SrcOwned = OpaqueU161OwnedInner;

    type DstOwned = OpaqueU161Owned;
}

pub struct OpaqueU161Owned {
    pub l: u16,
    pub data: Vec<u8>,
}

pub type OpaqueU161OwnedInner = (u16, Vec<u8>);

impl View for OpaqueU161Owned {
    type V = SpecOpaqueU161;

    open spec fn view(&self) -> Self::V {
        SpecOpaqueU161 { l: self.l@, data: self.data@ }
    }
}

impl From<OpaqueU161Owned> for OpaqueU161OwnedInner {
    fn ex_from(m: OpaqueU161Owned) -> OpaqueU161OwnedInner {
        (m.l, m.data)
    }
}

impl From<OpaqueU161OwnedInner> for OpaqueU161Owned {
    fn ex_from(m: OpaqueU161OwnedInner) -> OpaqueU161Owned {
        let (l, data) = m;
        OpaqueU161Owned { l, data }
    }
}

pub type SpecResponderId = SpecOpaqueU161;

pub type ResponderId<'a> = OpaqueU161<'a>;

pub type ResponderIdOwned = OpaqueU161Owned;

pub type SpecResponderIdListList = Seq<SpecResponderId>;

pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;

pub type ResponderIdListListOwned = RepeatResult<ResponderIdOwned>;

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

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for ResponderIdListMapper {
    type Src<'a> = ResponderIdListInner<'a>;

    type Dst<'a> = ResponderIdList<'a>;

    type SrcOwned = ResponderIdListOwnedInner;

    type DstOwned = ResponderIdListOwned;
}

pub struct ResponderIdListOwned {
    pub l: u16,
    pub list: ResponderIdListListOwned,
}

pub type ResponderIdListOwnedInner = (u16, ResponderIdListListOwned);

impl View for ResponderIdListOwned {
    type V = SpecResponderIdList;

    open spec fn view(&self) -> Self::V {
        SpecResponderIdList { l: self.l@, list: self.list@ }
    }
}

impl From<ResponderIdListOwned> for ResponderIdListOwnedInner {
    fn ex_from(m: ResponderIdListOwned) -> ResponderIdListOwnedInner {
        (m.l, m.list)
    }
}

impl From<ResponderIdListOwnedInner> for ResponderIdListOwned {
    fn ex_from(m: ResponderIdListOwnedInner) -> ResponderIdListOwned {
        let (l, list) = m;
        ResponderIdListOwned { l, list }
    }
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

pub struct SpecOpaqueU161Combinator(
    Mapped<SpecDepend<Refined<U16Le, Predicate11955646336730306823>, Bytes>, OpaqueU161Mapper>,
);

impl SpecCombinator for SpecOpaqueU161Combinator {
    type SpecResult = SpecOpaqueU161;

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

impl SecureSpecCombinator for SpecOpaqueU161Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecOpaqueU161CombinatorAlias::is_prefix_secure()
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

pub type SpecOpaqueU161CombinatorAlias = Mapped<
    SpecDepend<Refined<U16Le, Predicate11955646336730306823>, Bytes>,
    OpaqueU161Mapper,
>;

pub struct Predicate11955646336730306823;

impl View for Predicate11955646336730306823 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate11955646336730306823 {
    type Input<'a> = u16;

    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct OpaqueU161Cont;

pub struct OpaqueU161Combinator(
    Mapped<
        Depend<Refined<U16Le, Predicate11955646336730306823>, Bytes, OpaqueU161Cont>,
        OpaqueU161Mapper,
    >,
);

impl View for OpaqueU161Combinator {
    type V = SpecOpaqueU161Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecOpaqueU161Combinator(self.0@)
    }
}

impl Combinator for OpaqueU161Combinator {
    type Result<'a> = OpaqueU161<'a>;

    type Owned = OpaqueU161Owned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type OpaqueU161CombinatorAlias = Mapped<
    Depend<Refined<U16Le, Predicate11955646336730306823>, Bytes, OpaqueU161Cont>,
    OpaqueU161Mapper,
>;

pub struct SpecResponderIdCombinator(SpecOpaqueU161Combinator);

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

pub type SpecResponderIdCombinatorAlias = SpecOpaqueU161Combinator;

pub struct ResponderIdCombinator(OpaqueU161Combinator);

impl View for ResponderIdCombinator {
    type V = SpecResponderIdCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdCombinator(self.0@)
    }
}

impl Combinator for ResponderIdCombinator {
    type Result<'a> = ResponderId<'a>;

    type Owned = ResponderIdOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ResponderIdCombinatorAlias = OpaqueU161Combinator;

pub struct SpecResponderIdListListCombinator(AndThen<Bytes, Repeat<SpecResponderIdCombinator>>);

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

pub struct ResponderIdListListCombinator(AndThen<Bytes, Repeat<ResponderIdCombinator>>);

impl View for ResponderIdListListCombinator {
    type V = SpecResponderIdListListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListListCombinator(self.0@)
    }
}

impl Combinator for ResponderIdListListCombinator {
    type Result<'a> = ResponderIdListList<'a>;

    type Owned = ResponderIdListListOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ResponderIdListListCombinatorAlias = AndThen<Bytes, Repeat<ResponderIdCombinator>>;

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

pub struct SpecResponderIdListCombinator(
    Mapped<
        SpecDepend<Refined<U16Le, Predicate6556550293019859977>, SpecResponderIdListListCombinator>,
        ResponderIdListMapper,
    >,
);

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
    ResponderIdListMapper,
>;

pub struct Predicate6556550293019859977;

impl View for Predicate6556550293019859977 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate6556550293019859977 {
    type Input<'a> = u16;

    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct ResponderIdListCont;

pub struct ResponderIdListCombinator(
    Mapped<
        Depend<
            Refined<U16Le, Predicate6556550293019859977>,
            ResponderIdListListCombinator,
            ResponderIdListCont,
        >,
        ResponderIdListMapper,
    >,
);

impl View for ResponderIdListCombinator {
    type V = SpecResponderIdListCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecResponderIdListCombinator(self.0@)
    }
}

impl Combinator for ResponderIdListCombinator {
    type Result<'a> = ResponderIdList<'a>;

    type Owned = ResponderIdListOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ResponderIdListCombinatorAlias = Mapped<
    Depend<
        Refined<U16Le, Predicate6556550293019859977>,
        ResponderIdListListCombinator,
        ResponderIdListCont,
    >,
    ResponderIdListMapper,
>;

pub closed spec fn spec_opaque_u16_1() -> SpecOpaqueU161Combinator {
    let fst = Refined { inner: U16Le, predicate: Predicate11955646336730306823 };
    let snd = |deps| spec_opaque_u161_cont(deps);
    SpecOpaqueU161Combinator(Mapped { inner: SpecDepend { fst, snd }, mapper: OpaqueU161Mapper })
}

pub open spec fn spec_opaque_u161_cont(deps: u16) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

pub fn opaque_u16_1() -> (o: OpaqueU161Combinator)
    ensures
        o@ == spec_opaque_u16_1(),
{
    let fst = Refined { inner: U16Le, predicate: Predicate11955646336730306823 };
    let snd = OpaqueU161Cont;
    let spec_snd = Ghost(|deps| spec_opaque_u161_cont(deps));
    OpaqueU161Combinator(Mapped { inner: Depend { fst, snd, spec_snd }, mapper: OpaqueU161Mapper })
}

impl Continuation<u16> for OpaqueU161Cont {
    type Output = Bytes;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_opaque_u161_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}

pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_u16_1())
}

pub fn responder_id() -> (o: ResponderIdCombinator)
    ensures
        o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_u16_1())
}

pub closed spec fn spec_responder_id_list_list(l: u16) -> SpecResponderIdListListCombinator {
    SpecResponderIdListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id())))
}

pub fn responder_id_list_list<'a>(l: u16) -> (o: ResponderIdListListCombinator)
    ensures
        o@ == spec_responder_id_list_list(l@),
{
    ResponderIdListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(responder_id())))
}

pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    let fst = Refined { inner: U16Le, predicate: Predicate6556550293019859977 };
    let snd = |deps| spec_responder_id_list_cont(deps);
    SpecResponderIdListCombinator(
        Mapped { inner: SpecDepend { fst, snd }, mapper: ResponderIdListMapper },
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
    let fst = Refined { inner: U16Le, predicate: Predicate6556550293019859977 };
    let snd = ResponderIdListCont;
    let spec_snd = Ghost(|deps| spec_responder_id_list_cont(deps));
    ResponderIdListCombinator(
        Mapped { inner: Depend { fst, snd, spec_snd }, mapper: ResponderIdListMapper },
    )
}

impl Continuation<u16> for ResponderIdListCont {
    type Output = ResponderIdListListCombinator;

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
