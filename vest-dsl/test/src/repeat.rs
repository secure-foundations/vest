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

pub type SpecOpaqueU161Combinator = Mapped<
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

pub type OpaqueU161Combinator = Mapped<
    Depend<Refined<U16Le, Predicate11955646336730306823>, Bytes, OpaqueU161Cont>,
    OpaqueU161Mapper,
>;

pub type SpecResponderIdCombinator = SpecOpaqueU161Combinator;

pub type ResponderIdCombinator = OpaqueU161Combinator;

pub type SpecResponderIdListListCombinator = AndThen<Bytes, Repeat<SpecResponderIdCombinator>>;

pub type ResponderIdListListCombinator = AndThen<Bytes, Repeat<ResponderIdCombinator>>;

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

pub type SpecResponderIdListCombinator = Mapped<
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

pub type ResponderIdListCombinator = Mapped<
    Depend<
        Refined<U16Le, Predicate6556550293019859977>,
        ResponderIdListListCombinator,
        ResponderIdListCont,
    >,
    ResponderIdListMapper,
>;

pub open spec fn spec_opaque_u16_1() -> SpecOpaqueU161Combinator {
    let fst = Refined { inner: U16Le, predicate: Predicate11955646336730306823 };
    let snd = |deps| spec_opaque_u161_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: OpaqueU161Mapper }
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
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: OpaqueU161Mapper }
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

pub open spec fn spec_responder_id() -> SpecResponderIdCombinator {
    spec_opaque_u16_1()
}

pub fn responder_id() -> (o: ResponderIdCombinator)
    ensures
        o@ == spec_responder_id(),
{
    opaque_u16_1()
}

pub open spec fn spec_responder_id_list_list(l: u16) -> SpecResponderIdListListCombinator {
    AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id()))
}

pub fn responder_id_list_list<'a>(l: u16) -> (o: ResponderIdListListCombinator)
    ensures
        o@ == spec_responder_id_list_list(l@),
{
    AndThen(Bytes(l.ex_into()), Repeat(responder_id()))
}

pub open spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    let fst = Refined { inner: U16Le, predicate: Predicate6556550293019859977 };
    let snd = |deps| spec_responder_id_list_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: ResponderIdListMapper }
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
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: ResponderIdListMapper }
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

pub open spec fn parse_spec_opaque_u16_1(i: Seq<u8>) -> Result<(usize, SpecOpaqueU161), ()> {
    spec_opaque_u16_1().spec_parse(i)
}

pub open spec fn serialize_spec_opaque_u16_1(msg: SpecOpaqueU161) -> Result<Seq<u8>, ()> {
    spec_opaque_u16_1().spec_serialize(msg)
}

pub fn parse_opaque_u16_1(i: &[u8]) -> (o: Result<(usize, OpaqueU161<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_opaque_u16_1(i@) matches Ok(r_) && r@ == r_,
{
    opaque_u16_1().parse(i)
}

pub fn serialize_opaque_u16_1(msg: OpaqueU161<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_opaque_u16_1(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    opaque_u16_1().serialize(msg, data, pos)
}

pub open spec fn parse_spec_responder_id(i: Seq<u8>) -> Result<(usize, SpecResponderId), ()> {
    spec_responder_id().spec_parse(i)
}

pub open spec fn serialize_spec_responder_id(msg: SpecResponderId) -> Result<Seq<u8>, ()> {
    spec_responder_id().spec_serialize(msg)
}

pub fn parse_responder_id(i: &[u8]) -> (o: Result<(usize, ResponderId<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_responder_id(i@) matches Ok(r_) && r@ == r_,
{
    responder_id().parse(i)
}

pub fn serialize_responder_id(msg: ResponderId<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_responder_id(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    responder_id().serialize(msg, data, pos)
}

pub open spec fn parse_spec_responder_id_list_list(i: Seq<u8>, l: u16) -> Result<
    (usize, SpecResponderIdListList),
    (),
> {
    spec_responder_id_list_list(l).spec_parse(i)
}

pub open spec fn serialize_spec_responder_id_list_list(
    msg: SpecResponderIdListList,
    l: u16,
) -> Result<Seq<u8>, ()> {
    spec_responder_id_list_list(l).spec_serialize(msg)
}

pub fn parse_responder_id_list_list(i: &[u8], l: u16) -> (o: Result<
    (usize, ResponderIdListList<'_>),
    ParseError,
>)
    ensures
        o matches Ok(r) ==> parse_spec_responder_id_list_list(i@, l@) matches Ok(r_) && r@ == r_,
{
    responder_id_list_list(l).parse(i)
}

pub fn serialize_responder_id_list_list(
    msg: ResponderIdListList<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    l: u16,
) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_responder_id_list_list(msg@, l@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    responder_id_list_list(l).serialize(msg, data, pos)
}

pub open spec fn parse_spec_responder_id_list(i: Seq<u8>) -> Result<
    (usize, SpecResponderIdList),
    (),
> {
    spec_responder_id_list().spec_parse(i)
}

pub open spec fn serialize_spec_responder_id_list(msg: SpecResponderIdList) -> Result<Seq<u8>, ()> {
    spec_responder_id_list().spec_serialize(msg)
}

pub fn parse_responder_id_list(i: &[u8]) -> (o: Result<(usize, ResponderIdList<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_responder_id_list(i@) matches Ok(r_) && r@ == r_,
{
    responder_id_list().parse(i)
}

pub fn serialize_responder_id_list(msg: ResponderIdList<'_>, data: &mut Vec<u8>, pos: usize) -> (o:
    Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_responder_id_list(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    responder_id_list().serialize(msg, data, pos)
}

} // verus!
