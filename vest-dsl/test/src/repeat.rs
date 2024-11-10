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

pub type SpecOpaqueU16Combinator = Mapped<
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

pub type OpaqueU16Combinator<'a> = Mapped<
    Depend<'a, Refined<U16Le, Predicate11955646336730306823>, Bytes, OpaqueU16Cont<'a>>,
    OpaqueU16Mapper<'a>,
>;

pub open spec fn spec_opaque_u16() -> SpecOpaqueU16Combinator {
    let fst = Refined { inner: U16Le, predicate: Predicate11955646336730306823 };
    let snd = |deps| spec_opaque_u16_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: OpaqueU16Mapper::spec_new() }
}

pub open spec fn spec_opaque_u16_cont(deps: u16) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

pub fn opaque_u16<'a>() -> (o: OpaqueU16Combinator<'a>)
    ensures
        o@ == spec_opaque_u16(),
{
    let fst = Refined { inner: U16Le, predicate: Predicate11955646336730306823 };
    let snd = OpaqueU16Cont::new();
    let spec_snd = Ghost(|deps| spec_opaque_u16_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: OpaqueU16Mapper::new() }
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

pub open spec fn parse_spec_opaque_u16(i: Seq<u8>) -> Result<(usize, SpecOpaqueU16), ()> {
    spec_opaque_u16().spec_parse(i)
}

pub open spec fn serialize_spec_opaque_u16(msg: SpecOpaqueU16) -> Result<Seq<u8>, ()> {
    spec_opaque_u16().spec_serialize(msg)
}

pub fn parse_opaque_u16(i: &[u8]) -> (o: Result<(usize, OpaqueU16<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_opaque_u16(i@) matches Ok(r_) && r@ == r_,
{
    let c = opaque_u16();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_opaque_u16(msg: OpaqueU16<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_opaque_u16(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = opaque_u16();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub type SpecResponderId = SpecOpaqueU16;

pub type ResponderId<'a> = OpaqueU16<'a>;

pub type SpecResponderIdCombinator = SpecOpaqueU16Combinator;

pub type ResponderIdCombinator<'a> = OpaqueU16Combinator<'a>;

pub open spec fn spec_responder_id() -> SpecResponderIdCombinator {
    spec_opaque_u16()
}

pub fn responder_id<'a>() -> (o: ResponderIdCombinator<'a>)
    ensures
        o@ == spec_responder_id(),
{
    opaque_u16()
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
    let c = responder_id();
    assert(c.parse_requires());
    c.parse(i)
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
    let c = responder_id();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub type SpecResponderIdListList = Seq<SpecResponderId>;

pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;

pub type SpecResponderIdListListCombinator = AndThen<Bytes, Repeat<SpecResponderIdCombinator>>;

pub type ResponderIdListListCombinator<'a> = AndThen<Bytes, Repeat<ResponderIdCombinator<'a>>>;

pub open spec fn spec_responder_id_list_list(l: u16) -> SpecResponderIdListListCombinator {
    AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id()))
}

pub fn responder_id_list_list<'a>(l: u16) -> (o: ResponderIdListListCombinator<'a>)
    ensures
        o@ == spec_responder_id_list_list(l@),
{
    AndThen(Bytes(l.ex_into()), Repeat(responder_id()))
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
    let c = responder_id_list_list(l);
    assert(c.parse_requires());
    c.parse(i)
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
    let c = responder_id_list_list(l);
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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

pub type SpecResponderIdListCombinator = Mapped<
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

pub type ResponderIdListCombinator<'a> = Mapped<
    Depend<
        'a,
        Refined<U16Le, Predicate6556550293019859977>,
        ResponderIdListListCombinator<'a>,
        ResponderIdListCont<'a>,
    >,
    ResponderIdListMapper<'a>,
>;

pub open spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    let fst = Refined { inner: U16Le, predicate: Predicate6556550293019859977 };
    let snd = |deps| spec_responder_id_list_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: ResponderIdListMapper::spec_new() }
}

pub open spec fn spec_responder_id_list_cont(deps: u16) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}

pub fn responder_id_list<'a>() -> (o: ResponderIdListCombinator<'a>)
    ensures
        o@ == spec_responder_id_list(),
{
    let fst = Refined { inner: U16Le, predicate: Predicate6556550293019859977 };
    let snd = ResponderIdListCont::new();
    let spec_snd = Ghost(|deps| spec_responder_id_list_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: ResponderIdListMapper::new() }
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
    let c = responder_id_list();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_responder_id_list(msg: ResponderIdList<'_>, data: &mut Vec<u8>, pos: usize) -> (o:
    Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_responder_id_list(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = responder_id_list();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

} // verus!
