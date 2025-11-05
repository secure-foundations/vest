
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest_lib::regular::modifier::*;
use vest_lib::regular::bytes;
use vest_lib::regular::variant::*;
use vest_lib::regular::sequence::*;
use vest_lib::regular::repetition::*;
use vest_lib::regular::disjoint::DisjointFrom;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::utils::*;
use vest_lib::properties::*;
use vest_lib::bitcoin::varint::{BtcVarint, VarInt};
use vest_lib::regular::leb128::*;

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

pub spec const SPEC_ProtocolMagic_MavLink1: u8 = 254;
pub spec const SPEC_ProtocolMagic_MavLink2: u8 = 253;
pub exec static EXEC_ProtocolMagic_MavLink1: u8 ensures EXEC_ProtocolMagic_MavLink1 == SPEC_ProtocolMagic_MavLink1 { 254 }
pub exec static EXEC_ProtocolMagic_MavLink2: u8 ensures EXEC_ProtocolMagic_MavLink2 == SPEC_ProtocolMagic_MavLink2 { 253 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProtocolMagic {
    MavLink1 = 254,
MavLink2 = 253
}
pub type SpecProtocolMagic = ProtocolMagic;

pub type ProtocolMagicInner = u8;

pub type ProtocolMagicInnerRef<'a> = &'a u8;

impl View for ProtocolMagic {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ProtocolMagicInner> for ProtocolMagic {
    type Error = ();

    open spec fn spec_try_from(v: ProtocolMagicInner) -> Result<ProtocolMagic, ()> {
        match v {
            254u8 => Ok(ProtocolMagic::MavLink1),
            253u8 => Ok(ProtocolMagic::MavLink2),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<ProtocolMagic> for ProtocolMagicInner {
    type Error = ();

    open spec fn spec_try_from(v: ProtocolMagic) -> Result<ProtocolMagicInner, ()> {
        match v {
            ProtocolMagic::MavLink1 => Ok(SPEC_ProtocolMagic_MavLink1),
            ProtocolMagic::MavLink2 => Ok(SPEC_ProtocolMagic_MavLink2),
        }
    }
}

impl TryFrom<ProtocolMagicInner> for ProtocolMagic {
    type Error = ();

    fn ex_try_from(v: ProtocolMagicInner) -> Result<ProtocolMagic, ()> {
        match v {
            254u8 => Ok(ProtocolMagic::MavLink1),
            253u8 => Ok(ProtocolMagic::MavLink2),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a ProtocolMagic> for ProtocolMagicInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a ProtocolMagic) -> Result<ProtocolMagicInnerRef<'a>, ()> {
        match v {
            ProtocolMagic::MavLink1 => Ok(&EXEC_ProtocolMagic_MavLink1),
            ProtocolMagic::MavLink2 => Ok(&EXEC_ProtocolMagic_MavLink2),
        }
    }
}

pub struct ProtocolMagicMapper;

impl View for ProtocolMagicMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for ProtocolMagicMapper {
    type Src = ProtocolMagicInner;
    type Dst = ProtocolMagic;
}

impl SpecPartialIsoProof for ProtocolMagicMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl<'a> PartialIso<'a> for ProtocolMagicMapper {
    type Src = ProtocolMagicInner;
    type Dst = ProtocolMagic;
    type RefSrc = ProtocolMagicInnerRef<'a>;
}


pub struct SpecProtocolMagicCombinator(pub SpecProtocolMagicCombinatorAlias);

impl SpecCombinator for SpecProtocolMagicCombinator {
    type Type = SpecProtocolMagic;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProtocolMagicCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolMagicCombinatorAlias::is_prefix_secure() }
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
pub type SpecProtocolMagicCombinatorAlias = TryMap<U8, ProtocolMagicMapper>;

pub struct ProtocolMagicCombinator(pub ProtocolMagicCombinatorAlias);

impl View for ProtocolMagicCombinator {
    type V = SpecProtocolMagicCombinator;
    open spec fn view(&self) -> Self::V { SpecProtocolMagicCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProtocolMagicCombinator {
    type Type = ProtocolMagic;
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
pub type ProtocolMagicCombinatorAlias = TryMap<U8, ProtocolMagicMapper>;


pub open spec fn spec_protocol_magic() -> SpecProtocolMagicCombinator {
    SpecProtocolMagicCombinator(TryMap { inner: U8, mapper: ProtocolMagicMapper })
}

                
pub fn protocol_magic<'a>() -> (o: ProtocolMagicCombinator)
    ensures o@ == spec_protocol_magic(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProtocolMagicCombinator(TryMap { inner: U8, mapper: ProtocolMagicMapper });
    assert({
        &&& combinator@ == spec_protocol_magic()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_protocol_magic<'a>(input: &'a [u8]) -> (res: PResult<<ProtocolMagicCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_protocol_magic().spec_parse(input@) == Some((n as int, v@)),
        spec_protocol_magic().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_protocol_magic().spec_parse(input@) is None,
        spec_protocol_magic().spec_parse(input@) is None ==> res is Err,
{
    let combinator = protocol_magic();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_protocol_magic<'a>(v: <ProtocolMagicCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_protocol_magic().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_protocol_magic().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_protocol_magic().spec_serialize(v@))
        },
{
    let combinator = protocol_magic();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn protocol_magic_len<'a>(v: <ProtocolMagicCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_protocol_magic().wf(v@),
        spec_protocol_magic().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_protocol_magic().spec_serialize(v@).len(),
{
    let combinator = protocol_magic();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecMavlinkV1Msg {
    pub len: u8,
    pub seq: u8,
    pub sysid: u8,
    pub compid: u8,
    pub msgid: u8,
    pub payload: Seq<u8>,
    pub checksum: u16,
}

pub type SpecMavlinkV1MsgInner = (u8, (u8, (u8, (u8, (u8, (Seq<u8>, u16))))));


impl SpecFrom<SpecMavlinkV1Msg> for SpecMavlinkV1MsgInner {
    open spec fn spec_from(m: SpecMavlinkV1Msg) -> SpecMavlinkV1MsgInner {
        (m.len, (m.seq, (m.sysid, (m.compid, (m.msgid, (m.payload, m.checksum))))))
    }
}

impl SpecFrom<SpecMavlinkV1MsgInner> for SpecMavlinkV1Msg {
    open spec fn spec_from(m: SpecMavlinkV1MsgInner) -> SpecMavlinkV1Msg {
        let (len, (seq, (sysid, (compid, (msgid, (payload, checksum)))))) = m;
        SpecMavlinkV1Msg { len, seq, sysid, compid, msgid, payload, checksum }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MavlinkV1Msg<'a> {
    pub len: u8,
    pub seq: u8,
    pub sysid: u8,
    pub compid: u8,
    pub msgid: u8,
    pub payload: &'a [u8],
    pub checksum: u16,
}

impl View for MavlinkV1Msg<'_> {
    type V = SpecMavlinkV1Msg;

    open spec fn view(&self) -> Self::V {
        SpecMavlinkV1Msg {
            len: self.len@,
            seq: self.seq@,
            sysid: self.sysid@,
            compid: self.compid@,
            msgid: self.msgid@,
            payload: self.payload@,
            checksum: self.checksum@,
        }
    }
}
pub type MavlinkV1MsgInner<'a> = (u8, (u8, (u8, (u8, (u8, (&'a [u8], u16))))));

pub type MavlinkV1MsgInnerRef<'a> = (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a &'a [u8], &'a u16))))));
impl<'a> From<&'a MavlinkV1Msg<'a>> for MavlinkV1MsgInnerRef<'a> {
    fn ex_from(m: &'a MavlinkV1Msg) -> MavlinkV1MsgInnerRef<'a> {
        (&m.len, (&m.seq, (&m.sysid, (&m.compid, (&m.msgid, (&m.payload, &m.checksum))))))
    }
}

impl<'a> From<MavlinkV1MsgInner<'a>> for MavlinkV1Msg<'a> {
    fn ex_from(m: MavlinkV1MsgInner) -> MavlinkV1Msg {
        let (len, (seq, (sysid, (compid, (msgid, (payload, checksum)))))) = m;
        MavlinkV1Msg { len, seq, sysid, compid, msgid, payload, checksum }
    }
}

pub struct MavlinkV1MsgMapper;
impl View for MavlinkV1MsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkV1MsgMapper {
    type Src = SpecMavlinkV1MsgInner;
    type Dst = SpecMavlinkV1Msg;
}
impl SpecIsoProof for MavlinkV1MsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkV1MsgMapper {
    type Src = MavlinkV1MsgInner<'a>;
    type Dst = MavlinkV1Msg<'a>;
    type RefSrc = MavlinkV1MsgInnerRef<'a>;
}

pub struct SpecMavlinkV1MsgCombinator(pub SpecMavlinkV1MsgCombinatorAlias);

impl SpecCombinator for SpecMavlinkV1MsgCombinator {
    type Type = SpecMavlinkV1Msg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkV1MsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkV1MsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkV1MsgCombinatorAlias = Mapped<SpecPair<U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, (U8, (bytes::Variable, U16Le)))))>, MavlinkV1MsgMapper>;
pub struct Predicate3768926651291043512;
impl View for Predicate3768926651291043512 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3768926651291043512 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}
impl SpecPred<u8> for Predicate3768926651291043512 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}

pub struct MavlinkV1MsgCombinator(pub MavlinkV1MsgCombinatorAlias);

impl View for MavlinkV1MsgCombinator {
    type V = SpecMavlinkV1MsgCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkV1MsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkV1MsgCombinator {
    type Type = MavlinkV1Msg<'a>;
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
pub type MavlinkV1MsgCombinatorAlias = Mapped<Pair<U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, (U8, (bytes::Variable, U16Le))))), MavlinkV1MsgCont0>, MavlinkV1MsgMapper>;


pub open spec fn spec_mavlink_v1_msg() -> SpecMavlinkV1MsgCombinator {
    SpecMavlinkV1MsgCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_mavlink_v1_msg_cont0(deps)),
        mapper: MavlinkV1MsgMapper,
    })
}

pub open spec fn spec_mavlink_v1_msg_cont0(deps: u8) -> (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, (U8, (bytes::Variable, U16Le))))) {
    let len = deps;
    (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (U8, (bytes::Variable(len.spec_into()), U16Le)))))
}

impl View for MavlinkV1MsgCont0 {
    type V = spec_fn(u8) -> (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, (U8, (bytes::Variable, U16Le)))));

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_mavlink_v1_msg_cont0(deps)
        }
    }
}

                
pub fn mavlink_v1_msg<'a>() -> (o: MavlinkV1MsgCombinator)
    ensures o@ == spec_mavlink_v1_msg(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkV1MsgCombinator(
    Mapped {
        inner: Pair::new(U8, MavlinkV1MsgCont0),
        mapper: MavlinkV1MsgMapper,
    });
    assert({
        &&& combinator@ == spec_mavlink_v1_msg()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_v1_msg<'a>(input: &'a [u8]) -> (res: PResult<<MavlinkV1MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_v1_msg().spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_v1_msg().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_v1_msg().spec_parse(input@) is None,
        spec_mavlink_v1_msg().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_v1_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_v1_msg<'a>(v: <MavlinkV1MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_v1_msg().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_v1_msg().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_v1_msg().spec_serialize(v@))
        },
{
    let combinator = mavlink_v1_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mavlink_v1_msg_len<'a>(v: <MavlinkV1MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mavlink_v1_msg().wf(v@),
        spec_mavlink_v1_msg().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_v1_msg().spec_serialize(v@).len(),
{
    let combinator = mavlink_v1_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct MavlinkV1MsgCont0;
type MavlinkV1MsgCont0Type<'a, 'b> = &'b u8;
type MavlinkV1MsgCont0SType<'a, 'x> = &'x u8;
type MavlinkV1MsgCont0Input<'a, 'b, 'x> = POrSType<MavlinkV1MsgCont0Type<'a, 'b>, MavlinkV1MsgCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MavlinkV1MsgCont0Input<'a, 'b, 'x>> for MavlinkV1MsgCont0 {
    type Output = (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, (U8, (bytes::Variable, U16Le)))));

    open spec fn requires(&self, deps: MavlinkV1MsgCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MavlinkV1MsgCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_mavlink_v1_msg_cont0(deps@)
    }

    fn apply(&self, deps: MavlinkV1MsgCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = *deps;
                (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (U8, (bytes::Variable(len.ex_into()), U16Le)))))
            }
            POrSType::S(deps) => {
                let len = deps;
                let len = *len;
                (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (U8, (bytes::Variable(len.ex_into()), U16Le)))))
            }
        }
    }
}
                
pub mod IncompatFlags {
    use super::*;
    pub spec const SPEC_Signed: u8 = 1;
    pub exec const Signed: u8 ensures Signed == SPEC_Signed { 1 }
}


pub struct SpecIncompatFlagsCombinator(pub SpecIncompatFlagsCombinatorAlias);

impl SpecCombinator for SpecIncompatFlagsCombinator {
    type Type = u8;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIncompatFlagsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecIncompatFlagsCombinatorAlias::is_prefix_secure() }
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
pub type SpecIncompatFlagsCombinatorAlias = U8;

pub struct IncompatFlagsCombinator(pub IncompatFlagsCombinatorAlias);

impl View for IncompatFlagsCombinator {
    type V = SpecIncompatFlagsCombinator;
    open spec fn view(&self) -> Self::V { SpecIncompatFlagsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IncompatFlagsCombinator {
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
pub type IncompatFlagsCombinatorAlias = U8;


pub open spec fn spec_incompat_flags() -> SpecIncompatFlagsCombinator {
    SpecIncompatFlagsCombinator(U8)
}

                
pub fn incompat_flags<'a>() -> (o: IncompatFlagsCombinator)
    ensures o@ == spec_incompat_flags(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IncompatFlagsCombinator(U8);
    assert({
        &&& combinator@ == spec_incompat_flags()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_incompat_flags<'a>(input: &'a [u8]) -> (res: PResult<<IncompatFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_incompat_flags().spec_parse(input@) == Some((n as int, v@)),
        spec_incompat_flags().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_incompat_flags().spec_parse(input@) is None,
        spec_incompat_flags().spec_parse(input@) is None ==> res is Err,
{
    let combinator = incompat_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_incompat_flags<'a>(v: <IncompatFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_incompat_flags().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_incompat_flags().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_incompat_flags().spec_serialize(v@))
        },
{
    let combinator = incompat_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn incompat_flags_len<'a>(v: <IncompatFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_incompat_flags().wf(v@),
        spec_incompat_flags().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_incompat_flags().spec_serialize(v@).len(),
{
    let combinator = incompat_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod MessageIds {
    use super::*;
    pub spec const SPEC_CommandInt: u32 = 75;
    pub spec const SPEC_CommandLong: u32 = 76;
    pub spec const SPEC_CommandAck: u32 = 77;
    pub spec const SPEC_CommandCancel: u32 = 80;
    pub spec const SPEC_TerrainRequest: u32 = 134;
    pub spec const SPEC_Reserved: u32 = 8388608;
    pub exec const CommandInt: u32 ensures CommandInt == SPEC_CommandInt { 75 }
    pub exec const CommandLong: u32 ensures CommandLong == SPEC_CommandLong { 76 }
    pub exec const CommandAck: u32 ensures CommandAck == SPEC_CommandAck { 77 }
    pub exec const CommandCancel: u32 ensures CommandCancel == SPEC_CommandCancel { 80 }
    pub exec const TerrainRequest: u32 ensures TerrainRequest == SPEC_TerrainRequest { 134 }
    pub exec const Reserved: u32 ensures Reserved == SPEC_Reserved { 8388608 }
}


pub struct SpecMessageIdsCombinator(pub SpecMessageIdsCombinatorAlias);

impl SpecCombinator for SpecMessageIdsCombinator {
    type Type = u24;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMessageIdsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMessageIdsCombinatorAlias::is_prefix_secure() }
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
pub type SpecMessageIdsCombinatorAlias = U24Le;

pub struct MessageIdsCombinator(pub MessageIdsCombinatorAlias);

impl View for MessageIdsCombinator {
    type V = SpecMessageIdsCombinator;
    open spec fn view(&self) -> Self::V { SpecMessageIdsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MessageIdsCombinator {
    type Type = u24;
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
pub type MessageIdsCombinatorAlias = U24Le;


pub open spec fn spec_message_ids() -> SpecMessageIdsCombinator {
    SpecMessageIdsCombinator(U24Le)
}

                
pub fn message_ids<'a>() -> (o: MessageIdsCombinator)
    ensures o@ == spec_message_ids(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MessageIdsCombinator(U24Le);
    assert({
        &&& combinator@ == spec_message_ids()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_message_ids<'a>(input: &'a [u8]) -> (res: PResult<<MessageIdsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_message_ids().spec_parse(input@) == Some((n as int, v@)),
        spec_message_ids().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_message_ids().spec_parse(input@) is None,
        spec_message_ids().spec_parse(input@) is None ==> res is Err,
{
    let combinator = message_ids();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_message_ids<'a>(v: <MessageIdsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_message_ids().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_message_ids().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_message_ids().spec_serialize(v@))
        },
{
    let combinator = message_ids();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn message_ids_len<'a>(v: <MessageIdsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_message_ids().wf(v@),
        spec_message_ids().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_message_ids().spec_serialize(v@).len(),
{
    let combinator = message_ids();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_MavFrame_GLOBAL: u8 = 0;
pub spec const SPEC_MavFrame_LOCAL_NED: u8 = 1;
pub spec const SPEC_MavFrame_MISSION: u8 = 2;
pub spec const SPEC_MavFrame_GLOBAL_RELATIVE_ALT: u8 = 3;
pub spec const SPEC_MavFrame_LOCAL_ENU: u8 = 4;
pub spec const SPEC_MavFrame_GLOBAL_INT: u8 = 5;
pub spec const SPEC_MavFrame_GLOBAL_RELATIVE_ALT_INT: u8 = 6;
pub spec const SPEC_MavFrame_LOCAL_OFFSET_NED: u8 = 7;
pub spec const SPEC_MavFrame_BODY_NED: u8 = 8;
pub spec const SPEC_MavFrame_BODY_OFFSET_NED: u8 = 9;
pub spec const SPEC_MavFrame_GLOBAL_TERRAIN_ALT: u8 = 10;
pub spec const SPEC_MavFrame_GLOBAL_TERRAIN_ALT_INT: u8 = 11;
pub spec const SPEC_MavFrame_BODY_FRD: u8 = 12;
pub spec const SPEC_MavFrame_RESERVED_13: u8 = 13;
pub spec const SPEC_MavFrame_RESERVED_14: u8 = 14;
pub spec const SPEC_MavFrame_RESERVED_15: u8 = 15;
pub spec const SPEC_MavFrame_RESERVED_16: u8 = 16;
pub spec const SPEC_MavFrame_RESERVED_17: u8 = 17;
pub spec const SPEC_MavFrame_RESERVED_18: u8 = 18;
pub spec const SPEC_MavFrame_RESERVED_19: u8 = 19;
pub spec const SPEC_MavFrame_LOCAL_FRD: u8 = 20;
pub spec const SPEC_MavFrame_LOCAL_FLU: u8 = 21;
pub exec static EXEC_MavFrame_GLOBAL: u8 ensures EXEC_MavFrame_GLOBAL == SPEC_MavFrame_GLOBAL { 0 }
pub exec static EXEC_MavFrame_LOCAL_NED: u8 ensures EXEC_MavFrame_LOCAL_NED == SPEC_MavFrame_LOCAL_NED { 1 }
pub exec static EXEC_MavFrame_MISSION: u8 ensures EXEC_MavFrame_MISSION == SPEC_MavFrame_MISSION { 2 }
pub exec static EXEC_MavFrame_GLOBAL_RELATIVE_ALT: u8 ensures EXEC_MavFrame_GLOBAL_RELATIVE_ALT == SPEC_MavFrame_GLOBAL_RELATIVE_ALT { 3 }
pub exec static EXEC_MavFrame_LOCAL_ENU: u8 ensures EXEC_MavFrame_LOCAL_ENU == SPEC_MavFrame_LOCAL_ENU { 4 }
pub exec static EXEC_MavFrame_GLOBAL_INT: u8 ensures EXEC_MavFrame_GLOBAL_INT == SPEC_MavFrame_GLOBAL_INT { 5 }
pub exec static EXEC_MavFrame_GLOBAL_RELATIVE_ALT_INT: u8 ensures EXEC_MavFrame_GLOBAL_RELATIVE_ALT_INT == SPEC_MavFrame_GLOBAL_RELATIVE_ALT_INT { 6 }
pub exec static EXEC_MavFrame_LOCAL_OFFSET_NED: u8 ensures EXEC_MavFrame_LOCAL_OFFSET_NED == SPEC_MavFrame_LOCAL_OFFSET_NED { 7 }
pub exec static EXEC_MavFrame_BODY_NED: u8 ensures EXEC_MavFrame_BODY_NED == SPEC_MavFrame_BODY_NED { 8 }
pub exec static EXEC_MavFrame_BODY_OFFSET_NED: u8 ensures EXEC_MavFrame_BODY_OFFSET_NED == SPEC_MavFrame_BODY_OFFSET_NED { 9 }
pub exec static EXEC_MavFrame_GLOBAL_TERRAIN_ALT: u8 ensures EXEC_MavFrame_GLOBAL_TERRAIN_ALT == SPEC_MavFrame_GLOBAL_TERRAIN_ALT { 10 }
pub exec static EXEC_MavFrame_GLOBAL_TERRAIN_ALT_INT: u8 ensures EXEC_MavFrame_GLOBAL_TERRAIN_ALT_INT == SPEC_MavFrame_GLOBAL_TERRAIN_ALT_INT { 11 }
pub exec static EXEC_MavFrame_BODY_FRD: u8 ensures EXEC_MavFrame_BODY_FRD == SPEC_MavFrame_BODY_FRD { 12 }
pub exec static EXEC_MavFrame_RESERVED_13: u8 ensures EXEC_MavFrame_RESERVED_13 == SPEC_MavFrame_RESERVED_13 { 13 }
pub exec static EXEC_MavFrame_RESERVED_14: u8 ensures EXEC_MavFrame_RESERVED_14 == SPEC_MavFrame_RESERVED_14 { 14 }
pub exec static EXEC_MavFrame_RESERVED_15: u8 ensures EXEC_MavFrame_RESERVED_15 == SPEC_MavFrame_RESERVED_15 { 15 }
pub exec static EXEC_MavFrame_RESERVED_16: u8 ensures EXEC_MavFrame_RESERVED_16 == SPEC_MavFrame_RESERVED_16 { 16 }
pub exec static EXEC_MavFrame_RESERVED_17: u8 ensures EXEC_MavFrame_RESERVED_17 == SPEC_MavFrame_RESERVED_17 { 17 }
pub exec static EXEC_MavFrame_RESERVED_18: u8 ensures EXEC_MavFrame_RESERVED_18 == SPEC_MavFrame_RESERVED_18 { 18 }
pub exec static EXEC_MavFrame_RESERVED_19: u8 ensures EXEC_MavFrame_RESERVED_19 == SPEC_MavFrame_RESERVED_19 { 19 }
pub exec static EXEC_MavFrame_LOCAL_FRD: u8 ensures EXEC_MavFrame_LOCAL_FRD == SPEC_MavFrame_LOCAL_FRD { 20 }
pub exec static EXEC_MavFrame_LOCAL_FLU: u8 ensures EXEC_MavFrame_LOCAL_FLU == SPEC_MavFrame_LOCAL_FLU { 21 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MavFrame {
    GLOBAL = 0,
LOCAL_NED = 1,
MISSION = 2,
GLOBAL_RELATIVE_ALT = 3,
LOCAL_ENU = 4,
GLOBAL_INT = 5,
GLOBAL_RELATIVE_ALT_INT = 6,
LOCAL_OFFSET_NED = 7,
BODY_NED = 8,
BODY_OFFSET_NED = 9,
GLOBAL_TERRAIN_ALT = 10,
GLOBAL_TERRAIN_ALT_INT = 11,
BODY_FRD = 12,
RESERVED_13 = 13,
RESERVED_14 = 14,
RESERVED_15 = 15,
RESERVED_16 = 16,
RESERVED_17 = 17,
RESERVED_18 = 18,
RESERVED_19 = 19,
LOCAL_FRD = 20,
LOCAL_FLU = 21
}
pub type SpecMavFrame = MavFrame;

pub type MavFrameInner = u8;

pub type MavFrameInnerRef<'a> = &'a u8;

impl View for MavFrame {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MavFrameInner> for MavFrame {
    type Error = ();

    open spec fn spec_try_from(v: MavFrameInner) -> Result<MavFrame, ()> {
        match v {
            0u8 => Ok(MavFrame::GLOBAL),
            1u8 => Ok(MavFrame::LOCAL_NED),
            2u8 => Ok(MavFrame::MISSION),
            3u8 => Ok(MavFrame::GLOBAL_RELATIVE_ALT),
            4u8 => Ok(MavFrame::LOCAL_ENU),
            5u8 => Ok(MavFrame::GLOBAL_INT),
            6u8 => Ok(MavFrame::GLOBAL_RELATIVE_ALT_INT),
            7u8 => Ok(MavFrame::LOCAL_OFFSET_NED),
            8u8 => Ok(MavFrame::BODY_NED),
            9u8 => Ok(MavFrame::BODY_OFFSET_NED),
            10u8 => Ok(MavFrame::GLOBAL_TERRAIN_ALT),
            11u8 => Ok(MavFrame::GLOBAL_TERRAIN_ALT_INT),
            12u8 => Ok(MavFrame::BODY_FRD),
            13u8 => Ok(MavFrame::RESERVED_13),
            14u8 => Ok(MavFrame::RESERVED_14),
            15u8 => Ok(MavFrame::RESERVED_15),
            16u8 => Ok(MavFrame::RESERVED_16),
            17u8 => Ok(MavFrame::RESERVED_17),
            18u8 => Ok(MavFrame::RESERVED_18),
            19u8 => Ok(MavFrame::RESERVED_19),
            20u8 => Ok(MavFrame::LOCAL_FRD),
            21u8 => Ok(MavFrame::LOCAL_FLU),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MavFrame> for MavFrameInner {
    type Error = ();

    open spec fn spec_try_from(v: MavFrame) -> Result<MavFrameInner, ()> {
        match v {
            MavFrame::GLOBAL => Ok(SPEC_MavFrame_GLOBAL),
            MavFrame::LOCAL_NED => Ok(SPEC_MavFrame_LOCAL_NED),
            MavFrame::MISSION => Ok(SPEC_MavFrame_MISSION),
            MavFrame::GLOBAL_RELATIVE_ALT => Ok(SPEC_MavFrame_GLOBAL_RELATIVE_ALT),
            MavFrame::LOCAL_ENU => Ok(SPEC_MavFrame_LOCAL_ENU),
            MavFrame::GLOBAL_INT => Ok(SPEC_MavFrame_GLOBAL_INT),
            MavFrame::GLOBAL_RELATIVE_ALT_INT => Ok(SPEC_MavFrame_GLOBAL_RELATIVE_ALT_INT),
            MavFrame::LOCAL_OFFSET_NED => Ok(SPEC_MavFrame_LOCAL_OFFSET_NED),
            MavFrame::BODY_NED => Ok(SPEC_MavFrame_BODY_NED),
            MavFrame::BODY_OFFSET_NED => Ok(SPEC_MavFrame_BODY_OFFSET_NED),
            MavFrame::GLOBAL_TERRAIN_ALT => Ok(SPEC_MavFrame_GLOBAL_TERRAIN_ALT),
            MavFrame::GLOBAL_TERRAIN_ALT_INT => Ok(SPEC_MavFrame_GLOBAL_TERRAIN_ALT_INT),
            MavFrame::BODY_FRD => Ok(SPEC_MavFrame_BODY_FRD),
            MavFrame::RESERVED_13 => Ok(SPEC_MavFrame_RESERVED_13),
            MavFrame::RESERVED_14 => Ok(SPEC_MavFrame_RESERVED_14),
            MavFrame::RESERVED_15 => Ok(SPEC_MavFrame_RESERVED_15),
            MavFrame::RESERVED_16 => Ok(SPEC_MavFrame_RESERVED_16),
            MavFrame::RESERVED_17 => Ok(SPEC_MavFrame_RESERVED_17),
            MavFrame::RESERVED_18 => Ok(SPEC_MavFrame_RESERVED_18),
            MavFrame::RESERVED_19 => Ok(SPEC_MavFrame_RESERVED_19),
            MavFrame::LOCAL_FRD => Ok(SPEC_MavFrame_LOCAL_FRD),
            MavFrame::LOCAL_FLU => Ok(SPEC_MavFrame_LOCAL_FLU),
        }
    }
}

impl TryFrom<MavFrameInner> for MavFrame {
    type Error = ();

    fn ex_try_from(v: MavFrameInner) -> Result<MavFrame, ()> {
        match v {
            0u8 => Ok(MavFrame::GLOBAL),
            1u8 => Ok(MavFrame::LOCAL_NED),
            2u8 => Ok(MavFrame::MISSION),
            3u8 => Ok(MavFrame::GLOBAL_RELATIVE_ALT),
            4u8 => Ok(MavFrame::LOCAL_ENU),
            5u8 => Ok(MavFrame::GLOBAL_INT),
            6u8 => Ok(MavFrame::GLOBAL_RELATIVE_ALT_INT),
            7u8 => Ok(MavFrame::LOCAL_OFFSET_NED),
            8u8 => Ok(MavFrame::BODY_NED),
            9u8 => Ok(MavFrame::BODY_OFFSET_NED),
            10u8 => Ok(MavFrame::GLOBAL_TERRAIN_ALT),
            11u8 => Ok(MavFrame::GLOBAL_TERRAIN_ALT_INT),
            12u8 => Ok(MavFrame::BODY_FRD),
            13u8 => Ok(MavFrame::RESERVED_13),
            14u8 => Ok(MavFrame::RESERVED_14),
            15u8 => Ok(MavFrame::RESERVED_15),
            16u8 => Ok(MavFrame::RESERVED_16),
            17u8 => Ok(MavFrame::RESERVED_17),
            18u8 => Ok(MavFrame::RESERVED_18),
            19u8 => Ok(MavFrame::RESERVED_19),
            20u8 => Ok(MavFrame::LOCAL_FRD),
            21u8 => Ok(MavFrame::LOCAL_FLU),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a MavFrame> for MavFrameInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a MavFrame) -> Result<MavFrameInnerRef<'a>, ()> {
        match v {
            MavFrame::GLOBAL => Ok(&EXEC_MavFrame_GLOBAL),
            MavFrame::LOCAL_NED => Ok(&EXEC_MavFrame_LOCAL_NED),
            MavFrame::MISSION => Ok(&EXEC_MavFrame_MISSION),
            MavFrame::GLOBAL_RELATIVE_ALT => Ok(&EXEC_MavFrame_GLOBAL_RELATIVE_ALT),
            MavFrame::LOCAL_ENU => Ok(&EXEC_MavFrame_LOCAL_ENU),
            MavFrame::GLOBAL_INT => Ok(&EXEC_MavFrame_GLOBAL_INT),
            MavFrame::GLOBAL_RELATIVE_ALT_INT => Ok(&EXEC_MavFrame_GLOBAL_RELATIVE_ALT_INT),
            MavFrame::LOCAL_OFFSET_NED => Ok(&EXEC_MavFrame_LOCAL_OFFSET_NED),
            MavFrame::BODY_NED => Ok(&EXEC_MavFrame_BODY_NED),
            MavFrame::BODY_OFFSET_NED => Ok(&EXEC_MavFrame_BODY_OFFSET_NED),
            MavFrame::GLOBAL_TERRAIN_ALT => Ok(&EXEC_MavFrame_GLOBAL_TERRAIN_ALT),
            MavFrame::GLOBAL_TERRAIN_ALT_INT => Ok(&EXEC_MavFrame_GLOBAL_TERRAIN_ALT_INT),
            MavFrame::BODY_FRD => Ok(&EXEC_MavFrame_BODY_FRD),
            MavFrame::RESERVED_13 => Ok(&EXEC_MavFrame_RESERVED_13),
            MavFrame::RESERVED_14 => Ok(&EXEC_MavFrame_RESERVED_14),
            MavFrame::RESERVED_15 => Ok(&EXEC_MavFrame_RESERVED_15),
            MavFrame::RESERVED_16 => Ok(&EXEC_MavFrame_RESERVED_16),
            MavFrame::RESERVED_17 => Ok(&EXEC_MavFrame_RESERVED_17),
            MavFrame::RESERVED_18 => Ok(&EXEC_MavFrame_RESERVED_18),
            MavFrame::RESERVED_19 => Ok(&EXEC_MavFrame_RESERVED_19),
            MavFrame::LOCAL_FRD => Ok(&EXEC_MavFrame_LOCAL_FRD),
            MavFrame::LOCAL_FLU => Ok(&EXEC_MavFrame_LOCAL_FLU),
        }
    }
}

pub struct MavFrameMapper;

impl View for MavFrameMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MavFrameMapper {
    type Src = MavFrameInner;
    type Dst = MavFrame;
}

impl SpecPartialIsoProof for MavFrameMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl<'a> PartialIso<'a> for MavFrameMapper {
    type Src = MavFrameInner;
    type Dst = MavFrame;
    type RefSrc = MavFrameInnerRef<'a>;
}


pub struct SpecMavFrameCombinator(pub SpecMavFrameCombinatorAlias);

impl SpecCombinator for SpecMavFrameCombinator {
    type Type = SpecMavFrame;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavFrameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavFrameCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavFrameCombinatorAlias = TryMap<U8, MavFrameMapper>;

pub struct MavFrameCombinator(pub MavFrameCombinatorAlias);

impl View for MavFrameCombinator {
    type V = SpecMavFrameCombinator;
    open spec fn view(&self) -> Self::V { SpecMavFrameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavFrameCombinator {
    type Type = MavFrame;
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
pub type MavFrameCombinatorAlias = TryMap<U8, MavFrameMapper>;


pub open spec fn spec_mav_frame() -> SpecMavFrameCombinator {
    SpecMavFrameCombinator(TryMap { inner: U8, mapper: MavFrameMapper })
}

                
pub fn mav_frame<'a>() -> (o: MavFrameCombinator)
    ensures o@ == spec_mav_frame(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavFrameCombinator(TryMap { inner: U8, mapper: MavFrameMapper });
    assert({
        &&& combinator@ == spec_mav_frame()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mav_frame<'a>(input: &'a [u8]) -> (res: PResult<<MavFrameCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mav_frame().spec_parse(input@) == Some((n as int, v@)),
        spec_mav_frame().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mav_frame().spec_parse(input@) is None,
        spec_mav_frame().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mav_frame();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mav_frame<'a>(v: <MavFrameCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mav_frame().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mav_frame().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mav_frame().spec_serialize(v@))
        },
{
    let combinator = mav_frame();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mav_frame_len<'a>(v: <MavFrameCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mav_frame().wf(v@),
        spec_mav_frame().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mav_frame().spec_serialize(v@).len(),
{
    let combinator = mav_frame();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod MavCmd {
    use super::*;
    pub spec const SPEC_FlashBootloader: u16 = 42650;
    pub exec const FlashBootloader: u16 ensures FlashBootloader == SPEC_FlashBootloader { 42650 }
}


pub struct SpecMavCmdCombinator(pub SpecMavCmdCombinatorAlias);

impl SpecCombinator for SpecMavCmdCombinator {
    type Type = u16;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavCmdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavCmdCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavCmdCombinatorAlias = U16Le;

pub struct MavCmdCombinator(pub MavCmdCombinatorAlias);

impl View for MavCmdCombinator {
    type V = SpecMavCmdCombinator;
    open spec fn view(&self) -> Self::V { SpecMavCmdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavCmdCombinator {
    type Type = u16;
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
pub type MavCmdCombinatorAlias = U16Le;


pub open spec fn spec_mav_cmd() -> SpecMavCmdCombinator {
    SpecMavCmdCombinator(U16Le)
}

                
pub fn mav_cmd<'a>() -> (o: MavCmdCombinator)
    ensures o@ == spec_mav_cmd(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavCmdCombinator(U16Le);
    assert({
        &&& combinator@ == spec_mav_cmd()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mav_cmd<'a>(input: &'a [u8]) -> (res: PResult<<MavCmdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mav_cmd().spec_parse(input@) == Some((n as int, v@)),
        spec_mav_cmd().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mav_cmd().spec_parse(input@) is None,
        spec_mav_cmd().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mav_cmd();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mav_cmd<'a>(v: <MavCmdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mav_cmd().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mav_cmd().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mav_cmd().spec_serialize(v@))
        },
{
    let combinator = mav_cmd();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mav_cmd_len<'a>(v: <MavCmdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mav_cmd().wf(v@),
        spec_mav_cmd().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mav_cmd().spec_serialize(v@).len(),
{
    let combinator = mav_cmd();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCommandInt {
    pub target_system: u8,
    pub target_component: u8,
    pub frame: SpecMavFrame,
    pub command: u16,
    pub current: u8,
    pub autocontinue: u8,
    pub param1: u32,
    pub param2: u32,
    pub param3: u32,
    pub param4: u32,
    pub param5: u32,
    pub param6: u32,
    pub param7: u32,
}

pub type SpecCommandIntInner = (u8, (u8, (SpecMavFrame, (u16, (u8, (u8, (u32, (u32, (u32, (u32, (u32, (u32, u32))))))))))));


impl SpecFrom<SpecCommandInt> for SpecCommandIntInner {
    open spec fn spec_from(m: SpecCommandInt) -> SpecCommandIntInner {
        (m.target_system, (m.target_component, (m.frame, (m.command, (m.current, (m.autocontinue, (m.param1, (m.param2, (m.param3, (m.param4, (m.param5, (m.param6, m.param7))))))))))))
    }
}

impl SpecFrom<SpecCommandIntInner> for SpecCommandInt {
    open spec fn spec_from(m: SpecCommandIntInner) -> SpecCommandInt {
        let (target_system, (target_component, (frame, (command, (current, (autocontinue, (param1, (param2, (param3, (param4, (param5, (param6, param7)))))))))))) = m;
        SpecCommandInt { target_system, target_component, frame, command, current, autocontinue, param1, param2, param3, param4, param5, param6, param7 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CommandInt {
    pub target_system: u8,
    pub target_component: u8,
    pub frame: MavFrame,
    pub command: u16,
    pub current: u8,
    pub autocontinue: u8,
    pub param1: u32,
    pub param2: u32,
    pub param3: u32,
    pub param4: u32,
    pub param5: u32,
    pub param6: u32,
    pub param7: u32,
}

impl View for CommandInt {
    type V = SpecCommandInt;

    open spec fn view(&self) -> Self::V {
        SpecCommandInt {
            target_system: self.target_system@,
            target_component: self.target_component@,
            frame: self.frame@,
            command: self.command@,
            current: self.current@,
            autocontinue: self.autocontinue@,
            param1: self.param1@,
            param2: self.param2@,
            param3: self.param3@,
            param4: self.param4@,
            param5: self.param5@,
            param6: self.param6@,
            param7: self.param7@,
        }
    }
}
pub type CommandIntInner = (u8, (u8, (MavFrame, (u16, (u8, (u8, (u32, (u32, (u32, (u32, (u32, (u32, u32))))))))))));

pub type CommandIntInnerRef<'a> = (&'a u8, (&'a u8, (&'a MavFrame, (&'a u16, (&'a u8, (&'a u8, (&'a u32, (&'a u32, (&'a u32, (&'a u32, (&'a u32, (&'a u32, &'a u32))))))))))));
impl<'a> From<&'a CommandInt> for CommandIntInnerRef<'a> {
    fn ex_from(m: &'a CommandInt) -> CommandIntInnerRef<'a> {
        (&m.target_system, (&m.target_component, (&m.frame, (&m.command, (&m.current, (&m.autocontinue, (&m.param1, (&m.param2, (&m.param3, (&m.param4, (&m.param5, (&m.param6, &m.param7))))))))))))
    }
}

impl From<CommandIntInner> for CommandInt {
    fn ex_from(m: CommandIntInner) -> CommandInt {
        let (target_system, (target_component, (frame, (command, (current, (autocontinue, (param1, (param2, (param3, (param4, (param5, (param6, param7)))))))))))) = m;
        CommandInt { target_system, target_component, frame, command, current, autocontinue, param1, param2, param3, param4, param5, param6, param7 }
    }
}

pub struct CommandIntMapper;
impl View for CommandIntMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CommandIntMapper {
    type Src = SpecCommandIntInner;
    type Dst = SpecCommandInt;
}
impl SpecIsoProof for CommandIntMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CommandIntMapper {
    type Src = CommandIntInner;
    type Dst = CommandInt;
    type RefSrc = CommandIntInnerRef<'a>;
}
type SpecCommandIntCombinatorAlias1 = (U32Le, U32Le);
type SpecCommandIntCombinatorAlias2 = (U32Le, SpecCommandIntCombinatorAlias1);
type SpecCommandIntCombinatorAlias3 = (U32Le, SpecCommandIntCombinatorAlias2);
type SpecCommandIntCombinatorAlias4 = (U32Le, SpecCommandIntCombinatorAlias3);
type SpecCommandIntCombinatorAlias5 = (U32Le, SpecCommandIntCombinatorAlias4);
type SpecCommandIntCombinatorAlias6 = (U32Le, SpecCommandIntCombinatorAlias5);
type SpecCommandIntCombinatorAlias7 = (Refined<U8, Predicate2576612288366319398>, SpecCommandIntCombinatorAlias6);
type SpecCommandIntCombinatorAlias8 = (U8, SpecCommandIntCombinatorAlias7);
type SpecCommandIntCombinatorAlias9 = (SpecMavCmdCombinator, SpecCommandIntCombinatorAlias8);
type SpecCommandIntCombinatorAlias10 = (SpecMavFrameCombinator, SpecCommandIntCombinatorAlias9);
type SpecCommandIntCombinatorAlias11 = (U8, SpecCommandIntCombinatorAlias10);
type SpecCommandIntCombinatorAlias12 = (U8, SpecCommandIntCombinatorAlias11);
pub struct SpecCommandIntCombinator(pub SpecCommandIntCombinatorAlias);

impl SpecCombinator for SpecCommandIntCombinator {
    type Type = SpecCommandInt;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCommandIntCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCommandIntCombinatorAlias::is_prefix_secure() }
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
pub type SpecCommandIntCombinatorAlias = Mapped<SpecCommandIntCombinatorAlias12, CommandIntMapper>;
pub struct Predicate2576612288366319398;
impl View for Predicate2576612288366319398 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2576612288366319398 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
impl SpecPred<u8> for Predicate2576612288366319398 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
type CommandIntCombinatorAlias1 = (U32Le, U32Le);
type CommandIntCombinatorAlias2 = (U32Le, CommandIntCombinator1);
type CommandIntCombinatorAlias3 = (U32Le, CommandIntCombinator2);
type CommandIntCombinatorAlias4 = (U32Le, CommandIntCombinator3);
type CommandIntCombinatorAlias5 = (U32Le, CommandIntCombinator4);
type CommandIntCombinatorAlias6 = (U32Le, CommandIntCombinator5);
type CommandIntCombinatorAlias7 = (Refined<U8, Predicate2576612288366319398>, CommandIntCombinator6);
type CommandIntCombinatorAlias8 = (U8, CommandIntCombinator7);
type CommandIntCombinatorAlias9 = (MavCmdCombinator, CommandIntCombinator8);
type CommandIntCombinatorAlias10 = (MavFrameCombinator, CommandIntCombinator9);
type CommandIntCombinatorAlias11 = (U8, CommandIntCombinator10);
type CommandIntCombinatorAlias12 = (U8, CommandIntCombinator11);
pub struct CommandIntCombinator1(pub CommandIntCombinatorAlias1);
impl View for CommandIntCombinator1 {
    type V = SpecCommandIntCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator1, CommandIntCombinatorAlias1);

pub struct CommandIntCombinator2(pub CommandIntCombinatorAlias2);
impl View for CommandIntCombinator2 {
    type V = SpecCommandIntCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator2, CommandIntCombinatorAlias2);

pub struct CommandIntCombinator3(pub CommandIntCombinatorAlias3);
impl View for CommandIntCombinator3 {
    type V = SpecCommandIntCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator3, CommandIntCombinatorAlias3);

pub struct CommandIntCombinator4(pub CommandIntCombinatorAlias4);
impl View for CommandIntCombinator4 {
    type V = SpecCommandIntCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator4, CommandIntCombinatorAlias4);

pub struct CommandIntCombinator5(pub CommandIntCombinatorAlias5);
impl View for CommandIntCombinator5 {
    type V = SpecCommandIntCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator5, CommandIntCombinatorAlias5);

pub struct CommandIntCombinator6(pub CommandIntCombinatorAlias6);
impl View for CommandIntCombinator6 {
    type V = SpecCommandIntCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator6, CommandIntCombinatorAlias6);

pub struct CommandIntCombinator7(pub CommandIntCombinatorAlias7);
impl View for CommandIntCombinator7 {
    type V = SpecCommandIntCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator7, CommandIntCombinatorAlias7);

pub struct CommandIntCombinator8(pub CommandIntCombinatorAlias8);
impl View for CommandIntCombinator8 {
    type V = SpecCommandIntCombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator8, CommandIntCombinatorAlias8);

pub struct CommandIntCombinator9(pub CommandIntCombinatorAlias9);
impl View for CommandIntCombinator9 {
    type V = SpecCommandIntCombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator9, CommandIntCombinatorAlias9);

pub struct CommandIntCombinator10(pub CommandIntCombinatorAlias10);
impl View for CommandIntCombinator10 {
    type V = SpecCommandIntCombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator10, CommandIntCombinatorAlias10);

pub struct CommandIntCombinator11(pub CommandIntCombinatorAlias11);
impl View for CommandIntCombinator11 {
    type V = SpecCommandIntCombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator11, CommandIntCombinatorAlias11);

pub struct CommandIntCombinator12(pub CommandIntCombinatorAlias12);
impl View for CommandIntCombinator12 {
    type V = SpecCommandIntCombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandIntCombinator12, CommandIntCombinatorAlias12);

pub struct CommandIntCombinator(pub CommandIntCombinatorAlias);

impl View for CommandIntCombinator {
    type V = SpecCommandIntCombinator;
    open spec fn view(&self) -> Self::V { SpecCommandIntCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CommandIntCombinator {
    type Type = CommandInt;
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
pub type CommandIntCombinatorAlias = Mapped<CommandIntCombinator12, CommandIntMapper>;


pub open spec fn spec_command_int() -> SpecCommandIntCombinator {
    SpecCommandIntCombinator(
    Mapped {
        inner: (U8, (U8, (spec_mav_frame(), (spec_mav_cmd(), (U8, (Refined { inner: U8, predicate: Predicate2576612288366319398 }, (U32Le, (U32Le, (U32Le, (U32Le, (U32Le, (U32Le, U32Le)))))))))))),
        mapper: CommandIntMapper,
    })
}

                
pub fn command_int<'a>() -> (o: CommandIntCombinator)
    ensures o@ == spec_command_int(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CommandIntCombinator(
    Mapped {
        inner: CommandIntCombinator12((U8, CommandIntCombinator11((U8, CommandIntCombinator10((mav_frame(), CommandIntCombinator9((mav_cmd(), CommandIntCombinator8((U8, CommandIntCombinator7((Refined { inner: U8, predicate: Predicate2576612288366319398 }, CommandIntCombinator6((U32Le, CommandIntCombinator5((U32Le, CommandIntCombinator4((U32Le, CommandIntCombinator3((U32Le, CommandIntCombinator2((U32Le, CommandIntCombinator1((U32Le, U32Le)))))))))))))))))))))))),
        mapper: CommandIntMapper,
    });
    assert({
        &&& combinator@ == spec_command_int()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_command_int<'a>(input: &'a [u8]) -> (res: PResult<<CommandIntCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_command_int().spec_parse(input@) == Some((n as int, v@)),
        spec_command_int().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_command_int().spec_parse(input@) is None,
        spec_command_int().spec_parse(input@) is None ==> res is Err,
{
    let combinator = command_int();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_command_int<'a>(v: <CommandIntCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_command_int().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_command_int().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_command_int().spec_serialize(v@))
        },
{
    let combinator = command_int();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn command_int_len<'a>(v: <CommandIntCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_command_int().wf(v@),
        spec_command_int().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_command_int().spec_serialize(v@).len(),
{
    let combinator = command_int();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCommandLong {
    pub target_system: u8,
    pub target_component: u8,
    pub command: u16,
    pub confirmation: u8,
    pub param1: u32,
    pub param2: u32,
    pub param3: u32,
    pub param4: u32,
    pub param5: u32,
    pub param6: u32,
    pub param7: u32,
}

pub type SpecCommandLongInner = (u8, (u8, (u16, (u8, (u32, (u32, (u32, (u32, (u32, (u32, u32))))))))));


impl SpecFrom<SpecCommandLong> for SpecCommandLongInner {
    open spec fn spec_from(m: SpecCommandLong) -> SpecCommandLongInner {
        (m.target_system, (m.target_component, (m.command, (m.confirmation, (m.param1, (m.param2, (m.param3, (m.param4, (m.param5, (m.param6, m.param7))))))))))
    }
}

impl SpecFrom<SpecCommandLongInner> for SpecCommandLong {
    open spec fn spec_from(m: SpecCommandLongInner) -> SpecCommandLong {
        let (target_system, (target_component, (command, (confirmation, (param1, (param2, (param3, (param4, (param5, (param6, param7)))))))))) = m;
        SpecCommandLong { target_system, target_component, command, confirmation, param1, param2, param3, param4, param5, param6, param7 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CommandLong {
    pub target_system: u8,
    pub target_component: u8,
    pub command: u16,
    pub confirmation: u8,
    pub param1: u32,
    pub param2: u32,
    pub param3: u32,
    pub param4: u32,
    pub param5: u32,
    pub param6: u32,
    pub param7: u32,
}

impl View for CommandLong {
    type V = SpecCommandLong;

    open spec fn view(&self) -> Self::V {
        SpecCommandLong {
            target_system: self.target_system@,
            target_component: self.target_component@,
            command: self.command@,
            confirmation: self.confirmation@,
            param1: self.param1@,
            param2: self.param2@,
            param3: self.param3@,
            param4: self.param4@,
            param5: self.param5@,
            param6: self.param6@,
            param7: self.param7@,
        }
    }
}
pub type CommandLongInner = (u8, (u8, (u16, (u8, (u32, (u32, (u32, (u32, (u32, (u32, u32))))))))));

pub type CommandLongInnerRef<'a> = (&'a u8, (&'a u8, (&'a u16, (&'a u8, (&'a u32, (&'a u32, (&'a u32, (&'a u32, (&'a u32, (&'a u32, &'a u32))))))))));
impl<'a> From<&'a CommandLong> for CommandLongInnerRef<'a> {
    fn ex_from(m: &'a CommandLong) -> CommandLongInnerRef<'a> {
        (&m.target_system, (&m.target_component, (&m.command, (&m.confirmation, (&m.param1, (&m.param2, (&m.param3, (&m.param4, (&m.param5, (&m.param6, &m.param7))))))))))
    }
}

impl From<CommandLongInner> for CommandLong {
    fn ex_from(m: CommandLongInner) -> CommandLong {
        let (target_system, (target_component, (command, (confirmation, (param1, (param2, (param3, (param4, (param5, (param6, param7)))))))))) = m;
        CommandLong { target_system, target_component, command, confirmation, param1, param2, param3, param4, param5, param6, param7 }
    }
}

pub struct CommandLongMapper;
impl View for CommandLongMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CommandLongMapper {
    type Src = SpecCommandLongInner;
    type Dst = SpecCommandLong;
}
impl SpecIsoProof for CommandLongMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CommandLongMapper {
    type Src = CommandLongInner;
    type Dst = CommandLong;
    type RefSrc = CommandLongInnerRef<'a>;
}
type SpecCommandLongCombinatorAlias1 = (U32Le, U32Le);
type SpecCommandLongCombinatorAlias2 = (U32Le, SpecCommandLongCombinatorAlias1);
type SpecCommandLongCombinatorAlias3 = (U32Le, SpecCommandLongCombinatorAlias2);
type SpecCommandLongCombinatorAlias4 = (U32Le, SpecCommandLongCombinatorAlias3);
type SpecCommandLongCombinatorAlias5 = (U32Le, SpecCommandLongCombinatorAlias4);
type SpecCommandLongCombinatorAlias6 = (U32Le, SpecCommandLongCombinatorAlias5);
type SpecCommandLongCombinatorAlias7 = (U8, SpecCommandLongCombinatorAlias6);
type SpecCommandLongCombinatorAlias8 = (SpecMavCmdCombinator, SpecCommandLongCombinatorAlias7);
type SpecCommandLongCombinatorAlias9 = (U8, SpecCommandLongCombinatorAlias8);
type SpecCommandLongCombinatorAlias10 = (U8, SpecCommandLongCombinatorAlias9);
pub struct SpecCommandLongCombinator(pub SpecCommandLongCombinatorAlias);

impl SpecCombinator for SpecCommandLongCombinator {
    type Type = SpecCommandLong;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCommandLongCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCommandLongCombinatorAlias::is_prefix_secure() }
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
pub type SpecCommandLongCombinatorAlias = Mapped<SpecCommandLongCombinatorAlias10, CommandLongMapper>;
type CommandLongCombinatorAlias1 = (U32Le, U32Le);
type CommandLongCombinatorAlias2 = (U32Le, CommandLongCombinator1);
type CommandLongCombinatorAlias3 = (U32Le, CommandLongCombinator2);
type CommandLongCombinatorAlias4 = (U32Le, CommandLongCombinator3);
type CommandLongCombinatorAlias5 = (U32Le, CommandLongCombinator4);
type CommandLongCombinatorAlias6 = (U32Le, CommandLongCombinator5);
type CommandLongCombinatorAlias7 = (U8, CommandLongCombinator6);
type CommandLongCombinatorAlias8 = (MavCmdCombinator, CommandLongCombinator7);
type CommandLongCombinatorAlias9 = (U8, CommandLongCombinator8);
type CommandLongCombinatorAlias10 = (U8, CommandLongCombinator9);
pub struct CommandLongCombinator1(pub CommandLongCombinatorAlias1);
impl View for CommandLongCombinator1 {
    type V = SpecCommandLongCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator1, CommandLongCombinatorAlias1);

pub struct CommandLongCombinator2(pub CommandLongCombinatorAlias2);
impl View for CommandLongCombinator2 {
    type V = SpecCommandLongCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator2, CommandLongCombinatorAlias2);

pub struct CommandLongCombinator3(pub CommandLongCombinatorAlias3);
impl View for CommandLongCombinator3 {
    type V = SpecCommandLongCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator3, CommandLongCombinatorAlias3);

pub struct CommandLongCombinator4(pub CommandLongCombinatorAlias4);
impl View for CommandLongCombinator4 {
    type V = SpecCommandLongCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator4, CommandLongCombinatorAlias4);

pub struct CommandLongCombinator5(pub CommandLongCombinatorAlias5);
impl View for CommandLongCombinator5 {
    type V = SpecCommandLongCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator5, CommandLongCombinatorAlias5);

pub struct CommandLongCombinator6(pub CommandLongCombinatorAlias6);
impl View for CommandLongCombinator6 {
    type V = SpecCommandLongCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator6, CommandLongCombinatorAlias6);

pub struct CommandLongCombinator7(pub CommandLongCombinatorAlias7);
impl View for CommandLongCombinator7 {
    type V = SpecCommandLongCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator7, CommandLongCombinatorAlias7);

pub struct CommandLongCombinator8(pub CommandLongCombinatorAlias8);
impl View for CommandLongCombinator8 {
    type V = SpecCommandLongCombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator8, CommandLongCombinatorAlias8);

pub struct CommandLongCombinator9(pub CommandLongCombinatorAlias9);
impl View for CommandLongCombinator9 {
    type V = SpecCommandLongCombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator9, CommandLongCombinatorAlias9);

pub struct CommandLongCombinator10(pub CommandLongCombinatorAlias10);
impl View for CommandLongCombinator10 {
    type V = SpecCommandLongCombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandLongCombinator10, CommandLongCombinatorAlias10);

pub struct CommandLongCombinator(pub CommandLongCombinatorAlias);

impl View for CommandLongCombinator {
    type V = SpecCommandLongCombinator;
    open spec fn view(&self) -> Self::V { SpecCommandLongCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CommandLongCombinator {
    type Type = CommandLong;
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
pub type CommandLongCombinatorAlias = Mapped<CommandLongCombinator10, CommandLongMapper>;


pub open spec fn spec_command_long() -> SpecCommandLongCombinator {
    SpecCommandLongCombinator(
    Mapped {
        inner: (U8, (U8, (spec_mav_cmd(), (U8, (U32Le, (U32Le, (U32Le, (U32Le, (U32Le, (U32Le, U32Le)))))))))),
        mapper: CommandLongMapper,
    })
}

                
pub fn command_long<'a>() -> (o: CommandLongCombinator)
    ensures o@ == spec_command_long(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CommandLongCombinator(
    Mapped {
        inner: CommandLongCombinator10((U8, CommandLongCombinator9((U8, CommandLongCombinator8((mav_cmd(), CommandLongCombinator7((U8, CommandLongCombinator6((U32Le, CommandLongCombinator5((U32Le, CommandLongCombinator4((U32Le, CommandLongCombinator3((U32Le, CommandLongCombinator2((U32Le, CommandLongCombinator1((U32Le, U32Le)))))))))))))))))))),
        mapper: CommandLongMapper,
    });
    assert({
        &&& combinator@ == spec_command_long()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_command_long<'a>(input: &'a [u8]) -> (res: PResult<<CommandLongCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_command_long().spec_parse(input@) == Some((n as int, v@)),
        spec_command_long().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_command_long().spec_parse(input@) is None,
        spec_command_long().spec_parse(input@) is None ==> res is Err,
{
    let combinator = command_long();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_command_long<'a>(v: <CommandLongCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_command_long().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_command_long().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_command_long().spec_serialize(v@))
        },
{
    let combinator = command_long();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn command_long_len<'a>(v: <CommandLongCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_command_long().wf(v@),
        spec_command_long().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_command_long().spec_serialize(v@).len(),
{
    let combinator = command_long();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_MavResult_ACCEPTED: u8 = 0;
pub spec const SPEC_MavResult_TEMPORARILY_REJECTED: u8 = 1;
pub spec const SPEC_MavResult_DENIED: u8 = 2;
pub spec const SPEC_MavResult_UNSUPPORTED: u8 = 3;
pub spec const SPEC_MavResult_FAILED: u8 = 4;
pub spec const SPEC_MavResult_IN_PROGRESS: u8 = 5;
pub spec const SPEC_MavResult_CANCELLED: u8 = 6;
pub spec const SPEC_MavResult_COMMAND_LONG_ONLY: u8 = 7;
pub spec const SPEC_MavResult_COMMAND_INT_ONLY: u8 = 8;
pub spec const SPEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME: u8 = 9;
pub spec const SPEC_MavResult_NOT_IN_CONTROL: u8 = 10;
pub exec static EXEC_MavResult_ACCEPTED: u8 ensures EXEC_MavResult_ACCEPTED == SPEC_MavResult_ACCEPTED { 0 }
pub exec static EXEC_MavResult_TEMPORARILY_REJECTED: u8 ensures EXEC_MavResult_TEMPORARILY_REJECTED == SPEC_MavResult_TEMPORARILY_REJECTED { 1 }
pub exec static EXEC_MavResult_DENIED: u8 ensures EXEC_MavResult_DENIED == SPEC_MavResult_DENIED { 2 }
pub exec static EXEC_MavResult_UNSUPPORTED: u8 ensures EXEC_MavResult_UNSUPPORTED == SPEC_MavResult_UNSUPPORTED { 3 }
pub exec static EXEC_MavResult_FAILED: u8 ensures EXEC_MavResult_FAILED == SPEC_MavResult_FAILED { 4 }
pub exec static EXEC_MavResult_IN_PROGRESS: u8 ensures EXEC_MavResult_IN_PROGRESS == SPEC_MavResult_IN_PROGRESS { 5 }
pub exec static EXEC_MavResult_CANCELLED: u8 ensures EXEC_MavResult_CANCELLED == SPEC_MavResult_CANCELLED { 6 }
pub exec static EXEC_MavResult_COMMAND_LONG_ONLY: u8 ensures EXEC_MavResult_COMMAND_LONG_ONLY == SPEC_MavResult_COMMAND_LONG_ONLY { 7 }
pub exec static EXEC_MavResult_COMMAND_INT_ONLY: u8 ensures EXEC_MavResult_COMMAND_INT_ONLY == SPEC_MavResult_COMMAND_INT_ONLY { 8 }
pub exec static EXEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME: u8 ensures EXEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME == SPEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME { 9 }
pub exec static EXEC_MavResult_NOT_IN_CONTROL: u8 ensures EXEC_MavResult_NOT_IN_CONTROL == SPEC_MavResult_NOT_IN_CONTROL { 10 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MavResult {
    ACCEPTED = 0,
TEMPORARILY_REJECTED = 1,
DENIED = 2,
UNSUPPORTED = 3,
FAILED = 4,
IN_PROGRESS = 5,
CANCELLED = 6,
COMMAND_LONG_ONLY = 7,
COMMAND_INT_ONLY = 8,
COMMAND_UNSUPPORTED_MAV_FRAME = 9,
NOT_IN_CONTROL = 10
}
pub type SpecMavResult = MavResult;

pub type MavResultInner = u8;

pub type MavResultInnerRef<'a> = &'a u8;

impl View for MavResult {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MavResultInner> for MavResult {
    type Error = ();

    open spec fn spec_try_from(v: MavResultInner) -> Result<MavResult, ()> {
        match v {
            0u8 => Ok(MavResult::ACCEPTED),
            1u8 => Ok(MavResult::TEMPORARILY_REJECTED),
            2u8 => Ok(MavResult::DENIED),
            3u8 => Ok(MavResult::UNSUPPORTED),
            4u8 => Ok(MavResult::FAILED),
            5u8 => Ok(MavResult::IN_PROGRESS),
            6u8 => Ok(MavResult::CANCELLED),
            7u8 => Ok(MavResult::COMMAND_LONG_ONLY),
            8u8 => Ok(MavResult::COMMAND_INT_ONLY),
            9u8 => Ok(MavResult::COMMAND_UNSUPPORTED_MAV_FRAME),
            10u8 => Ok(MavResult::NOT_IN_CONTROL),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MavResult> for MavResultInner {
    type Error = ();

    open spec fn spec_try_from(v: MavResult) -> Result<MavResultInner, ()> {
        match v {
            MavResult::ACCEPTED => Ok(SPEC_MavResult_ACCEPTED),
            MavResult::TEMPORARILY_REJECTED => Ok(SPEC_MavResult_TEMPORARILY_REJECTED),
            MavResult::DENIED => Ok(SPEC_MavResult_DENIED),
            MavResult::UNSUPPORTED => Ok(SPEC_MavResult_UNSUPPORTED),
            MavResult::FAILED => Ok(SPEC_MavResult_FAILED),
            MavResult::IN_PROGRESS => Ok(SPEC_MavResult_IN_PROGRESS),
            MavResult::CANCELLED => Ok(SPEC_MavResult_CANCELLED),
            MavResult::COMMAND_LONG_ONLY => Ok(SPEC_MavResult_COMMAND_LONG_ONLY),
            MavResult::COMMAND_INT_ONLY => Ok(SPEC_MavResult_COMMAND_INT_ONLY),
            MavResult::COMMAND_UNSUPPORTED_MAV_FRAME => Ok(SPEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME),
            MavResult::NOT_IN_CONTROL => Ok(SPEC_MavResult_NOT_IN_CONTROL),
        }
    }
}

impl TryFrom<MavResultInner> for MavResult {
    type Error = ();

    fn ex_try_from(v: MavResultInner) -> Result<MavResult, ()> {
        match v {
            0u8 => Ok(MavResult::ACCEPTED),
            1u8 => Ok(MavResult::TEMPORARILY_REJECTED),
            2u8 => Ok(MavResult::DENIED),
            3u8 => Ok(MavResult::UNSUPPORTED),
            4u8 => Ok(MavResult::FAILED),
            5u8 => Ok(MavResult::IN_PROGRESS),
            6u8 => Ok(MavResult::CANCELLED),
            7u8 => Ok(MavResult::COMMAND_LONG_ONLY),
            8u8 => Ok(MavResult::COMMAND_INT_ONLY),
            9u8 => Ok(MavResult::COMMAND_UNSUPPORTED_MAV_FRAME),
            10u8 => Ok(MavResult::NOT_IN_CONTROL),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a MavResult> for MavResultInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a MavResult) -> Result<MavResultInnerRef<'a>, ()> {
        match v {
            MavResult::ACCEPTED => Ok(&EXEC_MavResult_ACCEPTED),
            MavResult::TEMPORARILY_REJECTED => Ok(&EXEC_MavResult_TEMPORARILY_REJECTED),
            MavResult::DENIED => Ok(&EXEC_MavResult_DENIED),
            MavResult::UNSUPPORTED => Ok(&EXEC_MavResult_UNSUPPORTED),
            MavResult::FAILED => Ok(&EXEC_MavResult_FAILED),
            MavResult::IN_PROGRESS => Ok(&EXEC_MavResult_IN_PROGRESS),
            MavResult::CANCELLED => Ok(&EXEC_MavResult_CANCELLED),
            MavResult::COMMAND_LONG_ONLY => Ok(&EXEC_MavResult_COMMAND_LONG_ONLY),
            MavResult::COMMAND_INT_ONLY => Ok(&EXEC_MavResult_COMMAND_INT_ONLY),
            MavResult::COMMAND_UNSUPPORTED_MAV_FRAME => Ok(&EXEC_MavResult_COMMAND_UNSUPPORTED_MAV_FRAME),
            MavResult::NOT_IN_CONTROL => Ok(&EXEC_MavResult_NOT_IN_CONTROL),
        }
    }
}

pub struct MavResultMapper;

impl View for MavResultMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MavResultMapper {
    type Src = MavResultInner;
    type Dst = MavResult;
}

impl SpecPartialIsoProof for MavResultMapper {
    proof fn spec_iso(s: Self::Src) { 
        assert(
            Self::spec_apply(s) matches Ok(v) ==> {
            &&& Self::spec_rev_apply(v) is Ok
            &&& Self::spec_rev_apply(v) matches Ok(s_) && s == s_
        });
    }

    proof fn spec_iso_rev(s: Self::Dst) { 
        assert(
            Self::spec_rev_apply(s) matches Ok(v) ==> {
            &&& Self::spec_apply(v) is Ok
            &&& Self::spec_apply(v) matches Ok(s_) && s == s_
        });
    }
}

impl<'a> PartialIso<'a> for MavResultMapper {
    type Src = MavResultInner;
    type Dst = MavResult;
    type RefSrc = MavResultInnerRef<'a>;
}


pub struct SpecMavResultCombinator(pub SpecMavResultCombinatorAlias);

impl SpecCombinator for SpecMavResultCombinator {
    type Type = SpecMavResult;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavResultCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavResultCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavResultCombinatorAlias = TryMap<U8, MavResultMapper>;

pub struct MavResultCombinator(pub MavResultCombinatorAlias);

impl View for MavResultCombinator {
    type V = SpecMavResultCombinator;
    open spec fn view(&self) -> Self::V { SpecMavResultCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavResultCombinator {
    type Type = MavResult;
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
pub type MavResultCombinatorAlias = TryMap<U8, MavResultMapper>;


pub open spec fn spec_mav_result() -> SpecMavResultCombinator {
    SpecMavResultCombinator(TryMap { inner: U8, mapper: MavResultMapper })
}

                
pub fn mav_result<'a>() -> (o: MavResultCombinator)
    ensures o@ == spec_mav_result(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavResultCombinator(TryMap { inner: U8, mapper: MavResultMapper });
    assert({
        &&& combinator@ == spec_mav_result()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mav_result<'a>(input: &'a [u8]) -> (res: PResult<<MavResultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mav_result().spec_parse(input@) == Some((n as int, v@)),
        spec_mav_result().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mav_result().spec_parse(input@) is None,
        spec_mav_result().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mav_result();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mav_result<'a>(v: <MavResultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mav_result().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mav_result().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mav_result().spec_serialize(v@))
        },
{
    let combinator = mav_result();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mav_result_len<'a>(v: <MavResultCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mav_result().wf(v@),
        spec_mav_result().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mav_result().spec_serialize(v@).len(),
{
    let combinator = mav_result();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCommandAck {
    pub command: u16,
    pub result: SpecMavResult,
    pub progress: u8,
    pub result_param2: u32,
    pub target_system: u8,
    pub target_component: u8,
}

pub type SpecCommandAckInner = (u16, (SpecMavResult, (u8, (u32, (u8, u8)))));


impl SpecFrom<SpecCommandAck> for SpecCommandAckInner {
    open spec fn spec_from(m: SpecCommandAck) -> SpecCommandAckInner {
        (m.command, (m.result, (m.progress, (m.result_param2, (m.target_system, m.target_component)))))
    }
}

impl SpecFrom<SpecCommandAckInner> for SpecCommandAck {
    open spec fn spec_from(m: SpecCommandAckInner) -> SpecCommandAck {
        let (command, (result, (progress, (result_param2, (target_system, target_component))))) = m;
        SpecCommandAck { command, result, progress, result_param2, target_system, target_component }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CommandAck {
    pub command: u16,
    pub result: MavResult,
    pub progress: u8,
    pub result_param2: u32,
    pub target_system: u8,
    pub target_component: u8,
}

impl View for CommandAck {
    type V = SpecCommandAck;

    open spec fn view(&self) -> Self::V {
        SpecCommandAck {
            command: self.command@,
            result: self.result@,
            progress: self.progress@,
            result_param2: self.result_param2@,
            target_system: self.target_system@,
            target_component: self.target_component@,
        }
    }
}
pub type CommandAckInner = (u16, (MavResult, (u8, (u32, (u8, u8)))));

pub type CommandAckInnerRef<'a> = (&'a u16, (&'a MavResult, (&'a u8, (&'a u32, (&'a u8, &'a u8)))));
impl<'a> From<&'a CommandAck> for CommandAckInnerRef<'a> {
    fn ex_from(m: &'a CommandAck) -> CommandAckInnerRef<'a> {
        (&m.command, (&m.result, (&m.progress, (&m.result_param2, (&m.target_system, &m.target_component)))))
    }
}

impl From<CommandAckInner> for CommandAck {
    fn ex_from(m: CommandAckInner) -> CommandAck {
        let (command, (result, (progress, (result_param2, (target_system, target_component))))) = m;
        CommandAck { command, result, progress, result_param2, target_system, target_component }
    }
}

pub struct CommandAckMapper;
impl View for CommandAckMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CommandAckMapper {
    type Src = SpecCommandAckInner;
    type Dst = SpecCommandAck;
}
impl SpecIsoProof for CommandAckMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CommandAckMapper {
    type Src = CommandAckInner;
    type Dst = CommandAck;
    type RefSrc = CommandAckInnerRef<'a>;
}
type SpecCommandAckCombinatorAlias1 = (U8, U8);
type SpecCommandAckCombinatorAlias2 = (U32Le, SpecCommandAckCombinatorAlias1);
type SpecCommandAckCombinatorAlias3 = (Refined<U8, Predicate5789190955059586907>, SpecCommandAckCombinatorAlias2);
type SpecCommandAckCombinatorAlias4 = (SpecMavResultCombinator, SpecCommandAckCombinatorAlias3);
type SpecCommandAckCombinatorAlias5 = (SpecMavCmdCombinator, SpecCommandAckCombinatorAlias4);
pub struct SpecCommandAckCombinator(pub SpecCommandAckCombinatorAlias);

impl SpecCombinator for SpecCommandAckCombinator {
    type Type = SpecCommandAck;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCommandAckCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCommandAckCombinatorAlias::is_prefix_secure() }
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
pub type SpecCommandAckCombinatorAlias = Mapped<SpecCommandAckCombinatorAlias5, CommandAckMapper>;
pub struct Predicate5789190955059586907;
impl View for Predicate5789190955059586907 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate5789190955059586907 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 101) || (i == 255)
    }
}
impl SpecPred<u8> for Predicate5789190955059586907 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 101) || (i == 255)
    }
}
type CommandAckCombinatorAlias1 = (U8, U8);
type CommandAckCombinatorAlias2 = (U32Le, CommandAckCombinator1);
type CommandAckCombinatorAlias3 = (Refined<U8, Predicate5789190955059586907>, CommandAckCombinator2);
type CommandAckCombinatorAlias4 = (MavResultCombinator, CommandAckCombinator3);
type CommandAckCombinatorAlias5 = (MavCmdCombinator, CommandAckCombinator4);
pub struct CommandAckCombinator1(pub CommandAckCombinatorAlias1);
impl View for CommandAckCombinator1 {
    type V = SpecCommandAckCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandAckCombinator1, CommandAckCombinatorAlias1);

pub struct CommandAckCombinator2(pub CommandAckCombinatorAlias2);
impl View for CommandAckCombinator2 {
    type V = SpecCommandAckCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandAckCombinator2, CommandAckCombinatorAlias2);

pub struct CommandAckCombinator3(pub CommandAckCombinatorAlias3);
impl View for CommandAckCombinator3 {
    type V = SpecCommandAckCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandAckCombinator3, CommandAckCombinatorAlias3);

pub struct CommandAckCombinator4(pub CommandAckCombinatorAlias4);
impl View for CommandAckCombinator4 {
    type V = SpecCommandAckCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandAckCombinator4, CommandAckCombinatorAlias4);

pub struct CommandAckCombinator5(pub CommandAckCombinatorAlias5);
impl View for CommandAckCombinator5 {
    type V = SpecCommandAckCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CommandAckCombinator5, CommandAckCombinatorAlias5);

pub struct CommandAckCombinator(pub CommandAckCombinatorAlias);

impl View for CommandAckCombinator {
    type V = SpecCommandAckCombinator;
    open spec fn view(&self) -> Self::V { SpecCommandAckCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CommandAckCombinator {
    type Type = CommandAck;
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
pub type CommandAckCombinatorAlias = Mapped<CommandAckCombinator5, CommandAckMapper>;


pub open spec fn spec_command_ack() -> SpecCommandAckCombinator {
    SpecCommandAckCombinator(
    Mapped {
        inner: (spec_mav_cmd(), (spec_mav_result(), (Refined { inner: U8, predicate: Predicate5789190955059586907 }, (U32Le, (U8, U8))))),
        mapper: CommandAckMapper,
    })
}

                
pub fn command_ack<'a>() -> (o: CommandAckCombinator)
    ensures o@ == spec_command_ack(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CommandAckCombinator(
    Mapped {
        inner: CommandAckCombinator5((mav_cmd(), CommandAckCombinator4((mav_result(), CommandAckCombinator3((Refined { inner: U8, predicate: Predicate5789190955059586907 }, CommandAckCombinator2((U32Le, CommandAckCombinator1((U8, U8)))))))))),
        mapper: CommandAckMapper,
    });
    assert({
        &&& combinator@ == spec_command_ack()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_command_ack<'a>(input: &'a [u8]) -> (res: PResult<<CommandAckCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_command_ack().spec_parse(input@) == Some((n as int, v@)),
        spec_command_ack().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_command_ack().spec_parse(input@) is None,
        spec_command_ack().spec_parse(input@) is None ==> res is Err,
{
    let combinator = command_ack();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_command_ack<'a>(v: <CommandAckCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_command_ack().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_command_ack().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_command_ack().spec_serialize(v@))
        },
{
    let combinator = command_ack();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn command_ack_len<'a>(v: <CommandAckCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_command_ack().wf(v@),
        spec_command_ack().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_command_ack().spec_serialize(v@).len(),
{
    let combinator = command_ack();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTerrainRequest {
    pub lat: u32,
    pub lon: u32,
    pub grid_spacing: u16,
    pub mask: u64,
}

pub type SpecTerrainRequestInner = (u32, (u32, (u16, u64)));


impl SpecFrom<SpecTerrainRequest> for SpecTerrainRequestInner {
    open spec fn spec_from(m: SpecTerrainRequest) -> SpecTerrainRequestInner {
        (m.lat, (m.lon, (m.grid_spacing, m.mask)))
    }
}

impl SpecFrom<SpecTerrainRequestInner> for SpecTerrainRequest {
    open spec fn spec_from(m: SpecTerrainRequestInner) -> SpecTerrainRequest {
        let (lat, (lon, (grid_spacing, mask))) = m;
        SpecTerrainRequest { lat, lon, grid_spacing, mask }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TerrainRequest {
    pub lat: u32,
    pub lon: u32,
    pub grid_spacing: u16,
    pub mask: u64,
}

impl View for TerrainRequest {
    type V = SpecTerrainRequest;

    open spec fn view(&self) -> Self::V {
        SpecTerrainRequest {
            lat: self.lat@,
            lon: self.lon@,
            grid_spacing: self.grid_spacing@,
            mask: self.mask@,
        }
    }
}
pub type TerrainRequestInner = (u32, (u32, (u16, u64)));

pub type TerrainRequestInnerRef<'a> = (&'a u32, (&'a u32, (&'a u16, &'a u64)));
impl<'a> From<&'a TerrainRequest> for TerrainRequestInnerRef<'a> {
    fn ex_from(m: &'a TerrainRequest) -> TerrainRequestInnerRef<'a> {
        (&m.lat, (&m.lon, (&m.grid_spacing, &m.mask)))
    }
}

impl From<TerrainRequestInner> for TerrainRequest {
    fn ex_from(m: TerrainRequestInner) -> TerrainRequest {
        let (lat, (lon, (grid_spacing, mask))) = m;
        TerrainRequest { lat, lon, grid_spacing, mask }
    }
}

pub struct TerrainRequestMapper;
impl View for TerrainRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TerrainRequestMapper {
    type Src = SpecTerrainRequestInner;
    type Dst = SpecTerrainRequest;
}
impl SpecIsoProof for TerrainRequestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TerrainRequestMapper {
    type Src = TerrainRequestInner;
    type Dst = TerrainRequest;
    type RefSrc = TerrainRequestInnerRef<'a>;
}
type SpecTerrainRequestCombinatorAlias1 = (U16Le, U64Le);
type SpecTerrainRequestCombinatorAlias2 = (U32Le, SpecTerrainRequestCombinatorAlias1);
type SpecTerrainRequestCombinatorAlias3 = (U32Le, SpecTerrainRequestCombinatorAlias2);
pub struct SpecTerrainRequestCombinator(pub SpecTerrainRequestCombinatorAlias);

impl SpecCombinator for SpecTerrainRequestCombinator {
    type Type = SpecTerrainRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTerrainRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTerrainRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecTerrainRequestCombinatorAlias = Mapped<SpecTerrainRequestCombinatorAlias3, TerrainRequestMapper>;
type TerrainRequestCombinatorAlias1 = (U16Le, U64Le);
type TerrainRequestCombinatorAlias2 = (U32Le, TerrainRequestCombinator1);
type TerrainRequestCombinatorAlias3 = (U32Le, TerrainRequestCombinator2);
pub struct TerrainRequestCombinator1(pub TerrainRequestCombinatorAlias1);
impl View for TerrainRequestCombinator1 {
    type V = SpecTerrainRequestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TerrainRequestCombinator1, TerrainRequestCombinatorAlias1);

pub struct TerrainRequestCombinator2(pub TerrainRequestCombinatorAlias2);
impl View for TerrainRequestCombinator2 {
    type V = SpecTerrainRequestCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TerrainRequestCombinator2, TerrainRequestCombinatorAlias2);

pub struct TerrainRequestCombinator3(pub TerrainRequestCombinatorAlias3);
impl View for TerrainRequestCombinator3 {
    type V = SpecTerrainRequestCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TerrainRequestCombinator3, TerrainRequestCombinatorAlias3);

pub struct TerrainRequestCombinator(pub TerrainRequestCombinatorAlias);

impl View for TerrainRequestCombinator {
    type V = SpecTerrainRequestCombinator;
    open spec fn view(&self) -> Self::V { SpecTerrainRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TerrainRequestCombinator {
    type Type = TerrainRequest;
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
pub type TerrainRequestCombinatorAlias = Mapped<TerrainRequestCombinator3, TerrainRequestMapper>;


pub open spec fn spec_terrain_request() -> SpecTerrainRequestCombinator {
    SpecTerrainRequestCombinator(
    Mapped {
        inner: (U32Le, (U32Le, (U16Le, U64Le))),
        mapper: TerrainRequestMapper,
    })
}

                
pub fn terrain_request<'a>() -> (o: TerrainRequestCombinator)
    ensures o@ == spec_terrain_request(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TerrainRequestCombinator(
    Mapped {
        inner: TerrainRequestCombinator3((U32Le, TerrainRequestCombinator2((U32Le, TerrainRequestCombinator1((U16Le, U64Le)))))),
        mapper: TerrainRequestMapper,
    });
    assert({
        &&& combinator@ == spec_terrain_request()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_terrain_request<'a>(input: &'a [u8]) -> (res: PResult<<TerrainRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_terrain_request().spec_parse(input@) == Some((n as int, v@)),
        spec_terrain_request().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_terrain_request().spec_parse(input@) is None,
        spec_terrain_request().spec_parse(input@) is None ==> res is Err,
{
    let combinator = terrain_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_terrain_request<'a>(v: <TerrainRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_terrain_request().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_terrain_request().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_terrain_request().spec_serialize(v@))
        },
{
    let combinator = terrain_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn terrain_request_len<'a>(v: <TerrainRequestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_terrain_request().wf(v@),
        spec_terrain_request().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_terrain_request().spec_serialize(v@).len(),
{
    let combinator = terrain_request();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecMavlinkV2MsgPayload {
    CommandInt(SpecCommandInt),
    CommandLong(SpecCommandLong),
    CommandAck(SpecCommandAck),
    TerrainRequest(SpecTerrainRequest),
    Unrecognized(Seq<u8>),
}

pub type SpecMavlinkV2MsgPayloadInner = Either<SpecCommandInt, Either<SpecCommandLong, Either<SpecCommandAck, Either<SpecTerrainRequest, Seq<u8>>>>>;

impl SpecFrom<SpecMavlinkV2MsgPayload> for SpecMavlinkV2MsgPayloadInner {
    open spec fn spec_from(m: SpecMavlinkV2MsgPayload) -> SpecMavlinkV2MsgPayloadInner {
        match m {
            SpecMavlinkV2MsgPayload::CommandInt(m) => Either::Left(m),
            SpecMavlinkV2MsgPayload::CommandLong(m) => Either::Right(Either::Left(m)),
            SpecMavlinkV2MsgPayload::CommandAck(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMavlinkV2MsgPayload::TerrainRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecMavlinkV2MsgPayload::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

                
impl SpecFrom<SpecMavlinkV2MsgPayloadInner> for SpecMavlinkV2MsgPayload {
    open spec fn spec_from(m: SpecMavlinkV2MsgPayloadInner) -> SpecMavlinkV2MsgPayload {
        match m {
            Either::Left(m) => SpecMavlinkV2MsgPayload::CommandInt(m),
            Either::Right(Either::Left(m)) => SpecMavlinkV2MsgPayload::CommandLong(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMavlinkV2MsgPayload::CommandAck(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecMavlinkV2MsgPayload::TerrainRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => SpecMavlinkV2MsgPayload::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MavlinkV2MsgPayload<'a> {
    CommandInt(CommandInt),
    CommandLong(CommandLong),
    CommandAck(CommandAck),
    TerrainRequest(TerrainRequest),
    Unrecognized(&'a [u8]),
}

pub type MavlinkV2MsgPayloadInner<'a> = Either<CommandInt, Either<CommandLong, Either<CommandAck, Either<TerrainRequest, &'a [u8]>>>>;

pub type MavlinkV2MsgPayloadInnerRef<'a> = Either<&'a CommandInt, Either<&'a CommandLong, Either<&'a CommandAck, Either<&'a TerrainRequest, &'a &'a [u8]>>>>;


impl<'a> View for MavlinkV2MsgPayload<'a> {
    type V = SpecMavlinkV2MsgPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            MavlinkV2MsgPayload::CommandInt(m) => SpecMavlinkV2MsgPayload::CommandInt(m@),
            MavlinkV2MsgPayload::CommandLong(m) => SpecMavlinkV2MsgPayload::CommandLong(m@),
            MavlinkV2MsgPayload::CommandAck(m) => SpecMavlinkV2MsgPayload::CommandAck(m@),
            MavlinkV2MsgPayload::TerrainRequest(m) => SpecMavlinkV2MsgPayload::TerrainRequest(m@),
            MavlinkV2MsgPayload::Unrecognized(m) => SpecMavlinkV2MsgPayload::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a MavlinkV2MsgPayload<'a>> for MavlinkV2MsgPayloadInnerRef<'a> {
    fn ex_from(m: &'a MavlinkV2MsgPayload<'a>) -> MavlinkV2MsgPayloadInnerRef<'a> {
        match m {
            MavlinkV2MsgPayload::CommandInt(m) => Either::Left(m),
            MavlinkV2MsgPayload::CommandLong(m) => Either::Right(Either::Left(m)),
            MavlinkV2MsgPayload::CommandAck(m) => Either::Right(Either::Right(Either::Left(m))),
            MavlinkV2MsgPayload::TerrainRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            MavlinkV2MsgPayload::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

impl<'a> From<MavlinkV2MsgPayloadInner<'a>> for MavlinkV2MsgPayload<'a> {
    fn ex_from(m: MavlinkV2MsgPayloadInner<'a>) -> MavlinkV2MsgPayload<'a> {
        match m {
            Either::Left(m) => MavlinkV2MsgPayload::CommandInt(m),
            Either::Right(Either::Left(m)) => MavlinkV2MsgPayload::CommandLong(m),
            Either::Right(Either::Right(Either::Left(m))) => MavlinkV2MsgPayload::CommandAck(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => MavlinkV2MsgPayload::TerrainRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => MavlinkV2MsgPayload::Unrecognized(m),
        }
    }
    
}


pub struct MavlinkV2MsgPayloadMapper;
impl View for MavlinkV2MsgPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkV2MsgPayloadMapper {
    type Src = SpecMavlinkV2MsgPayloadInner;
    type Dst = SpecMavlinkV2MsgPayload;
}
impl SpecIsoProof for MavlinkV2MsgPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkV2MsgPayloadMapper {
    type Src = MavlinkV2MsgPayloadInner<'a>;
    type Dst = MavlinkV2MsgPayload<'a>;
    type RefSrc = MavlinkV2MsgPayloadInnerRef<'a>;
}

type SpecMavlinkV2MsgPayloadCombinatorAlias1 = Choice<Cond<SpecTerrainRequestCombinator>, Cond<bytes::Variable>>;
type SpecMavlinkV2MsgPayloadCombinatorAlias2 = Choice<Cond<SpecCommandAckCombinator>, SpecMavlinkV2MsgPayloadCombinatorAlias1>;
type SpecMavlinkV2MsgPayloadCombinatorAlias3 = Choice<Cond<SpecCommandLongCombinator>, SpecMavlinkV2MsgPayloadCombinatorAlias2>;
type SpecMavlinkV2MsgPayloadCombinatorAlias4 = Choice<Cond<SpecCommandIntCombinator>, SpecMavlinkV2MsgPayloadCombinatorAlias3>;
pub struct SpecMavlinkV2MsgPayloadCombinator(pub SpecMavlinkV2MsgPayloadCombinatorAlias);

impl SpecCombinator for SpecMavlinkV2MsgPayloadCombinator {
    type Type = SpecMavlinkV2MsgPayload;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkV2MsgPayloadCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkV2MsgPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkV2MsgPayloadCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecMavlinkV2MsgPayloadCombinatorAlias4, MavlinkV2MsgPayloadMapper>>;
type MavlinkV2MsgPayloadCombinatorAlias1 = Choice<Cond<TerrainRequestCombinator>, Cond<bytes::Variable>>;
type MavlinkV2MsgPayloadCombinatorAlias2 = Choice<Cond<CommandAckCombinator>, MavlinkV2MsgPayloadCombinator1>;
type MavlinkV2MsgPayloadCombinatorAlias3 = Choice<Cond<CommandLongCombinator>, MavlinkV2MsgPayloadCombinator2>;
type MavlinkV2MsgPayloadCombinatorAlias4 = Choice<Cond<CommandIntCombinator>, MavlinkV2MsgPayloadCombinator3>;
pub struct MavlinkV2MsgPayloadCombinator1(pub MavlinkV2MsgPayloadCombinatorAlias1);
impl View for MavlinkV2MsgPayloadCombinator1 {
    type V = SpecMavlinkV2MsgPayloadCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkV2MsgPayloadCombinator1, MavlinkV2MsgPayloadCombinatorAlias1);

pub struct MavlinkV2MsgPayloadCombinator2(pub MavlinkV2MsgPayloadCombinatorAlias2);
impl View for MavlinkV2MsgPayloadCombinator2 {
    type V = SpecMavlinkV2MsgPayloadCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkV2MsgPayloadCombinator2, MavlinkV2MsgPayloadCombinatorAlias2);

pub struct MavlinkV2MsgPayloadCombinator3(pub MavlinkV2MsgPayloadCombinatorAlias3);
impl View for MavlinkV2MsgPayloadCombinator3 {
    type V = SpecMavlinkV2MsgPayloadCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkV2MsgPayloadCombinator3, MavlinkV2MsgPayloadCombinatorAlias3);

pub struct MavlinkV2MsgPayloadCombinator4(pub MavlinkV2MsgPayloadCombinatorAlias4);
impl View for MavlinkV2MsgPayloadCombinator4 {
    type V = SpecMavlinkV2MsgPayloadCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkV2MsgPayloadCombinator4, MavlinkV2MsgPayloadCombinatorAlias4);

pub struct MavlinkV2MsgPayloadCombinator(pub MavlinkV2MsgPayloadCombinatorAlias);

impl View for MavlinkV2MsgPayloadCombinator {
    type V = SpecMavlinkV2MsgPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkV2MsgPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkV2MsgPayloadCombinator {
    type Type = MavlinkV2MsgPayload<'a>;
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
pub type MavlinkV2MsgPayloadCombinatorAlias = AndThen<bytes::Variable, Mapped<MavlinkV2MsgPayloadCombinator4, MavlinkV2MsgPayloadMapper>>;


pub open spec fn spec_mavlink_v2_msg_payload(msgid: u24, len: u8) -> SpecMavlinkV2MsgPayloadCombinator {
    SpecMavlinkV2MsgPayloadCombinator(AndThen(bytes::Variable(len.spec_into()), Mapped { inner: Choice(Cond { cond: msgid.spec_as_u32() == MessageIds::SPEC_CommandInt, inner: spec_command_int() }, Choice(Cond { cond: msgid.spec_as_u32() == MessageIds::SPEC_CommandLong, inner: spec_command_long() }, Choice(Cond { cond: msgid.spec_as_u32() == MessageIds::SPEC_CommandAck, inner: spec_command_ack() }, Choice(Cond { cond: msgid.spec_as_u32() == MessageIds::SPEC_TerrainRequest, inner: spec_terrain_request() }, Cond { cond: !(msgid.spec_as_u32() == MessageIds::SPEC_CommandInt || msgid.spec_as_u32() == MessageIds::SPEC_CommandLong || msgid.spec_as_u32() == MessageIds::SPEC_CommandAck || msgid.spec_as_u32() == MessageIds::SPEC_TerrainRequest), inner: bytes::Variable(len.spec_into()) })))), mapper: MavlinkV2MsgPayloadMapper }))
}

pub fn mavlink_v2_msg_payload<'a>(msgid: u24, len: u8) -> (o: MavlinkV2MsgPayloadCombinator)
    ensures o@ == spec_mavlink_v2_msg_payload(msgid@, len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkV2MsgPayloadCombinator(AndThen(bytes::Variable(len.ex_into()), Mapped { inner: MavlinkV2MsgPayloadCombinator4(Choice::new(Cond { cond: msgid.as_u32() == MessageIds::CommandInt, inner: command_int() }, MavlinkV2MsgPayloadCombinator3(Choice::new(Cond { cond: msgid.as_u32() == MessageIds::CommandLong, inner: command_long() }, MavlinkV2MsgPayloadCombinator2(Choice::new(Cond { cond: msgid.as_u32() == MessageIds::CommandAck, inner: command_ack() }, MavlinkV2MsgPayloadCombinator1(Choice::new(Cond { cond: msgid.as_u32() == MessageIds::TerrainRequest, inner: terrain_request() }, Cond { cond: !(msgid.as_u32() == MessageIds::CommandInt || msgid.as_u32() == MessageIds::CommandLong || msgid.as_u32() == MessageIds::CommandAck || msgid.as_u32() == MessageIds::TerrainRequest), inner: bytes::Variable(len.ex_into()) })))))))), mapper: MavlinkV2MsgPayloadMapper }));
    assert({
        &&& combinator@ == spec_mavlink_v2_msg_payload(msgid@, len@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_v2_msg_payload<'a>(input: &'a [u8], msgid: u24, len: u8) -> (res: PResult<<MavlinkV2MsgPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_v2_msg_payload(msgid@, len@).spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_v2_msg_payload(msgid@, len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_v2_msg_payload(msgid@, len@).spec_parse(input@) is None,
        spec_mavlink_v2_msg_payload(msgid@, len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_v2_msg_payload( msgid, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_v2_msg_payload<'a>(v: <MavlinkV2MsgPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, msgid: u24, len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_v2_msg_payload(msgid@, len@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_v2_msg_payload(msgid@, len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_v2_msg_payload(msgid@, len@).spec_serialize(v@))
        },
{
    let combinator = mavlink_v2_msg_payload( msgid, len );
    combinator.serialize(v, data, pos)
}

pub fn mavlink_v2_msg_payload_len<'a>(v: <MavlinkV2MsgPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, msgid: u24, len: u8) -> (serialize_len: usize)
    requires
        spec_mavlink_v2_msg_payload(msgid@, len@).wf(v@),
        spec_mavlink_v2_msg_payload(msgid@, len@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_v2_msg_payload(msgid@, len@).spec_serialize(v@).len(),
{
    let combinator = mavlink_v2_msg_payload( msgid, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecMavlinkV2MsgSignature {
    Variant0(Seq<u8>),
    Variant1(Seq<u8>),
}

pub type SpecMavlinkV2MsgSignatureInner = Either<Seq<u8>, Seq<u8>>;

impl SpecFrom<SpecMavlinkV2MsgSignature> for SpecMavlinkV2MsgSignatureInner {
    open spec fn spec_from(m: SpecMavlinkV2MsgSignature) -> SpecMavlinkV2MsgSignatureInner {
        match m {
            SpecMavlinkV2MsgSignature::Variant0(m) => Either::Left(m),
            SpecMavlinkV2MsgSignature::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMavlinkV2MsgSignatureInner> for SpecMavlinkV2MsgSignature {
    open spec fn spec_from(m: SpecMavlinkV2MsgSignatureInner) -> SpecMavlinkV2MsgSignature {
        match m {
            Either::Left(m) => SpecMavlinkV2MsgSignature::Variant0(m),
            Either::Right(m) => SpecMavlinkV2MsgSignature::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MavlinkV2MsgSignature<'a> {
    Variant0(&'a [u8]),
    Variant1(&'a [u8]),
}

pub type MavlinkV2MsgSignatureInner<'a> = Either<&'a [u8], &'a [u8]>;

pub type MavlinkV2MsgSignatureInnerRef<'a> = Either<&'a &'a [u8], &'a &'a [u8]>;


impl<'a> View for MavlinkV2MsgSignature<'a> {
    type V = SpecMavlinkV2MsgSignature;
    open spec fn view(&self) -> Self::V {
        match self {
            MavlinkV2MsgSignature::Variant0(m) => SpecMavlinkV2MsgSignature::Variant0(m@),
            MavlinkV2MsgSignature::Variant1(m) => SpecMavlinkV2MsgSignature::Variant1(m@),
        }
    }
}


impl<'a> From<&'a MavlinkV2MsgSignature<'a>> for MavlinkV2MsgSignatureInnerRef<'a> {
    fn ex_from(m: &'a MavlinkV2MsgSignature<'a>) -> MavlinkV2MsgSignatureInnerRef<'a> {
        match m {
            MavlinkV2MsgSignature::Variant0(m) => Either::Left(m),
            MavlinkV2MsgSignature::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<MavlinkV2MsgSignatureInner<'a>> for MavlinkV2MsgSignature<'a> {
    fn ex_from(m: MavlinkV2MsgSignatureInner<'a>) -> MavlinkV2MsgSignature<'a> {
        match m {
            Either::Left(m) => MavlinkV2MsgSignature::Variant0(m),
            Either::Right(m) => MavlinkV2MsgSignature::Variant1(m),
        }
    }
    
}


pub struct MavlinkV2MsgSignatureMapper;
impl View for MavlinkV2MsgSignatureMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkV2MsgSignatureMapper {
    type Src = SpecMavlinkV2MsgSignatureInner;
    type Dst = SpecMavlinkV2MsgSignature;
}
impl SpecIsoProof for MavlinkV2MsgSignatureMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkV2MsgSignatureMapper {
    type Src = MavlinkV2MsgSignatureInner<'a>;
    type Dst = MavlinkV2MsgSignature<'a>;
    type RefSrc = MavlinkV2MsgSignatureInnerRef<'a>;
}

type SpecMavlinkV2MsgSignatureCombinatorAlias1 = Choice<Cond<bytes::Fixed<13>>, Cond<bytes::Fixed<0>>>;
pub struct SpecMavlinkV2MsgSignatureCombinator(pub SpecMavlinkV2MsgSignatureCombinatorAlias);

impl SpecCombinator for SpecMavlinkV2MsgSignatureCombinator {
    type Type = SpecMavlinkV2MsgSignature;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkV2MsgSignatureCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkV2MsgSignatureCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkV2MsgSignatureCombinatorAlias = Mapped<SpecMavlinkV2MsgSignatureCombinatorAlias1, MavlinkV2MsgSignatureMapper>;
type MavlinkV2MsgSignatureCombinatorAlias1 = Choice<Cond<bytes::Fixed<13>>, Cond<bytes::Fixed<0>>>;
pub struct MavlinkV2MsgSignatureCombinator1(pub MavlinkV2MsgSignatureCombinatorAlias1);
impl View for MavlinkV2MsgSignatureCombinator1 {
    type V = SpecMavlinkV2MsgSignatureCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkV2MsgSignatureCombinator1, MavlinkV2MsgSignatureCombinatorAlias1);

pub struct MavlinkV2MsgSignatureCombinator(pub MavlinkV2MsgSignatureCombinatorAlias);

impl View for MavlinkV2MsgSignatureCombinator {
    type V = SpecMavlinkV2MsgSignatureCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkV2MsgSignatureCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkV2MsgSignatureCombinator {
    type Type = MavlinkV2MsgSignature<'a>;
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
pub type MavlinkV2MsgSignatureCombinatorAlias = Mapped<MavlinkV2MsgSignatureCombinator1, MavlinkV2MsgSignatureMapper>;


pub open spec fn spec_mavlink_v2_msg_signature(incompat_flags: u8) -> SpecMavlinkV2MsgSignatureCombinator {
    SpecMavlinkV2MsgSignatureCombinator(Mapped { inner: Choice(Cond { cond: incompat_flags == 1, inner: bytes::Fixed::<13> }, Cond { cond: !(incompat_flags == 1), inner: bytes::Fixed::<0> }), mapper: MavlinkV2MsgSignatureMapper })
}

pub fn mavlink_v2_msg_signature<'a>(incompat_flags: u8) -> (o: MavlinkV2MsgSignatureCombinator)
    ensures o@ == spec_mavlink_v2_msg_signature(incompat_flags@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkV2MsgSignatureCombinator(Mapped { inner: MavlinkV2MsgSignatureCombinator1(Choice::new(Cond { cond: incompat_flags == 1, inner: bytes::Fixed::<13> }, Cond { cond: !(incompat_flags == 1), inner: bytes::Fixed::<0> })), mapper: MavlinkV2MsgSignatureMapper });
    assert({
        &&& combinator@ == spec_mavlink_v2_msg_signature(incompat_flags@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_v2_msg_signature<'a>(input: &'a [u8], incompat_flags: u8) -> (res: PResult<<MavlinkV2MsgSignatureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_v2_msg_signature(incompat_flags@).spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_v2_msg_signature(incompat_flags@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_v2_msg_signature(incompat_flags@).spec_parse(input@) is None,
        spec_mavlink_v2_msg_signature(incompat_flags@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_v2_msg_signature( incompat_flags );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_v2_msg_signature<'a>(v: <MavlinkV2MsgSignatureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, incompat_flags: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_v2_msg_signature(incompat_flags@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_v2_msg_signature(incompat_flags@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_v2_msg_signature(incompat_flags@).spec_serialize(v@))
        },
{
    let combinator = mavlink_v2_msg_signature( incompat_flags );
    combinator.serialize(v, data, pos)
}

pub fn mavlink_v2_msg_signature_len<'a>(v: <MavlinkV2MsgSignatureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, incompat_flags: u8) -> (serialize_len: usize)
    requires
        spec_mavlink_v2_msg_signature(incompat_flags@).wf(v@),
        spec_mavlink_v2_msg_signature(incompat_flags@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_v2_msg_signature(incompat_flags@).spec_serialize(v@).len(),
{
    let combinator = mavlink_v2_msg_signature( incompat_flags );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMavlinkV2Msg {
    pub len: u8,
    pub incompat_flags: u8,
    pub compat_flags: u8,
    pub seq: u8,
    pub sysid: u8,
    pub compid: u8,
    pub msgid: u24,
    pub payload: SpecMavlinkV2MsgPayload,
    pub checksum: u16,
    pub signature: SpecMavlinkV2MsgSignature,
}

pub type SpecMavlinkV2MsgInner = (((u8, u8), (u8, (u8, (u8, (u8, u24))))), (SpecMavlinkV2MsgPayload, (u16, SpecMavlinkV2MsgSignature)));


impl SpecFrom<SpecMavlinkV2Msg> for SpecMavlinkV2MsgInner {
    open spec fn spec_from(m: SpecMavlinkV2Msg) -> SpecMavlinkV2MsgInner {
        (((m.len, m.incompat_flags), (m.compat_flags, (m.seq, (m.sysid, (m.compid, m.msgid))))), (m.payload, (m.checksum, m.signature)))
    }
}

impl SpecFrom<SpecMavlinkV2MsgInner> for SpecMavlinkV2Msg {
    open spec fn spec_from(m: SpecMavlinkV2MsgInner) -> SpecMavlinkV2Msg {
        let (((len, incompat_flags), (compat_flags, (seq, (sysid, (compid, msgid))))), (payload, (checksum, signature))) = m;
        SpecMavlinkV2Msg { len, incompat_flags, compat_flags, seq, sysid, compid, msgid, payload, checksum, signature }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MavlinkV2Msg<'a> {
    pub len: u8,
    pub incompat_flags: u8,
    pub compat_flags: u8,
    pub seq: u8,
    pub sysid: u8,
    pub compid: u8,
    pub msgid: u24,
    pub payload: MavlinkV2MsgPayload<'a>,
    pub checksum: u16,
    pub signature: MavlinkV2MsgSignature<'a>,
}

impl View for MavlinkV2Msg<'_> {
    type V = SpecMavlinkV2Msg;

    open spec fn view(&self) -> Self::V {
        SpecMavlinkV2Msg {
            len: self.len@,
            incompat_flags: self.incompat_flags@,
            compat_flags: self.compat_flags@,
            seq: self.seq@,
            sysid: self.sysid@,
            compid: self.compid@,
            msgid: self.msgid@,
            payload: self.payload@,
            checksum: self.checksum@,
            signature: self.signature@,
        }
    }
}
pub type MavlinkV2MsgInner<'a> = (((u8, u8), (u8, (u8, (u8, (u8, u24))))), (MavlinkV2MsgPayload<'a>, (u16, MavlinkV2MsgSignature<'a>)));

pub type MavlinkV2MsgInnerRef<'a> = (((&'a u8, &'a u8), (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u24))))), (&'a MavlinkV2MsgPayload<'a>, (&'a u16, &'a MavlinkV2MsgSignature<'a>)));
impl<'a> From<&'a MavlinkV2Msg<'a>> for MavlinkV2MsgInnerRef<'a> {
    fn ex_from(m: &'a MavlinkV2Msg) -> MavlinkV2MsgInnerRef<'a> {
        (((&m.len, &m.incompat_flags), (&m.compat_flags, (&m.seq, (&m.sysid, (&m.compid, &m.msgid))))), (&m.payload, (&m.checksum, &m.signature)))
    }
}

impl<'a> From<MavlinkV2MsgInner<'a>> for MavlinkV2Msg<'a> {
    fn ex_from(m: MavlinkV2MsgInner) -> MavlinkV2Msg {
        let (((len, incompat_flags), (compat_flags, (seq, (sysid, (compid, msgid))))), (payload, (checksum, signature))) = m;
        MavlinkV2Msg { len, incompat_flags, compat_flags, seq, sysid, compid, msgid, payload, checksum, signature }
    }
}

pub struct MavlinkV2MsgMapper;
impl View for MavlinkV2MsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkV2MsgMapper {
    type Src = SpecMavlinkV2MsgInner;
    type Dst = SpecMavlinkV2Msg;
}
impl SpecIsoProof for MavlinkV2MsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkV2MsgMapper {
    type Src = MavlinkV2MsgInner<'a>;
    type Dst = MavlinkV2Msg<'a>;
    type RefSrc = MavlinkV2MsgInnerRef<'a>;
}

pub struct SpecMavlinkV2MsgCombinator(pub SpecMavlinkV2MsgCombinatorAlias);

impl SpecCombinator for SpecMavlinkV2MsgCombinator {
    type Type = SpecMavlinkV2Msg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkV2MsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkV2MsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkV2MsgCombinatorAlias = Mapped<SpecPair<SpecPair<SpecPair<U8, SpecIncompatFlagsCombinator>, (U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, SpecMessageIdsCombinator))))>, (SpecMavlinkV2MsgPayloadCombinator, (U16Le, SpecMavlinkV2MsgSignatureCombinator))>, MavlinkV2MsgMapper>;

pub struct MavlinkV2MsgCombinator(pub MavlinkV2MsgCombinatorAlias);

impl View for MavlinkV2MsgCombinator {
    type V = SpecMavlinkV2MsgCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkV2MsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkV2MsgCombinator {
    type Type = MavlinkV2Msg<'a>;
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
pub type MavlinkV2MsgCombinatorAlias = Mapped<Pair<Pair<Pair<U8, IncompatFlagsCombinator, MavlinkV2MsgCont2>, (U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, MessageIdsCombinator)))), MavlinkV2MsgCont1>, (MavlinkV2MsgPayloadCombinator, (U16Le, MavlinkV2MsgSignatureCombinator)), MavlinkV2MsgCont0>, MavlinkV2MsgMapper>;


pub open spec fn spec_mavlink_v2_msg() -> SpecMavlinkV2MsgCombinator {
    SpecMavlinkV2MsgCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(Pair::spec_new(U8, |deps| spec_mavlink_v2_msg_cont2(deps)), |deps| spec_mavlink_v2_msg_cont1(deps)), |deps| spec_mavlink_v2_msg_cont0(deps)),
        mapper: MavlinkV2MsgMapper,
    })
}

pub open spec fn spec_mavlink_v2_msg_cont2(deps: u8) -> SpecIncompatFlagsCombinator {
    let len = deps;
    spec_incompat_flags()
}

impl View for MavlinkV2MsgCont2 {
    type V = spec_fn(u8) -> SpecIncompatFlagsCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_mavlink_v2_msg_cont2(deps)
        }
    }
}

pub open spec fn spec_mavlink_v2_msg_cont1(deps: (u8, u8)) -> (U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, SpecMessageIdsCombinator)))) {
    let (len, incompat_flags) = deps;
    (U8, (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, spec_message_ids()))))
}

impl View for MavlinkV2MsgCont1 {
    type V = spec_fn((u8, u8)) -> (U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, SpecMessageIdsCombinator))));

    open spec fn view(&self) -> Self::V {
        |deps: (u8, u8)| {
            spec_mavlink_v2_msg_cont1(deps)
        }
    }
}

pub open spec fn spec_mavlink_v2_msg_cont0(deps: ((u8, u8), (u8, (u8, (u8, (u8, u24)))))) -> (SpecMavlinkV2MsgPayloadCombinator, (U16Le, SpecMavlinkV2MsgSignatureCombinator)) {
    let ((len, incompat_flags), (_, (_, (_, (_, msgid))))) = deps;
    (spec_mavlink_v2_msg_payload(msgid, len), (U16Le, spec_mavlink_v2_msg_signature(incompat_flags)))
}

impl View for MavlinkV2MsgCont0 {
    type V = spec_fn(((u8, u8), (u8, (u8, (u8, (u8, u24)))))) -> (SpecMavlinkV2MsgPayloadCombinator, (U16Le, SpecMavlinkV2MsgSignatureCombinator));

    open spec fn view(&self) -> Self::V {
        |deps: ((u8, u8), (u8, (u8, (u8, (u8, u24)))))| {
            spec_mavlink_v2_msg_cont0(deps)
        }
    }
}

                
pub fn mavlink_v2_msg<'a>() -> (o: MavlinkV2MsgCombinator)
    ensures o@ == spec_mavlink_v2_msg(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkV2MsgCombinator(
    Mapped {
        inner: Pair::new(Pair::new(Pair::new(U8, MavlinkV2MsgCont2), MavlinkV2MsgCont1), MavlinkV2MsgCont0),
        mapper: MavlinkV2MsgMapper,
    });
    assert({
        &&& combinator@ == spec_mavlink_v2_msg()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_v2_msg<'a>(input: &'a [u8]) -> (res: PResult<<MavlinkV2MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_v2_msg().spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_v2_msg().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_v2_msg().spec_parse(input@) is None,
        spec_mavlink_v2_msg().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_v2_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_v2_msg<'a>(v: <MavlinkV2MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_v2_msg().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_v2_msg().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_v2_msg().spec_serialize(v@))
        },
{
    let combinator = mavlink_v2_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mavlink_v2_msg_len<'a>(v: <MavlinkV2MsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mavlink_v2_msg().wf(v@),
        spec_mavlink_v2_msg().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_v2_msg().spec_serialize(v@).len(),
{
    let combinator = mavlink_v2_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct MavlinkV2MsgCont2;
type MavlinkV2MsgCont2Type<'a, 'b> = &'b u8;
type MavlinkV2MsgCont2SType<'a, 'x> = &'x u8;
type MavlinkV2MsgCont2Input<'a, 'b, 'x> = POrSType<MavlinkV2MsgCont2Type<'a, 'b>, MavlinkV2MsgCont2SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MavlinkV2MsgCont2Input<'a, 'b, 'x>> for MavlinkV2MsgCont2 {
    type Output = IncompatFlagsCombinator;

    open spec fn requires(&self, deps: MavlinkV2MsgCont2Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MavlinkV2MsgCont2Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_mavlink_v2_msg_cont2(deps@)
    }

    fn apply(&self, deps: MavlinkV2MsgCont2Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = *deps;
                incompat_flags()
            }
            POrSType::S(deps) => {
                let len = deps;
                let len = *len;
                incompat_flags()
            }
        }
    }
}
pub struct MavlinkV2MsgCont1;
type MavlinkV2MsgCont1Type<'a, 'b> = &'b (u8, u8);
type MavlinkV2MsgCont1SType<'a, 'x> = (&'x u8, &'x u8);
type MavlinkV2MsgCont1Input<'a, 'b, 'x> = POrSType<MavlinkV2MsgCont1Type<'a, 'b>, MavlinkV2MsgCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MavlinkV2MsgCont1Input<'a, 'b, 'x>> for MavlinkV2MsgCont1 {
    type Output = (U8, (U8, (Refined<U8, Predicate3768926651291043512>, (Refined<U8, Predicate3768926651291043512>, MessageIdsCombinator))));

    open spec fn requires(&self, deps: MavlinkV2MsgCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MavlinkV2MsgCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_mavlink_v2_msg_cont1(deps@)
    }

    fn apply(&self, deps: MavlinkV2MsgCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (len, incompat_flags) = *deps;
                (U8, (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, message_ids()))))
            }
            POrSType::S(deps) => {
                let (len, incompat_flags) = deps;
                let (len, incompat_flags) = (*len, *incompat_flags);
                (U8, (U8, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, (Refined { inner: U8, predicate: Predicate3768926651291043512 }, message_ids()))))
            }
        }
    }
}
pub struct MavlinkV2MsgCont0;
type MavlinkV2MsgCont0Type<'a, 'b> = &'b ((u8, u8), (u8, (u8, (u8, (u8, u24)))));
type MavlinkV2MsgCont0SType<'a, 'x> = ((&'x u8, &'x u8), (&'x u8, (&'x u8, (&'x u8, (&'x u8, &'x u24)))));
type MavlinkV2MsgCont0Input<'a, 'b, 'x> = POrSType<MavlinkV2MsgCont0Type<'a, 'b>, MavlinkV2MsgCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MavlinkV2MsgCont0Input<'a, 'b, 'x>> for MavlinkV2MsgCont0 {
    type Output = (MavlinkV2MsgPayloadCombinator, (U16Le, MavlinkV2MsgSignatureCombinator));

    open spec fn requires(&self, deps: MavlinkV2MsgCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MavlinkV2MsgCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_mavlink_v2_msg_cont0(deps@)
    }

    fn apply(&self, deps: MavlinkV2MsgCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((len, incompat_flags), (_, (_, (_, (_, msgid))))) = *deps;
                (mavlink_v2_msg_payload(msgid, len), (U16Le, mavlink_v2_msg_signature(incompat_flags)))
            }
            POrSType::S(deps) => {
                let ((len, incompat_flags), (_, (_, (_, (_, msgid))))) = deps;
                let ((len, incompat_flags), msgid) = ((*len, *incompat_flags), *msgid);
                (mavlink_v2_msg_payload(msgid, len), (U16Le, mavlink_v2_msg_signature(incompat_flags)))
            }
        }
    }
}
                

pub enum SpecMavlinkMsgMsg {
    MavLink1(SpecMavlinkV1Msg),
    MavLink2(SpecMavlinkV2Msg),
}

pub type SpecMavlinkMsgMsgInner = Either<SpecMavlinkV1Msg, SpecMavlinkV2Msg>;

impl SpecFrom<SpecMavlinkMsgMsg> for SpecMavlinkMsgMsgInner {
    open spec fn spec_from(m: SpecMavlinkMsgMsg) -> SpecMavlinkMsgMsgInner {
        match m {
            SpecMavlinkMsgMsg::MavLink1(m) => Either::Left(m),
            SpecMavlinkMsgMsg::MavLink2(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecMavlinkMsgMsgInner> for SpecMavlinkMsgMsg {
    open spec fn spec_from(m: SpecMavlinkMsgMsgInner) -> SpecMavlinkMsgMsg {
        match m {
            Either::Left(m) => SpecMavlinkMsgMsg::MavLink1(m),
            Either::Right(m) => SpecMavlinkMsgMsg::MavLink2(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MavlinkMsgMsg<'a> {
    MavLink1(MavlinkV1Msg<'a>),
    MavLink2(MavlinkV2Msg<'a>),
}

pub type MavlinkMsgMsgInner<'a> = Either<MavlinkV1Msg<'a>, MavlinkV2Msg<'a>>;

pub type MavlinkMsgMsgInnerRef<'a> = Either<&'a MavlinkV1Msg<'a>, &'a MavlinkV2Msg<'a>>;


impl<'a> View for MavlinkMsgMsg<'a> {
    type V = SpecMavlinkMsgMsg;
    open spec fn view(&self) -> Self::V {
        match self {
            MavlinkMsgMsg::MavLink1(m) => SpecMavlinkMsgMsg::MavLink1(m@),
            MavlinkMsgMsg::MavLink2(m) => SpecMavlinkMsgMsg::MavLink2(m@),
        }
    }
}


impl<'a> From<&'a MavlinkMsgMsg<'a>> for MavlinkMsgMsgInnerRef<'a> {
    fn ex_from(m: &'a MavlinkMsgMsg<'a>) -> MavlinkMsgMsgInnerRef<'a> {
        match m {
            MavlinkMsgMsg::MavLink1(m) => Either::Left(m),
            MavlinkMsgMsg::MavLink2(m) => Either::Right(m),
        }
    }

}

impl<'a> From<MavlinkMsgMsgInner<'a>> for MavlinkMsgMsg<'a> {
    fn ex_from(m: MavlinkMsgMsgInner<'a>) -> MavlinkMsgMsg<'a> {
        match m {
            Either::Left(m) => MavlinkMsgMsg::MavLink1(m),
            Either::Right(m) => MavlinkMsgMsg::MavLink2(m),
        }
    }
    
}


pub struct MavlinkMsgMsgMapper;
impl View for MavlinkMsgMsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkMsgMsgMapper {
    type Src = SpecMavlinkMsgMsgInner;
    type Dst = SpecMavlinkMsgMsg;
}
impl SpecIsoProof for MavlinkMsgMsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkMsgMsgMapper {
    type Src = MavlinkMsgMsgInner<'a>;
    type Dst = MavlinkMsgMsg<'a>;
    type RefSrc = MavlinkMsgMsgInnerRef<'a>;
}

type SpecMavlinkMsgMsgCombinatorAlias1 = Choice<Cond<SpecMavlinkV1MsgCombinator>, Cond<SpecMavlinkV2MsgCombinator>>;
pub struct SpecMavlinkMsgMsgCombinator(pub SpecMavlinkMsgMsgCombinatorAlias);

impl SpecCombinator for SpecMavlinkMsgMsgCombinator {
    type Type = SpecMavlinkMsgMsg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkMsgMsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkMsgMsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkMsgMsgCombinatorAlias = Mapped<SpecMavlinkMsgMsgCombinatorAlias1, MavlinkMsgMsgMapper>;
type MavlinkMsgMsgCombinatorAlias1 = Choice<Cond<MavlinkV1MsgCombinator>, Cond<MavlinkV2MsgCombinator>>;
pub struct MavlinkMsgMsgCombinator1(pub MavlinkMsgMsgCombinatorAlias1);
impl View for MavlinkMsgMsgCombinator1 {
    type V = SpecMavlinkMsgMsgCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MavlinkMsgMsgCombinator1, MavlinkMsgMsgCombinatorAlias1);

pub struct MavlinkMsgMsgCombinator(pub MavlinkMsgMsgCombinatorAlias);

impl View for MavlinkMsgMsgCombinator {
    type V = SpecMavlinkMsgMsgCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkMsgMsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkMsgMsgCombinator {
    type Type = MavlinkMsgMsg<'a>;
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
pub type MavlinkMsgMsgCombinatorAlias = Mapped<MavlinkMsgMsgCombinator1, MavlinkMsgMsgMapper>;


pub open spec fn spec_mavlink_msg_msg(magic: SpecProtocolMagic) -> SpecMavlinkMsgMsgCombinator {
    SpecMavlinkMsgMsgCombinator(Mapped { inner: Choice(Cond { cond: magic == ProtocolMagic::MavLink1, inner: spec_mavlink_v1_msg() }, Cond { cond: magic == ProtocolMagic::MavLink2, inner: spec_mavlink_v2_msg() }), mapper: MavlinkMsgMsgMapper })
}

pub fn mavlink_msg_msg<'a>(magic: ProtocolMagic) -> (o: MavlinkMsgMsgCombinator)
    ensures o@ == spec_mavlink_msg_msg(magic@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkMsgMsgCombinator(Mapped { inner: MavlinkMsgMsgCombinator1(Choice::new(Cond { cond: magic == ProtocolMagic::MavLink1, inner: mavlink_v1_msg() }, Cond { cond: magic == ProtocolMagic::MavLink2, inner: mavlink_v2_msg() })), mapper: MavlinkMsgMsgMapper });
    assert({
        &&& combinator@ == spec_mavlink_msg_msg(magic@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_msg_msg<'a>(input: &'a [u8], magic: ProtocolMagic) -> (res: PResult<<MavlinkMsgMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_msg_msg(magic@).spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_msg_msg(magic@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_msg_msg(magic@).spec_parse(input@) is None,
        spec_mavlink_msg_msg(magic@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_msg_msg( magic );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_msg_msg<'a>(v: <MavlinkMsgMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, magic: ProtocolMagic) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_msg_msg(magic@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_msg_msg(magic@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_msg_msg(magic@).spec_serialize(v@))
        },
{
    let combinator = mavlink_msg_msg( magic );
    combinator.serialize(v, data, pos)
}

pub fn mavlink_msg_msg_len<'a>(v: <MavlinkMsgMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, magic: ProtocolMagic) -> (serialize_len: usize)
    requires
        spec_mavlink_msg_msg(magic@).wf(v@),
        spec_mavlink_msg_msg(magic@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_msg_msg(magic@).spec_serialize(v@).len(),
{
    let combinator = mavlink_msg_msg( magic );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecMavlinkMsg {
    pub magic: SpecProtocolMagic,
    pub msg: SpecMavlinkMsgMsg,
}

pub type SpecMavlinkMsgInner = (SpecProtocolMagic, SpecMavlinkMsgMsg);


impl SpecFrom<SpecMavlinkMsg> for SpecMavlinkMsgInner {
    open spec fn spec_from(m: SpecMavlinkMsg) -> SpecMavlinkMsgInner {
        (m.magic, m.msg)
    }
}

impl SpecFrom<SpecMavlinkMsgInner> for SpecMavlinkMsg {
    open spec fn spec_from(m: SpecMavlinkMsgInner) -> SpecMavlinkMsg {
        let (magic, msg) = m;
        SpecMavlinkMsg { magic, msg }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MavlinkMsg<'a> {
    pub magic: ProtocolMagic,
    pub msg: MavlinkMsgMsg<'a>,
}

impl View for MavlinkMsg<'_> {
    type V = SpecMavlinkMsg;

    open spec fn view(&self) -> Self::V {
        SpecMavlinkMsg {
            magic: self.magic@,
            msg: self.msg@,
        }
    }
}
pub type MavlinkMsgInner<'a> = (ProtocolMagic, MavlinkMsgMsg<'a>);

pub type MavlinkMsgInnerRef<'a> = (&'a ProtocolMagic, &'a MavlinkMsgMsg<'a>);
impl<'a> From<&'a MavlinkMsg<'a>> for MavlinkMsgInnerRef<'a> {
    fn ex_from(m: &'a MavlinkMsg) -> MavlinkMsgInnerRef<'a> {
        (&m.magic, &m.msg)
    }
}

impl<'a> From<MavlinkMsgInner<'a>> for MavlinkMsg<'a> {
    fn ex_from(m: MavlinkMsgInner) -> MavlinkMsg {
        let (magic, msg) = m;
        MavlinkMsg { magic, msg }
    }
}

pub struct MavlinkMsgMapper;
impl View for MavlinkMsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MavlinkMsgMapper {
    type Src = SpecMavlinkMsgInner;
    type Dst = SpecMavlinkMsg;
}
impl SpecIsoProof for MavlinkMsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MavlinkMsgMapper {
    type Src = MavlinkMsgInner<'a>;
    type Dst = MavlinkMsg<'a>;
    type RefSrc = MavlinkMsgInnerRef<'a>;
}

pub struct SpecMavlinkMsgCombinator(pub SpecMavlinkMsgCombinatorAlias);

impl SpecCombinator for SpecMavlinkMsgCombinator {
    type Type = SpecMavlinkMsg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMavlinkMsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMavlinkMsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecMavlinkMsgCombinatorAlias = Mapped<SpecPair<SpecProtocolMagicCombinator, SpecMavlinkMsgMsgCombinator>, MavlinkMsgMapper>;

pub struct MavlinkMsgCombinator(pub MavlinkMsgCombinatorAlias);

impl View for MavlinkMsgCombinator {
    type V = SpecMavlinkMsgCombinator;
    open spec fn view(&self) -> Self::V { SpecMavlinkMsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MavlinkMsgCombinator {
    type Type = MavlinkMsg<'a>;
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
pub type MavlinkMsgCombinatorAlias = Mapped<Pair<ProtocolMagicCombinator, MavlinkMsgMsgCombinator, MavlinkMsgCont0>, MavlinkMsgMapper>;


pub open spec fn spec_mavlink_msg() -> SpecMavlinkMsgCombinator {
    SpecMavlinkMsgCombinator(
    Mapped {
        inner: Pair::spec_new(spec_protocol_magic(), |deps| spec_mavlink_msg_cont0(deps)),
        mapper: MavlinkMsgMapper,
    })
}

pub open spec fn spec_mavlink_msg_cont0(deps: SpecProtocolMagic) -> SpecMavlinkMsgMsgCombinator {
    let magic = deps;
    spec_mavlink_msg_msg(magic)
}

impl View for MavlinkMsgCont0 {
    type V = spec_fn(SpecProtocolMagic) -> SpecMavlinkMsgMsgCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecProtocolMagic| {
            spec_mavlink_msg_cont0(deps)
        }
    }
}

                
pub fn mavlink_msg<'a>() -> (o: MavlinkMsgCombinator)
    ensures o@ == spec_mavlink_msg(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = MavlinkMsgCombinator(
    Mapped {
        inner: Pair::new(protocol_magic(), MavlinkMsgCont0),
        mapper: MavlinkMsgMapper,
    });
    assert({
        &&& combinator@ == spec_mavlink_msg()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_mavlink_msg<'a>(input: &'a [u8]) -> (res: PResult<<MavlinkMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_mavlink_msg().spec_parse(input@) == Some((n as int, v@)),
        spec_mavlink_msg().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_mavlink_msg().spec_parse(input@) is None,
        spec_mavlink_msg().spec_parse(input@) is None ==> res is Err,
{
    let combinator = mavlink_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_mavlink_msg<'a>(v: <MavlinkMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_mavlink_msg().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_mavlink_msg().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_mavlink_msg().spec_serialize(v@))
        },
{
    let combinator = mavlink_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn mavlink_msg_len<'a>(v: <MavlinkMsgCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_mavlink_msg().wf(v@),
        spec_mavlink_msg().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_mavlink_msg().spec_serialize(v@).len(),
{
    let combinator = mavlink_msg();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct MavlinkMsgCont0;
type MavlinkMsgCont0Type<'a, 'b> = &'b ProtocolMagic;
type MavlinkMsgCont0SType<'a, 'x> = &'x ProtocolMagic;
type MavlinkMsgCont0Input<'a, 'b, 'x> = POrSType<MavlinkMsgCont0Type<'a, 'b>, MavlinkMsgCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MavlinkMsgCont0Input<'a, 'b, 'x>> for MavlinkMsgCont0 {
    type Output = MavlinkMsgMsgCombinator;

    open spec fn requires(&self, deps: MavlinkMsgCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MavlinkMsgCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_mavlink_msg_cont0(deps@)
    }

    fn apply(&self, deps: MavlinkMsgCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let magic = *deps;
                mavlink_msg_msg(magic)
            }
            POrSType::S(deps) => {
                let magic = deps;
                let magic = *magic;
                mavlink_msg_msg(magic)
            }
        }
    }
}
                

}
