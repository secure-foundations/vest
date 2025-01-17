#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vstd::prelude::*;
use vest::properties::*;
use vest::utils::*;
use vest::regular::map::*;
use vest::regular::tag::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::uints::*;
use vest::regular::tail::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::depend::*;
use vest::regular::and_then::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::repeat_n::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::preceded::*;
use vest::regular::terminated::*;
use vest::regular::disjoint::DisjointFrom;
verus!{

pub struct SpecScript {
    pub l: VarInt,
    pub data: Seq<u8>,
}

pub type SpecScriptInner = (VarInt, Seq<u8>);
impl SpecFrom<SpecScript> for SpecScriptInner {
    open spec fn spec_from(m: SpecScript) -> SpecScriptInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecScriptInner> for SpecScript {
    open spec fn spec_from(m: SpecScriptInner) -> SpecScript {
        let (l, data) = m;
        SpecScript { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Script<'a> {
    pub l: VarInt,
    pub data: &'a [u8],
}

impl View for Script<'_> {
    type V = SpecScript;

    open spec fn view(&self) -> Self::V {
        SpecScript {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type ScriptInner<'a> = (VarInt, &'a [u8]);
impl<'a> From<Script<'a>> for ScriptInner<'a> {
    fn ex_from(m: Script) -> ScriptInner {
        (m.l, m.data)
    }
}
impl<'a> From<ScriptInner<'a>> for Script<'a> {
    fn ex_from(m: ScriptInner) -> Script {
        let (l, data) = m;
        Script { l, data }
    }
}

pub struct ScriptMapper<'a>(PhantomData<&'a ()>);
impl<'a> ScriptMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ScriptMapper(PhantomData)
    }
    pub fn new() -> Self {
        ScriptMapper(PhantomData)
    }
}
impl View for ScriptMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ScriptMapper<'_> {
    type Src = SpecScriptInner;
    type Dst = SpecScript;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ScriptMapper<'a> {
    type Src = ScriptInner<'a>;
    type Dst = Script<'a>;
}

pub struct SpecScriptCombinator(SpecScriptCombinatorAlias);

impl SpecCombinator for SpecScriptCombinator {
    type Type = SpecScript;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecScriptCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecScriptCombinatorAlias::is_prefix_secure() }
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
pub type SpecScriptCombinatorAlias = Mapped<SpecDepend<BtcVarint, Bytes>, ScriptMapper<'static>>;

pub struct ScriptCombinator<'a>(ScriptCombinatorAlias<'a>);

impl<'a> View for ScriptCombinator<'a> {
    type V = SpecScriptCombinator;
    closed spec fn view(&self) -> Self::V { SpecScriptCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ScriptCombinator<'a> {
    type Type = Script<'a>;
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
pub type ScriptCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BtcVarint, Bytes, ScriptCont0<'a>>, ScriptMapper<'a>>;


pub closed spec fn spec_script() -> SpecScriptCombinator {
    SpecScriptCombinator(
    Mapped {
        inner: SpecDepend { fst: BtcVarint, snd: |deps| spec_script_cont0(deps) },
        mapper: ScriptMapper::spec_new(),
    })
}

pub open spec fn spec_script_cont0(deps: VarInt) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn script<'a>() -> (o: ScriptCombinator<'a>)
    ensures o@ == spec_script(),
{
    ScriptCombinator(
    Mapped {
        inner: Depend { fst: BtcVarint, snd: ScriptCont0::new(), spec_snd: Ghost(|deps| spec_script_cont0(deps)) },
        mapper: ScriptMapper::new(),
    })
}

pub struct ScriptCont0<'a>(PhantomData<&'a ()>);
impl<'a> ScriptCont0<'a> {
    pub fn new() -> Self {
        ScriptCont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for ScriptCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_script_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecOutpoint {
    pub hash: Seq<u8>,
    pub index: u32,
}

pub type SpecOutpointInner = (Seq<u8>, u32);
impl SpecFrom<SpecOutpoint> for SpecOutpointInner {
    open spec fn spec_from(m: SpecOutpoint) -> SpecOutpointInner {
        (m.hash, m.index)
    }
}
impl SpecFrom<SpecOutpointInner> for SpecOutpoint {
    open spec fn spec_from(m: SpecOutpointInner) -> SpecOutpoint {
        let (hash, index) = m;
        SpecOutpoint { hash, index }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Outpoint<'a> {
    pub hash: &'a [u8],
    pub index: u32,
}

impl View for Outpoint<'_> {
    type V = SpecOutpoint;

    open spec fn view(&self) -> Self::V {
        SpecOutpoint {
            hash: self.hash@,
            index: self.index@,
        }
    }
}
pub type OutpointInner<'a> = (&'a [u8], u32);
impl<'a> From<Outpoint<'a>> for OutpointInner<'a> {
    fn ex_from(m: Outpoint) -> OutpointInner {
        (m.hash, m.index)
    }
}
impl<'a> From<OutpointInner<'a>> for Outpoint<'a> {
    fn ex_from(m: OutpointInner) -> Outpoint {
        let (hash, index) = m;
        Outpoint { hash, index }
    }
}

pub struct OutpointMapper<'a>(PhantomData<&'a ()>);
impl<'a> OutpointMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OutpointMapper(PhantomData)
    }
    pub fn new() -> Self {
        OutpointMapper(PhantomData)
    }
}
impl View for OutpointMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OutpointMapper<'_> {
    type Src = SpecOutpointInner;
    type Dst = SpecOutpoint;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OutpointMapper<'a> {
    type Src = OutpointInner<'a>;
    type Dst = Outpoint<'a>;
}

pub struct SpecOutpointCombinator(SpecOutpointCombinatorAlias);

impl SpecCombinator for SpecOutpointCombinator {
    type Type = SpecOutpoint;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOutpointCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOutpointCombinatorAlias::is_prefix_secure() }
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
pub type SpecOutpointCombinatorAlias = Mapped<(BytesN<32>, U32Le), OutpointMapper<'static>>;

pub struct OutpointCombinator<'a>(OutpointCombinatorAlias<'a>);

impl<'a> View for OutpointCombinator<'a> {
    type V = SpecOutpointCombinator;
    closed spec fn view(&self) -> Self::V { SpecOutpointCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OutpointCombinator<'a> {
    type Type = Outpoint<'a>;
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
pub type OutpointCombinatorAlias<'a> = Mapped<(BytesN<32>, U32Le), OutpointMapper<'a>>;


pub closed spec fn spec_outpoint() -> SpecOutpointCombinator {
    SpecOutpointCombinator(
    Mapped {
        inner: (BytesN::<32>, U32Le),
        mapper: OutpointMapper::spec_new(),
    })
}

                
pub fn outpoint<'a>() -> (o: OutpointCombinator<'a>)
    ensures o@ == spec_outpoint(),
{
    OutpointCombinator(
    Mapped {
        inner: (BytesN::<32>, U32Le),
        mapper: OutpointMapper::new(),
    })
}

                

pub struct SpecScriptSig {
    pub l: VarInt,
    pub data: Seq<u8>,
}

pub type SpecScriptSigInner = (VarInt, Seq<u8>);
impl SpecFrom<SpecScriptSig> for SpecScriptSigInner {
    open spec fn spec_from(m: SpecScriptSig) -> SpecScriptSigInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecScriptSigInner> for SpecScriptSig {
    open spec fn spec_from(m: SpecScriptSigInner) -> SpecScriptSig {
        let (l, data) = m;
        SpecScriptSig { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ScriptSig<'a> {
    pub l: VarInt,
    pub data: &'a [u8],
}

impl View for ScriptSig<'_> {
    type V = SpecScriptSig;

    open spec fn view(&self) -> Self::V {
        SpecScriptSig {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type ScriptSigInner<'a> = (VarInt, &'a [u8]);
impl<'a> From<ScriptSig<'a>> for ScriptSigInner<'a> {
    fn ex_from(m: ScriptSig) -> ScriptSigInner {
        (m.l, m.data)
    }
}
impl<'a> From<ScriptSigInner<'a>> for ScriptSig<'a> {
    fn ex_from(m: ScriptSigInner) -> ScriptSig {
        let (l, data) = m;
        ScriptSig { l, data }
    }
}

pub struct ScriptSigMapper<'a>(PhantomData<&'a ()>);
impl<'a> ScriptSigMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ScriptSigMapper(PhantomData)
    }
    pub fn new() -> Self {
        ScriptSigMapper(PhantomData)
    }
}
impl View for ScriptSigMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ScriptSigMapper<'_> {
    type Src = SpecScriptSigInner;
    type Dst = SpecScriptSig;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ScriptSigMapper<'a> {
    type Src = ScriptSigInner<'a>;
    type Dst = ScriptSig<'a>;
}

pub struct SpecScriptSigCombinator(SpecScriptSigCombinatorAlias);

impl SpecCombinator for SpecScriptSigCombinator {
    type Type = SpecScriptSig;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecScriptSigCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecScriptSigCombinatorAlias::is_prefix_secure() }
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
pub type SpecScriptSigCombinatorAlias = Mapped<SpecDepend<BtcVarint, Bytes>, ScriptSigMapper<'static>>;

pub struct ScriptSigCombinator<'a>(ScriptSigCombinatorAlias<'a>);

impl<'a> View for ScriptSigCombinator<'a> {
    type V = SpecScriptSigCombinator;
    closed spec fn view(&self) -> Self::V { SpecScriptSigCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ScriptSigCombinator<'a> {
    type Type = ScriptSig<'a>;
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
pub type ScriptSigCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BtcVarint, Bytes, ScriptSigCont0<'a>>, ScriptSigMapper<'a>>;


pub closed spec fn spec_script_sig() -> SpecScriptSigCombinator {
    SpecScriptSigCombinator(
    Mapped {
        inner: SpecDepend { fst: BtcVarint, snd: |deps| spec_script_sig_cont0(deps) },
        mapper: ScriptSigMapper::spec_new(),
    })
}

pub open spec fn spec_script_sig_cont0(deps: VarInt) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn script_sig<'a>() -> (o: ScriptSigCombinator<'a>)
    ensures o@ == spec_script_sig(),
{
    ScriptSigCombinator(
    Mapped {
        inner: Depend { fst: BtcVarint, snd: ScriptSigCont0::new(), spec_snd: Ghost(|deps| spec_script_sig_cont0(deps)) },
        mapper: ScriptSigMapper::new(),
    })
}

pub struct ScriptSigCont0<'a>(PhantomData<&'a ()>);
impl<'a> ScriptSigCont0<'a> {
    pub fn new() -> Self {
        ScriptSigCont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for ScriptSigCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_script_sig_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecTxin {
    pub previous_output: SpecOutpoint,
    pub script_sig: SpecScriptSig,
    pub sequence: u32,
}

pub type SpecTxinInner = (SpecOutpoint, (SpecScriptSig, u32));
impl SpecFrom<SpecTxin> for SpecTxinInner {
    open spec fn spec_from(m: SpecTxin) -> SpecTxinInner {
        (m.previous_output, (m.script_sig, m.sequence))
    }
}
impl SpecFrom<SpecTxinInner> for SpecTxin {
    open spec fn spec_from(m: SpecTxinInner) -> SpecTxin {
        let (previous_output, (script_sig, sequence)) = m;
        SpecTxin { previous_output, script_sig, sequence }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Txin<'a> {
    pub previous_output: Outpoint<'a>,
    pub script_sig: ScriptSig<'a>,
    pub sequence: u32,
}

impl View for Txin<'_> {
    type V = SpecTxin;

    open spec fn view(&self) -> Self::V {
        SpecTxin {
            previous_output: self.previous_output@,
            script_sig: self.script_sig@,
            sequence: self.sequence@,
        }
    }
}
pub type TxinInner<'a> = (Outpoint<'a>, (ScriptSig<'a>, u32));
impl<'a> From<Txin<'a>> for TxinInner<'a> {
    fn ex_from(m: Txin) -> TxinInner {
        (m.previous_output, (m.script_sig, m.sequence))
    }
}
impl<'a> From<TxinInner<'a>> for Txin<'a> {
    fn ex_from(m: TxinInner) -> Txin {
        let (previous_output, (script_sig, sequence)) = m;
        Txin { previous_output, script_sig, sequence }
    }
}

pub struct TxinMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxinMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxinMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxinMapper(PhantomData)
    }
}
impl View for TxinMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxinMapper<'_> {
    type Src = SpecTxinInner;
    type Dst = SpecTxin;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxinMapper<'a> {
    type Src = TxinInner<'a>;
    type Dst = Txin<'a>;
}

pub struct SpecTxinCombinator(SpecTxinCombinatorAlias);

impl SpecCombinator for SpecTxinCombinator {
    type Type = SpecTxin;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxinCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxinCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxinCombinatorAlias = Mapped<(SpecOutpointCombinator, (SpecScriptSigCombinator, U32Le)), TxinMapper<'static>>;

pub struct TxinCombinator<'a>(TxinCombinatorAlias<'a>);

impl<'a> View for TxinCombinator<'a> {
    type V = SpecTxinCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxinCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxinCombinator<'a> {
    type Type = Txin<'a>;
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
pub type TxinCombinatorAlias<'a> = Mapped<(OutpointCombinator<'a>, (ScriptSigCombinator<'a>, U32Le)), TxinMapper<'a>>;


pub closed spec fn spec_txin() -> SpecTxinCombinator {
    SpecTxinCombinator(
    Mapped {
        inner: (spec_outpoint(), (spec_script_sig(), U32Le)),
        mapper: TxinMapper::spec_new(),
    })
}

                
pub fn txin<'a>() -> (o: TxinCombinator<'a>)
    ensures o@ == spec_txin(),
{
    TxinCombinator(
    Mapped {
        inner: (outpoint(), (script_sig(), U32Le)),
        mapper: TxinMapper::new(),
    })
}

                

pub struct SpecTxout {
    pub value: u64,
    pub script_pubkey: SpecScript,
}

pub type SpecTxoutInner = (u64, SpecScript);
impl SpecFrom<SpecTxout> for SpecTxoutInner {
    open spec fn spec_from(m: SpecTxout) -> SpecTxoutInner {
        (m.value, m.script_pubkey)
    }
}
impl SpecFrom<SpecTxoutInner> for SpecTxout {
    open spec fn spec_from(m: SpecTxoutInner) -> SpecTxout {
        let (value, script_pubkey) = m;
        SpecTxout { value, script_pubkey }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Txout<'a> {
    pub value: u64,
    pub script_pubkey: Script<'a>,
}

impl View for Txout<'_> {
    type V = SpecTxout;

    open spec fn view(&self) -> Self::V {
        SpecTxout {
            value: self.value@,
            script_pubkey: self.script_pubkey@,
        }
    }
}
pub type TxoutInner<'a> = (u64, Script<'a>);
impl<'a> From<Txout<'a>> for TxoutInner<'a> {
    fn ex_from(m: Txout) -> TxoutInner {
        (m.value, m.script_pubkey)
    }
}
impl<'a> From<TxoutInner<'a>> for Txout<'a> {
    fn ex_from(m: TxoutInner) -> Txout {
        let (value, script_pubkey) = m;
        Txout { value, script_pubkey }
    }
}

pub struct TxoutMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxoutMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxoutMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxoutMapper(PhantomData)
    }
}
impl View for TxoutMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxoutMapper<'_> {
    type Src = SpecTxoutInner;
    type Dst = SpecTxout;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxoutMapper<'a> {
    type Src = TxoutInner<'a>;
    type Dst = Txout<'a>;
}

pub struct SpecTxoutCombinator(SpecTxoutCombinatorAlias);

impl SpecCombinator for SpecTxoutCombinator {
    type Type = SpecTxout;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxoutCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxoutCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxoutCombinatorAlias = Mapped<(U64Le, SpecScriptCombinator), TxoutMapper<'static>>;

pub struct TxoutCombinator<'a>(TxoutCombinatorAlias<'a>);

impl<'a> View for TxoutCombinator<'a> {
    type V = SpecTxoutCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxoutCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxoutCombinator<'a> {
    type Type = Txout<'a>;
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
pub type TxoutCombinatorAlias<'a> = Mapped<(U64Le, ScriptCombinator<'a>), TxoutMapper<'a>>;


pub closed spec fn spec_txout() -> SpecTxoutCombinator {
    SpecTxoutCombinator(
    Mapped {
        inner: (U64Le, spec_script()),
        mapper: TxoutMapper::spec_new(),
    })
}

                
pub fn txout<'a>() -> (o: TxoutCombinator<'a>)
    ensures o@ == spec_txout(),
{
    TxoutCombinator(
    Mapped {
        inner: (U64Le, script()),
        mapper: TxoutMapper::new(),
    })
}

                

pub enum SpecLockTime {
    BlockNo(u32),
    Timestamp(u32),
}

pub type SpecLockTimeInner = Either<u32, u32>;



impl SpecFrom<SpecLockTime> for SpecLockTimeInner {
    open spec fn spec_from(m: SpecLockTime) -> SpecLockTimeInner {
        match m {
            SpecLockTime::BlockNo(m) => Either::Left(m),
            SpecLockTime::Timestamp(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecLockTimeInner> for SpecLockTime {
    open spec fn spec_from(m: SpecLockTimeInner) -> SpecLockTime {
        match m {
            Either::Left(m) => SpecLockTime::BlockNo(m),
            Either::Right(m) => SpecLockTime::Timestamp(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LockTime {
    BlockNo(u32),
    Timestamp(u32),
}

pub type LockTimeInner = Either<u32, u32>;


impl View for LockTime {
    type V = SpecLockTime;
    open spec fn view(&self) -> Self::V {
        match self {
            LockTime::BlockNo(m) => SpecLockTime::BlockNo(m@),
            LockTime::Timestamp(m) => SpecLockTime::Timestamp(m@),
        }
    }
}


impl From<LockTime> for LockTimeInner {
    fn ex_from(m: LockTime) -> LockTimeInner {
        match m {
            LockTime::BlockNo(m) => Either::Left(m),
            LockTime::Timestamp(m) => Either::Right(m),
        }
    }

}

impl From<LockTimeInner> for LockTime {
    fn ex_from(m: LockTimeInner) -> LockTime {
        match m {
            Either::Left(m) => LockTime::BlockNo(m),
            Either::Right(m) => LockTime::Timestamp(m),
        }
    }
    
}


pub struct LockTimeMapper;
impl LockTimeMapper {
    pub closed spec fn spec_new() -> Self {
        LockTimeMapper
    }
    pub fn new() -> Self {
        LockTimeMapper
    }
}
impl View for LockTimeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LockTimeMapper {
    type Src = SpecLockTimeInner;
    type Dst = SpecLockTime;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for LockTimeMapper {
    type Src = LockTimeInner;
    type Dst = LockTime;
}


pub struct SpecLockTimeCombinator(SpecLockTimeCombinatorAlias);

impl SpecCombinator for SpecLockTimeCombinator {
    type Type = SpecLockTime;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLockTimeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLockTimeCombinatorAlias::is_prefix_secure() }
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
pub type SpecLockTimeCombinatorAlias = Mapped<OrdChoice<Refined<U32Le, Predicate675963002568997194>, Refined<U32Le, Predicate3133141078119142300>>, LockTimeMapper>;
pub struct Predicate675963002568997194;
impl View for Predicate675963002568997194 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate675963002568997194 {
    type Input = u32;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 499999999)
    }
}
impl SpecPred for Predicate675963002568997194 {
    type Input = u32;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 499999999)
    }
}
pub struct Predicate3133141078119142300;
impl View for Predicate3133141078119142300 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate3133141078119142300 {
    type Input = u32;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 500000000)
    }
}
impl SpecPred for Predicate3133141078119142300 {
    type Input = u32;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 500000000)
    }
}

pub struct LockTimeCombinator(LockTimeCombinatorAlias);

impl View for LockTimeCombinator {
    type V = SpecLockTimeCombinator;
    closed spec fn view(&self) -> Self::V { SpecLockTimeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for LockTimeCombinator {
    type Type = LockTime;
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
pub type LockTimeCombinatorAlias = Mapped<OrdChoice<Refined<U32Le, Predicate675963002568997194>, Refined<U32Le, Predicate3133141078119142300>>, LockTimeMapper>;


pub closed spec fn spec_lock_time() -> SpecLockTimeCombinator {
    SpecLockTimeCombinator(Mapped { inner: OrdChoice(Refined { inner: U32Le, predicate: Predicate675963002568997194 }, Refined { inner: U32Le, predicate: Predicate3133141078119142300 }), mapper: LockTimeMapper::spec_new() })
}

                
pub fn lock_time() -> (o: LockTimeCombinator)
    ensures o@ == spec_lock_time(),
{
    LockTimeCombinator(Mapped { inner: OrdChoice::new(Refined { inner: U32Le, predicate: Predicate675963002568997194 }, Refined { inner: U32Le, predicate: Predicate3133141078119142300 }), mapper: LockTimeMapper::new() })
}

                

pub struct SpecTxNonsegwit {
    pub txins: Seq<SpecTxin>,
    pub txout_count: VarInt,
    pub txouts: Seq<SpecTxout>,
    pub lock_time: SpecLockTime,
}

pub type SpecTxNonsegwitInner = ((Seq<SpecTxin>, VarInt), (Seq<SpecTxout>, SpecLockTime));
impl SpecFrom<SpecTxNonsegwit> for SpecTxNonsegwitInner {
    open spec fn spec_from(m: SpecTxNonsegwit) -> SpecTxNonsegwitInner {
        ((m.txins, m.txout_count), (m.txouts, m.lock_time))
    }
}
impl SpecFrom<SpecTxNonsegwitInner> for SpecTxNonsegwit {
    open spec fn spec_from(m: SpecTxNonsegwitInner) -> SpecTxNonsegwit {
        let ((txins, txout_count), (txouts, lock_time)) = m;
        SpecTxNonsegwit { txins, txout_count, txouts, lock_time }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TxNonsegwit<'a> {
    pub txins: RepeatResult<Txin<'a>>,
    pub txout_count: VarInt,
    pub txouts: RepeatResult<Txout<'a>>,
    pub lock_time: LockTime,
}

impl View for TxNonsegwit<'_> {
    type V = SpecTxNonsegwit;

    open spec fn view(&self) -> Self::V {
        SpecTxNonsegwit {
            txins: self.txins@,
            txout_count: self.txout_count@,
            txouts: self.txouts@,
            lock_time: self.lock_time@,
        }
    }
}
pub type TxNonsegwitInner<'a> = ((RepeatResult<Txin<'a>>, VarInt), (RepeatResult<Txout<'a>>, LockTime));
impl<'a> From<TxNonsegwit<'a>> for TxNonsegwitInner<'a> {
    fn ex_from(m: TxNonsegwit) -> TxNonsegwitInner {
        ((m.txins, m.txout_count), (m.txouts, m.lock_time))
    }
}
impl<'a> From<TxNonsegwitInner<'a>> for TxNonsegwit<'a> {
    fn ex_from(m: TxNonsegwitInner) -> TxNonsegwit {
        let ((txins, txout_count), (txouts, lock_time)) = m;
        TxNonsegwit { txins, txout_count, txouts, lock_time }
    }
}

pub struct TxNonsegwitMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxNonsegwitMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxNonsegwitMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxNonsegwitMapper(PhantomData)
    }
}
impl View for TxNonsegwitMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxNonsegwitMapper<'_> {
    type Src = SpecTxNonsegwitInner;
    type Dst = SpecTxNonsegwit;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxNonsegwitMapper<'a> {
    type Src = TxNonsegwitInner<'a>;
    type Dst = TxNonsegwit<'a>;
}

pub struct SpecTxNonsegwitCombinator(SpecTxNonsegwitCombinatorAlias);

impl SpecCombinator for SpecTxNonsegwitCombinator {
    type Type = SpecTxNonsegwit;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxNonsegwitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxNonsegwitCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxNonsegwitCombinatorAlias = Mapped<SpecDepend<(RepeatN<SpecTxinCombinator>, BtcVarint), (RepeatN<SpecTxoutCombinator>, SpecLockTimeCombinator)>, TxNonsegwitMapper<'static>>;

pub struct TxNonsegwitCombinator<'a>(TxNonsegwitCombinatorAlias<'a>);

impl<'a> View for TxNonsegwitCombinator<'a> {
    type V = SpecTxNonsegwitCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxNonsegwitCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxNonsegwitCombinator<'a> {
    type Type = TxNonsegwit<'a>;
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
pub type TxNonsegwitCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (RepeatN<TxinCombinator<'a>>, BtcVarint), (RepeatN<TxoutCombinator<'a>>, LockTimeCombinator), TxNonsegwitCont0<'a>>, TxNonsegwitMapper<'a>>;


pub closed spec fn spec_tx_nonsegwit(txin_count: VarInt) -> SpecTxNonsegwitCombinator {
    SpecTxNonsegwitCombinator(
    Mapped {
        inner: SpecDepend { fst: (RepeatN(spec_txin(), txin_count.spec_into()), BtcVarint), snd: |deps| spec_tx_nonsegwit_cont0(deps) },
        mapper: TxNonsegwitMapper::spec_new(),
    })
}

pub open spec fn spec_tx_nonsegwit_cont0(deps: (Seq<SpecTxin>, VarInt)) -> (RepeatN<SpecTxoutCombinator>, SpecLockTimeCombinator) {
    let (_, txout_count) = deps;
    (RepeatN(spec_txout(), txout_count.spec_into()), spec_lock_time())
}
                
pub fn tx_nonsegwit<'a>(txin_count: VarInt) -> (o: TxNonsegwitCombinator<'a>)
    ensures o@ == spec_tx_nonsegwit(txin_count@),
{
    TxNonsegwitCombinator(
    Mapped {
        inner: Depend { fst: (RepeatN(txin(), txin_count.ex_into()), BtcVarint), snd: TxNonsegwitCont0::new(), spec_snd: Ghost(|deps| spec_tx_nonsegwit_cont0(deps)) },
        mapper: TxNonsegwitMapper::new(),
    })
}

pub struct TxNonsegwitCont0<'a>(PhantomData<&'a ()>);
impl<'a> TxNonsegwitCont0<'a> {
    pub fn new() -> Self {
        TxNonsegwitCont0(PhantomData)
    }
}
impl<'a> Continuation<&(RepeatResult<Txin<'a>>, VarInt)> for TxNonsegwitCont0<'a> {
    type Output = (RepeatN<TxoutCombinator<'a>>, LockTimeCombinator);

    open spec fn requires(&self, deps: &(RepeatResult<Txin<'a>>, VarInt)) -> bool { true }

    open spec fn ensures(&self, deps: &(RepeatResult<Txin<'a>>, VarInt), o: Self::Output) -> bool {
        o@ == spec_tx_nonsegwit_cont0(deps@)
    }

    fn apply(&self, deps: &(RepeatResult<Txin<'a>>, VarInt)) -> Self::Output {
        let (_, txout_count) = *deps;
        (RepeatN(txout(), txout_count.ex_into()), lock_time())
    }
}
                

pub struct SpecWitnessComponent {
    pub l: VarInt,
    pub data: Seq<u8>,
}

pub type SpecWitnessComponentInner = (VarInt, Seq<u8>);
impl SpecFrom<SpecWitnessComponent> for SpecWitnessComponentInner {
    open spec fn spec_from(m: SpecWitnessComponent) -> SpecWitnessComponentInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecWitnessComponentInner> for SpecWitnessComponent {
    open spec fn spec_from(m: SpecWitnessComponentInner) -> SpecWitnessComponent {
        let (l, data) = m;
        SpecWitnessComponent { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct WitnessComponent<'a> {
    pub l: VarInt,
    pub data: &'a [u8],
}

impl View for WitnessComponent<'_> {
    type V = SpecWitnessComponent;

    open spec fn view(&self) -> Self::V {
        SpecWitnessComponent {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type WitnessComponentInner<'a> = (VarInt, &'a [u8]);
impl<'a> From<WitnessComponent<'a>> for WitnessComponentInner<'a> {
    fn ex_from(m: WitnessComponent) -> WitnessComponentInner {
        (m.l, m.data)
    }
}
impl<'a> From<WitnessComponentInner<'a>> for WitnessComponent<'a> {
    fn ex_from(m: WitnessComponentInner) -> WitnessComponent {
        let (l, data) = m;
        WitnessComponent { l, data }
    }
}

pub struct WitnessComponentMapper<'a>(PhantomData<&'a ()>);
impl<'a> WitnessComponentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        WitnessComponentMapper(PhantomData)
    }
    pub fn new() -> Self {
        WitnessComponentMapper(PhantomData)
    }
}
impl View for WitnessComponentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for WitnessComponentMapper<'_> {
    type Src = SpecWitnessComponentInner;
    type Dst = SpecWitnessComponent;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for WitnessComponentMapper<'a> {
    type Src = WitnessComponentInner<'a>;
    type Dst = WitnessComponent<'a>;
}

pub struct SpecWitnessComponentCombinator(SpecWitnessComponentCombinatorAlias);

impl SpecCombinator for SpecWitnessComponentCombinator {
    type Type = SpecWitnessComponent;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecWitnessComponentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecWitnessComponentCombinatorAlias::is_prefix_secure() }
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
pub type SpecWitnessComponentCombinatorAlias = Mapped<SpecDepend<BtcVarint, Bytes>, WitnessComponentMapper<'static>>;

pub struct WitnessComponentCombinator<'a>(WitnessComponentCombinatorAlias<'a>);

impl<'a> View for WitnessComponentCombinator<'a> {
    type V = SpecWitnessComponentCombinator;
    closed spec fn view(&self) -> Self::V { SpecWitnessComponentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for WitnessComponentCombinator<'a> {
    type Type = WitnessComponent<'a>;
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
pub type WitnessComponentCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BtcVarint, Bytes, WitnessComponentCont0<'a>>, WitnessComponentMapper<'a>>;


pub closed spec fn spec_witness_component() -> SpecWitnessComponentCombinator {
    SpecWitnessComponentCombinator(
    Mapped {
        inner: SpecDepend { fst: BtcVarint, snd: |deps| spec_witness_component_cont0(deps) },
        mapper: WitnessComponentMapper::spec_new(),
    })
}

pub open spec fn spec_witness_component_cont0(deps: VarInt) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn witness_component<'a>() -> (o: WitnessComponentCombinator<'a>)
    ensures o@ == spec_witness_component(),
{
    WitnessComponentCombinator(
    Mapped {
        inner: Depend { fst: BtcVarint, snd: WitnessComponentCont0::new(), spec_snd: Ghost(|deps| spec_witness_component_cont0(deps)) },
        mapper: WitnessComponentMapper::new(),
    })
}

pub struct WitnessComponentCont0<'a>(PhantomData<&'a ()>);
impl<'a> WitnessComponentCont0<'a> {
    pub fn new() -> Self {
        WitnessComponentCont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for WitnessComponentCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_witness_component_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecWitness {
    pub count: VarInt,
    pub data: Seq<SpecWitnessComponent>,
}

pub type SpecWitnessInner = (VarInt, Seq<SpecWitnessComponent>);
impl SpecFrom<SpecWitness> for SpecWitnessInner {
    open spec fn spec_from(m: SpecWitness) -> SpecWitnessInner {
        (m.count, m.data)
    }
}
impl SpecFrom<SpecWitnessInner> for SpecWitness {
    open spec fn spec_from(m: SpecWitnessInner) -> SpecWitness {
        let (count, data) = m;
        SpecWitness { count, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Witness<'a> {
    pub count: VarInt,
    pub data: RepeatResult<WitnessComponent<'a>>,
}

impl View for Witness<'_> {
    type V = SpecWitness;

    open spec fn view(&self) -> Self::V {
        SpecWitness {
            count: self.count@,
            data: self.data@,
        }
    }
}
pub type WitnessInner<'a> = (VarInt, RepeatResult<WitnessComponent<'a>>);
impl<'a> From<Witness<'a>> for WitnessInner<'a> {
    fn ex_from(m: Witness) -> WitnessInner {
        (m.count, m.data)
    }
}
impl<'a> From<WitnessInner<'a>> for Witness<'a> {
    fn ex_from(m: WitnessInner) -> Witness {
        let (count, data) = m;
        Witness { count, data }
    }
}

pub struct WitnessMapper<'a>(PhantomData<&'a ()>);
impl<'a> WitnessMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        WitnessMapper(PhantomData)
    }
    pub fn new() -> Self {
        WitnessMapper(PhantomData)
    }
}
impl View for WitnessMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for WitnessMapper<'_> {
    type Src = SpecWitnessInner;
    type Dst = SpecWitness;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for WitnessMapper<'a> {
    type Src = WitnessInner<'a>;
    type Dst = Witness<'a>;
}

pub struct SpecWitnessCombinator(SpecWitnessCombinatorAlias);

impl SpecCombinator for SpecWitnessCombinator {
    type Type = SpecWitness;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecWitnessCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecWitnessCombinatorAlias::is_prefix_secure() }
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
pub type SpecWitnessCombinatorAlias = Mapped<SpecDepend<BtcVarint, RepeatN<SpecWitnessComponentCombinator>>, WitnessMapper<'static>>;

pub struct WitnessCombinator<'a>(WitnessCombinatorAlias<'a>);

impl<'a> View for WitnessCombinator<'a> {
    type V = SpecWitnessCombinator;
    closed spec fn view(&self) -> Self::V { SpecWitnessCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for WitnessCombinator<'a> {
    type Type = Witness<'a>;
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
pub type WitnessCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BtcVarint, RepeatN<WitnessComponentCombinator<'a>>, WitnessCont0<'a>>, WitnessMapper<'a>>;


pub closed spec fn spec_witness() -> SpecWitnessCombinator {
    SpecWitnessCombinator(
    Mapped {
        inner: SpecDepend { fst: BtcVarint, snd: |deps| spec_witness_cont0(deps) },
        mapper: WitnessMapper::spec_new(),
    })
}

pub open spec fn spec_witness_cont0(deps: VarInt) -> RepeatN<SpecWitnessComponentCombinator> {
    let count = deps;
    RepeatN(spec_witness_component(), count.spec_into())
}
                
pub fn witness<'a>() -> (o: WitnessCombinator<'a>)
    ensures o@ == spec_witness(),
{
    WitnessCombinator(
    Mapped {
        inner: Depend { fst: BtcVarint, snd: WitnessCont0::new(), spec_snd: Ghost(|deps| spec_witness_cont0(deps)) },
        mapper: WitnessMapper::new(),
    })
}

pub struct WitnessCont0<'a>(PhantomData<&'a ()>);
impl<'a> WitnessCont0<'a> {
    pub fn new() -> Self {
        WitnessCont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for WitnessCont0<'a> {
    type Output = RepeatN<WitnessComponentCombinator<'a>>;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_witness_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let count = *deps;
        RepeatN(witness_component(), count.ex_into())
    }
}
                

pub struct SpecTxSegwit {
    pub flag: u8,
    pub txin_count: VarInt,
    pub txins: Seq<SpecTxin>,
    pub txout_count: VarInt,
    pub txouts: Seq<SpecTxout>,
    pub witness: Seq<SpecWitness>,
    pub lock_time: SpecLockTime,
}

pub type SpecTxSegwitInner = (((u8, VarInt), (Seq<SpecTxin>, VarInt)), (Seq<SpecTxout>, (Seq<SpecWitness>, SpecLockTime)));
impl SpecFrom<SpecTxSegwit> for SpecTxSegwitInner {
    open spec fn spec_from(m: SpecTxSegwit) -> SpecTxSegwitInner {
        (((m.flag, m.txin_count), (m.txins, m.txout_count)), (m.txouts, (m.witness, m.lock_time)))
    }
}
impl SpecFrom<SpecTxSegwitInner> for SpecTxSegwit {
    open spec fn spec_from(m: SpecTxSegwitInner) -> SpecTxSegwit {
        let (((flag, txin_count), (txins, txout_count)), (txouts, (witness, lock_time))) = m;
        SpecTxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TxSegwit<'a> {
    pub flag: u8,
    pub txin_count: VarInt,
    pub txins: RepeatResult<Txin<'a>>,
    pub txout_count: VarInt,
    pub txouts: RepeatResult<Txout<'a>>,
    pub witness: RepeatResult<Witness<'a>>,
    pub lock_time: LockTime,
}

impl View for TxSegwit<'_> {
    type V = SpecTxSegwit;

    open spec fn view(&self) -> Self::V {
        SpecTxSegwit {
            flag: self.flag@,
            txin_count: self.txin_count@,
            txins: self.txins@,
            txout_count: self.txout_count@,
            txouts: self.txouts@,
            witness: self.witness@,
            lock_time: self.lock_time@,
        }
    }
}
pub type TxSegwitInner<'a> = (((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt)), (RepeatResult<Txout<'a>>, (RepeatResult<Witness<'a>>, LockTime)));
impl<'a> From<TxSegwit<'a>> for TxSegwitInner<'a> {
    fn ex_from(m: TxSegwit) -> TxSegwitInner {
        (((m.flag, m.txin_count), (m.txins, m.txout_count)), (m.txouts, (m.witness, m.lock_time)))
    }
}
impl<'a> From<TxSegwitInner<'a>> for TxSegwit<'a> {
    fn ex_from(m: TxSegwitInner) -> TxSegwit {
        let (((flag, txin_count), (txins, txout_count)), (txouts, (witness, lock_time))) = m;
        TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time }
    }
}

pub struct TxSegwitMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxSegwitMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxSegwitMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxSegwitMapper(PhantomData)
    }
}
impl View for TxSegwitMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxSegwitMapper<'_> {
    type Src = SpecTxSegwitInner;
    type Dst = SpecTxSegwit;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxSegwitMapper<'a> {
    type Src = TxSegwitInner<'a>;
    type Dst = TxSegwit<'a>;
}
pub const TXSEGWITFLAG_CONST: u8 = 1;

pub struct SpecTxSegwitCombinator(SpecTxSegwitCombinatorAlias);

impl SpecCombinator for SpecTxSegwitCombinator {
    type Type = SpecTxSegwit;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxSegwitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxSegwitCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxSegwitCombinatorAlias = Mapped<SpecDepend<SpecDepend<(Refined<U8, TagPred<u8>>, BtcVarint), (RepeatN<SpecTxinCombinator>, BtcVarint)>, (RepeatN<SpecTxoutCombinator>, (RepeatN<SpecWitnessCombinator>, SpecLockTimeCombinator))>, TxSegwitMapper<'static>>;

pub struct TxSegwitCombinator<'a>(TxSegwitCombinatorAlias<'a>);

impl<'a> View for TxSegwitCombinator<'a> {
    type V = SpecTxSegwitCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxSegwitCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxSegwitCombinator<'a> {
    type Type = TxSegwit<'a>;
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
pub type TxSegwitCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, (Refined<U8, TagPred<u8>>, BtcVarint), (RepeatN<TxinCombinator<'a>>, BtcVarint), TxSegwitCont1<'a>>, (RepeatN<TxoutCombinator<'a>>, (RepeatN<WitnessCombinator<'a>>, LockTimeCombinator)), TxSegwitCont0<'a>>, TxSegwitMapper<'a>>;


pub closed spec fn spec_tx_segwit() -> SpecTxSegwitCombinator {
    SpecTxSegwitCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: (Refined { inner: U8, predicate: TagPred(TXSEGWITFLAG_CONST) }, BtcVarint), snd: |deps| spec_tx_segwit_cont1(deps) }, snd: |deps| spec_tx_segwit_cont0(deps) },
        mapper: TxSegwitMapper::spec_new(),
    })
}

pub open spec fn spec_tx_segwit_cont1(deps: (u8, VarInt)) -> (RepeatN<SpecTxinCombinator>, BtcVarint) {
    let (_, txin_count) = deps;
    (RepeatN(spec_txin(), txin_count.spec_into()), BtcVarint)
}
pub open spec fn spec_tx_segwit_cont0(deps: ((u8, VarInt), (Seq<SpecTxin>, VarInt))) -> (RepeatN<SpecTxoutCombinator>, (RepeatN<SpecWitnessCombinator>, SpecLockTimeCombinator)) {
    let ((_, txin_count), (_, txout_count)) = deps;
    (RepeatN(spec_txout(), txout_count.spec_into()), (RepeatN(spec_witness(), txin_count.spec_into()), spec_lock_time()))
}
                
pub fn tx_segwit<'a>() -> (o: TxSegwitCombinator<'a>)
    ensures o@ == spec_tx_segwit(),
{
    TxSegwitCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: (Refined { inner: U8, predicate: TagPred(TXSEGWITFLAG_CONST) }, BtcVarint), snd: TxSegwitCont1::new(), spec_snd: Ghost(|deps| spec_tx_segwit_cont1(deps)) }, snd: TxSegwitCont0::new(), spec_snd: Ghost(|deps| spec_tx_segwit_cont0(deps)) },
        mapper: TxSegwitMapper::new(),
    })
}

pub struct TxSegwitCont1<'a>(PhantomData<&'a ()>);
impl<'a> TxSegwitCont1<'a> {
    pub fn new() -> Self {
        TxSegwitCont1(PhantomData)
    }
}
impl<'a> Continuation<&(u8, VarInt)> for TxSegwitCont1<'a> {
    type Output = (RepeatN<TxinCombinator<'a>>, BtcVarint);

    open spec fn requires(&self, deps: &(u8, VarInt)) -> bool { true }

    open spec fn ensures(&self, deps: &(u8, VarInt), o: Self::Output) -> bool {
        o@ == spec_tx_segwit_cont1(deps@)
    }

    fn apply(&self, deps: &(u8, VarInt)) -> Self::Output {
        let (_, txin_count) = *deps;
        (RepeatN(txin(), txin_count.ex_into()), BtcVarint)
    }
}
pub struct TxSegwitCont0<'a>(PhantomData<&'a ()>);
impl<'a> TxSegwitCont0<'a> {
    pub fn new() -> Self {
        TxSegwitCont0(PhantomData)
    }
}
impl<'a> Continuation<&((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt))> for TxSegwitCont0<'a> {
    type Output = (RepeatN<TxoutCombinator<'a>>, (RepeatN<WitnessCombinator<'a>>, LockTimeCombinator));

    open spec fn requires(&self, deps: &((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt))) -> bool { true }

    open spec fn ensures(&self, deps: &((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt)), o: Self::Output) -> bool {
        o@ == spec_tx_segwit_cont0(deps@)
    }

    fn apply(&self, deps: &((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt))) -> Self::Output {
        let ((_, txin_count), (_, txout_count)) = *deps;
        (RepeatN(txout(), txout_count.ex_into()), (RepeatN(witness(), txin_count.ex_into()), lock_time()))
    }
}
                

pub enum SpecTxRest {
    Variant0(SpecTxSegwit),
    Variant1(SpecTxNonsegwit),
}

pub type SpecTxRestInner = Either<SpecTxSegwit, SpecTxNonsegwit>;



impl SpecFrom<SpecTxRest> for SpecTxRestInner {
    open spec fn spec_from(m: SpecTxRest) -> SpecTxRestInner {
        match m {
            SpecTxRest::Variant0(m) => Either::Left(m),
            SpecTxRest::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecTxRestInner> for SpecTxRest {
    open spec fn spec_from(m: SpecTxRestInner) -> SpecTxRest {
        match m {
            Either::Left(m) => SpecTxRest::Variant0(m),
            Either::Right(m) => SpecTxRest::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TxRest<'a> {
    Variant0(TxSegwit<'a>),
    Variant1(TxNonsegwit<'a>),
}

pub type TxRestInner<'a> = Either<TxSegwit<'a>, TxNonsegwit<'a>>;


impl<'a> View for TxRest<'a> {
    type V = SpecTxRest;
    open spec fn view(&self) -> Self::V {
        match self {
            TxRest::Variant0(m) => SpecTxRest::Variant0(m@),
            TxRest::Variant1(m) => SpecTxRest::Variant1(m@),
        }
    }
}


impl<'a> From<TxRest<'a>> for TxRestInner<'a> {
    fn ex_from(m: TxRest<'a>) -> TxRestInner<'a> {
        match m {
            TxRest::Variant0(m) => Either::Left(m),
            TxRest::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<TxRestInner<'a>> for TxRest<'a> {
    fn ex_from(m: TxRestInner<'a>) -> TxRest<'a> {
        match m {
            Either::Left(m) => TxRest::Variant0(m),
            Either::Right(m) => TxRest::Variant1(m),
        }
    }
    
}


pub struct TxRestMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxRestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxRestMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxRestMapper(PhantomData)
    }
}
impl View for TxRestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxRestMapper<'_> {
    type Src = SpecTxRestInner;
    type Dst = SpecTxRest;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxRestMapper<'a> {
    type Src = TxRestInner<'a>;
    type Dst = TxRest<'a>;
}


pub struct SpecTxRestCombinator(SpecTxRestCombinatorAlias);

impl SpecCombinator for SpecTxRestCombinator {
    type Type = SpecTxRest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxRestCombinatorAlias = Mapped<OrdChoice<Cond<SpecTxSegwitCombinator>, Cond<SpecTxNonsegwitCombinator>>, TxRestMapper<'static>>;

pub struct TxRestCombinator<'a>(TxRestCombinatorAlias<'a>);

impl<'a> View for TxRestCombinator<'a> {
    type V = SpecTxRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxRestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxRestCombinator<'a> {
    type Type = TxRest<'a>;
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
pub type TxRestCombinatorAlias<'a> = Mapped<OrdChoice<Cond<TxSegwitCombinator<'a>>, Cond<TxNonsegwitCombinator<'a>>>, TxRestMapper<'a>>;


pub closed spec fn spec_tx_rest(txin_count: VarInt) -> SpecTxRestCombinator {
    SpecTxRestCombinator(Mapped { inner: OrdChoice(Cond { cond: txin_count.spec_as_usize() == 0, inner: spec_tx_segwit() }, Cond { cond: !(txin_count.spec_as_usize() == 0), inner: spec_tx_nonsegwit(txin_count) }), mapper: TxRestMapper::spec_new() })
}

                
pub fn tx_rest<'a>(txin_count: VarInt) -> (o: TxRestCombinator<'a>)
    ensures o@ == spec_tx_rest(txin_count@),
{
    TxRestCombinator(Mapped { inner: OrdChoice::new(Cond { cond: txin_count.as_usize() == 0, inner: tx_segwit() }, Cond { cond: !(txin_count.as_usize() == 0), inner: tx_nonsegwit(txin_count) }), mapper: TxRestMapper::new() })
}

                

pub struct SpecTx {
    pub version: u32,
    pub txin_count: VarInt,
    pub rest: SpecTxRest,
}

pub type SpecTxInner = ((u32, VarInt), SpecTxRest);
impl SpecFrom<SpecTx> for SpecTxInner {
    open spec fn spec_from(m: SpecTx) -> SpecTxInner {
        ((m.version, m.txin_count), m.rest)
    }
}
impl SpecFrom<SpecTxInner> for SpecTx {
    open spec fn spec_from(m: SpecTxInner) -> SpecTx {
        let ((version, txin_count), rest) = m;
        SpecTx { version, txin_count, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tx<'a> {
    pub version: u32,
    pub txin_count: VarInt,
    pub rest: TxRest<'a>,
}

impl View for Tx<'_> {
    type V = SpecTx;

    open spec fn view(&self) -> Self::V {
        SpecTx {
            version: self.version@,
            txin_count: self.txin_count@,
            rest: self.rest@,
        }
    }
}
pub type TxInner<'a> = ((u32, VarInt), TxRest<'a>);
impl<'a> From<Tx<'a>> for TxInner<'a> {
    fn ex_from(m: Tx) -> TxInner {
        ((m.version, m.txin_count), m.rest)
    }
}
impl<'a> From<TxInner<'a>> for Tx<'a> {
    fn ex_from(m: TxInner) -> Tx {
        let ((version, txin_count), rest) = m;
        Tx { version, txin_count, rest }
    }
}

pub struct TxMapper<'a>(PhantomData<&'a ()>);
impl<'a> TxMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TxMapper(PhantomData)
    }
    pub fn new() -> Self {
        TxMapper(PhantomData)
    }
}
impl View for TxMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxMapper<'_> {
    type Src = SpecTxInner;
    type Dst = SpecTx;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TxMapper<'a> {
    type Src = TxInner<'a>;
    type Dst = Tx<'a>;
}

pub struct SpecTxCombinator(SpecTxCombinatorAlias);

impl SpecCombinator for SpecTxCombinator {
    type Type = SpecTx;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTxCombinatorAlias::is_prefix_secure() }
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
pub type SpecTxCombinatorAlias = Mapped<SpecDepend<(U32Le, BtcVarint), SpecTxRestCombinator>, TxMapper<'static>>;

pub struct TxCombinator<'a>(TxCombinatorAlias<'a>);

impl<'a> View for TxCombinator<'a> {
    type V = SpecTxCombinator;
    closed spec fn view(&self) -> Self::V { SpecTxCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TxCombinator<'a> {
    type Type = Tx<'a>;
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
pub type TxCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (U32Le, BtcVarint), TxRestCombinator<'a>, TxCont0<'a>>, TxMapper<'a>>;


pub closed spec fn spec_tx() -> SpecTxCombinator {
    SpecTxCombinator(
    Mapped {
        inner: SpecDepend { fst: (U32Le, BtcVarint), snd: |deps| spec_tx_cont0(deps) },
        mapper: TxMapper::spec_new(),
    })
}

pub open spec fn spec_tx_cont0(deps: (u32, VarInt)) -> SpecTxRestCombinator {
    let (_, txin_count) = deps;
    spec_tx_rest(txin_count)
}
                
pub fn tx<'a>() -> (o: TxCombinator<'a>)
    ensures o@ == spec_tx(),
{
    TxCombinator(
    Mapped {
        inner: Depend { fst: (U32Le, BtcVarint), snd: TxCont0::new(), spec_snd: Ghost(|deps| spec_tx_cont0(deps)) },
        mapper: TxMapper::new(),
    })
}

pub struct TxCont0<'a>(PhantomData<&'a ()>);
impl<'a> TxCont0<'a> {
    pub fn new() -> Self {
        TxCont0(PhantomData)
    }
}
impl<'a> Continuation<&(u32, VarInt)> for TxCont0<'a> {
    type Output = TxRestCombinator<'a>;

    open spec fn requires(&self, deps: &(u32, VarInt)) -> bool { true }

    open spec fn ensures(&self, deps: &(u32, VarInt), o: Self::Output) -> bool {
        o@ == spec_tx_cont0(deps@)
    }

    fn apply(&self, deps: &(u32, VarInt)) -> Self::Output {
        let (_, txin_count) = *deps;
        tx_rest(txin_count)
    }
}
                

pub struct SpecBlock {
    pub version: u32,
    pub prev_block: Seq<u8>,
    pub merkle_root: Seq<u8>,
    pub timestamp: u32,
    pub bits: u32,
    pub nonce: u32,
    pub tx_count: VarInt,
    pub txs: Seq<SpecTx>,
}

pub type SpecBlockInner = ((u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, VarInt)))))), Seq<SpecTx>);
impl SpecFrom<SpecBlock> for SpecBlockInner {
    open spec fn spec_from(m: SpecBlock) -> SpecBlockInner {
        ((m.version, (m.prev_block, (m.merkle_root, (m.timestamp, (m.bits, (m.nonce, m.tx_count)))))), m.txs)
    }
}
impl SpecFrom<SpecBlockInner> for SpecBlock {
    open spec fn spec_from(m: SpecBlockInner) -> SpecBlock {
        let ((version, (prev_block, (merkle_root, (timestamp, (bits, (nonce, tx_count)))))), txs) = m;
        SpecBlock { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Block<'a> {
    pub version: u32,
    pub prev_block: &'a [u8],
    pub merkle_root: &'a [u8],
    pub timestamp: u32,
    pub bits: u32,
    pub nonce: u32,
    pub tx_count: VarInt,
    pub txs: RepeatResult<Tx<'a>>,
}

impl View for Block<'_> {
    type V = SpecBlock;

    open spec fn view(&self) -> Self::V {
        SpecBlock {
            version: self.version@,
            prev_block: self.prev_block@,
            merkle_root: self.merkle_root@,
            timestamp: self.timestamp@,
            bits: self.bits@,
            nonce: self.nonce@,
            tx_count: self.tx_count@,
            txs: self.txs@,
        }
    }
}
pub type BlockInner<'a> = ((u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt)))))), RepeatResult<Tx<'a>>);
impl<'a> From<Block<'a>> for BlockInner<'a> {
    fn ex_from(m: Block) -> BlockInner {
        ((m.version, (m.prev_block, (m.merkle_root, (m.timestamp, (m.bits, (m.nonce, m.tx_count)))))), m.txs)
    }
}
impl<'a> From<BlockInner<'a>> for Block<'a> {
    fn ex_from(m: BlockInner) -> Block {
        let ((version, (prev_block, (merkle_root, (timestamp, (bits, (nonce, tx_count)))))), txs) = m;
        Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs }
    }
}

pub struct BlockMapper<'a>(PhantomData<&'a ()>);
impl<'a> BlockMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        BlockMapper(PhantomData)
    }
    pub fn new() -> Self {
        BlockMapper(PhantomData)
    }
}
impl View for BlockMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BlockMapper<'_> {
    type Src = SpecBlockInner;
    type Dst = SpecBlock;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for BlockMapper<'a> {
    type Src = BlockInner<'a>;
    type Dst = Block<'a>;
}

pub struct SpecBlockCombinator(SpecBlockCombinatorAlias);

impl SpecCombinator for SpecBlockCombinator {
    type Type = SpecBlock;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBlockCombinatorAlias::is_prefix_secure() }
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
pub type SpecBlockCombinatorAlias = Mapped<SpecDepend<(U32Le, (BytesN<32>, (BytesN<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), RepeatN<SpecTxCombinator>>, BlockMapper<'static>>;

pub struct BlockCombinator<'a>(BlockCombinatorAlias<'a>);

impl<'a> View for BlockCombinator<'a> {
    type V = SpecBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecBlockCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for BlockCombinator<'a> {
    type Type = Block<'a>;
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
pub type BlockCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (U32Le, (BytesN<32>, (BytesN<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), RepeatN<TxCombinator<'a>>, BlockCont0<'a>>, BlockMapper<'a>>;


pub closed spec fn spec_block() -> SpecBlockCombinator {
    SpecBlockCombinator(
    Mapped {
        inner: SpecDepend { fst: (U32Le, (BytesN::<32>, (BytesN::<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), snd: |deps| spec_block_cont0(deps) },
        mapper: BlockMapper::spec_new(),
    })
}

pub open spec fn spec_block_cont0(deps: (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, VarInt))))))) -> RepeatN<SpecTxCombinator> {
    let (_, (_, (_, (_, (_, (_, tx_count)))))) = deps;
    RepeatN(spec_tx(), tx_count.spec_into())
}
                
pub fn block<'a>() -> (o: BlockCombinator<'a>)
    ensures o@ == spec_block(),
{
    BlockCombinator(
    Mapped {
        inner: Depend { fst: (U32Le, (BytesN::<32>, (BytesN::<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), snd: BlockCont0::new(), spec_snd: Ghost(|deps| spec_block_cont0(deps)) },
        mapper: BlockMapper::new(),
    })
}

pub struct BlockCont0<'a>(PhantomData<&'a ()>);
impl<'a> BlockCont0<'a> {
    pub fn new() -> Self {
        BlockCont0(PhantomData)
    }
}
impl<'a> Continuation<&(u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt))))))> for BlockCont0<'a> {
    type Output = RepeatN<TxCombinator<'a>>;

    open spec fn requires(&self, deps: &(u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt))))))) -> bool { true }

    open spec fn ensures(&self, deps: &(u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt)))))), o: Self::Output) -> bool {
        o@ == spec_block_cont0(deps@)
    }

    fn apply(&self, deps: &(u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt))))))) -> Self::Output {
        let (_, (_, (_, (_, (_, (_, tx_count)))))) = *deps;
        RepeatN(tx(), tx_count.ex_into())
    }
}
                

}
