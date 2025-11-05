
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
                open spec fn ex_requires(&self) -> bool
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

pub type OutpointInnerRef<'a> = (&'a &'a [u8], &'a u32);
impl<'a> From<&'a Outpoint<'a>> for OutpointInnerRef<'a> {
    fn ex_from(m: &'a Outpoint) -> OutpointInnerRef<'a> {
        (&m.hash, &m.index)
    }
}

impl<'a> From<OutpointInner<'a>> for Outpoint<'a> {
    fn ex_from(m: OutpointInner) -> Outpoint {
        let (hash, index) = m;
        Outpoint { hash, index }
    }
}

pub struct OutpointMapper;
impl View for OutpointMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OutpointMapper {
    type Src = SpecOutpointInner;
    type Dst = SpecOutpoint;
}
impl SpecIsoProof for OutpointMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OutpointMapper {
    type Src = OutpointInner<'a>;
    type Dst = Outpoint<'a>;
    type RefSrc = OutpointInnerRef<'a>;
}
type SpecOutpointCombinatorAlias1 = (bytes::Fixed<32>, U32Le);
pub struct SpecOutpointCombinator(pub SpecOutpointCombinatorAlias);

impl SpecCombinator for SpecOutpointCombinator {
    type Type = SpecOutpoint;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecOutpointCombinatorAlias = Mapped<SpecOutpointCombinatorAlias1, OutpointMapper>;
type OutpointCombinatorAlias1 = (bytes::Fixed<32>, U32Le);
pub struct OutpointCombinator1(pub OutpointCombinatorAlias1);
impl View for OutpointCombinator1 {
    type V = SpecOutpointCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(OutpointCombinator1, OutpointCombinatorAlias1);

pub struct OutpointCombinator(pub OutpointCombinatorAlias);

impl View for OutpointCombinator {
    type V = SpecOutpointCombinator;
    open spec fn view(&self) -> Self::V { SpecOutpointCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OutpointCombinator {
    type Type = Outpoint<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OutpointCombinatorAlias = Mapped<OutpointCombinator1, OutpointMapper>;


pub open spec fn spec_outpoint() -> SpecOutpointCombinator {
    SpecOutpointCombinator(
    Mapped {
        inner: (bytes::Fixed::<32>, U32Le),
        mapper: OutpointMapper,
    })
}

                
pub fn outpoint<'a>() -> (o: OutpointCombinator)
    ensures o@ == spec_outpoint(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = OutpointCombinator(
    Mapped {
        inner: OutpointCombinator1((bytes::Fixed::<32>, U32Le)),
        mapper: OutpointMapper,
    });
    assert({
        &&& combinator@ == spec_outpoint()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_outpoint<'a>(input: &'a [u8]) -> (res: PResult<<OutpointCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_outpoint().spec_parse(input@) == Some((n as int, v@)),
        spec_outpoint().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_outpoint().spec_parse(input@) is None,
        spec_outpoint().spec_parse(input@) is None ==> res is Err,
{
    let combinator = outpoint();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_outpoint<'a>(v: <OutpointCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_outpoint().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_outpoint().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_outpoint().spec_serialize(v@))
        },
{
    let combinator = outpoint();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn outpoint_len<'a>(v: <OutpointCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_outpoint().wf(v@),
        spec_outpoint().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_outpoint().spec_serialize(v@).len(),
{
    let combinator = outpoint();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
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

pub type ScriptSigInnerRef<'a> = (&'a VarInt, &'a &'a [u8]);
impl<'a> From<&'a ScriptSig<'a>> for ScriptSigInnerRef<'a> {
    fn ex_from(m: &'a ScriptSig) -> ScriptSigInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<ScriptSigInner<'a>> for ScriptSig<'a> {
    fn ex_from(m: ScriptSigInner) -> ScriptSig {
        let (l, data) = m;
        ScriptSig { l, data }
    }
}

pub struct ScriptSigMapper;
impl View for ScriptSigMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ScriptSigMapper {
    type Src = SpecScriptSigInner;
    type Dst = SpecScriptSig;
}
impl SpecIsoProof for ScriptSigMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ScriptSigMapper {
    type Src = ScriptSigInner<'a>;
    type Dst = ScriptSig<'a>;
    type RefSrc = ScriptSigInnerRef<'a>;
}

pub struct SpecScriptSigCombinator(pub SpecScriptSigCombinatorAlias);

impl SpecCombinator for SpecScriptSigCombinator {
    type Type = SpecScriptSig;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecScriptSigCombinatorAlias = Mapped<SpecPair<BtcVarint, bytes::Variable>, ScriptSigMapper>;

pub struct ScriptSigCombinator(pub ScriptSigCombinatorAlias);

impl View for ScriptSigCombinator {
    type V = SpecScriptSigCombinator;
    open spec fn view(&self) -> Self::V { SpecScriptSigCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ScriptSigCombinator {
    type Type = ScriptSig<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ScriptSigCombinatorAlias = Mapped<Pair<BtcVarint, bytes::Variable, ScriptSigCont0>, ScriptSigMapper>;


pub open spec fn spec_script_sig() -> SpecScriptSigCombinator {
    SpecScriptSigCombinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_script_sig_cont0(deps)),
        mapper: ScriptSigMapper,
    })
}

pub open spec fn spec_script_sig_cont0(deps: VarInt) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for ScriptSigCont0 {
    type V = spec_fn(VarInt) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_script_sig_cont0(deps)
        }
    }
}

                
pub fn script_sig<'a>() -> (o: ScriptSigCombinator)
    ensures o@ == spec_script_sig(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ScriptSigCombinator(
    Mapped {
        inner: Pair::new(BtcVarint, ScriptSigCont0),
        mapper: ScriptSigMapper,
    });
    assert({
        &&& combinator@ == spec_script_sig()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_script_sig<'a>(input: &'a [u8]) -> (res: PResult<<ScriptSigCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_script_sig().spec_parse(input@) == Some((n as int, v@)),
        spec_script_sig().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_script_sig().spec_parse(input@) is None,
        spec_script_sig().spec_parse(input@) is None ==> res is Err,
{
    let combinator = script_sig();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_script_sig<'a>(v: <ScriptSigCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_script_sig().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_script_sig().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_script_sig().spec_serialize(v@))
        },
{
    let combinator = script_sig();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn script_sig_len<'a>(v: <ScriptSigCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_script_sig().wf(v@),
        spec_script_sig().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_script_sig().spec_serialize(v@).len(),
{
    let combinator = script_sig();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct ScriptSigCont0;
type ScriptSigCont0Type<'a, 'b> = &'b VarInt;
type ScriptSigCont0SType<'a, 'x> = &'x VarInt;
type ScriptSigCont0Input<'a, 'b, 'x> = POrSType<ScriptSigCont0Type<'a, 'b>, ScriptSigCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ScriptSigCont0Input<'a, 'b, 'x>> for ScriptSigCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: ScriptSigCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ScriptSigCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_script_sig_cont0(deps@)
    }

    fn apply(&self, deps: ScriptSigCont0Input<'a, 'b, 'x>) -> Self::Output {
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

pub type TxinInnerRef<'a> = (&'a Outpoint<'a>, (&'a ScriptSig<'a>, &'a u32));
impl<'a> From<&'a Txin<'a>> for TxinInnerRef<'a> {
    fn ex_from(m: &'a Txin) -> TxinInnerRef<'a> {
        (&m.previous_output, (&m.script_sig, &m.sequence))
    }
}

impl<'a> From<TxinInner<'a>> for Txin<'a> {
    fn ex_from(m: TxinInner) -> Txin {
        let (previous_output, (script_sig, sequence)) = m;
        Txin { previous_output, script_sig, sequence }
    }
}

pub struct TxinMapper;
impl View for TxinMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxinMapper {
    type Src = SpecTxinInner;
    type Dst = SpecTxin;
}
impl SpecIsoProof for TxinMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxinMapper {
    type Src = TxinInner<'a>;
    type Dst = Txin<'a>;
    type RefSrc = TxinInnerRef<'a>;
}
type SpecTxinCombinatorAlias1 = (SpecScriptSigCombinator, U32Le);
type SpecTxinCombinatorAlias2 = (SpecOutpointCombinator, SpecTxinCombinatorAlias1);
pub struct SpecTxinCombinator(pub SpecTxinCombinatorAlias);

impl SpecCombinator for SpecTxinCombinator {
    type Type = SpecTxin;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxinCombinatorAlias = Mapped<SpecTxinCombinatorAlias2, TxinMapper>;
type TxinCombinatorAlias1 = (ScriptSigCombinator, U32Le);
type TxinCombinatorAlias2 = (OutpointCombinator, TxinCombinator1);
pub struct TxinCombinator1(pub TxinCombinatorAlias1);
impl View for TxinCombinator1 {
    type V = SpecTxinCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TxinCombinator1, TxinCombinatorAlias1);

pub struct TxinCombinator2(pub TxinCombinatorAlias2);
impl View for TxinCombinator2 {
    type V = SpecTxinCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TxinCombinator2, TxinCombinatorAlias2);

pub struct TxinCombinator(pub TxinCombinatorAlias);

impl View for TxinCombinator {
    type V = SpecTxinCombinator;
    open spec fn view(&self) -> Self::V { SpecTxinCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxinCombinator {
    type Type = Txin<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxinCombinatorAlias = Mapped<TxinCombinator2, TxinMapper>;


pub open spec fn spec_txin() -> SpecTxinCombinator {
    SpecTxinCombinator(
    Mapped {
        inner: (spec_outpoint(), (spec_script_sig(), U32Le)),
        mapper: TxinMapper,
    })
}

                
pub fn txin<'a>() -> (o: TxinCombinator)
    ensures o@ == spec_txin(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxinCombinator(
    Mapped {
        inner: TxinCombinator2((outpoint(), TxinCombinator1((script_sig(), U32Le)))),
        mapper: TxinMapper,
    });
    assert({
        &&& combinator@ == spec_txin()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_txin<'a>(input: &'a [u8]) -> (res: PResult<<TxinCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_txin().spec_parse(input@) == Some((n as int, v@)),
        spec_txin().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_txin().spec_parse(input@) is None,
        spec_txin().spec_parse(input@) is None ==> res is Err,
{
    let combinator = txin();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_txin<'a>(v: <TxinCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_txin().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_txin().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_txin().spec_serialize(v@))
        },
{
    let combinator = txin();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn txin_len<'a>(v: <TxinCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_txin().wf(v@),
        spec_txin().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_txin().spec_serialize(v@).len(),
{
    let combinator = txin();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

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

pub type ScriptInnerRef<'a> = (&'a VarInt, &'a &'a [u8]);
impl<'a> From<&'a Script<'a>> for ScriptInnerRef<'a> {
    fn ex_from(m: &'a Script) -> ScriptInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<ScriptInner<'a>> for Script<'a> {
    fn ex_from(m: ScriptInner) -> Script {
        let (l, data) = m;
        Script { l, data }
    }
}

pub struct ScriptMapper;
impl View for ScriptMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ScriptMapper {
    type Src = SpecScriptInner;
    type Dst = SpecScript;
}
impl SpecIsoProof for ScriptMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ScriptMapper {
    type Src = ScriptInner<'a>;
    type Dst = Script<'a>;
    type RefSrc = ScriptInnerRef<'a>;
}

pub struct SpecScriptCombinator(pub SpecScriptCombinatorAlias);

impl SpecCombinator for SpecScriptCombinator {
    type Type = SpecScript;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecScriptCombinatorAlias = Mapped<SpecPair<BtcVarint, bytes::Variable>, ScriptMapper>;

pub struct ScriptCombinator(pub ScriptCombinatorAlias);

impl View for ScriptCombinator {
    type V = SpecScriptCombinator;
    open spec fn view(&self) -> Self::V { SpecScriptCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ScriptCombinator {
    type Type = Script<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ScriptCombinatorAlias = Mapped<Pair<BtcVarint, bytes::Variable, ScriptCont0>, ScriptMapper>;


pub open spec fn spec_script() -> SpecScriptCombinator {
    SpecScriptCombinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_script_cont0(deps)),
        mapper: ScriptMapper,
    })
}

pub open spec fn spec_script_cont0(deps: VarInt) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for ScriptCont0 {
    type V = spec_fn(VarInt) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_script_cont0(deps)
        }
    }
}

                
pub fn script<'a>() -> (o: ScriptCombinator)
    ensures o@ == spec_script(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ScriptCombinator(
    Mapped {
        inner: Pair::new(BtcVarint, ScriptCont0),
        mapper: ScriptMapper,
    });
    assert({
        &&& combinator@ == spec_script()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_script<'a>(input: &'a [u8]) -> (res: PResult<<ScriptCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_script().spec_parse(input@) == Some((n as int, v@)),
        spec_script().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_script().spec_parse(input@) is None,
        spec_script().spec_parse(input@) is None ==> res is Err,
{
    let combinator = script();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_script<'a>(v: <ScriptCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_script().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_script().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_script().spec_serialize(v@))
        },
{
    let combinator = script();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn script_len<'a>(v: <ScriptCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_script().wf(v@),
        spec_script().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_script().spec_serialize(v@).len(),
{
    let combinator = script();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct ScriptCont0;
type ScriptCont0Type<'a, 'b> = &'b VarInt;
type ScriptCont0SType<'a, 'x> = &'x VarInt;
type ScriptCont0Input<'a, 'b, 'x> = POrSType<ScriptCont0Type<'a, 'b>, ScriptCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ScriptCont0Input<'a, 'b, 'x>> for ScriptCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: ScriptCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ScriptCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_script_cont0(deps@)
    }

    fn apply(&self, deps: ScriptCont0Input<'a, 'b, 'x>) -> Self::Output {
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

pub type TxoutInnerRef<'a> = (&'a u64, &'a Script<'a>);
impl<'a> From<&'a Txout<'a>> for TxoutInnerRef<'a> {
    fn ex_from(m: &'a Txout) -> TxoutInnerRef<'a> {
        (&m.value, &m.script_pubkey)
    }
}

impl<'a> From<TxoutInner<'a>> for Txout<'a> {
    fn ex_from(m: TxoutInner) -> Txout {
        let (value, script_pubkey) = m;
        Txout { value, script_pubkey }
    }
}

pub struct TxoutMapper;
impl View for TxoutMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxoutMapper {
    type Src = SpecTxoutInner;
    type Dst = SpecTxout;
}
impl SpecIsoProof for TxoutMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxoutMapper {
    type Src = TxoutInner<'a>;
    type Dst = Txout<'a>;
    type RefSrc = TxoutInnerRef<'a>;
}
type SpecTxoutCombinatorAlias1 = (U64Le, SpecScriptCombinator);
pub struct SpecTxoutCombinator(pub SpecTxoutCombinatorAlias);

impl SpecCombinator for SpecTxoutCombinator {
    type Type = SpecTxout;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxoutCombinatorAlias = Mapped<SpecTxoutCombinatorAlias1, TxoutMapper>;
type TxoutCombinatorAlias1 = (U64Le, ScriptCombinator);
pub struct TxoutCombinator1(pub TxoutCombinatorAlias1);
impl View for TxoutCombinator1 {
    type V = SpecTxoutCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TxoutCombinator1, TxoutCombinatorAlias1);

pub struct TxoutCombinator(pub TxoutCombinatorAlias);

impl View for TxoutCombinator {
    type V = SpecTxoutCombinator;
    open spec fn view(&self) -> Self::V { SpecTxoutCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxoutCombinator {
    type Type = Txout<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxoutCombinatorAlias = Mapped<TxoutCombinator1, TxoutMapper>;


pub open spec fn spec_txout() -> SpecTxoutCombinator {
    SpecTxoutCombinator(
    Mapped {
        inner: (U64Le, spec_script()),
        mapper: TxoutMapper,
    })
}

                
pub fn txout<'a>() -> (o: TxoutCombinator)
    ensures o@ == spec_txout(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxoutCombinator(
    Mapped {
        inner: TxoutCombinator1((U64Le, script())),
        mapper: TxoutMapper,
    });
    assert({
        &&& combinator@ == spec_txout()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_txout<'a>(input: &'a [u8]) -> (res: PResult<<TxoutCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_txout().spec_parse(input@) == Some((n as int, v@)),
        spec_txout().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_txout().spec_parse(input@) is None,
        spec_txout().spec_parse(input@) is None ==> res is Err,
{
    let combinator = txout();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_txout<'a>(v: <TxoutCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_txout().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_txout().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_txout().spec_serialize(v@))
        },
{
    let combinator = txout();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn txout_len<'a>(v: <TxoutCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_txout().wf(v@),
        spec_txout().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_txout().spec_serialize(v@).len(),
{
    let combinator = txout();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
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

pub type WitnessComponentInnerRef<'a> = (&'a VarInt, &'a &'a [u8]);
impl<'a> From<&'a WitnessComponent<'a>> for WitnessComponentInnerRef<'a> {
    fn ex_from(m: &'a WitnessComponent) -> WitnessComponentInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<WitnessComponentInner<'a>> for WitnessComponent<'a> {
    fn ex_from(m: WitnessComponentInner) -> WitnessComponent {
        let (l, data) = m;
        WitnessComponent { l, data }
    }
}

pub struct WitnessComponentMapper;
impl View for WitnessComponentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for WitnessComponentMapper {
    type Src = SpecWitnessComponentInner;
    type Dst = SpecWitnessComponent;
}
impl SpecIsoProof for WitnessComponentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for WitnessComponentMapper {
    type Src = WitnessComponentInner<'a>;
    type Dst = WitnessComponent<'a>;
    type RefSrc = WitnessComponentInnerRef<'a>;
}

pub struct SpecWitnessComponentCombinator(pub SpecWitnessComponentCombinatorAlias);

impl SpecCombinator for SpecWitnessComponentCombinator {
    type Type = SpecWitnessComponent;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecWitnessComponentCombinatorAlias = Mapped<SpecPair<BtcVarint, bytes::Variable>, WitnessComponentMapper>;

pub struct WitnessComponentCombinator(pub WitnessComponentCombinatorAlias);

impl View for WitnessComponentCombinator {
    type V = SpecWitnessComponentCombinator;
    open spec fn view(&self) -> Self::V { SpecWitnessComponentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for WitnessComponentCombinator {
    type Type = WitnessComponent<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type WitnessComponentCombinatorAlias = Mapped<Pair<BtcVarint, bytes::Variable, WitnessComponentCont0>, WitnessComponentMapper>;


pub open spec fn spec_witness_component() -> SpecWitnessComponentCombinator {
    SpecWitnessComponentCombinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_witness_component_cont0(deps)),
        mapper: WitnessComponentMapper,
    })
}

pub open spec fn spec_witness_component_cont0(deps: VarInt) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for WitnessComponentCont0 {
    type V = spec_fn(VarInt) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_witness_component_cont0(deps)
        }
    }
}

                
pub fn witness_component<'a>() -> (o: WitnessComponentCombinator)
    ensures o@ == spec_witness_component(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = WitnessComponentCombinator(
    Mapped {
        inner: Pair::new(BtcVarint, WitnessComponentCont0),
        mapper: WitnessComponentMapper,
    });
    assert({
        &&& combinator@ == spec_witness_component()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_witness_component<'a>(input: &'a [u8]) -> (res: PResult<<WitnessComponentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_witness_component().spec_parse(input@) == Some((n as int, v@)),
        spec_witness_component().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_witness_component().spec_parse(input@) is None,
        spec_witness_component().spec_parse(input@) is None ==> res is Err,
{
    let combinator = witness_component();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_witness_component<'a>(v: <WitnessComponentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_witness_component().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_witness_component().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_witness_component().spec_serialize(v@))
        },
{
    let combinator = witness_component();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn witness_component_len<'a>(v: <WitnessComponentCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_witness_component().wf(v@),
        spec_witness_component().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_witness_component().spec_serialize(v@).len(),
{
    let combinator = witness_component();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct WitnessComponentCont0;
type WitnessComponentCont0Type<'a, 'b> = &'b VarInt;
type WitnessComponentCont0SType<'a, 'x> = &'x VarInt;
type WitnessComponentCont0Input<'a, 'b, 'x> = POrSType<WitnessComponentCont0Type<'a, 'b>, WitnessComponentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<WitnessComponentCont0Input<'a, 'b, 'x>> for WitnessComponentCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: WitnessComponentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: WitnessComponentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_witness_component_cont0(deps@)
    }

    fn apply(&self, deps: WitnessComponentCont0Input<'a, 'b, 'x>) -> Self::Output {
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

pub type WitnessInnerRef<'a> = (&'a VarInt, &'a RepeatResult<WitnessComponent<'a>>);
impl<'a> From<&'a Witness<'a>> for WitnessInnerRef<'a> {
    fn ex_from(m: &'a Witness) -> WitnessInnerRef<'a> {
        (&m.count, &m.data)
    }
}

impl<'a> From<WitnessInner<'a>> for Witness<'a> {
    fn ex_from(m: WitnessInner) -> Witness {
        let (count, data) = m;
        Witness { count, data }
    }
}

pub struct WitnessMapper;
impl View for WitnessMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for WitnessMapper {
    type Src = SpecWitnessInner;
    type Dst = SpecWitness;
}
impl SpecIsoProof for WitnessMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for WitnessMapper {
    type Src = WitnessInner<'a>;
    type Dst = Witness<'a>;
    type RefSrc = WitnessInnerRef<'a>;
}

pub struct SpecWitnessCombinator(pub SpecWitnessCombinatorAlias);

impl SpecCombinator for SpecWitnessCombinator {
    type Type = SpecWitness;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecWitnessCombinatorAlias = Mapped<SpecPair<BtcVarint, RepeatN<SpecWitnessComponentCombinator>>, WitnessMapper>;

pub struct WitnessCombinator(pub WitnessCombinatorAlias);

impl View for WitnessCombinator {
    type V = SpecWitnessCombinator;
    open spec fn view(&self) -> Self::V { SpecWitnessCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for WitnessCombinator {
    type Type = Witness<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type WitnessCombinatorAlias = Mapped<Pair<BtcVarint, RepeatN<WitnessComponentCombinator>, WitnessCont0>, WitnessMapper>;


pub open spec fn spec_witness() -> SpecWitnessCombinator {
    SpecWitnessCombinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_witness_cont0(deps)),
        mapper: WitnessMapper,
    })
}

pub open spec fn spec_witness_cont0(deps: VarInt) -> RepeatN<SpecWitnessComponentCombinator> {
    let count = deps;
    RepeatN(spec_witness_component(), count.spec_into())
}

impl View for WitnessCont0 {
    type V = spec_fn(VarInt) -> RepeatN<SpecWitnessComponentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_witness_cont0(deps)
        }
    }
}

                
pub fn witness<'a>() -> (o: WitnessCombinator)
    ensures o@ == spec_witness(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = WitnessCombinator(
    Mapped {
        inner: Pair::new(BtcVarint, WitnessCont0),
        mapper: WitnessMapper,
    });
    assert({
        &&& combinator@ == spec_witness()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_witness<'a>(input: &'a [u8]) -> (res: PResult<<WitnessCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_witness().spec_parse(input@) == Some((n as int, v@)),
        spec_witness().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_witness().spec_parse(input@) is None,
        spec_witness().spec_parse(input@) is None ==> res is Err,
{
    let combinator = witness();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_witness<'a>(v: <WitnessCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_witness().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_witness().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_witness().spec_serialize(v@))
        },
{
    let combinator = witness();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn witness_len<'a>(v: <WitnessCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_witness().wf(v@),
        spec_witness().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_witness().spec_serialize(v@).len(),
{
    let combinator = witness();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct WitnessCont0;
type WitnessCont0Type<'a, 'b> = &'b VarInt;
type WitnessCont0SType<'a, 'x> = &'x VarInt;
type WitnessCont0Input<'a, 'b, 'x> = POrSType<WitnessCont0Type<'a, 'b>, WitnessCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<WitnessCont0Input<'a, 'b, 'x>> for WitnessCont0 {
    type Output = RepeatN<WitnessComponentCombinator>;

    open spec fn requires(&self, deps: WitnessCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: WitnessCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_witness_cont0(deps@)
    }

    fn apply(&self, deps: WitnessCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let count = *deps;
                RepeatN(witness_component(), count.ex_into())
            }
            POrSType::S(deps) => {
                let count = deps;
                let count = *count;
                RepeatN(witness_component(), count.ex_into())
            }
        }
    }
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

pub type LockTimeInnerRef<'a> = Either<&'a u32, &'a u32>;


impl View for LockTime {
    type V = SpecLockTime;
    open spec fn view(&self) -> Self::V {
        match self {
            LockTime::BlockNo(m) => SpecLockTime::BlockNo(m@),
            LockTime::Timestamp(m) => SpecLockTime::Timestamp(m@),
        }
    }
}


impl<'a> From<&'a LockTime> for LockTimeInnerRef<'a> {
    fn ex_from(m: &'a LockTime) -> LockTimeInnerRef<'a> {
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
impl View for LockTimeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LockTimeMapper {
    type Src = SpecLockTimeInner;
    type Dst = SpecLockTime;
}
impl SpecIsoProof for LockTimeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LockTimeMapper {
    type Src = LockTimeInner;
    type Dst = LockTime;
    type RefSrc = LockTimeInnerRef<'a>;
}

type SpecLockTimeCombinatorAlias1 = Choice<Refined<U32Le, Predicate675963002568997194>, Refined<U32Le, Predicate3133141078119142300>>;
pub struct SpecLockTimeCombinator(pub SpecLockTimeCombinatorAlias);

impl SpecCombinator for SpecLockTimeCombinator {
    type Type = SpecLockTime;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecLockTimeCombinatorAlias = Mapped<SpecLockTimeCombinatorAlias1, LockTimeMapper>;
pub struct Predicate675963002568997194;
impl View for Predicate675963002568997194 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u32> for Predicate675963002568997194 {
    fn apply(&self, i: &u32) -> bool {
        let i = (*i);
        (i >= 0 && i <= 499999999)
    }
}
impl SpecPred<u32> for Predicate675963002568997194 {
    open spec fn spec_apply(&self, i: &u32) -> bool {
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
impl Pred<u32> for Predicate3133141078119142300 {
    fn apply(&self, i: &u32) -> bool {
        let i = (*i);
        (i >= 500000000)
    }
}
impl SpecPred<u32> for Predicate3133141078119142300 {
    open spec fn spec_apply(&self, i: &u32) -> bool {
        let i = (*i);
        (i >= 500000000)
    }
}
type LockTimeCombinatorAlias1 = Choice<Refined<U32Le, Predicate675963002568997194>, Refined<U32Le, Predicate3133141078119142300>>;
pub struct LockTimeCombinator1(pub LockTimeCombinatorAlias1);
impl View for LockTimeCombinator1 {
    type V = SpecLockTimeCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(LockTimeCombinator1, LockTimeCombinatorAlias1);

pub struct LockTimeCombinator(pub LockTimeCombinatorAlias);

impl View for LockTimeCombinator {
    type V = SpecLockTimeCombinator;
    open spec fn view(&self) -> Self::V { SpecLockTimeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LockTimeCombinator {
    type Type = LockTime;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type LockTimeCombinatorAlias = Mapped<LockTimeCombinator1, LockTimeMapper>;


pub open spec fn spec_lock_time() -> SpecLockTimeCombinator {
    SpecLockTimeCombinator(Mapped { inner: Choice(Refined { inner: U32Le, predicate: Predicate675963002568997194 }, Refined { inner: U32Le, predicate: Predicate3133141078119142300 }), mapper: LockTimeMapper })
}

                
pub fn lock_time<'a>() -> (o: LockTimeCombinator)
    ensures o@ == spec_lock_time(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = LockTimeCombinator(Mapped { inner: LockTimeCombinator1(Choice::new(Refined { inner: U32Le, predicate: Predicate675963002568997194 }, Refined { inner: U32Le, predicate: Predicate3133141078119142300 })), mapper: LockTimeMapper });
    assert({
        &&& combinator@ == spec_lock_time()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_lock_time<'a>(input: &'a [u8]) -> (res: PResult<<LockTimeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_lock_time().spec_parse(input@) == Some((n as int, v@)),
        spec_lock_time().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_lock_time().spec_parse(input@) is None,
        spec_lock_time().spec_parse(input@) is None ==> res is Err,
{
    let combinator = lock_time();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_lock_time<'a>(v: <LockTimeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_lock_time().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_lock_time().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_lock_time().spec_serialize(v@))
        },
{
    let combinator = lock_time();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn lock_time_len<'a>(v: <LockTimeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_lock_time().wf(v@),
        spec_lock_time().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_lock_time().spec_serialize(v@).len(),
{
    let combinator = lock_time();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
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

pub type TxSegwitInnerRef<'a> = (((&'a u8, &'a VarInt), (&'a RepeatResult<Txin<'a>>, &'a VarInt)), (&'a RepeatResult<Txout<'a>>, (&'a RepeatResult<Witness<'a>>, &'a LockTime)));
impl<'a> From<&'a TxSegwit<'a>> for TxSegwitInnerRef<'a> {
    fn ex_from(m: &'a TxSegwit) -> TxSegwitInnerRef<'a> {
        (((&m.flag, &m.txin_count), (&m.txins, &m.txout_count)), (&m.txouts, (&m.witness, &m.lock_time)))
    }
}

impl<'a> From<TxSegwitInner<'a>> for TxSegwit<'a> {
    fn ex_from(m: TxSegwitInner) -> TxSegwit {
        let (((flag, txin_count), (txins, txout_count)), (txouts, (witness, lock_time))) = m;
        TxSegwit { flag, txin_count, txins, txout_count, txouts, witness, lock_time }
    }
}

pub struct TxSegwitMapper;
impl View for TxSegwitMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxSegwitMapper {
    type Src = SpecTxSegwitInner;
    type Dst = SpecTxSegwit;
}
impl SpecIsoProof for TxSegwitMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxSegwitMapper {
    type Src = TxSegwitInner<'a>;
    type Dst = TxSegwit<'a>;
    type RefSrc = TxSegwitInnerRef<'a>;
}
pub const TXSEGWITFLAG_CONST: u8 = 1;

pub struct SpecTxSegwitCombinator(pub SpecTxSegwitCombinatorAlias);

impl SpecCombinator for SpecTxSegwitCombinator {
    type Type = SpecTxSegwit;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxSegwitCombinatorAlias = Mapped<SpecPair<SpecPair<(Refined<U8, TagPred<u8>>, BtcVarint), (RepeatN<SpecTxinCombinator>, BtcVarint)>, (RepeatN<SpecTxoutCombinator>, (RepeatN<SpecWitnessCombinator>, SpecLockTimeCombinator))>, TxSegwitMapper>;

pub struct TxSegwitCombinator(pub TxSegwitCombinatorAlias);

impl View for TxSegwitCombinator {
    type V = SpecTxSegwitCombinator;
    open spec fn view(&self) -> Self::V { SpecTxSegwitCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxSegwitCombinator {
    type Type = TxSegwit<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxSegwitCombinatorAlias = Mapped<Pair<Pair<(Refined<U8, TagPred<u8>>, BtcVarint), (RepeatN<TxinCombinator>, BtcVarint), TxSegwitCont1>, (RepeatN<TxoutCombinator>, (RepeatN<WitnessCombinator>, LockTimeCombinator)), TxSegwitCont0>, TxSegwitMapper>;


pub open spec fn spec_tx_segwit() -> SpecTxSegwitCombinator {
    SpecTxSegwitCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new((Refined { inner: U8, predicate: TagPred(TXSEGWITFLAG_CONST) }, BtcVarint), |deps| spec_tx_segwit_cont1(deps)), |deps| spec_tx_segwit_cont0(deps)),
        mapper: TxSegwitMapper,
    })
}

pub open spec fn spec_tx_segwit_cont1(deps: (u8, VarInt)) -> (RepeatN<SpecTxinCombinator>, BtcVarint) {
    let (_, txin_count) = deps;
    (RepeatN(spec_txin(), txin_count.spec_into()), BtcVarint)
}

impl View for TxSegwitCont1 {
    type V = spec_fn((u8, VarInt)) -> (RepeatN<SpecTxinCombinator>, BtcVarint);

    open spec fn view(&self) -> Self::V {
        |deps: (u8, VarInt)| {
            spec_tx_segwit_cont1(deps)
        }
    }
}

pub open spec fn spec_tx_segwit_cont0(deps: ((u8, VarInt), (Seq<SpecTxin>, VarInt))) -> (RepeatN<SpecTxoutCombinator>, (RepeatN<SpecWitnessCombinator>, SpecLockTimeCombinator)) {
    let ((_, txin_count), (_, txout_count)) = deps;
    (RepeatN(spec_txout(), txout_count.spec_into()), (RepeatN(spec_witness(), txin_count.spec_into()), spec_lock_time()))
}

impl View for TxSegwitCont0 {
    type V = spec_fn(((u8, VarInt), (Seq<SpecTxin>, VarInt))) -> (RepeatN<SpecTxoutCombinator>, (RepeatN<SpecWitnessCombinator>, SpecLockTimeCombinator));

    open spec fn view(&self) -> Self::V {
        |deps: ((u8, VarInt), (Seq<SpecTxin>, VarInt))| {
            spec_tx_segwit_cont0(deps)
        }
    }
}

                
pub fn tx_segwit<'a>() -> (o: TxSegwitCombinator)
    ensures o@ == spec_tx_segwit(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxSegwitCombinator(
    Mapped {
        inner: Pair::new(Pair::new((Refined { inner: U8, predicate: TagPred(TXSEGWITFLAG_CONST) }, BtcVarint), TxSegwitCont1), TxSegwitCont0),
        mapper: TxSegwitMapper,
    });
    assert({
        &&& combinator@ == spec_tx_segwit()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_tx_segwit<'a>(input: &'a [u8]) -> (res: PResult<<TxSegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tx_segwit().spec_parse(input@) == Some((n as int, v@)),
        spec_tx_segwit().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tx_segwit().spec_parse(input@) is None,
        spec_tx_segwit().spec_parse(input@) is None ==> res is Err,
{
    let combinator = tx_segwit();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tx_segwit<'a>(v: <TxSegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tx_segwit().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tx_segwit().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tx_segwit().spec_serialize(v@))
        },
{
    let combinator = tx_segwit();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn tx_segwit_len<'a>(v: <TxSegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_tx_segwit().wf(v@),
        spec_tx_segwit().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tx_segwit().spec_serialize(v@).len(),
{
    let combinator = tx_segwit();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TxSegwitCont1;
type TxSegwitCont1Type<'a, 'b> = &'b (u8, VarInt);
type TxSegwitCont1SType<'a, 'x> = (&'x u8, &'x VarInt);
type TxSegwitCont1Input<'a, 'b, 'x> = POrSType<TxSegwitCont1Type<'a, 'b>, TxSegwitCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TxSegwitCont1Input<'a, 'b, 'x>> for TxSegwitCont1 {
    type Output = (RepeatN<TxinCombinator>, BtcVarint);

    open spec fn requires(&self, deps: TxSegwitCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TxSegwitCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tx_segwit_cont1(deps@)
    }

    fn apply(&self, deps: TxSegwitCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, txin_count) = *deps;
                (RepeatN(txin(), txin_count.ex_into()), BtcVarint)
            }
            POrSType::S(deps) => {
                let (_, txin_count) = deps;
                let txin_count = *txin_count;
                (RepeatN(txin(), txin_count.ex_into()), BtcVarint)
            }
        }
    }
}
pub struct TxSegwitCont0;
type TxSegwitCont0Type<'a, 'b> = &'b ((u8, VarInt), (RepeatResult<Txin<'a>>, VarInt));
type TxSegwitCont0SType<'a, 'x> = ((&'x u8, &'x VarInt), (&'x RepeatResult<Txin<'a>>, &'x VarInt));
type TxSegwitCont0Input<'a, 'b, 'x> = POrSType<TxSegwitCont0Type<'a, 'b>, TxSegwitCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TxSegwitCont0Input<'a, 'b, 'x>> for TxSegwitCont0 {
    type Output = (RepeatN<TxoutCombinator>, (RepeatN<WitnessCombinator>, LockTimeCombinator));

    open spec fn requires(&self, deps: TxSegwitCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TxSegwitCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tx_segwit_cont0(deps@)
    }

    fn apply(&self, deps: TxSegwitCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((_, txin_count), (_, txout_count)) = *deps;
                (RepeatN(txout(), txout_count.ex_into()), (RepeatN(witness(), txin_count.ex_into()), lock_time()))
            }
            POrSType::S(deps) => {
                let ((_, txin_count), (_, txout_count)) = deps;
                let (txin_count, txout_count) = (*txin_count, *txout_count);
                (RepeatN(txout(), txout_count.ex_into()), (RepeatN(witness(), txin_count.ex_into()), lock_time()))
            }
        }
    }
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

pub type TxNonsegwitInnerRef<'a> = ((&'a RepeatResult<Txin<'a>>, &'a VarInt), (&'a RepeatResult<Txout<'a>>, &'a LockTime));
impl<'a> From<&'a TxNonsegwit<'a>> for TxNonsegwitInnerRef<'a> {
    fn ex_from(m: &'a TxNonsegwit) -> TxNonsegwitInnerRef<'a> {
        ((&m.txins, &m.txout_count), (&m.txouts, &m.lock_time))
    }
}

impl<'a> From<TxNonsegwitInner<'a>> for TxNonsegwit<'a> {
    fn ex_from(m: TxNonsegwitInner) -> TxNonsegwit {
        let ((txins, txout_count), (txouts, lock_time)) = m;
        TxNonsegwit { txins, txout_count, txouts, lock_time }
    }
}

pub struct TxNonsegwitMapper;
impl View for TxNonsegwitMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxNonsegwitMapper {
    type Src = SpecTxNonsegwitInner;
    type Dst = SpecTxNonsegwit;
}
impl SpecIsoProof for TxNonsegwitMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxNonsegwitMapper {
    type Src = TxNonsegwitInner<'a>;
    type Dst = TxNonsegwit<'a>;
    type RefSrc = TxNonsegwitInnerRef<'a>;
}

pub struct SpecTxNonsegwitCombinator(pub SpecTxNonsegwitCombinatorAlias);

impl SpecCombinator for SpecTxNonsegwitCombinator {
    type Type = SpecTxNonsegwit;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxNonsegwitCombinatorAlias = Mapped<SpecPair<(RepeatN<SpecTxinCombinator>, BtcVarint), (RepeatN<SpecTxoutCombinator>, SpecLockTimeCombinator)>, TxNonsegwitMapper>;

pub struct TxNonsegwitCombinator(pub TxNonsegwitCombinatorAlias);

impl View for TxNonsegwitCombinator {
    type V = SpecTxNonsegwitCombinator;
    open spec fn view(&self) -> Self::V { SpecTxNonsegwitCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxNonsegwitCombinator {
    type Type = TxNonsegwit<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxNonsegwitCombinatorAlias = Mapped<Pair<(RepeatN<TxinCombinator>, BtcVarint), (RepeatN<TxoutCombinator>, LockTimeCombinator), TxNonsegwitCont0>, TxNonsegwitMapper>;


pub open spec fn spec_tx_nonsegwit(txin_count: VarInt) -> SpecTxNonsegwitCombinator {
    SpecTxNonsegwitCombinator(
    Mapped {
        inner: Pair::spec_new((RepeatN(spec_txin(), txin_count.spec_into()), BtcVarint), |deps| spec_tx_nonsegwit_cont0(deps)),
        mapper: TxNonsegwitMapper,
    })
}

pub open spec fn spec_tx_nonsegwit_cont0(deps: (Seq<SpecTxin>, VarInt)) -> (RepeatN<SpecTxoutCombinator>, SpecLockTimeCombinator) {
    let (_, txout_count) = deps;
    (RepeatN(spec_txout(), txout_count.spec_into()), spec_lock_time())
}

impl View for TxNonsegwitCont0 {
    type V = spec_fn((Seq<SpecTxin>, VarInt)) -> (RepeatN<SpecTxoutCombinator>, SpecLockTimeCombinator);

    open spec fn view(&self) -> Self::V {
        |deps: (Seq<SpecTxin>, VarInt)| {
            spec_tx_nonsegwit_cont0(deps)
        }
    }
}

pub fn tx_nonsegwit<'a>(txin_count: VarInt) -> (o: TxNonsegwitCombinator)
    ensures o@ == spec_tx_nonsegwit(txin_count@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxNonsegwitCombinator(
    Mapped {
        inner: Pair::new((RepeatN(txin(), txin_count.ex_into()), BtcVarint), TxNonsegwitCont0),
        mapper: TxNonsegwitMapper,
    });
    assert({
        &&& combinator@ == spec_tx_nonsegwit(txin_count@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_tx_nonsegwit<'a>(input: &'a [u8], txin_count: VarInt) -> (res: PResult<<TxNonsegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tx_nonsegwit(txin_count@).spec_parse(input@) == Some((n as int, v@)),
        spec_tx_nonsegwit(txin_count@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tx_nonsegwit(txin_count@).spec_parse(input@) is None,
        spec_tx_nonsegwit(txin_count@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = tx_nonsegwit( txin_count );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tx_nonsegwit<'a>(v: <TxNonsegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, txin_count: VarInt) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tx_nonsegwit(txin_count@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tx_nonsegwit(txin_count@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tx_nonsegwit(txin_count@).spec_serialize(v@))
        },
{
    let combinator = tx_nonsegwit( txin_count );
    combinator.serialize(v, data, pos)
}

pub fn tx_nonsegwit_len<'a>(v: <TxNonsegwitCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, txin_count: VarInt) -> (serialize_len: usize)
    requires
        spec_tx_nonsegwit(txin_count@).wf(v@),
        spec_tx_nonsegwit(txin_count@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tx_nonsegwit(txin_count@).spec_serialize(v@).len(),
{
    let combinator = tx_nonsegwit( txin_count );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TxNonsegwitCont0;
type TxNonsegwitCont0Type<'a, 'b> = &'b (RepeatResult<Txin<'a>>, VarInt);
type TxNonsegwitCont0SType<'a, 'x> = (&'x RepeatResult<Txin<'a>>, &'x VarInt);
type TxNonsegwitCont0Input<'a, 'b, 'x> = POrSType<TxNonsegwitCont0Type<'a, 'b>, TxNonsegwitCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TxNonsegwitCont0Input<'a, 'b, 'x>> for TxNonsegwitCont0 {
    type Output = (RepeatN<TxoutCombinator>, LockTimeCombinator);

    open spec fn requires(&self, deps: TxNonsegwitCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TxNonsegwitCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tx_nonsegwit_cont0(deps@)
    }

    fn apply(&self, deps: TxNonsegwitCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, txout_count) = *deps;
                (RepeatN(txout(), txout_count.ex_into()), lock_time())
            }
            POrSType::S(deps) => {
                let (_, txout_count) = deps;
                let txout_count = *txout_count;
                (RepeatN(txout(), txout_count.ex_into()), lock_time())
            }
        }
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

pub type TxRestInnerRef<'a> = Either<&'a TxSegwit<'a>, &'a TxNonsegwit<'a>>;


impl<'a> View for TxRest<'a> {
    type V = SpecTxRest;
    open spec fn view(&self) -> Self::V {
        match self {
            TxRest::Variant0(m) => SpecTxRest::Variant0(m@),
            TxRest::Variant1(m) => SpecTxRest::Variant1(m@),
        }
    }
}


impl<'a> From<&'a TxRest<'a>> for TxRestInnerRef<'a> {
    fn ex_from(m: &'a TxRest<'a>) -> TxRestInnerRef<'a> {
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


pub struct TxRestMapper;
impl View for TxRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxRestMapper {
    type Src = SpecTxRestInner;
    type Dst = SpecTxRest;
}
impl SpecIsoProof for TxRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxRestMapper {
    type Src = TxRestInner<'a>;
    type Dst = TxRest<'a>;
    type RefSrc = TxRestInnerRef<'a>;
}

type SpecTxRestCombinatorAlias1 = Choice<Cond<SpecTxSegwitCombinator>, Cond<SpecTxNonsegwitCombinator>>;
pub struct SpecTxRestCombinator(pub SpecTxRestCombinatorAlias);

impl SpecCombinator for SpecTxRestCombinator {
    type Type = SpecTxRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxRestCombinatorAlias = Mapped<SpecTxRestCombinatorAlias1, TxRestMapper>;
type TxRestCombinatorAlias1 = Choice<Cond<TxSegwitCombinator>, Cond<TxNonsegwitCombinator>>;
pub struct TxRestCombinator1(pub TxRestCombinatorAlias1);
impl View for TxRestCombinator1 {
    type V = SpecTxRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TxRestCombinator1, TxRestCombinatorAlias1);

pub struct TxRestCombinator(pub TxRestCombinatorAlias);

impl View for TxRestCombinator {
    type V = SpecTxRestCombinator;
    open spec fn view(&self) -> Self::V { SpecTxRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxRestCombinator {
    type Type = TxRest<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxRestCombinatorAlias = Mapped<TxRestCombinator1, TxRestMapper>;


pub open spec fn spec_tx_rest(txin_count: VarInt) -> SpecTxRestCombinator {
    SpecTxRestCombinator(Mapped { inner: Choice(Cond { cond: txin_count.spec_as_usize() == 0, inner: spec_tx_segwit() }, Cond { cond: !(txin_count.spec_as_usize() == 0), inner: spec_tx_nonsegwit(txin_count) }), mapper: TxRestMapper })
}

pub fn tx_rest<'a>(txin_count: VarInt) -> (o: TxRestCombinator)
    ensures o@ == spec_tx_rest(txin_count@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxRestCombinator(Mapped { inner: TxRestCombinator1(Choice::new(Cond { cond: txin_count.as_usize() == 0, inner: tx_segwit() }, Cond { cond: !(txin_count.as_usize() == 0), inner: tx_nonsegwit(txin_count) })), mapper: TxRestMapper });
    assert({
        &&& combinator@ == spec_tx_rest(txin_count@)
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_tx_rest<'a>(input: &'a [u8], txin_count: VarInt) -> (res: PResult<<TxRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tx_rest(txin_count@).spec_parse(input@) == Some((n as int, v@)),
        spec_tx_rest(txin_count@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tx_rest(txin_count@).spec_parse(input@) is None,
        spec_tx_rest(txin_count@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = tx_rest( txin_count );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tx_rest<'a>(v: <TxRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, txin_count: VarInt) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tx_rest(txin_count@).wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tx_rest(txin_count@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tx_rest(txin_count@).spec_serialize(v@))
        },
{
    let combinator = tx_rest( txin_count );
    combinator.serialize(v, data, pos)
}

pub fn tx_rest_len<'a>(v: <TxRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, txin_count: VarInt) -> (serialize_len: usize)
    requires
        spec_tx_rest(txin_count@).wf(v@),
        spec_tx_rest(txin_count@).spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tx_rest(txin_count@).spec_serialize(v@).len(),
{
    let combinator = tx_rest( txin_count );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
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

pub type TxInnerRef<'a> = ((&'a u32, &'a VarInt), &'a TxRest<'a>);
impl<'a> From<&'a Tx<'a>> for TxInnerRef<'a> {
    fn ex_from(m: &'a Tx) -> TxInnerRef<'a> {
        ((&m.version, &m.txin_count), &m.rest)
    }
}

impl<'a> From<TxInner<'a>> for Tx<'a> {
    fn ex_from(m: TxInner) -> Tx {
        let ((version, txin_count), rest) = m;
        Tx { version, txin_count, rest }
    }
}

pub struct TxMapper;
impl View for TxMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TxMapper {
    type Src = SpecTxInner;
    type Dst = SpecTx;
}
impl SpecIsoProof for TxMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TxMapper {
    type Src = TxInner<'a>;
    type Dst = Tx<'a>;
    type RefSrc = TxInnerRef<'a>;
}

pub struct SpecTxCombinator(pub SpecTxCombinatorAlias);

impl SpecCombinator for SpecTxCombinator {
    type Type = SpecTx;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecTxCombinatorAlias = Mapped<SpecPair<(U32Le, BtcVarint), SpecTxRestCombinator>, TxMapper>;

pub struct TxCombinator(pub TxCombinatorAlias);

impl View for TxCombinator {
    type V = SpecTxCombinator;
    open spec fn view(&self) -> Self::V { SpecTxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TxCombinator {
    type Type = Tx<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TxCombinatorAlias = Mapped<Pair<(U32Le, BtcVarint), TxRestCombinator, TxCont0>, TxMapper>;


pub open spec fn spec_tx() -> SpecTxCombinator {
    SpecTxCombinator(
    Mapped {
        inner: Pair::spec_new((U32Le, BtcVarint), |deps| spec_tx_cont0(deps)),
        mapper: TxMapper,
    })
}

pub open spec fn spec_tx_cont0(deps: (u32, VarInt)) -> SpecTxRestCombinator {
    let (_, txin_count) = deps;
    spec_tx_rest(txin_count)
}

impl View for TxCont0 {
    type V = spec_fn((u32, VarInt)) -> SpecTxRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (u32, VarInt)| {
            spec_tx_cont0(deps)
        }
    }
}

                
pub fn tx<'a>() -> (o: TxCombinator)
    ensures o@ == spec_tx(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TxCombinator(
    Mapped {
        inner: Pair::new((U32Le, BtcVarint), TxCont0),
        mapper: TxMapper,
    });
    assert({
        &&& combinator@ == spec_tx()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_tx<'a>(input: &'a [u8]) -> (res: PResult<<TxCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_tx().spec_parse(input@) == Some((n as int, v@)),
        spec_tx().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_tx().spec_parse(input@) is None,
        spec_tx().spec_parse(input@) is None ==> res is Err,
{
    let combinator = tx();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_tx<'a>(v: <TxCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_tx().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_tx().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_tx().spec_serialize(v@))
        },
{
    let combinator = tx();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn tx_len<'a>(v: <TxCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_tx().wf(v@),
        spec_tx().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_tx().spec_serialize(v@).len(),
{
    let combinator = tx();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TxCont0;
type TxCont0Type<'a, 'b> = &'b (u32, VarInt);
type TxCont0SType<'a, 'x> = (&'x u32, &'x VarInt);
type TxCont0Input<'a, 'b, 'x> = POrSType<TxCont0Type<'a, 'b>, TxCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TxCont0Input<'a, 'b, 'x>> for TxCont0 {
    type Output = TxRestCombinator;

    open spec fn requires(&self, deps: TxCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TxCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tx_cont0(deps@)
    }

    fn apply(&self, deps: TxCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, txin_count) = *deps;
                tx_rest(txin_count)
            }
            POrSType::S(deps) => {
                let (_, txin_count) = deps;
                let txin_count = *txin_count;
                tx_rest(txin_count)
            }
        }
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

pub type BlockInnerRef<'a> = ((&'a u32, (&'a &'a [u8], (&'a &'a [u8], (&'a u32, (&'a u32, (&'a u32, &'a VarInt)))))), &'a RepeatResult<Tx<'a>>);
impl<'a> From<&'a Block<'a>> for BlockInnerRef<'a> {
    fn ex_from(m: &'a Block) -> BlockInnerRef<'a> {
        ((&m.version, (&m.prev_block, (&m.merkle_root, (&m.timestamp, (&m.bits, (&m.nonce, &m.tx_count)))))), &m.txs)
    }
}

impl<'a> From<BlockInner<'a>> for Block<'a> {
    fn ex_from(m: BlockInner) -> Block {
        let ((version, (prev_block, (merkle_root, (timestamp, (bits, (nonce, tx_count)))))), txs) = m;
        Block { version, prev_block, merkle_root, timestamp, bits, nonce, tx_count, txs }
    }
}

pub struct BlockMapper;
impl View for BlockMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BlockMapper {
    type Src = SpecBlockInner;
    type Dst = SpecBlock;
}
impl SpecIsoProof for BlockMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for BlockMapper {
    type Src = BlockInner<'a>;
    type Dst = Block<'a>;
    type RefSrc = BlockInnerRef<'a>;
}

pub struct SpecBlockCombinator(pub SpecBlockCombinatorAlias);

impl SpecCombinator for SpecBlockCombinator {
    type Type = SpecBlock;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
    open spec fn is_productive(&self) -> bool 
    { self.0.is_productive() }
    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
    { self.0.lemma_parse_productive(s) }
}
pub type SpecBlockCombinatorAlias = Mapped<SpecPair<(U32Le, (bytes::Fixed<32>, (bytes::Fixed<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), RepeatN<SpecTxCombinator>>, BlockMapper>;

pub struct BlockCombinator(pub BlockCombinatorAlias);

impl View for BlockCombinator {
    type V = SpecBlockCombinator;
    open spec fn view(&self) -> Self::V { SpecBlockCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for BlockCombinator {
    type Type = Block<'a>;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type BlockCombinatorAlias = Mapped<Pair<(U32Le, (bytes::Fixed<32>, (bytes::Fixed<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), RepeatN<TxCombinator>, BlockCont0>, BlockMapper>;


pub open spec fn spec_block() -> SpecBlockCombinator {
    SpecBlockCombinator(
    Mapped {
        inner: Pair::spec_new((U32Le, (bytes::Fixed::<32>, (bytes::Fixed::<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), |deps| spec_block_cont0(deps)),
        mapper: BlockMapper,
    })
}

pub open spec fn spec_block_cont0(deps: (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, VarInt))))))) -> RepeatN<SpecTxCombinator> {
    let (_, (_, (_, (_, (_, (_, tx_count)))))) = deps;
    RepeatN(spec_tx(), tx_count.spec_into())
}

impl View for BlockCont0 {
    type V = spec_fn((u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, VarInt))))))) -> RepeatN<SpecTxCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: (u32, (Seq<u8>, (Seq<u8>, (u32, (u32, (u32, VarInt))))))| {
            spec_block_cont0(deps)
        }
    }
}

                
pub fn block<'a>() -> (o: BlockCombinator)
    ensures o@ == spec_block(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = BlockCombinator(
    Mapped {
        inner: Pair::new((U32Le, (bytes::Fixed::<32>, (bytes::Fixed::<32>, (U32Le, (U32Le, (U32Le, BtcVarint)))))), BlockCont0),
        mapper: BlockMapper,
    });
    assert({
        &&& combinator@ == spec_block()
        &&& combinator@.requires()
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    });
    combinator
}

pub fn parse_block<'a>(input: &'a [u8]) -> (res: PResult<<BlockCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_block().spec_parse(input@) == Some((n as int, v@)),
        spec_block().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_block().spec_parse(input@) is None,
        spec_block().spec_parse(input@) is None ==> res is Err,
{
    let combinator = block();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_block<'a>(v: <BlockCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_block().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_block().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_block().spec_serialize(v@))
        },
{
    let combinator = block();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn block_len<'a>(v: <BlockCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_block().wf(v@),
        spec_block().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_block().spec_serialize(v@).len(),
{
    let combinator = block();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct BlockCont0;
type BlockCont0Type<'a, 'b> = &'b (u32, (&'a [u8], (&'a [u8], (u32, (u32, (u32, VarInt))))));
type BlockCont0SType<'a, 'x> = (&'x u32, (&'x &'a [u8], (&'x &'a [u8], (&'x u32, (&'x u32, (&'x u32, &'x VarInt))))));
type BlockCont0Input<'a, 'b, 'x> = POrSType<BlockCont0Type<'a, 'b>, BlockCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<BlockCont0Input<'a, 'b, 'x>> for BlockCont0 {
    type Output = RepeatN<TxCombinator>;

    open spec fn requires(&self, deps: BlockCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: BlockCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_block_cont0(deps@)
    }

    fn apply(&self, deps: BlockCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, (_, (_, (_, (_, (_, tx_count)))))) = *deps;
                RepeatN(tx(), tx_count.ex_into())
            }
            POrSType::S(deps) => {
                let (_, (_, (_, (_, (_, (_, tx_count)))))) = deps;
                let tx_count = *tx_count;
                RepeatN(tx(), tx_count.ex_into())
            }
        }
    }
}
                

}
