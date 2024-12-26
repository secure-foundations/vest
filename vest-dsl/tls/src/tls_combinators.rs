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
verus!{
pub type SpecExtensionType = u16;
pub type ExtensionType = u16;


pub struct SpecExtensionTypeCombinator(SpecExtensionTypeCombinatorAlias);

impl SpecCombinator for SpecExtensionTypeCombinator {
    type SpecResult = SpecExtensionType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecExtensionTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecExtensionTypeCombinatorAlias = U16Be;

pub struct ExtensionTypeCombinator(ExtensionTypeCombinatorAlias);

impl View for ExtensionTypeCombinator {
    type V = SpecExtensionTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExtensionTypeCombinator {
    type Result = ExtensionType;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExtensionTypeCombinatorAlias = U16Be;


pub closed spec fn spec_extension_type() -> SpecExtensionTypeCombinator {
    SpecExtensionTypeCombinator(U16Be)
}

                
pub fn extension_type() -> (o: ExtensionTypeCombinator)
    ensures o@ == spec_extension_type(),
{
    ExtensionTypeCombinator(U16Be)
}

                

pub struct SpecPreSharedKeyServerExtension {
    pub selected_identity: u16,
}

pub type SpecPreSharedKeyServerExtensionInner = u16;
impl SpecFrom<SpecPreSharedKeyServerExtension> for SpecPreSharedKeyServerExtensionInner {
    open spec fn spec_from(m: SpecPreSharedKeyServerExtension) -> SpecPreSharedKeyServerExtensionInner {
        m.selected_identity
    }
}
impl SpecFrom<SpecPreSharedKeyServerExtensionInner> for SpecPreSharedKeyServerExtension {
    open spec fn spec_from(m: SpecPreSharedKeyServerExtensionInner) -> SpecPreSharedKeyServerExtension {
        let selected_identity = m;
        SpecPreSharedKeyServerExtension { selected_identity }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PreSharedKeyServerExtension {
    pub selected_identity: u16,
}

impl View for PreSharedKeyServerExtension {
    type V = SpecPreSharedKeyServerExtension;

    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyServerExtension {
            selected_identity: self.selected_identity@,
        }
    }
}
pub type PreSharedKeyServerExtensionInner = u16;
impl From<PreSharedKeyServerExtension> for PreSharedKeyServerExtensionInner {
    fn ex_from(m: PreSharedKeyServerExtension) -> PreSharedKeyServerExtensionInner {
        m.selected_identity
    }
}
impl From<PreSharedKeyServerExtensionInner> for PreSharedKeyServerExtension {
    fn ex_from(m: PreSharedKeyServerExtensionInner) -> PreSharedKeyServerExtension {
        let selected_identity = m;
        PreSharedKeyServerExtension { selected_identity }
    }
}

pub struct PreSharedKeyServerExtensionMapper;
impl PreSharedKeyServerExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        PreSharedKeyServerExtensionMapper
    }
    pub fn new() -> Self {
        PreSharedKeyServerExtensionMapper
    }
}
impl View for PreSharedKeyServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyServerExtensionMapper {
    type Src = SpecPreSharedKeyServerExtensionInner;
    type Dst = SpecPreSharedKeyServerExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for PreSharedKeyServerExtensionMapper {
    type Src = PreSharedKeyServerExtensionInner;
    type Dst = PreSharedKeyServerExtension;
}

pub struct SpecPreSharedKeyServerExtensionCombinator(SpecPreSharedKeyServerExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    type SpecResult = SpecPreSharedKeyServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;

pub struct PreSharedKeyServerExtensionCombinator(PreSharedKeyServerExtensionCombinatorAlias);

impl View for PreSharedKeyServerExtensionCombinator {
    type V = SpecPreSharedKeyServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PreSharedKeyServerExtensionCombinator {
    type Result = PreSharedKeyServerExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;


pub closed spec fn spec_pre_shared_key_server_extension() -> SpecPreSharedKeyServerExtensionCombinator {
    SpecPreSharedKeyServerExtensionCombinator(
    Mapped {
        inner: U16Be,
        mapper: PreSharedKeyServerExtensionMapper::spec_new(),
    })
}

                
pub fn pre_shared_key_server_extension() -> (o: PreSharedKeyServerExtensionCombinator)
    ensures o@ == spec_pre_shared_key_server_extension(),
{
    PreSharedKeyServerExtensionCombinator(
    Mapped {
        inner: U16Be,
        mapper: PreSharedKeyServerExtensionMapper::new(),
    })
}

                
pub type SpecProtocolVersion = u16;
pub type ProtocolVersion = u16;


pub struct SpecProtocolVersionCombinator(SpecProtocolVersionCombinatorAlias);

impl SpecCombinator for SpecProtocolVersionCombinator {
    type SpecResult = SpecProtocolVersion;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolVersionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolVersionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolVersionCombinatorAlias = U16Be;

pub struct ProtocolVersionCombinator(ProtocolVersionCombinatorAlias);

impl View for ProtocolVersionCombinator {
    type V = SpecProtocolVersionCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolVersionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ProtocolVersionCombinator {
    type Result = ProtocolVersion;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ProtocolVersionCombinatorAlias = U16Be;


pub closed spec fn spec_protocol_version() -> SpecProtocolVersionCombinator {
    SpecProtocolVersionCombinator(U16Be)
}

                
pub fn protocol_version() -> (o: ProtocolVersionCombinator)
    ensures o@ == spec_protocol_version(),
{
    ProtocolVersionCombinator(U16Be)
}

                
pub type SpecSupportedVersionsServer = SpecProtocolVersion;
pub type SupportedVersionsServer = ProtocolVersion;


pub struct SpecSupportedVersionsServerCombinator(SpecSupportedVersionsServerCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsServerCombinator {
    type SpecResult = SpecSupportedVersionsServer;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsServerCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsServerCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsServerCombinatorAlias = SpecProtocolVersionCombinator;

pub struct SupportedVersionsServerCombinator(SupportedVersionsServerCombinatorAlias);

impl View for SupportedVersionsServerCombinator {
    type V = SpecSupportedVersionsServerCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsServerCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SupportedVersionsServerCombinator {
    type Result = SupportedVersionsServer;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SupportedVersionsServerCombinatorAlias = ProtocolVersionCombinator;


pub closed spec fn spec_supported_versions_server() -> SpecSupportedVersionsServerCombinator {
    SpecSupportedVersionsServerCombinator(spec_protocol_version())
}

                
pub fn supported_versions_server() -> (o: SupportedVersionsServerCombinator)
    ensures o@ == spec_supported_versions_server(),
{
    SupportedVersionsServerCombinator(protocol_version())
}

                
pub type SpecNamedGroup = u16;
pub type NamedGroup = u16;


pub struct SpecNamedGroupCombinator(SpecNamedGroupCombinatorAlias);

impl SpecCombinator for SpecNamedGroupCombinator {
    type SpecResult = SpecNamedGroup;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupCombinatorAlias = U16Be;

pub struct NamedGroupCombinator(NamedGroupCombinatorAlias);

impl View for NamedGroupCombinator {
    type V = SpecNamedGroupCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NamedGroupCombinator {
    type Result = NamedGroup;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NamedGroupCombinatorAlias = U16Be;


pub closed spec fn spec_named_group() -> SpecNamedGroupCombinator {
    SpecNamedGroupCombinator(U16Be)
}

                
pub fn named_group() -> (o: NamedGroupCombinator)
    ensures o@ == spec_named_group(),
{
    NamedGroupCombinator(U16Be)
}

                
pub type SpecUint1Ffff = u16;
pub type Uint1Ffff = u16;


pub struct SpecUint1FfffCombinator(SpecUint1FfffCombinatorAlias);

impl SpecCombinator for SpecUint1FfffCombinator {
    type SpecResult = SpecUint1Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint1FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint1FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint1FfffCombinatorAlias = Refined<U16Be, Predicate17626095872143391426>;
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

pub struct Uint1FfffCombinator(Uint1FfffCombinatorAlias);

impl View for Uint1FfffCombinator {
    type V = SpecUint1FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint1FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint1FfffCombinator {
    type Result = Uint1Ffff;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint1FfffCombinatorAlias = Refined<U16Be, Predicate17626095872143391426>;


pub closed spec fn spec_uint_1_ffff() -> SpecUint1FfffCombinator {
    SpecUint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate17626095872143391426 })
}

                
pub fn uint_1_ffff() -> (o: Uint1FfffCombinator)
    ensures o@ == spec_uint_1_ffff(),
{
    Uint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate17626095872143391426 })
}

                

pub struct SpecKeyShareEntry {
    pub group: SpecNamedGroup,
    pub l: SpecUint1Ffff,
    pub key_exchange: Seq<u8>,
}

pub type SpecKeyShareEntryInner = ((SpecNamedGroup, SpecUint1Ffff), Seq<u8>);
impl SpecFrom<SpecKeyShareEntry> for SpecKeyShareEntryInner {
    open spec fn spec_from(m: SpecKeyShareEntry) -> SpecKeyShareEntryInner {
        ((m.group, m.l), m.key_exchange)
    }
}
impl SpecFrom<SpecKeyShareEntryInner> for SpecKeyShareEntry {
    open spec fn spec_from(m: SpecKeyShareEntryInner) -> SpecKeyShareEntry {
        let ((group, l), key_exchange) = m;
        SpecKeyShareEntry { group, l, key_exchange }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct KeyShareEntry<'a> {
    pub group: NamedGroup,
    pub l: Uint1Ffff,
    pub key_exchange: &'a [u8],
}

impl View for KeyShareEntry<'_> {
    type V = SpecKeyShareEntry;

    open spec fn view(&self) -> Self::V {
        SpecKeyShareEntry {
            group: self.group@,
            l: self.l@,
            key_exchange: self.key_exchange@,
        }
    }
}
pub type KeyShareEntryInner<'a> = ((NamedGroup, Uint1Ffff), &'a [u8]);
impl<'a> From<KeyShareEntry<'a>> for KeyShareEntryInner<'a> {
    fn ex_from(m: KeyShareEntry) -> KeyShareEntryInner {
        ((m.group, m.l), m.key_exchange)
    }
}
impl<'a> From<KeyShareEntryInner<'a>> for KeyShareEntry<'a> {
    fn ex_from(m: KeyShareEntryInner) -> KeyShareEntry {
        let ((group, l), key_exchange) = m;
        KeyShareEntry { group, l, key_exchange }
    }
}

pub struct KeyShareEntryMapper<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareEntryMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        KeyShareEntryMapper(PhantomData)
    }
    pub fn new() -> Self {
        KeyShareEntryMapper(PhantomData)
    }
}
impl View for KeyShareEntryMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareEntryMapper<'_> {
    type Src = SpecKeyShareEntryInner;
    type Dst = SpecKeyShareEntry;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for KeyShareEntryMapper<'a> {
    type Src = KeyShareEntryInner<'a>;
    type Dst = KeyShareEntry<'a>;
}

pub struct SpecKeyShareEntryCombinator(SpecKeyShareEntryCombinatorAlias);

impl SpecCombinator for SpecKeyShareEntryCombinator {
    type SpecResult = SpecKeyShareEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareEntryCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecNamedGroupCombinator, SpecUint1FfffCombinator>, Bytes>, KeyShareEntryMapper<'static>>;

pub struct KeyShareEntryCombinator<'a>(KeyShareEntryCombinatorAlias<'a>);

impl<'a> View for KeyShareEntryCombinator<'a> {
    type V = SpecKeyShareEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareEntryCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyShareEntryCombinator<'a> {
    type Result = KeyShareEntry<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyShareEntryCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, NamedGroupCombinator, Uint1FfffCombinator, KeyShareEntryCont1<'a>>, Bytes, KeyShareEntryCont0<'a>>, KeyShareEntryMapper<'a>>;


pub closed spec fn spec_key_share_entry() -> SpecKeyShareEntryCombinator {
    SpecKeyShareEntryCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_named_group(), snd: |deps| spec_key_share_entry_cont1(deps) }, snd: |deps| spec_key_share_entry_cont0(deps) },
        mapper: KeyShareEntryMapper::spec_new(),
    })
}

pub open spec fn spec_key_share_entry_cont1(deps: SpecNamedGroup) -> SpecUint1FfffCombinator {
    let group = deps;
    spec_uint_1_ffff()
}
pub open spec fn spec_key_share_entry_cont0(deps: (SpecNamedGroup, SpecUint1Ffff)) -> Bytes {
    let (group, l) = deps;
    Bytes(l.spec_into())
}
                
pub fn key_share_entry<'a>() -> (o: KeyShareEntryCombinator<'a>)
    ensures o@ == spec_key_share_entry(),
{
    KeyShareEntryCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: named_group(), snd: KeyShareEntryCont1::new(), spec_snd: Ghost(|deps| spec_key_share_entry_cont1(deps)) }, snd: KeyShareEntryCont0::new(), spec_snd: Ghost(|deps| spec_key_share_entry_cont0(deps)) },
        mapper: KeyShareEntryMapper::new(),
    })
}

pub struct KeyShareEntryCont1<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareEntryCont1<'a> {
    pub fn new() -> Self {
        KeyShareEntryCont1(PhantomData)
    }
}
impl<'a> Continuation<&NamedGroup> for KeyShareEntryCont1<'a> {
    type Output = Uint1FfffCombinator;

    open spec fn requires(&self, deps: &NamedGroup) -> bool { true }

    open spec fn ensures(&self, deps: &NamedGroup, o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont1(deps@)
    }

    fn apply(&self, deps: &NamedGroup) -> Self::Output {
        let group = *deps;
        uint_1_ffff()
    }
}
pub struct KeyShareEntryCont0<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareEntryCont0<'a> {
    pub fn new() -> Self {
        KeyShareEntryCont0(PhantomData)
    }
}
impl<'a> Continuation<&(NamedGroup, Uint1Ffff)> for KeyShareEntryCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &(NamedGroup, Uint1Ffff)) -> bool { true }

    open spec fn ensures(&self, deps: &(NamedGroup, Uint1Ffff), o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont0(deps@)
    }

    fn apply(&self, deps: &(NamedGroup, Uint1Ffff)) -> Self::Output {
        let (group, l) = *deps;
        Bytes(l.ex_into())
    }
}
                

pub enum SpecSeverHelloExtensionExtensionData {
    PreSharedKey(SpecPreSharedKeyServerExtension),
    SupportedVersions(SpecSupportedVersionsServer),
    KeyShare(SpecKeyShareEntry),
    Unrecognized(Seq<u8>),
}

pub type SpecSeverHelloExtensionExtensionDataInner = Either<SpecPreSharedKeyServerExtension, Either<SpecSupportedVersionsServer, Either<SpecKeyShareEntry, Seq<u8>>>>;



impl SpecFrom<SpecSeverHelloExtensionExtensionData> for SpecSeverHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionData) -> SpecSeverHelloExtensionExtensionDataInner {
        match m {
            SpecSeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Left(m),
            SpecSeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Left(m)),
            SpecSeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecSeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecSeverHelloExtensionExtensionDataInner> for SpecSeverHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionDataInner) -> SpecSeverHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Left(m)) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecSeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecSeverHelloExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeverHelloExtensionExtensionData<'a> {
    PreSharedKey(PreSharedKeyServerExtension),
    SupportedVersions(SupportedVersionsServer),
    KeyShare(KeyShareEntry<'a>),
    Unrecognized(&'a [u8]),
}

pub type SeverHelloExtensionExtensionDataInner<'a> = Either<PreSharedKeyServerExtension, Either<SupportedVersionsServer, Either<KeyShareEntry<'a>, &'a [u8]>>>;


impl<'a> View for SeverHelloExtensionExtensionData<'a> {
    type V = SpecSeverHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            SeverHelloExtensionExtensionData::PreSharedKey(m) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m@),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m@),
            SeverHelloExtensionExtensionData::KeyShare(m) => SpecSeverHelloExtensionExtensionData::KeyShare(m@),
            SeverHelloExtensionExtensionData::Unrecognized(m) => SpecSeverHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<SeverHelloExtensionExtensionData<'a>> for SeverHelloExtensionExtensionDataInner<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionData<'a>) -> SeverHelloExtensionExtensionDataInner<'a> {
        match m {
            SeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Left(m),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Left(m)),
            SeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Left(m))),
            SeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<SeverHelloExtensionExtensionDataInner<'a>> for SeverHelloExtensionExtensionData<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionDataInner<'a>) -> SeverHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => SeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Left(m)) => SeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Left(m))) => SeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(m))) => SeverHelloExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct SeverHelloExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> SeverHelloExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SeverHelloExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        SeverHelloExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for SeverHelloExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionExtensionDataMapper<'_> {
    type Src = SpecSeverHelloExtensionExtensionDataInner;
    type Dst = SpecSeverHelloExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SeverHelloExtensionExtensionDataMapper<'a> {
    type Src = SeverHelloExtensionExtensionDataInner<'a>;
    type Dst = SeverHelloExtensionExtensionData<'a>;
}


pub struct SpecSeverHelloExtensionExtensionDataCombinator(SpecSeverHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    type SpecResult = SpecSeverHelloExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecPreSharedKeyServerExtensionCombinator>, OrdChoice<Cond<SpecSupportedVersionsServerCombinator>, OrdChoice<Cond<SpecKeyShareEntryCombinator>, Cond<Bytes>>>>, SeverHelloExtensionExtensionDataMapper<'static>>>;

pub struct SeverHelloExtensionExtensionDataCombinator<'a>(SeverHelloExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for SeverHelloExtensionExtensionDataCombinator<'a> {
    type V = SpecSeverHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SeverHelloExtensionExtensionDataCombinator<'a> {
    type Result = SeverHelloExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SeverHelloExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<PreSharedKeyServerExtensionCombinator>, OrdChoice<Cond<SupportedVersionsServerCombinator>, OrdChoice<Cond<KeyShareEntryCombinator<'a>>, Cond<Bytes>>>>, SeverHelloExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_sever_hello_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecSeverHelloExtensionExtensionDataCombinator {
    SpecSeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_server_extension() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_server() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_entry() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) }))), mapper: SeverHelloExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn sever_hello_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: SeverHelloExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_sever_hello_extension_extension_data(extension_type@, ext_len@),
{
    SeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 41, inner: pre_shared_key_server_extension() }, OrdChoice::new(Cond { cond: extension_type == 43, inner: supported_versions_server() }, OrdChoice::new(Cond { cond: extension_type == 51, inner: key_share_entry() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) }))), mapper: SeverHelloExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecSeverHelloExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecSeverHelloExtensionExtensionData,
}

pub type SpecSeverHelloExtensionInner = ((SpecExtensionType, u16), SpecSeverHelloExtensionExtensionData);
impl SpecFrom<SpecSeverHelloExtension> for SpecSeverHelloExtensionInner {
    open spec fn spec_from(m: SpecSeverHelloExtension) -> SpecSeverHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecSeverHelloExtensionInner> for SpecSeverHelloExtension {
    open spec fn spec_from(m: SpecSeverHelloExtensionInner) -> SpecSeverHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecSeverHelloExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SeverHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: SeverHelloExtensionExtensionData<'a>,
}

impl View for SeverHelloExtension<'_> {
    type V = SpecSeverHelloExtension;

    open spec fn view(&self) -> Self::V {
        SpecSeverHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type SeverHelloExtensionInner<'a> = ((ExtensionType, u16), SeverHelloExtensionExtensionData<'a>);
impl<'a> From<SeverHelloExtension<'a>> for SeverHelloExtensionInner<'a> {
    fn ex_from(m: SeverHelloExtension) -> SeverHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<SeverHelloExtensionInner<'a>> for SeverHelloExtension<'a> {
    fn ex_from(m: SeverHelloExtensionInner) -> SeverHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SeverHelloExtension { extension_type, ext_len, extension_data }
    }
}

pub struct SeverHelloExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> SeverHelloExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SeverHelloExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        SeverHelloExtensionMapper(PhantomData)
    }
}
impl View for SeverHelloExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionMapper<'_> {
    type Src = SpecSeverHelloExtensionInner;
    type Dst = SpecSeverHelloExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SeverHelloExtensionMapper<'a> {
    type Src = SeverHelloExtensionInner<'a>;
    type Dst = SeverHelloExtension<'a>;
}

pub struct SpecSeverHelloExtensionCombinator(SpecSeverHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionCombinator {
    type SpecResult = SpecSeverHelloExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverHelloExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecSeverHelloExtensionExtensionDataCombinator>, SeverHelloExtensionMapper<'static>>;

pub struct SeverHelloExtensionCombinator<'a>(SeverHelloExtensionCombinatorAlias<'a>);

impl<'a> View for SeverHelloExtensionCombinator<'a> {
    type V = SpecSeverHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SeverHelloExtensionCombinator<'a> {
    type Result = SeverHelloExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SeverHelloExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, SeverHelloExtensionCont1<'a>>, SeverHelloExtensionExtensionDataCombinator<'a>, SeverHelloExtensionCont0<'a>>, SeverHelloExtensionMapper<'a>>;


pub closed spec fn spec_sever_hello_extension() -> SpecSeverHelloExtensionCombinator {
    SpecSeverHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_sever_hello_extension_cont1(deps) }, snd: |deps| spec_sever_hello_extension_cont0(deps) },
        mapper: SeverHelloExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_sever_hello_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_sever_hello_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecSeverHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_sever_hello_extension_extension_data(extension_type, ext_len)
}
                
pub fn sever_hello_extension<'a>() -> (o: SeverHelloExtensionCombinator<'a>)
    ensures o@ == spec_sever_hello_extension(),
{
    SeverHelloExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: SeverHelloExtensionCont1::new(), spec_snd: Ghost(|deps| spec_sever_hello_extension_cont1(deps)) }, snd: SeverHelloExtensionCont0::new(), spec_snd: Ghost(|deps| spec_sever_hello_extension_cont0(deps)) },
        mapper: SeverHelloExtensionMapper::new(),
    })
}

pub struct SeverHelloExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> SeverHelloExtensionCont1<'a> {
    pub fn new() -> Self {
        SeverHelloExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for SeverHelloExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct SeverHelloExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> SeverHelloExtensionCont0<'a> {
    pub fn new() -> Self {
        SeverHelloExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for SeverHelloExtensionCont0<'a> {
    type Output = SeverHelloExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        sever_hello_extension_extension_data(extension_type, ext_len)
    }
}
                

pub struct SpecOpaque1Ffff {
    pub l: SpecUint1Ffff,
    pub data: Seq<u8>,
}

pub type SpecOpaque1FfffInner = (SpecUint1Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque1Ffff> for SpecOpaque1FfffInner {
    open spec fn spec_from(m: SpecOpaque1Ffff) -> SpecOpaque1FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfffInner> for SpecOpaque1Ffff {
    open spec fn spec_from(m: SpecOpaque1FfffInner) -> SpecOpaque1Ffff {
        let (l, data) = m;
        SpecOpaque1Ffff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque1Ffff<'a> {
    pub l: Uint1Ffff,
    pub data: &'a [u8],
}

impl View for Opaque1Ffff<'_> {
    type V = SpecOpaque1Ffff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque1FfffInner<'a> = (Uint1Ffff, &'a [u8]);
impl<'a> From<Opaque1Ffff<'a>> for Opaque1FfffInner<'a> {
    fn ex_from(m: Opaque1Ffff) -> Opaque1FfffInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffInner<'a>> for Opaque1Ffff<'a> {
    fn ex_from(m: Opaque1FfffInner) -> Opaque1Ffff {
        let (l, data) = m;
        Opaque1Ffff { l, data }
    }
}

pub struct Opaque1FfffMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque1FfffMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque1FfffMapper(PhantomData)
    }
}
impl View for Opaque1FfffMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffMapper<'_> {
    type Src = SpecOpaque1FfffInner;
    type Dst = SpecOpaque1Ffff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque1FfffMapper<'a> {
    type Src = Opaque1FfffInner<'a>;
    type Dst = Opaque1Ffff<'a>;
}

pub struct SpecOpaque1FfffCombinator(SpecOpaque1FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffCombinator {
    type SpecResult = SpecOpaque1Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfffCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, Bytes>, Opaque1FfffMapper<'static>>;

pub struct Opaque1FfffCombinator<'a>(Opaque1FfffCombinatorAlias<'a>);

impl<'a> View for Opaque1FfffCombinator<'a> {
    type V = SpecOpaque1FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque1FfffCombinator<'a> {
    type Result = Opaque1Ffff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque1FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, Bytes, Opaque1FfffCont0<'a>>, Opaque1FfffMapper<'a>>;


pub closed spec fn spec_opaque_1_ffff() -> SpecOpaque1FfffCombinator {
    SpecOpaque1FfffCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ffff(), snd: |deps| spec_opaque1_ffff_cont0(deps) },
        mapper: Opaque1FfffMapper::spec_new(),
    })
}

pub open spec fn spec_opaque1_ffff_cont0(deps: SpecUint1Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_1_ffff<'a>() -> (o: Opaque1FfffCombinator<'a>)
    ensures o@ == spec_opaque_1_ffff(),
{
    Opaque1FfffCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ffff(), snd: Opaque1FfffCont0::new(), spec_snd: Ghost(|deps| spec_opaque1_ffff_cont0(deps)) },
        mapper: Opaque1FfffMapper::new(),
    })
}

pub struct Opaque1FfffCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffCont0<'a> {
    pub fn new() -> Self {
        Opaque1FfffCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ffff> for Opaque1FfffCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &Uint1Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffff_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ffff) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecPskIdentity {
    pub identity: SpecOpaque1Ffff,
    pub obfuscated_ticket_age: u32,
}

pub type SpecPskIdentityInner = (SpecOpaque1Ffff, u32);
impl SpecFrom<SpecPskIdentity> for SpecPskIdentityInner {
    open spec fn spec_from(m: SpecPskIdentity) -> SpecPskIdentityInner {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl SpecFrom<SpecPskIdentityInner> for SpecPskIdentity {
    open spec fn spec_from(m: SpecPskIdentityInner) -> SpecPskIdentity {
        let (identity, obfuscated_ticket_age) = m;
        SpecPskIdentity { identity, obfuscated_ticket_age }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskIdentity<'a> {
    pub identity: Opaque1Ffff<'a>,
    pub obfuscated_ticket_age: u32,
}

impl View for PskIdentity<'_> {
    type V = SpecPskIdentity;

    open spec fn view(&self) -> Self::V {
        SpecPskIdentity {
            identity: self.identity@,
            obfuscated_ticket_age: self.obfuscated_ticket_age@,
        }
    }
}
pub type PskIdentityInner<'a> = (Opaque1Ffff<'a>, u32);
impl<'a> From<PskIdentity<'a>> for PskIdentityInner<'a> {
    fn ex_from(m: PskIdentity) -> PskIdentityInner {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl<'a> From<PskIdentityInner<'a>> for PskIdentity<'a> {
    fn ex_from(m: PskIdentityInner) -> PskIdentity {
        let (identity, obfuscated_ticket_age) = m;
        PskIdentity { identity, obfuscated_ticket_age }
    }
}

pub struct PskIdentityMapper<'a>(PhantomData<&'a ()>);
impl<'a> PskIdentityMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        PskIdentityMapper(PhantomData)
    }
    pub fn new() -> Self {
        PskIdentityMapper(PhantomData)
    }
}
impl View for PskIdentityMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentityMapper<'_> {
    type Src = SpecPskIdentityInner;
    type Dst = SpecPskIdentity;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for PskIdentityMapper<'a> {
    type Src = PskIdentityInner<'a>;
    type Dst = PskIdentity<'a>;
}

pub struct SpecPskIdentityCombinator(SpecPskIdentityCombinatorAlias);

impl SpecCombinator for SpecPskIdentityCombinator {
    type SpecResult = SpecPskIdentity;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentityCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentityCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentityCombinatorAlias = Mapped<(SpecOpaque1FfffCombinator, U32Be), PskIdentityMapper<'static>>;

pub struct PskIdentityCombinator<'a>(PskIdentityCombinatorAlias<'a>);

impl<'a> View for PskIdentityCombinator<'a> {
    type V = SpecPskIdentityCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentityCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskIdentityCombinator<'a> {
    type Result = PskIdentity<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskIdentityCombinatorAlias<'a> = Mapped<(Opaque1FfffCombinator<'a>, U32Be), PskIdentityMapper<'a>>;


pub closed spec fn spec_psk_identity() -> SpecPskIdentityCombinator {
    SpecPskIdentityCombinator(
    Mapped {
        inner: (spec_opaque_1_ffff(), U32Be),
        mapper: PskIdentityMapper::spec_new(),
    })
}

                
pub fn psk_identity<'a>() -> (o: PskIdentityCombinator<'a>)
    ensures o@ == spec_psk_identity(),
{
    PskIdentityCombinator(
    Mapped {
        inner: (opaque_1_ffff(), U32Be),
        mapper: PskIdentityMapper::new(),
    })
}

                
pub type SpecPskIdentitiesIdentities = Seq<SpecPskIdentity>;
pub type PskIdentitiesIdentities<'a> = RepeatResult<PskIdentity<'a>>;


pub struct SpecPskIdentitiesIdentitiesCombinator(SpecPskIdentitiesIdentitiesCombinatorAlias);

impl SpecCombinator for SpecPskIdentitiesIdentitiesCombinator {
    type SpecResult = SpecPskIdentitiesIdentities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentitiesIdentitiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentitiesIdentitiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentitiesIdentitiesCombinatorAlias = AndThen<Bytes, Repeat<SpecPskIdentityCombinator>>;

pub struct PskIdentitiesIdentitiesCombinator<'a>(PskIdentitiesIdentitiesCombinatorAlias<'a>);

impl<'a> View for PskIdentitiesIdentitiesCombinator<'a> {
    type V = SpecPskIdentitiesIdentitiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentitiesIdentitiesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskIdentitiesIdentitiesCombinator<'a> {
    type Result = PskIdentitiesIdentities<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskIdentitiesIdentitiesCombinatorAlias<'a> = AndThen<Bytes, Repeat<PskIdentityCombinator<'a>>>;


pub closed spec fn spec_psk_identities_identities(l: u16) -> SpecPskIdentitiesIdentitiesCombinator {
    SpecPskIdentitiesIdentitiesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_identity())))
}

                
pub fn psk_identities_identities<'a>(l: u16) -> (o: PskIdentitiesIdentitiesCombinator<'a>)
    ensures o@ == spec_psk_identities_identities(l@),
{
    PskIdentitiesIdentitiesCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_identity())))
}

                

pub struct SpecPskIdentities {
    pub l: u16,
    pub identities: SpecPskIdentitiesIdentities,
}

pub type SpecPskIdentitiesInner = (u16, SpecPskIdentitiesIdentities);
impl SpecFrom<SpecPskIdentities> for SpecPskIdentitiesInner {
    open spec fn spec_from(m: SpecPskIdentities) -> SpecPskIdentitiesInner {
        (m.l, m.identities)
    }
}
impl SpecFrom<SpecPskIdentitiesInner> for SpecPskIdentities {
    open spec fn spec_from(m: SpecPskIdentitiesInner) -> SpecPskIdentities {
        let (l, identities) = m;
        SpecPskIdentities { l, identities }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskIdentities<'a> {
    pub l: u16,
    pub identities: PskIdentitiesIdentities<'a>,
}

impl View for PskIdentities<'_> {
    type V = SpecPskIdentities;

    open spec fn view(&self) -> Self::V {
        SpecPskIdentities {
            l: self.l@,
            identities: self.identities@,
        }
    }
}
pub type PskIdentitiesInner<'a> = (u16, PskIdentitiesIdentities<'a>);
impl<'a> From<PskIdentities<'a>> for PskIdentitiesInner<'a> {
    fn ex_from(m: PskIdentities) -> PskIdentitiesInner {
        (m.l, m.identities)
    }
}
impl<'a> From<PskIdentitiesInner<'a>> for PskIdentities<'a> {
    fn ex_from(m: PskIdentitiesInner) -> PskIdentities {
        let (l, identities) = m;
        PskIdentities { l, identities }
    }
}

pub struct PskIdentitiesMapper<'a>(PhantomData<&'a ()>);
impl<'a> PskIdentitiesMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        PskIdentitiesMapper(PhantomData)
    }
    pub fn new() -> Self {
        PskIdentitiesMapper(PhantomData)
    }
}
impl View for PskIdentitiesMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentitiesMapper<'_> {
    type Src = SpecPskIdentitiesInner;
    type Dst = SpecPskIdentities;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for PskIdentitiesMapper<'a> {
    type Src = PskIdentitiesInner<'a>;
    type Dst = PskIdentities<'a>;
}

pub struct SpecPskIdentitiesCombinator(SpecPskIdentitiesCombinatorAlias);

impl SpecCombinator for SpecPskIdentitiesCombinator {
    type SpecResult = SpecPskIdentities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentitiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentitiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentitiesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate2530354110630676415>, SpecPskIdentitiesIdentitiesCombinator>, PskIdentitiesMapper<'static>>;
pub struct Predicate2530354110630676415;
impl View for Predicate2530354110630676415 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate2530354110630676415 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 7 && i <= 65535)
    }
}
impl SpecPred for Predicate2530354110630676415 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 7 && i <= 65535)
    }
}

pub struct PskIdentitiesCombinator<'a>(PskIdentitiesCombinatorAlias<'a>);

impl<'a> View for PskIdentitiesCombinator<'a> {
    type V = SpecPskIdentitiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentitiesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskIdentitiesCombinator<'a> {
    type Result = PskIdentities<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskIdentitiesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate2530354110630676415>, PskIdentitiesIdentitiesCombinator<'a>, PskIdentitiesCont0<'a>>, PskIdentitiesMapper<'a>>;


pub closed spec fn spec_psk_identities() -> SpecPskIdentitiesCombinator {
    SpecPskIdentitiesCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate2530354110630676415 }, snd: |deps| spec_psk_identities_cont0(deps) },
        mapper: PskIdentitiesMapper::spec_new(),
    })
}

pub open spec fn spec_psk_identities_cont0(deps: u16) -> SpecPskIdentitiesIdentitiesCombinator {
    let l = deps;
    spec_psk_identities_identities(l)
}
                
pub fn psk_identities<'a>() -> (o: PskIdentitiesCombinator<'a>)
    ensures o@ == spec_psk_identities(),
{
    PskIdentitiesCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate2530354110630676415 }, snd: PskIdentitiesCont0::new(), spec_snd: Ghost(|deps| spec_psk_identities_cont0(deps)) },
        mapper: PskIdentitiesMapper::new(),
    })
}

pub struct PskIdentitiesCont0<'a>(PhantomData<&'a ()>);
impl<'a> PskIdentitiesCont0<'a> {
    pub fn new() -> Self {
        PskIdentitiesCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for PskIdentitiesCont0<'a> {
    type Output = PskIdentitiesIdentitiesCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_psk_identities_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        psk_identities_identities(l)
    }
}
                
pub type SpecUint0Fffe = u16;
pub type Uint0Fffe = u16;


pub struct SpecUint0FffeCombinator(SpecUint0FffeCombinatorAlias);

impl SpecCombinator for SpecUint0FffeCombinator {
    type SpecResult = SpecUint0Fffe;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FffeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FffeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FffeCombinatorAlias = Refined<U16Be, Predicate8699513167145984875>;
pub struct Predicate8699513167145984875;
impl View for Predicate8699513167145984875 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate8699513167145984875 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65534)
    }
}
impl SpecPred for Predicate8699513167145984875 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65534)
    }
}

pub struct Uint0FffeCombinator(Uint0FffeCombinatorAlias);

impl View for Uint0FffeCombinator {
    type V = SpecUint0FffeCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FffeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint0FffeCombinator {
    type Result = Uint0Fffe;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint0FffeCombinatorAlias = Refined<U16Be, Predicate8699513167145984875>;


pub closed spec fn spec_uint_0_fffe() -> SpecUint0FffeCombinator {
    SpecUint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate8699513167145984875 })
}

                
pub fn uint_0_fffe() -> (o: Uint0FffeCombinator)
    ensures o@ == spec_uint_0_fffe(),
{
    Uint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate8699513167145984875 })
}

                
pub type SpecUint0Ffff = u16;
pub type Uint0Ffff = u16;


pub struct SpecUint0FfffCombinator(SpecUint0FfffCombinatorAlias);

impl SpecCombinator for SpecUint0FfffCombinator {
    type SpecResult = SpecUint0Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FfffCombinatorAlias = U16Be;

pub struct Uint0FfffCombinator(Uint0FfffCombinatorAlias);

impl View for Uint0FfffCombinator {
    type V = SpecUint0FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint0FfffCombinator {
    type Result = Uint0Ffff;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint0FfffCombinatorAlias = U16Be;


pub closed spec fn spec_uint_0_ffff() -> SpecUint0FfffCombinator {
    SpecUint0FfffCombinator(U16Be)
}

                
pub fn uint_0_ffff() -> (o: Uint0FfffCombinator)
    ensures o@ == spec_uint_0_ffff(),
{
    Uint0FfffCombinator(U16Be)
}

                
pub type SpecUint1Ff = u8;
pub type Uint1Ff = u8;


pub struct SpecUint1FfCombinator(SpecUint1FfCombinatorAlias);

impl SpecCombinator for SpecUint1FfCombinator {
    type SpecResult = SpecUint1Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint1FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint1FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint1FfCombinatorAlias = Refined<U8, Predicate3651688686135228051>;
pub struct Predicate3651688686135228051;
impl View for Predicate3651688686135228051 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate3651688686135228051 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}
impl SpecPred for Predicate3651688686135228051 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}

pub struct Uint1FfCombinator(Uint1FfCombinatorAlias);

impl View for Uint1FfCombinator {
    type V = SpecUint1FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint1FfCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint1FfCombinator {
    type Result = Uint1Ff;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint1FfCombinatorAlias = Refined<U8, Predicate3651688686135228051>;


pub closed spec fn spec_uint_1_ff() -> SpecUint1FfCombinator {
    SpecUint1FfCombinator(Refined { inner: U8, predicate: Predicate3651688686135228051 })
}

                
pub fn uint_1_ff() -> (o: Uint1FfCombinator)
    ensures o@ == spec_uint_1_ff(),
{
    Uint1FfCombinator(Refined { inner: U8, predicate: Predicate3651688686135228051 })
}

                

pub struct SpecOpaque1Ff {
    pub l: SpecUint1Ff,
    pub data: Seq<u8>,
}

pub type SpecOpaque1FfInner = (SpecUint1Ff, Seq<u8>);
impl SpecFrom<SpecOpaque1Ff> for SpecOpaque1FfInner {
    open spec fn spec_from(m: SpecOpaque1Ff) -> SpecOpaque1FfInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfInner> for SpecOpaque1Ff {
    open spec fn spec_from(m: SpecOpaque1FfInner) -> SpecOpaque1Ff {
        let (l, data) = m;
        SpecOpaque1Ff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque1Ff<'a> {
    pub l: Uint1Ff,
    pub data: &'a [u8],
}

impl View for Opaque1Ff<'_> {
    type V = SpecOpaque1Ff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque1FfInner<'a> = (Uint1Ff, &'a [u8]);
impl<'a> From<Opaque1Ff<'a>> for Opaque1FfInner<'a> {
    fn ex_from(m: Opaque1Ff) -> Opaque1FfInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfInner<'a>> for Opaque1Ff<'a> {
    fn ex_from(m: Opaque1FfInner) -> Opaque1Ff {
        let (l, data) = m;
        Opaque1Ff { l, data }
    }
}

pub struct Opaque1FfMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque1FfMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque1FfMapper(PhantomData)
    }
}
impl View for Opaque1FfMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfMapper<'_> {
    type Src = SpecOpaque1FfInner;
    type Dst = SpecOpaque1Ff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque1FfMapper<'a> {
    type Src = Opaque1FfInner<'a>;
    type Dst = Opaque1Ff<'a>;
}

pub struct SpecOpaque1FfCombinator(SpecOpaque1FfCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfCombinator {
    type SpecResult = SpecOpaque1Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, Bytes>, Opaque1FfMapper<'static>>;

pub struct Opaque1FfCombinator<'a>(Opaque1FfCombinatorAlias<'a>);

impl<'a> View for Opaque1FfCombinator<'a> {
    type V = SpecOpaque1FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque1FfCombinator<'a> {
    type Result = Opaque1Ff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque1FfCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, Bytes, Opaque1FfCont0<'a>>, Opaque1FfMapper<'a>>;


pub closed spec fn spec_opaque_1_ff() -> SpecOpaque1FfCombinator {
    SpecOpaque1FfCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ff(), snd: |deps| spec_opaque1_ff_cont0(deps) },
        mapper: Opaque1FfMapper::spec_new(),
    })
}

pub open spec fn spec_opaque1_ff_cont0(deps: SpecUint1Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_1_ff<'a>() -> (o: Opaque1FfCombinator<'a>)
    ensures o@ == spec_opaque_1_ff(),
{
    Opaque1FfCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ff(), snd: Opaque1FfCont0::new(), spec_snd: Ghost(|deps| spec_opaque1_ff_cont0(deps)) },
        mapper: Opaque1FfMapper::new(),
    })
}

pub struct Opaque1FfCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfCont0<'a> {
    pub fn new() -> Self {
        Opaque1FfCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ff> for Opaque1FfCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &Uint1Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ff_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ff) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecOpaque0Ffff {
    pub l: SpecUint0Ffff,
    pub data: Seq<u8>,
}

pub type SpecOpaque0FfffInner = (SpecUint0Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque0Ffff> for SpecOpaque0FfffInner {
    open spec fn spec_from(m: SpecOpaque0Ffff) -> SpecOpaque0FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfffInner> for SpecOpaque0Ffff {
    open spec fn spec_from(m: SpecOpaque0FfffInner) -> SpecOpaque0Ffff {
        let (l, data) = m;
        SpecOpaque0Ffff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque0Ffff<'a> {
    pub l: Uint0Ffff,
    pub data: &'a [u8],
}

impl View for Opaque0Ffff<'_> {
    type V = SpecOpaque0Ffff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque0FfffInner<'a> = (Uint0Ffff, &'a [u8]);
impl<'a> From<Opaque0Ffff<'a>> for Opaque0FfffInner<'a> {
    fn ex_from(m: Opaque0Ffff) -> Opaque0FfffInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffInner<'a>> for Opaque0Ffff<'a> {
    fn ex_from(m: Opaque0FfffInner) -> Opaque0Ffff {
        let (l, data) = m;
        Opaque0Ffff { l, data }
    }
}

pub struct Opaque0FfffMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque0FfffMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque0FfffMapper(PhantomData)
    }
}
impl View for Opaque0FfffMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffMapper<'_> {
    type Src = SpecOpaque0FfffInner;
    type Dst = SpecOpaque0Ffff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque0FfffMapper<'a> {
    type Src = Opaque0FfffInner<'a>;
    type Dst = Opaque0Ffff<'a>;
}

pub struct SpecOpaque0FfffCombinator(SpecOpaque0FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffCombinator {
    type SpecResult = SpecOpaque0Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfffCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, Bytes>, Opaque0FfffMapper<'static>>;

pub struct Opaque0FfffCombinator<'a>(Opaque0FfffCombinatorAlias<'a>);

impl<'a> View for Opaque0FfffCombinator<'a> {
    type V = SpecOpaque0FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque0FfffCombinator<'a> {
    type Result = Opaque0Ffff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque0FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, Bytes, Opaque0FfffCont0<'a>>, Opaque0FfffMapper<'a>>;


pub closed spec fn spec_opaque_0_ffff() -> SpecOpaque0FfffCombinator {
    SpecOpaque0FfffCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_opaque0_ffff_cont0(deps) },
        mapper: Opaque0FfffMapper::spec_new(),
    })
}

pub open spec fn spec_opaque0_ffff_cont0(deps: SpecUint0Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_0_ffff<'a>() -> (o: Opaque0FfffCombinator<'a>)
    ensures o@ == spec_opaque_0_ffff(),
{
    Opaque0FfffCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: Opaque0FfffCont0::new(), spec_snd: Ghost(|deps| spec_opaque0_ffff_cont0(deps)) },
        mapper: Opaque0FfffMapper::new(),
    })
}

pub struct Opaque0FfffCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffCont0<'a> {
    pub fn new() -> Self {
        Opaque0FfffCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for Opaque0FfffCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffff_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecOidFilter {
    pub certificate_extension_oid: SpecOpaque1Ff,
    pub certificate_extension_values: SpecOpaque0Ffff,
}

pub type SpecOidFilterInner = (SpecOpaque1Ff, SpecOpaque0Ffff);
impl SpecFrom<SpecOidFilter> for SpecOidFilterInner {
    open spec fn spec_from(m: SpecOidFilter) -> SpecOidFilterInner {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl SpecFrom<SpecOidFilterInner> for SpecOidFilter {
    open spec fn spec_from(m: SpecOidFilterInner) -> SpecOidFilter {
        let (certificate_extension_oid, certificate_extension_values) = m;
        SpecOidFilter { certificate_extension_oid, certificate_extension_values }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OidFilter<'a> {
    pub certificate_extension_oid: Opaque1Ff<'a>,
    pub certificate_extension_values: Opaque0Ffff<'a>,
}

impl View for OidFilter<'_> {
    type V = SpecOidFilter;

    open spec fn view(&self) -> Self::V {
        SpecOidFilter {
            certificate_extension_oid: self.certificate_extension_oid@,
            certificate_extension_values: self.certificate_extension_values@,
        }
    }
}
pub type OidFilterInner<'a> = (Opaque1Ff<'a>, Opaque0Ffff<'a>);
impl<'a> From<OidFilter<'a>> for OidFilterInner<'a> {
    fn ex_from(m: OidFilter) -> OidFilterInner {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl<'a> From<OidFilterInner<'a>> for OidFilter<'a> {
    fn ex_from(m: OidFilterInner) -> OidFilter {
        let (certificate_extension_oid, certificate_extension_values) = m;
        OidFilter { certificate_extension_oid, certificate_extension_values }
    }
}

pub struct OidFilterMapper<'a>(PhantomData<&'a ()>);
impl<'a> OidFilterMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OidFilterMapper(PhantomData)
    }
    pub fn new() -> Self {
        OidFilterMapper(PhantomData)
    }
}
impl View for OidFilterMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterMapper<'_> {
    type Src = SpecOidFilterInner;
    type Dst = SpecOidFilter;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OidFilterMapper<'a> {
    type Src = OidFilterInner<'a>;
    type Dst = OidFilter<'a>;
}

pub struct SpecOidFilterCombinator(SpecOidFilterCombinatorAlias);

impl SpecCombinator for SpecOidFilterCombinator {
    type SpecResult = SpecOidFilter;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterCombinatorAlias = Mapped<(SpecOpaque1FfCombinator, SpecOpaque0FfffCombinator), OidFilterMapper<'static>>;

pub struct OidFilterCombinator<'a>(OidFilterCombinatorAlias<'a>);

impl<'a> View for OidFilterCombinator<'a> {
    type V = SpecOidFilterCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OidFilterCombinator<'a> {
    type Result = OidFilter<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OidFilterCombinatorAlias<'a> = Mapped<(Opaque1FfCombinator<'a>, Opaque0FfffCombinator<'a>), OidFilterMapper<'a>>;


pub closed spec fn spec_oid_filter() -> SpecOidFilterCombinator {
    SpecOidFilterCombinator(
    Mapped {
        inner: (spec_opaque_1_ff(), spec_opaque_0_ffff()),
        mapper: OidFilterMapper::spec_new(),
    })
}

                
pub fn oid_filter<'a>() -> (o: OidFilterCombinator<'a>)
    ensures o@ == spec_oid_filter(),
{
    OidFilterCombinator(
    Mapped {
        inner: (opaque_1_ff(), opaque_0_ffff()),
        mapper: OidFilterMapper::new(),
    })
}

                
pub type SpecOidFilterExtensionFilters = Seq<SpecOidFilter>;
pub type OidFilterExtensionFilters<'a> = RepeatResult<OidFilter<'a>>;


pub struct SpecOidFilterExtensionFiltersCombinator(SpecOidFilterExtensionFiltersCombinatorAlias);

impl SpecCombinator for SpecOidFilterExtensionFiltersCombinator {
    type SpecResult = SpecOidFilterExtensionFilters;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterExtensionFiltersCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterExtensionFiltersCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterExtensionFiltersCombinatorAlias = AndThen<Bytes, Repeat<SpecOidFilterCombinator>>;

pub struct OidFilterExtensionFiltersCombinator<'a>(OidFilterExtensionFiltersCombinatorAlias<'a>);

impl<'a> View for OidFilterExtensionFiltersCombinator<'a> {
    type V = SpecOidFilterExtensionFiltersCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterExtensionFiltersCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OidFilterExtensionFiltersCombinator<'a> {
    type Result = OidFilterExtensionFilters<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OidFilterExtensionFiltersCombinatorAlias<'a> = AndThen<Bytes, Repeat<OidFilterCombinator<'a>>>;


pub closed spec fn spec_oid_filter_extension_filters(l: SpecUint0Ffff) -> SpecOidFilterExtensionFiltersCombinator {
    SpecOidFilterExtensionFiltersCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_oid_filter())))
}

                
pub fn oid_filter_extension_filters<'a>(l: Uint0Ffff) -> (o: OidFilterExtensionFiltersCombinator<'a>)
    ensures o@ == spec_oid_filter_extension_filters(l@),
{
    OidFilterExtensionFiltersCombinator(AndThen(Bytes(l.ex_into()), Repeat(oid_filter())))
}

                

pub struct SpecOidFilterExtension {
    pub l: SpecUint0Ffff,
    pub filters: SpecOidFilterExtensionFilters,
}

pub type SpecOidFilterExtensionInner = (SpecUint0Ffff, SpecOidFilterExtensionFilters);
impl SpecFrom<SpecOidFilterExtension> for SpecOidFilterExtensionInner {
    open spec fn spec_from(m: SpecOidFilterExtension) -> SpecOidFilterExtensionInner {
        (m.l, m.filters)
    }
}
impl SpecFrom<SpecOidFilterExtensionInner> for SpecOidFilterExtension {
    open spec fn spec_from(m: SpecOidFilterExtensionInner) -> SpecOidFilterExtension {
        let (l, filters) = m;
        SpecOidFilterExtension { l, filters }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OidFilterExtension<'a> {
    pub l: Uint0Ffff,
    pub filters: OidFilterExtensionFilters<'a>,
}

impl View for OidFilterExtension<'_> {
    type V = SpecOidFilterExtension;

    open spec fn view(&self) -> Self::V {
        SpecOidFilterExtension {
            l: self.l@,
            filters: self.filters@,
        }
    }
}
pub type OidFilterExtensionInner<'a> = (Uint0Ffff, OidFilterExtensionFilters<'a>);
impl<'a> From<OidFilterExtension<'a>> for OidFilterExtensionInner<'a> {
    fn ex_from(m: OidFilterExtension) -> OidFilterExtensionInner {
        (m.l, m.filters)
    }
}
impl<'a> From<OidFilterExtensionInner<'a>> for OidFilterExtension<'a> {
    fn ex_from(m: OidFilterExtensionInner) -> OidFilterExtension {
        let (l, filters) = m;
        OidFilterExtension { l, filters }
    }
}

pub struct OidFilterExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> OidFilterExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OidFilterExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        OidFilterExtensionMapper(PhantomData)
    }
}
impl View for OidFilterExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterExtensionMapper<'_> {
    type Src = SpecOidFilterExtensionInner;
    type Dst = SpecOidFilterExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OidFilterExtensionMapper<'a> {
    type Src = OidFilterExtensionInner<'a>;
    type Dst = OidFilterExtension<'a>;
}

pub struct SpecOidFilterExtensionCombinator(SpecOidFilterExtensionCombinatorAlias);

impl SpecCombinator for SpecOidFilterExtensionCombinator {
    type SpecResult = SpecOidFilterExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecOidFilterExtensionFiltersCombinator>, OidFilterExtensionMapper<'static>>;

pub struct OidFilterExtensionCombinator<'a>(OidFilterExtensionCombinatorAlias<'a>);

impl<'a> View for OidFilterExtensionCombinator<'a> {
    type V = SpecOidFilterExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OidFilterExtensionCombinator<'a> {
    type Result = OidFilterExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OidFilterExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, OidFilterExtensionFiltersCombinator<'a>, OidFilterExtensionCont0<'a>>, OidFilterExtensionMapper<'a>>;


pub closed spec fn spec_oid_filter_extension() -> SpecOidFilterExtensionCombinator {
    SpecOidFilterExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_oid_filter_extension_cont0(deps) },
        mapper: OidFilterExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_oid_filter_extension_cont0(deps: SpecUint0Ffff) -> SpecOidFilterExtensionFiltersCombinator {
    let l = deps;
    spec_oid_filter_extension_filters(l)
}
                
pub fn oid_filter_extension<'a>() -> (o: OidFilterExtensionCombinator<'a>)
    ensures o@ == spec_oid_filter_extension(),
{
    OidFilterExtensionCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: OidFilterExtensionCont0::new(), spec_snd: Ghost(|deps| spec_oid_filter_extension_cont0(deps)) },
        mapper: OidFilterExtensionMapper::new(),
    })
}

pub struct OidFilterExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> OidFilterExtensionCont0<'a> {
    pub fn new() -> Self {
        OidFilterExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for OidFilterExtensionCont0<'a> {
    type Output = OidFilterExtensionFiltersCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_oid_filter_extension_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        oid_filter_extension_filters(l)
    }
}
                
pub type SpecCipherSuite = u16;
pub type CipherSuite = u16;


pub struct SpecCipherSuiteCombinator(SpecCipherSuiteCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteCombinator {
    type SpecResult = SpecCipherSuite;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteCombinatorAlias = U16Be;

pub struct CipherSuiteCombinator(CipherSuiteCombinatorAlias);

impl View for CipherSuiteCombinator {
    type V = SpecCipherSuiteCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CipherSuiteCombinator {
    type Result = CipherSuite;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CipherSuiteCombinatorAlias = U16Be;


pub closed spec fn spec_cipher_suite() -> SpecCipherSuiteCombinator {
    SpecCipherSuiteCombinator(U16Be)
}

                
pub fn cipher_suite() -> (o: CipherSuiteCombinator)
    ensures o@ == spec_cipher_suite(),
{
    CipherSuiteCombinator(U16Be)
}

                
pub type SpecCookie = SpecOpaque1Ffff;
pub type Cookie<'a> = Opaque1Ffff<'a>;


pub struct SpecCookieCombinator(SpecCookieCombinatorAlias);

impl SpecCombinator for SpecCookieCombinator {
    type SpecResult = SpecCookie;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCookieCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCookieCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCookieCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct CookieCombinator<'a>(CookieCombinatorAlias<'a>);

impl<'a> View for CookieCombinator<'a> {
    type V = SpecCookieCombinator;
    closed spec fn view(&self) -> Self::V { SpecCookieCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CookieCombinator<'a> {
    type Result = Cookie<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CookieCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_cookie() -> SpecCookieCombinator {
    SpecCookieCombinator(spec_opaque_1_ffff())
}

                
pub fn cookie<'a>() -> (o: CookieCombinator<'a>)
    ensures o@ == spec_cookie(),
{
    CookieCombinator(opaque_1_ffff())
}

                
pub type SpecEcPointFormat = u8;
pub type EcPointFormat = u8;


pub struct SpecEcPointFormatCombinator(SpecEcPointFormatCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatCombinator {
    type SpecResult = SpecEcPointFormat;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatCombinatorAlias = U8;

pub struct EcPointFormatCombinator(EcPointFormatCombinatorAlias);

impl View for EcPointFormatCombinator {
    type V = SpecEcPointFormatCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EcPointFormatCombinator {
    type Result = EcPointFormat;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EcPointFormatCombinatorAlias = U8;


pub closed spec fn spec_ec_point_format() -> SpecEcPointFormatCombinator {
    SpecEcPointFormatCombinator(U8)
}

                
pub fn ec_point_format() -> (o: EcPointFormatCombinator)
    ensures o@ == spec_ec_point_format(),
{
    EcPointFormatCombinator(U8)
}

                
pub type SpecEcPointFormatListList = Seq<SpecEcPointFormat>;
pub type EcPointFormatListList = RepeatResult<EcPointFormat>;


pub struct SpecEcPointFormatListListCombinator(SpecEcPointFormatListListCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatListListCombinator {
    type SpecResult = SpecEcPointFormatListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatListListCombinatorAlias = AndThen<Bytes, Repeat<SpecEcPointFormatCombinator>>;

pub struct EcPointFormatListListCombinator(EcPointFormatListListCombinatorAlias);

impl View for EcPointFormatListListCombinator {
    type V = SpecEcPointFormatListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EcPointFormatListListCombinator {
    type Result = EcPointFormatListList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EcPointFormatListListCombinatorAlias = AndThen<Bytes, Repeat<EcPointFormatCombinator>>;


pub closed spec fn spec_ec_point_format_list_list(l: SpecUint1Ff) -> SpecEcPointFormatListListCombinator {
    SpecEcPointFormatListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_ec_point_format())))
}

                
pub fn ec_point_format_list_list<'a>(l: Uint1Ff) -> (o: EcPointFormatListListCombinator)
    ensures o@ == spec_ec_point_format_list_list(l@),
{
    EcPointFormatListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(ec_point_format())))
}

                

pub struct SpecZeroByte {
    pub zero: u8,
}

pub type SpecZeroByteInner = u8;
impl SpecFrom<SpecZeroByte> for SpecZeroByteInner {
    open spec fn spec_from(m: SpecZeroByte) -> SpecZeroByteInner {
        m.zero
    }
}
impl SpecFrom<SpecZeroByteInner> for SpecZeroByte {
    open spec fn spec_from(m: SpecZeroByteInner) -> SpecZeroByte {
        let zero = m;
        SpecZeroByte { zero }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ZeroByte {
    pub zero: u8,
}

impl View for ZeroByte {
    type V = SpecZeroByte;

    open spec fn view(&self) -> Self::V {
        SpecZeroByte {
            zero: self.zero@,
        }
    }
}
pub type ZeroByteInner = u8;
impl From<ZeroByte> for ZeroByteInner {
    fn ex_from(m: ZeroByte) -> ZeroByteInner {
        m.zero
    }
}
impl From<ZeroByteInner> for ZeroByte {
    fn ex_from(m: ZeroByteInner) -> ZeroByte {
        let zero = m;
        ZeroByte { zero }
    }
}

pub struct ZeroByteMapper;
impl ZeroByteMapper {
    pub closed spec fn spec_new() -> Self {
        ZeroByteMapper
    }
    pub fn new() -> Self {
        ZeroByteMapper
    }
}
impl View for ZeroByteMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ZeroByteMapper {
    type Src = SpecZeroByteInner;
    type Dst = SpecZeroByte;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ZeroByteMapper {
    type Src = ZeroByteInner;
    type Dst = ZeroByte;
}
pub const ZEROBYTE_ZERO: u8 = 0;

pub struct SpecZeroByteCombinator(SpecZeroByteCombinatorAlias);

impl SpecCombinator for SpecZeroByteCombinator {
    type SpecResult = SpecZeroByte;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecZeroByteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecZeroByteCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;

pub struct ZeroByteCombinator(ZeroByteCombinatorAlias);

impl View for ZeroByteCombinator {
    type V = SpecZeroByteCombinator;
    closed spec fn view(&self) -> Self::V { SpecZeroByteCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ZeroByteCombinator {
    type Result = ZeroByte;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;


pub closed spec fn spec_zero_byte() -> SpecZeroByteCombinator {
    SpecZeroByteCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) },
        mapper: ZeroByteMapper::spec_new(),
    })
}

                
pub fn zero_byte() -> (o: ZeroByteCombinator)
    ensures o@ == spec_zero_byte(),
{
    ZeroByteCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) },
        mapper: ZeroByteMapper::new(),
    })
}

                
pub type SpecPaddingExtensionPadding = Seq<SpecZeroByte>;
pub type PaddingExtensionPadding = RepeatResult<ZeroByte>;


pub struct SpecPaddingExtensionPaddingCombinator(SpecPaddingExtensionPaddingCombinatorAlias);

impl SpecCombinator for SpecPaddingExtensionPaddingCombinator {
    type SpecResult = SpecPaddingExtensionPadding;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPaddingExtensionPaddingCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPaddingExtensionPaddingCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPaddingExtensionPaddingCombinatorAlias = AndThen<Bytes, Repeat<SpecZeroByteCombinator>>;

pub struct PaddingExtensionPaddingCombinator(PaddingExtensionPaddingCombinatorAlias);

impl View for PaddingExtensionPaddingCombinator {
    type V = SpecPaddingExtensionPaddingCombinator;
    closed spec fn view(&self) -> Self::V { SpecPaddingExtensionPaddingCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PaddingExtensionPaddingCombinator {
    type Result = PaddingExtensionPadding;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PaddingExtensionPaddingCombinatorAlias = AndThen<Bytes, Repeat<ZeroByteCombinator>>;


pub closed spec fn spec_padding_extension_padding(l: SpecUint0Ffff) -> SpecPaddingExtensionPaddingCombinator {
    SpecPaddingExtensionPaddingCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_zero_byte())))
}

                
pub fn padding_extension_padding<'a>(l: Uint0Ffff) -> (o: PaddingExtensionPaddingCombinator)
    ensures o@ == spec_padding_extension_padding(l@),
{
    PaddingExtensionPaddingCombinator(AndThen(Bytes(l.ex_into()), Repeat(zero_byte())))
}

                

pub struct SpecPaddingExtension {
    pub l: SpecUint0Ffff,
    pub padding: SpecPaddingExtensionPadding,
}

pub type SpecPaddingExtensionInner = (SpecUint0Ffff, SpecPaddingExtensionPadding);
impl SpecFrom<SpecPaddingExtension> for SpecPaddingExtensionInner {
    open spec fn spec_from(m: SpecPaddingExtension) -> SpecPaddingExtensionInner {
        (m.l, m.padding)
    }
}
impl SpecFrom<SpecPaddingExtensionInner> for SpecPaddingExtension {
    open spec fn spec_from(m: SpecPaddingExtensionInner) -> SpecPaddingExtension {
        let (l, padding) = m;
        SpecPaddingExtension { l, padding }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PaddingExtension {
    pub l: Uint0Ffff,
    pub padding: PaddingExtensionPadding,
}

impl View for PaddingExtension {
    type V = SpecPaddingExtension;

    open spec fn view(&self) -> Self::V {
        SpecPaddingExtension {
            l: self.l@,
            padding: self.padding@,
        }
    }
}
pub type PaddingExtensionInner = (Uint0Ffff, PaddingExtensionPadding);
impl From<PaddingExtension> for PaddingExtensionInner {
    fn ex_from(m: PaddingExtension) -> PaddingExtensionInner {
        (m.l, m.padding)
    }
}
impl From<PaddingExtensionInner> for PaddingExtension {
    fn ex_from(m: PaddingExtensionInner) -> PaddingExtension {
        let (l, padding) = m;
        PaddingExtension { l, padding }
    }
}

pub struct PaddingExtensionMapper;
impl PaddingExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        PaddingExtensionMapper
    }
    pub fn new() -> Self {
        PaddingExtensionMapper
    }
}
impl View for PaddingExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PaddingExtensionMapper {
    type Src = SpecPaddingExtensionInner;
    type Dst = SpecPaddingExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for PaddingExtensionMapper {
    type Src = PaddingExtensionInner;
    type Dst = PaddingExtension;
}

pub struct SpecPaddingExtensionCombinator(SpecPaddingExtensionCombinatorAlias);

impl SpecCombinator for SpecPaddingExtensionCombinator {
    type SpecResult = SpecPaddingExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPaddingExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPaddingExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPaddingExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecPaddingExtensionPaddingCombinator>, PaddingExtensionMapper>;

pub struct PaddingExtensionCombinator<'a>(PaddingExtensionCombinatorAlias<'a>);

impl<'a> View for PaddingExtensionCombinator<'a> {
    type V = SpecPaddingExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPaddingExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PaddingExtensionCombinator<'a> {
    type Result = PaddingExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PaddingExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, PaddingExtensionPaddingCombinator, PaddingExtensionCont0<'a>>, PaddingExtensionMapper>;


pub closed spec fn spec_padding_extension() -> SpecPaddingExtensionCombinator {
    SpecPaddingExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_padding_extension_cont0(deps) },
        mapper: PaddingExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_padding_extension_cont0(deps: SpecUint0Ffff) -> SpecPaddingExtensionPaddingCombinator {
    let l = deps;
    spec_padding_extension_padding(l)
}
                
pub fn padding_extension<'a>() -> (o: PaddingExtensionCombinator<'a>)
    ensures o@ == spec_padding_extension(),
{
    PaddingExtensionCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: PaddingExtensionCont0::new(), spec_snd: Ghost(|deps| spec_padding_extension_cont0(deps)) },
        mapper: PaddingExtensionMapper::new(),
    })
}

pub struct PaddingExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> PaddingExtensionCont0<'a> {
    pub fn new() -> Self {
        PaddingExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for PaddingExtensionCont0<'a> {
    type Output = PaddingExtensionPaddingCombinator;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_padding_extension_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        padding_extension_padding(l)
    }
}
                
pub type SpecSignatureScheme = u16;
pub type SignatureScheme = u16;


pub struct SpecSignatureSchemeCombinator(SpecSignatureSchemeCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeCombinator {
    type SpecResult = SpecSignatureScheme;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeCombinatorAlias = U16Be;

pub struct SignatureSchemeCombinator(SignatureSchemeCombinatorAlias);

impl View for SignatureSchemeCombinator {
    type V = SpecSignatureSchemeCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SignatureSchemeCombinator {
    type Result = SignatureScheme;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SignatureSchemeCombinatorAlias = U16Be;


pub closed spec fn spec_signature_scheme() -> SpecSignatureSchemeCombinator {
    SpecSignatureSchemeCombinator(U16Be)
}

                
pub fn signature_scheme() -> (o: SignatureSchemeCombinator)
    ensures o@ == spec_signature_scheme(),
{
    SignatureSchemeCombinator(U16Be)
}

                

pub struct SpecCertificateVerify {
    pub algorithm: SpecSignatureScheme,
    pub signature: SpecOpaque0Ffff,
}

pub type SpecCertificateVerifyInner = (SpecSignatureScheme, SpecOpaque0Ffff);
impl SpecFrom<SpecCertificateVerify> for SpecCertificateVerifyInner {
    open spec fn spec_from(m: SpecCertificateVerify) -> SpecCertificateVerifyInner {
        (m.algorithm, m.signature)
    }
}
impl SpecFrom<SpecCertificateVerifyInner> for SpecCertificateVerify {
    open spec fn spec_from(m: SpecCertificateVerifyInner) -> SpecCertificateVerify {
        let (algorithm, signature) = m;
        SpecCertificateVerify { algorithm, signature }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateVerify<'a> {
    pub algorithm: SignatureScheme,
    pub signature: Opaque0Ffff<'a>,
}

impl View for CertificateVerify<'_> {
    type V = SpecCertificateVerify;

    open spec fn view(&self) -> Self::V {
        SpecCertificateVerify {
            algorithm: self.algorithm@,
            signature: self.signature@,
        }
    }
}
pub type CertificateVerifyInner<'a> = (SignatureScheme, Opaque0Ffff<'a>);
impl<'a> From<CertificateVerify<'a>> for CertificateVerifyInner<'a> {
    fn ex_from(m: CertificateVerify) -> CertificateVerifyInner {
        (m.algorithm, m.signature)
    }
}
impl<'a> From<CertificateVerifyInner<'a>> for CertificateVerify<'a> {
    fn ex_from(m: CertificateVerifyInner) -> CertificateVerify {
        let (algorithm, signature) = m;
        CertificateVerify { algorithm, signature }
    }
}

pub struct CertificateVerifyMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateVerifyMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateVerifyMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateVerifyMapper(PhantomData)
    }
}
impl View for CertificateVerifyMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateVerifyMapper<'_> {
    type Src = SpecCertificateVerifyInner;
    type Dst = SpecCertificateVerify;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateVerifyMapper<'a> {
    type Src = CertificateVerifyInner<'a>;
    type Dst = CertificateVerify<'a>;
}

pub struct SpecCertificateVerifyCombinator(SpecCertificateVerifyCombinatorAlias);

impl SpecCombinator for SpecCertificateVerifyCombinator {
    type SpecResult = SpecCertificateVerify;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateVerifyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateVerifyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateVerifyCombinatorAlias = Mapped<(SpecSignatureSchemeCombinator, SpecOpaque0FfffCombinator), CertificateVerifyMapper<'static>>;

pub struct CertificateVerifyCombinator<'a>(CertificateVerifyCombinatorAlias<'a>);

impl<'a> View for CertificateVerifyCombinator<'a> {
    type V = SpecCertificateVerifyCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateVerifyCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateVerifyCombinator<'a> {
    type Result = CertificateVerify<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateVerifyCombinatorAlias<'a> = Mapped<(SignatureSchemeCombinator, Opaque0FfffCombinator<'a>), CertificateVerifyMapper<'a>>;


pub closed spec fn spec_certificate_verify() -> SpecCertificateVerifyCombinator {
    SpecCertificateVerifyCombinator(
    Mapped {
        inner: (spec_signature_scheme(), spec_opaque_0_ffff()),
        mapper: CertificateVerifyMapper::spec_new(),
    })
}

                
pub fn certificate_verify<'a>() -> (o: CertificateVerifyCombinator<'a>)
    ensures o@ == spec_certificate_verify(),
{
    CertificateVerifyCombinator(
    Mapped {
        inner: (signature_scheme(), opaque_0_ffff()),
        mapper: CertificateVerifyMapper::new(),
    })
}

                
pub type SpecPskKeyExchangeMode = u8;
pub type PskKeyExchangeMode = u8;


pub struct SpecPskKeyExchangeModeCombinator(SpecPskKeyExchangeModeCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModeCombinator {
    type SpecResult = SpecPskKeyExchangeMode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModeCombinatorAlias = U8;

pub struct PskKeyExchangeModeCombinator(PskKeyExchangeModeCombinatorAlias);

impl View for PskKeyExchangeModeCombinator {
    type V = SpecPskKeyExchangeModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskKeyExchangeModeCombinator {
    type Result = PskKeyExchangeMode;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskKeyExchangeModeCombinatorAlias = U8;


pub closed spec fn spec_psk_key_exchange_mode() -> SpecPskKeyExchangeModeCombinator {
    SpecPskKeyExchangeModeCombinator(U8)
}

                
pub fn psk_key_exchange_mode() -> (o: PskKeyExchangeModeCombinator)
    ensures o@ == spec_psk_key_exchange_mode(),
{
    PskKeyExchangeModeCombinator(U8)
}

                
pub type SpecPskKeyExchangeModesModes = Seq<SpecPskKeyExchangeMode>;
pub type PskKeyExchangeModesModes = RepeatResult<PskKeyExchangeMode>;


pub struct SpecPskKeyExchangeModesModesCombinator(SpecPskKeyExchangeModesModesCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModesModesCombinator {
    type SpecResult = SpecPskKeyExchangeModesModes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModesModesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModesModesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModesModesCombinatorAlias = AndThen<Bytes, Repeat<SpecPskKeyExchangeModeCombinator>>;

pub struct PskKeyExchangeModesModesCombinator(PskKeyExchangeModesModesCombinatorAlias);

impl View for PskKeyExchangeModesModesCombinator {
    type V = SpecPskKeyExchangeModesModesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModesModesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskKeyExchangeModesModesCombinator {
    type Result = PskKeyExchangeModesModes;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskKeyExchangeModesModesCombinatorAlias = AndThen<Bytes, Repeat<PskKeyExchangeModeCombinator>>;


pub closed spec fn spec_psk_key_exchange_modes_modes(l: SpecUint1Ff) -> SpecPskKeyExchangeModesModesCombinator {
    SpecPskKeyExchangeModesModesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_key_exchange_mode())))
}

                
pub fn psk_key_exchange_modes_modes<'a>(l: Uint1Ff) -> (o: PskKeyExchangeModesModesCombinator)
    ensures o@ == spec_psk_key_exchange_modes_modes(l@),
{
    PskKeyExchangeModesModesCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_key_exchange_mode())))
}

                
pub type SpecProtocolName = SpecOpaque1Ff;
pub type ProtocolName<'a> = Opaque1Ff<'a>;


pub struct SpecProtocolNameCombinator(SpecProtocolNameCombinatorAlias);

impl SpecCombinator for SpecProtocolNameCombinator {
    type SpecResult = SpecProtocolName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameCombinatorAlias = SpecOpaque1FfCombinator;

pub struct ProtocolNameCombinator<'a>(ProtocolNameCombinatorAlias<'a>);

impl<'a> View for ProtocolNameCombinator<'a> {
    type V = SpecProtocolNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ProtocolNameCombinator<'a> {
    type Result = ProtocolName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ProtocolNameCombinatorAlias<'a> = Opaque1FfCombinator<'a>;


pub closed spec fn spec_protocol_name() -> SpecProtocolNameCombinator {
    SpecProtocolNameCombinator(spec_opaque_1_ff())
}

                
pub fn protocol_name<'a>() -> (o: ProtocolNameCombinator<'a>)
    ensures o@ == spec_protocol_name(),
{
    ProtocolNameCombinator(opaque_1_ff())
}

                
pub type SpecProtocolNameListList = Seq<SpecProtocolName>;
pub type ProtocolNameListList<'a> = RepeatResult<ProtocolName<'a>>;


pub struct SpecProtocolNameListListCombinator(SpecProtocolNameListListCombinatorAlias);

impl SpecCombinator for SpecProtocolNameListListCombinator {
    type SpecResult = SpecProtocolNameListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameListListCombinatorAlias = AndThen<Bytes, Repeat<SpecProtocolNameCombinator>>;

pub struct ProtocolNameListListCombinator<'a>(ProtocolNameListListCombinatorAlias<'a>);

impl<'a> View for ProtocolNameListListCombinator<'a> {
    type V = SpecProtocolNameListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ProtocolNameListListCombinator<'a> {
    type Result = ProtocolNameListList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ProtocolNameListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<ProtocolNameCombinator<'a>>>;


pub closed spec fn spec_protocol_name_list_list(l: SpecUint2Ffff) -> SpecProtocolNameListListCombinator {
    SpecProtocolNameListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_protocol_name())))
}

                
pub fn protocol_name_list_list<'a>(l: Uint2Ffff) -> (o: ProtocolNameListListCombinator<'a>)
    ensures o@ == spec_protocol_name_list_list(l@),
{
    ProtocolNameListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(protocol_name())))
}

                

pub struct SpecSessionId {
    pub l: u8,
    pub id: Seq<u8>,
}

pub type SpecSessionIdInner = (u8, Seq<u8>);
impl SpecFrom<SpecSessionId> for SpecSessionIdInner {
    open spec fn spec_from(m: SpecSessionId) -> SpecSessionIdInner {
        (m.l, m.id)
    }
}
impl SpecFrom<SpecSessionIdInner> for SpecSessionId {
    open spec fn spec_from(m: SpecSessionIdInner) -> SpecSessionId {
        let (l, id) = m;
        SpecSessionId { l, id }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SessionId<'a> {
    pub l: u8,
    pub id: &'a [u8],
}

impl View for SessionId<'_> {
    type V = SpecSessionId;

    open spec fn view(&self) -> Self::V {
        SpecSessionId {
            l: self.l@,
            id: self.id@,
        }
    }
}
pub type SessionIdInner<'a> = (u8, &'a [u8]);
impl<'a> From<SessionId<'a>> for SessionIdInner<'a> {
    fn ex_from(m: SessionId) -> SessionIdInner {
        (m.l, m.id)
    }
}
impl<'a> From<SessionIdInner<'a>> for SessionId<'a> {
    fn ex_from(m: SessionIdInner) -> SessionId {
        let (l, id) = m;
        SessionId { l, id }
    }
}

pub struct SessionIdMapper<'a>(PhantomData<&'a ()>);
impl<'a> SessionIdMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SessionIdMapper(PhantomData)
    }
    pub fn new() -> Self {
        SessionIdMapper(PhantomData)
    }
}
impl View for SessionIdMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SessionIdMapper<'_> {
    type Src = SpecSessionIdInner;
    type Dst = SpecSessionId;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SessionIdMapper<'a> {
    type Src = SessionIdInner<'a>;
    type Dst = SessionId<'a>;
}

pub struct SpecSessionIdCombinator(SpecSessionIdCombinatorAlias);

impl SpecCombinator for SpecSessionIdCombinator {
    type SpecResult = SpecSessionId;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSessionIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSessionIdCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSessionIdCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate14254733753739482027>, Bytes>, SessionIdMapper<'static>>;
pub struct Predicate14254733753739482027;
impl View for Predicate14254733753739482027 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14254733753739482027 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32)
    }
}
impl SpecPred for Predicate14254733753739482027 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32)
    }
}

pub struct SessionIdCombinator<'a>(SessionIdCombinatorAlias<'a>);

impl<'a> View for SessionIdCombinator<'a> {
    type V = SpecSessionIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecSessionIdCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SessionIdCombinator<'a> {
    type Result = SessionId<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SessionIdCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate14254733753739482027>, Bytes, SessionIdCont0<'a>>, SessionIdMapper<'a>>;


pub closed spec fn spec_session_id() -> SpecSessionIdCombinator {
    SpecSessionIdCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U8, predicate: Predicate14254733753739482027 }, snd: |deps| spec_session_id_cont0(deps) },
        mapper: SessionIdMapper::spec_new(),
    })
}

pub open spec fn spec_session_id_cont0(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn session_id<'a>() -> (o: SessionIdCombinator<'a>)
    ensures o@ == spec_session_id(),
{
    SessionIdCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U8, predicate: Predicate14254733753739482027 }, snd: SessionIdCont0::new(), spec_snd: Ghost(|deps| spec_session_id_cont0(deps)) },
        mapper: SessionIdMapper::new(),
    })
}

pub struct SessionIdCont0<'a>(PhantomData<&'a ()>);
impl<'a> SessionIdCont0<'a> {
    pub fn new() -> Self {
        SessionIdCont0(PhantomData)
    }
}
impl<'a> Continuation<&u8> for SessionIdCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &u8) -> bool { true }

    open spec fn ensures(&self, deps: &u8, o: Self::Output) -> bool {
        o@ == spec_session_id_cont0(deps@)
    }

    fn apply(&self, deps: &u8) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub enum SpecHelloRetryExtensionExtensionData {
    SupportedVersions(SpecSupportedVersionsServer),
    Cookie(SpecCookie),
    KeyShare(SpecNamedGroup),
    Unrecognized(Seq<u8>),
}

pub type SpecHelloRetryExtensionExtensionDataInner = Either<SpecSupportedVersionsServer, Either<SpecCookie, Either<SpecNamedGroup, Seq<u8>>>>;



impl SpecFrom<SpecHelloRetryExtensionExtensionData> for SpecHelloRetryExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecHelloRetryExtensionExtensionData) -> SpecHelloRetryExtensionExtensionDataInner {
        match m {
            SpecHelloRetryExtensionExtensionData::SupportedVersions(m) => Either::Left(m),
            SpecHelloRetryExtensionExtensionData::Cookie(m) => Either::Right(Either::Left(m)),
            SpecHelloRetryExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecHelloRetryExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecHelloRetryExtensionExtensionDataInner> for SpecHelloRetryExtensionExtensionData {
    open spec fn spec_from(m: SpecHelloRetryExtensionExtensionDataInner) -> SpecHelloRetryExtensionExtensionData {
        match m {
            Either::Left(m) => SpecHelloRetryExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Left(m)) => SpecHelloRetryExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecHelloRetryExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecHelloRetryExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HelloRetryExtensionExtensionData<'a> {
    SupportedVersions(SupportedVersionsServer),
    Cookie(Cookie<'a>),
    KeyShare(NamedGroup),
    Unrecognized(&'a [u8]),
}

pub type HelloRetryExtensionExtensionDataInner<'a> = Either<SupportedVersionsServer, Either<Cookie<'a>, Either<NamedGroup, &'a [u8]>>>;


impl<'a> View for HelloRetryExtensionExtensionData<'a> {
    type V = SpecHelloRetryExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            HelloRetryExtensionExtensionData::SupportedVersions(m) => SpecHelloRetryExtensionExtensionData::SupportedVersions(m@),
            HelloRetryExtensionExtensionData::Cookie(m) => SpecHelloRetryExtensionExtensionData::Cookie(m@),
            HelloRetryExtensionExtensionData::KeyShare(m) => SpecHelloRetryExtensionExtensionData::KeyShare(m@),
            HelloRetryExtensionExtensionData::Unrecognized(m) => SpecHelloRetryExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<HelloRetryExtensionExtensionData<'a>> for HelloRetryExtensionExtensionDataInner<'a> {
    fn ex_from(m: HelloRetryExtensionExtensionData<'a>) -> HelloRetryExtensionExtensionDataInner<'a> {
        match m {
            HelloRetryExtensionExtensionData::SupportedVersions(m) => Either::Left(m),
            HelloRetryExtensionExtensionData::Cookie(m) => Either::Right(Either::Left(m)),
            HelloRetryExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Left(m))),
            HelloRetryExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<HelloRetryExtensionExtensionDataInner<'a>> for HelloRetryExtensionExtensionData<'a> {
    fn ex_from(m: HelloRetryExtensionExtensionDataInner<'a>) -> HelloRetryExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => HelloRetryExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Left(m)) => HelloRetryExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Left(m))) => HelloRetryExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(m))) => HelloRetryExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct HelloRetryExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HelloRetryExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        HelloRetryExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for HelloRetryExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionExtensionDataMapper<'_> {
    type Src = SpecHelloRetryExtensionExtensionDataInner;
    type Dst = SpecHelloRetryExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HelloRetryExtensionExtensionDataMapper<'a> {
    type Src = HelloRetryExtensionExtensionDataInner<'a>;
    type Dst = HelloRetryExtensionExtensionData<'a>;
}


pub struct SpecHelloRetryExtensionExtensionDataCombinator(SpecHelloRetryExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionExtensionDataCombinator {
    type SpecResult = SpecHelloRetryExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHelloRetryExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHelloRetryExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecSupportedVersionsServerCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecNamedGroupCombinator>, Cond<Bytes>>>>, HelloRetryExtensionExtensionDataMapper<'static>>>;

pub struct HelloRetryExtensionExtensionDataCombinator<'a>(HelloRetryExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for HelloRetryExtensionExtensionDataCombinator<'a> {
    type V = SpecHelloRetryExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryExtensionExtensionDataCombinator<'a> {
    type Result = HelloRetryExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HelloRetryExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<SupportedVersionsServerCombinator>, OrdChoice<Cond<CookieCombinator<'a>>, OrdChoice<Cond<NamedGroupCombinator>, Cond<Bytes>>>>, HelloRetryExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_hello_retry_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecHelloRetryExtensionExtensionDataCombinator {
    SpecHelloRetryExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_server() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_named_group() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) }))), mapper: HelloRetryExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn hello_retry_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: HelloRetryExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_hello_retry_extension_extension_data(extension_type@, ext_len@),
{
    HelloRetryExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 43, inner: supported_versions_server() }, OrdChoice::new(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice::new(Cond { cond: extension_type == 51, inner: named_group() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) }))), mapper: HelloRetryExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecHelloRetryExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecHelloRetryExtensionExtensionData,
}

pub type SpecHelloRetryExtensionInner = ((SpecExtensionType, u16), SpecHelloRetryExtensionExtensionData);
impl SpecFrom<SpecHelloRetryExtension> for SpecHelloRetryExtensionInner {
    open spec fn spec_from(m: SpecHelloRetryExtension) -> SpecHelloRetryExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecHelloRetryExtensionInner> for SpecHelloRetryExtension {
    open spec fn spec_from(m: SpecHelloRetryExtensionInner) -> SpecHelloRetryExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecHelloRetryExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct HelloRetryExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: HelloRetryExtensionExtensionData<'a>,
}

impl View for HelloRetryExtension<'_> {
    type V = SpecHelloRetryExtension;

    open spec fn view(&self) -> Self::V {
        SpecHelloRetryExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type HelloRetryExtensionInner<'a> = ((ExtensionType, u16), HelloRetryExtensionExtensionData<'a>);
impl<'a> From<HelloRetryExtension<'a>> for HelloRetryExtensionInner<'a> {
    fn ex_from(m: HelloRetryExtension) -> HelloRetryExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<HelloRetryExtensionInner<'a>> for HelloRetryExtension<'a> {
    fn ex_from(m: HelloRetryExtensionInner) -> HelloRetryExtension {
        let ((extension_type, ext_len), extension_data) = m;
        HelloRetryExtension { extension_type, ext_len, extension_data }
    }
}

pub struct HelloRetryExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HelloRetryExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        HelloRetryExtensionMapper(PhantomData)
    }
}
impl View for HelloRetryExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionMapper<'_> {
    type Src = SpecHelloRetryExtensionInner;
    type Dst = SpecHelloRetryExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HelloRetryExtensionMapper<'a> {
    type Src = HelloRetryExtensionInner<'a>;
    type Dst = HelloRetryExtension<'a>;
}

pub struct SpecHelloRetryExtensionCombinator(SpecHelloRetryExtensionCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionCombinator {
    type SpecResult = SpecHelloRetryExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHelloRetryExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHelloRetryExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecHelloRetryExtensionExtensionDataCombinator>, HelloRetryExtensionMapper<'static>>;

pub struct HelloRetryExtensionCombinator<'a>(HelloRetryExtensionCombinatorAlias<'a>);

impl<'a> View for HelloRetryExtensionCombinator<'a> {
    type V = SpecHelloRetryExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryExtensionCombinator<'a> {
    type Result = HelloRetryExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HelloRetryExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, HelloRetryExtensionCont1<'a>>, HelloRetryExtensionExtensionDataCombinator<'a>, HelloRetryExtensionCont0<'a>>, HelloRetryExtensionMapper<'a>>;


pub closed spec fn spec_hello_retry_extension() -> SpecHelloRetryExtensionCombinator {
    SpecHelloRetryExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_hello_retry_extension_cont1(deps) }, snd: |deps| spec_hello_retry_extension_cont0(deps) },
        mapper: HelloRetryExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_hello_retry_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_hello_retry_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecHelloRetryExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_hello_retry_extension_extension_data(extension_type, ext_len)
}
                
pub fn hello_retry_extension<'a>() -> (o: HelloRetryExtensionCombinator<'a>)
    ensures o@ == spec_hello_retry_extension(),
{
    HelloRetryExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: HelloRetryExtensionCont1::new(), spec_snd: Ghost(|deps| spec_hello_retry_extension_cont1(deps)) }, snd: HelloRetryExtensionCont0::new(), spec_snd: Ghost(|deps| spec_hello_retry_extension_cont0(deps)) },
        mapper: HelloRetryExtensionMapper::new(),
    })
}

pub struct HelloRetryExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionCont1<'a> {
    pub fn new() -> Self {
        HelloRetryExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for HelloRetryExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_hello_retry_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct HelloRetryExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionCont0<'a> {
    pub fn new() -> Self {
        HelloRetryExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for HelloRetryExtensionCont0<'a> {
    type Output = HelloRetryExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_hello_retry_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        hello_retry_extension_extension_data(extension_type, ext_len)
    }
}
                
pub type SpecHelloRetryExtensionsExtensions = Seq<SpecHelloRetryExtension>;
pub type HelloRetryExtensionsExtensions<'a> = RepeatResult<HelloRetryExtension<'a>>;


pub struct SpecHelloRetryExtensionsExtensionsCombinator(SpecHelloRetryExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionsExtensionsCombinator {
    type SpecResult = SpecHelloRetryExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHelloRetryExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHelloRetryExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecHelloRetryExtensionCombinator>>;

pub struct HelloRetryExtensionsExtensionsCombinator<'a>(HelloRetryExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for HelloRetryExtensionsExtensionsCombinator<'a> {
    type V = SpecHelloRetryExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryExtensionsExtensionsCombinator<'a> {
    type Result = HelloRetryExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HelloRetryExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<HelloRetryExtensionCombinator<'a>>>;


pub closed spec fn spec_hello_retry_extensions_extensions(l: u16) -> SpecHelloRetryExtensionsExtensionsCombinator {
    SpecHelloRetryExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_hello_retry_extension())))
}

                
pub fn hello_retry_extensions_extensions<'a>(l: u16) -> (o: HelloRetryExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_hello_retry_extensions_extensions(l@),
{
    HelloRetryExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(hello_retry_extension())))
}

                

pub struct SpecHelloRetryExtensions {
    pub l: u16,
    pub extensions: SpecHelloRetryExtensionsExtensions,
}

pub type SpecHelloRetryExtensionsInner = (u16, SpecHelloRetryExtensionsExtensions);
impl SpecFrom<SpecHelloRetryExtensions> for SpecHelloRetryExtensionsInner {
    open spec fn spec_from(m: SpecHelloRetryExtensions) -> SpecHelloRetryExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecHelloRetryExtensionsInner> for SpecHelloRetryExtensions {
    open spec fn spec_from(m: SpecHelloRetryExtensionsInner) -> SpecHelloRetryExtensions {
        let (l, extensions) = m;
        SpecHelloRetryExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct HelloRetryExtensions<'a> {
    pub l: u16,
    pub extensions: HelloRetryExtensionsExtensions<'a>,
}

impl View for HelloRetryExtensions<'_> {
    type V = SpecHelloRetryExtensions;

    open spec fn view(&self) -> Self::V {
        SpecHelloRetryExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type HelloRetryExtensionsInner<'a> = (u16, HelloRetryExtensionsExtensions<'a>);
impl<'a> From<HelloRetryExtensions<'a>> for HelloRetryExtensionsInner<'a> {
    fn ex_from(m: HelloRetryExtensions) -> HelloRetryExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<HelloRetryExtensionsInner<'a>> for HelloRetryExtensions<'a> {
    fn ex_from(m: HelloRetryExtensionsInner) -> HelloRetryExtensions {
        let (l, extensions) = m;
        HelloRetryExtensions { l, extensions }
    }
}

pub struct HelloRetryExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HelloRetryExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        HelloRetryExtensionsMapper(PhantomData)
    }
}
impl View for HelloRetryExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionsMapper<'_> {
    type Src = SpecHelloRetryExtensionsInner;
    type Dst = SpecHelloRetryExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HelloRetryExtensionsMapper<'a> {
    type Src = HelloRetryExtensionsInner<'a>;
    type Dst = HelloRetryExtensions<'a>;
}

pub struct SpecHelloRetryExtensionsCombinator(SpecHelloRetryExtensionsCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionsCombinator {
    type SpecResult = SpecHelloRetryExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHelloRetryExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHelloRetryExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate3289024863945113924>, SpecHelloRetryExtensionsExtensionsCombinator>, HelloRetryExtensionsMapper<'static>>;
pub struct Predicate3289024863945113924;
impl View for Predicate3289024863945113924 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate3289024863945113924 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 6 && i <= 65535)
    }
}
impl SpecPred for Predicate3289024863945113924 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 6 && i <= 65535)
    }
}

pub struct HelloRetryExtensionsCombinator<'a>(HelloRetryExtensionsCombinatorAlias<'a>);

impl<'a> View for HelloRetryExtensionsCombinator<'a> {
    type V = SpecHelloRetryExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryExtensionsCombinator<'a> {
    type Result = HelloRetryExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HelloRetryExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate3289024863945113924>, HelloRetryExtensionsExtensionsCombinator<'a>, HelloRetryExtensionsCont0<'a>>, HelloRetryExtensionsMapper<'a>>;


pub closed spec fn spec_hello_retry_extensions() -> SpecHelloRetryExtensionsCombinator {
    SpecHelloRetryExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate3289024863945113924 }, snd: |deps| spec_hello_retry_extensions_cont0(deps) },
        mapper: HelloRetryExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_hello_retry_extensions_cont0(deps: u16) -> SpecHelloRetryExtensionsExtensionsCombinator {
    let l = deps;
    spec_hello_retry_extensions_extensions(l)
}
                
pub fn hello_retry_extensions<'a>() -> (o: HelloRetryExtensionsCombinator<'a>)
    ensures o@ == spec_hello_retry_extensions(),
{
    HelloRetryExtensionsCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate3289024863945113924 }, snd: HelloRetryExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_hello_retry_extensions_cont0(deps)) },
        mapper: HelloRetryExtensionsMapper::new(),
    })
}

pub struct HelloRetryExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryExtensionsCont0<'a> {
    pub fn new() -> Self {
        HelloRetryExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for HelloRetryExtensionsCont0<'a> {
    type Output = HelloRetryExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_hello_retry_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        hello_retry_extensions_extensions(l)
    }
}
                

pub struct SpecHelloRetryRequest {
    pub legacy_session_id_echo: SpecSessionId,
    pub cipher_suite: SpecCipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: SpecHelloRetryExtensions,
}

pub type SpecHelloRetryRequestInner = (SpecSessionId, (SpecCipherSuite, (u8, SpecHelloRetryExtensions)));
impl SpecFrom<SpecHelloRetryRequest> for SpecHelloRetryRequestInner {
    open spec fn spec_from(m: SpecHelloRetryRequest) -> SpecHelloRetryRequestInner {
        (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))
    }
}
impl SpecFrom<SpecHelloRetryRequestInner> for SpecHelloRetryRequest {
    open spec fn spec_from(m: SpecHelloRetryRequestInner) -> SpecHelloRetryRequest {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        SpecHelloRetryRequest { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct HelloRetryRequest<'a> {
    pub legacy_session_id_echo: SessionId<'a>,
    pub cipher_suite: CipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: HelloRetryExtensions<'a>,
}

impl View for HelloRetryRequest<'_> {
    type V = SpecHelloRetryRequest;

    open spec fn view(&self) -> Self::V {
        SpecHelloRetryRequest {
            legacy_session_id_echo: self.legacy_session_id_echo@,
            cipher_suite: self.cipher_suite@,
            legacy_compression_method: self.legacy_compression_method@,
            extensions: self.extensions@,
        }
    }
}
pub type HelloRetryRequestInner<'a> = (SessionId<'a>, (CipherSuite, (u8, HelloRetryExtensions<'a>)));
impl<'a> From<HelloRetryRequest<'a>> for HelloRetryRequestInner<'a> {
    fn ex_from(m: HelloRetryRequest) -> HelloRetryRequestInner {
        (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))
    }
}
impl<'a> From<HelloRetryRequestInner<'a>> for HelloRetryRequest<'a> {
    fn ex_from(m: HelloRetryRequestInner) -> HelloRetryRequest {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        HelloRetryRequest { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}

pub struct HelloRetryRequestMapper<'a>(PhantomData<&'a ()>);
impl<'a> HelloRetryRequestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HelloRetryRequestMapper(PhantomData)
    }
    pub fn new() -> Self {
        HelloRetryRequestMapper(PhantomData)
    }
}
impl View for HelloRetryRequestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryRequestMapper<'_> {
    type Src = SpecHelloRetryRequestInner;
    type Dst = SpecHelloRetryRequest;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HelloRetryRequestMapper<'a> {
    type Src = HelloRetryRequestInner<'a>;
    type Dst = HelloRetryRequest<'a>;
}
pub const HELLORETRYREQUEST_LEGACY_COMPRESSION_METHOD: u8 = 0;

pub struct SpecHelloRetryRequestCombinator(SpecHelloRetryRequestCombinatorAlias);

impl SpecCombinator for SpecHelloRetryRequestCombinator {
    type SpecResult = SpecHelloRetryRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHelloRetryRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHelloRetryRequestCombinatorAlias = Mapped<(SpecSessionIdCombinator, (SpecCipherSuiteCombinator, (Refined<U8, TagPred<u8>>, SpecHelloRetryExtensionsCombinator))), HelloRetryRequestMapper<'static>>;

pub struct HelloRetryRequestCombinator<'a>(HelloRetryRequestCombinatorAlias<'a>);

impl<'a> View for HelloRetryRequestCombinator<'a> {
    type V = SpecHelloRetryRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryRequestCombinator<'a> {
    type Result = HelloRetryRequest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HelloRetryRequestCombinatorAlias<'a> = Mapped<(SessionIdCombinator<'a>, (CipherSuiteCombinator, (Refined<U8, TagPred<u8>>, HelloRetryExtensionsCombinator<'a>))), HelloRetryRequestMapper<'a>>;


pub closed spec fn spec_hello_retry_request() -> SpecHelloRetryRequestCombinator {
    SpecHelloRetryRequestCombinator(
    Mapped {
        inner: (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(HELLORETRYREQUEST_LEGACY_COMPRESSION_METHOD) }, spec_hello_retry_extensions()))),
        mapper: HelloRetryRequestMapper::spec_new(),
    })
}

                
pub fn hello_retry_request<'a>() -> (o: HelloRetryRequestCombinator<'a>)
    ensures o@ == spec_hello_retry_request(),
{
    HelloRetryRequestCombinator(
    Mapped {
        inner: (session_id(), (cipher_suite(), (Refined { inner: U8, predicate: TagPred(HELLORETRYREQUEST_LEGACY_COMPRESSION_METHOD) }, hello_retry_extensions()))),
        mapper: HelloRetryRequestMapper::new(),
    })
}

                
pub type SpecUint2Ffff = u16;
pub type Uint2Ffff = u16;


pub struct SpecUint2FfffCombinator(SpecUint2FfffCombinatorAlias);

impl SpecCombinator for SpecUint2FfffCombinator {
    type SpecResult = SpecUint2Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint2FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint2FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint2FfffCombinatorAlias = Refined<U16Be, Predicate3016150102856496288>;
pub struct Predicate3016150102856496288;
impl View for Predicate3016150102856496288 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate3016150102856496288 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}
impl SpecPred for Predicate3016150102856496288 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}

pub struct Uint2FfffCombinator(Uint2FfffCombinatorAlias);

impl View for Uint2FfffCombinator {
    type V = SpecUint2FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint2FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint2FfffCombinator {
    type Result = Uint2Ffff;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint2FfffCombinatorAlias = Refined<U16Be, Predicate3016150102856496288>;


pub closed spec fn spec_uint_2_ffff() -> SpecUint2FfffCombinator {
    SpecUint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate3016150102856496288 })
}

                
pub fn uint_2_ffff() -> (o: Uint2FfffCombinator)
    ensures o@ == spec_uint_2_ffff(),
{
    Uint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate3016150102856496288 })
}

                
pub type SpecSrtpProtectionProfile = Seq<u8>;
pub type SrtpProtectionProfile<'a> = &'a [u8];


pub struct SpecSrtpProtectionProfileCombinator(SpecSrtpProtectionProfileCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfileCombinator {
    type SpecResult = SpecSrtpProtectionProfile;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfileCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfileCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfileCombinatorAlias = BytesN<2>;

pub struct SrtpProtectionProfileCombinator(SrtpProtectionProfileCombinatorAlias);

impl View for SrtpProtectionProfileCombinator {
    type V = SpecSrtpProtectionProfileCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfileCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SrtpProtectionProfileCombinator {
    type Result = SrtpProtectionProfile<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SrtpProtectionProfileCombinatorAlias = BytesN<2>;


pub closed spec fn spec_srtp_protection_profile() -> SpecSrtpProtectionProfileCombinator {
    SpecSrtpProtectionProfileCombinator(BytesN::<2>)
}

                
pub fn srtp_protection_profile() -> (o: SrtpProtectionProfileCombinator)
    ensures o@ == spec_srtp_protection_profile(),
{
    SrtpProtectionProfileCombinator(BytesN::<2>)
}

                
pub type SpecSrtpProtectionProfilesList = Seq<SpecSrtpProtectionProfile>;
pub type SrtpProtectionProfilesList<'a> = RepeatResult<SrtpProtectionProfile<'a>>;


pub struct SpecSrtpProtectionProfilesListCombinator(SpecSrtpProtectionProfilesListCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfilesListCombinator {
    type SpecResult = SpecSrtpProtectionProfilesList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfilesListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfilesListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfilesListCombinatorAlias = AndThen<Bytes, Repeat<SpecSrtpProtectionProfileCombinator>>;

pub struct SrtpProtectionProfilesListCombinator(SrtpProtectionProfilesListCombinatorAlias);

impl View for SrtpProtectionProfilesListCombinator {
    type V = SpecSrtpProtectionProfilesListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfilesListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SrtpProtectionProfilesListCombinator {
    type Result = SrtpProtectionProfilesList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SrtpProtectionProfilesListCombinatorAlias = AndThen<Bytes, Repeat<SrtpProtectionProfileCombinator>>;


pub closed spec fn spec_srtp_protection_profiles_list(l: SpecUint2Ffff) -> SpecSrtpProtectionProfilesListCombinator {
    SpecSrtpProtectionProfilesListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_srtp_protection_profile())))
}

                
pub fn srtp_protection_profiles_list<'a>(l: Uint2Ffff) -> (o: SrtpProtectionProfilesListCombinator)
    ensures o@ == spec_srtp_protection_profiles_list(l@),
{
    SrtpProtectionProfilesListCombinator(AndThen(Bytes(l.ex_into()), Repeat(srtp_protection_profile())))
}

                

pub struct SpecSrtpProtectionProfiles {
    pub l: SpecUint2Ffff,
    pub list: SpecSrtpProtectionProfilesList,
}

pub type SpecSrtpProtectionProfilesInner = (SpecUint2Ffff, SpecSrtpProtectionProfilesList);
impl SpecFrom<SpecSrtpProtectionProfiles> for SpecSrtpProtectionProfilesInner {
    open spec fn spec_from(m: SpecSrtpProtectionProfiles) -> SpecSrtpProtectionProfilesInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSrtpProtectionProfilesInner> for SpecSrtpProtectionProfiles {
    open spec fn spec_from(m: SpecSrtpProtectionProfilesInner) -> SpecSrtpProtectionProfiles {
        let (l, list) = m;
        SpecSrtpProtectionProfiles { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SrtpProtectionProfiles<'a> {
    pub l: Uint2Ffff,
    pub list: SrtpProtectionProfilesList<'a>,
}

impl View for SrtpProtectionProfiles<'_> {
    type V = SpecSrtpProtectionProfiles;

    open spec fn view(&self) -> Self::V {
        SpecSrtpProtectionProfiles {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type SrtpProtectionProfilesInner<'a> = (Uint2Ffff, SrtpProtectionProfilesList<'a>);
impl<'a> From<SrtpProtectionProfiles<'a>> for SrtpProtectionProfilesInner<'a> {
    fn ex_from(m: SrtpProtectionProfiles) -> SrtpProtectionProfilesInner {
        (m.l, m.list)
    }
}
impl<'a> From<SrtpProtectionProfilesInner<'a>> for SrtpProtectionProfiles<'a> {
    fn ex_from(m: SrtpProtectionProfilesInner) -> SrtpProtectionProfiles {
        let (l, list) = m;
        SrtpProtectionProfiles { l, list }
    }
}

pub struct SrtpProtectionProfilesMapper<'a>(PhantomData<&'a ()>);
impl<'a> SrtpProtectionProfilesMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SrtpProtectionProfilesMapper(PhantomData)
    }
    pub fn new() -> Self {
        SrtpProtectionProfilesMapper(PhantomData)
    }
}
impl View for SrtpProtectionProfilesMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SrtpProtectionProfilesMapper<'_> {
    type Src = SpecSrtpProtectionProfilesInner;
    type Dst = SpecSrtpProtectionProfiles;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SrtpProtectionProfilesMapper<'a> {
    type Src = SrtpProtectionProfilesInner<'a>;
    type Dst = SrtpProtectionProfiles<'a>;
}

pub struct SpecSrtpProtectionProfilesCombinator(SpecSrtpProtectionProfilesCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfilesCombinator {
    type SpecResult = SpecSrtpProtectionProfiles;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfilesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfilesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfilesCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecSrtpProtectionProfilesListCombinator>, SrtpProtectionProfilesMapper<'static>>;

pub struct SrtpProtectionProfilesCombinator<'a>(SrtpProtectionProfilesCombinatorAlias<'a>);

impl<'a> View for SrtpProtectionProfilesCombinator<'a> {
    type V = SpecSrtpProtectionProfilesCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfilesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SrtpProtectionProfilesCombinator<'a> {
    type Result = SrtpProtectionProfiles<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SrtpProtectionProfilesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, SrtpProtectionProfilesListCombinator, SrtpProtectionProfilesCont0<'a>>, SrtpProtectionProfilesMapper<'a>>;


pub closed spec fn spec_srtp_protection_profiles() -> SpecSrtpProtectionProfilesCombinator {
    SpecSrtpProtectionProfilesCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_ffff(), snd: |deps| spec_srtp_protection_profiles_cont0(deps) },
        mapper: SrtpProtectionProfilesMapper::spec_new(),
    })
}

pub open spec fn spec_srtp_protection_profiles_cont0(deps: SpecUint2Ffff) -> SpecSrtpProtectionProfilesListCombinator {
    let l = deps;
    spec_srtp_protection_profiles_list(l)
}
                
pub fn srtp_protection_profiles<'a>() -> (o: SrtpProtectionProfilesCombinator<'a>)
    ensures o@ == spec_srtp_protection_profiles(),
{
    SrtpProtectionProfilesCombinator(
    Mapped {
        inner: Depend { fst: uint_2_ffff(), snd: SrtpProtectionProfilesCont0::new(), spec_snd: Ghost(|deps| spec_srtp_protection_profiles_cont0(deps)) },
        mapper: SrtpProtectionProfilesMapper::new(),
    })
}

pub struct SrtpProtectionProfilesCont0<'a>(PhantomData<&'a ()>);
impl<'a> SrtpProtectionProfilesCont0<'a> {
    pub fn new() -> Self {
        SrtpProtectionProfilesCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Ffff> for SrtpProtectionProfilesCont0<'a> {
    type Output = SrtpProtectionProfilesListCombinator;

    open spec fn requires(&self, deps: &Uint2Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_srtp_protection_profiles_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Ffff) -> Self::Output {
        let l = *deps;
        srtp_protection_profiles_list(l)
    }
}
                
pub type SpecCertificateType = u8;
pub type CertificateType = u8;


pub struct SpecCertificateTypeCombinator(SpecCertificateTypeCombinatorAlias);

impl SpecCombinator for SpecCertificateTypeCombinator {
    type SpecResult = SpecCertificateType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateTypeCombinatorAlias = U8;

pub struct CertificateTypeCombinator(CertificateTypeCombinatorAlias);

impl View for CertificateTypeCombinator {
    type V = SpecCertificateTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateTypeCombinator {
    type Result = CertificateType;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateTypeCombinatorAlias = U8;


pub closed spec fn spec_certificate_type() -> SpecCertificateTypeCombinator {
    SpecCertificateTypeCombinator(U8)
}

                
pub fn certificate_type() -> (o: CertificateTypeCombinator)
    ensures o@ == spec_certificate_type(),
{
    CertificateTypeCombinator(U8)
}

                
pub type SpecServerCertTypeClientExtensionTypes = Seq<SpecCertificateType>;
pub type ServerCertTypeClientExtensionTypes = RepeatResult<CertificateType>;


pub struct SpecServerCertTypeClientExtensionTypesCombinator(SpecServerCertTypeClientExtensionTypesCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeClientExtensionTypesCombinator {
    type SpecResult = SpecServerCertTypeClientExtensionTypes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeClientExtensionTypesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeClientExtensionTypesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateTypeCombinator>>;

pub struct ServerCertTypeClientExtensionTypesCombinator(ServerCertTypeClientExtensionTypesCombinatorAlias);

impl View for ServerCertTypeClientExtensionTypesCombinator {
    type V = SpecServerCertTypeClientExtensionTypesCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeClientExtensionTypesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerCertTypeClientExtensionTypesCombinator {
    type Result = ServerCertTypeClientExtensionTypes;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<CertificateTypeCombinator>>;


pub closed spec fn spec_server_cert_type_client_extension_types(l: SpecUint1Ff) -> SpecServerCertTypeClientExtensionTypesCombinator {
    SpecServerCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_type())))
}

                
pub fn server_cert_type_client_extension_types<'a>(l: Uint1Ff) -> (o: ServerCertTypeClientExtensionTypesCombinator)
    ensures o@ == spec_server_cert_type_client_extension_types(l@),
{
    ServerCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_type())))
}

                
pub type SpecUint2Fffe = u16;
pub type Uint2Fffe = u16;


pub struct SpecUint2FffeCombinator(SpecUint2FffeCombinatorAlias);

impl SpecCombinator for SpecUint2FffeCombinator {
    type SpecResult = SpecUint2Fffe;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint2FffeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint2FffeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint2FffeCombinatorAlias = Refined<U16Be, Predicate16475346874978760473>;
pub struct Predicate16475346874978760473;
impl View for Predicate16475346874978760473 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate16475346874978760473 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65534)
    }
}
impl SpecPred for Predicate16475346874978760473 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65534)
    }
}

pub struct Uint2FffeCombinator(Uint2FffeCombinatorAlias);

impl View for Uint2FffeCombinator {
    type V = SpecUint2FffeCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint2FffeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint2FffeCombinator {
    type Result = Uint2Fffe;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint2FffeCombinatorAlias = Refined<U16Be, Predicate16475346874978760473>;


pub closed spec fn spec_uint_2_fffe() -> SpecUint2FffeCombinator {
    SpecUint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate16475346874978760473 })
}

                
pub fn uint_2_fffe() -> (o: Uint2FffeCombinator)
    ensures o@ == spec_uint_2_fffe(),
{
    Uint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate16475346874978760473 })
}

                

pub struct SpecOpaque1Ffffff {
    pub l: u24,
    pub data: Seq<u8>,
}

pub type SpecOpaque1FfffffInner = (u24, Seq<u8>);
impl SpecFrom<SpecOpaque1Ffffff> for SpecOpaque1FfffffInner {
    open spec fn spec_from(m: SpecOpaque1Ffffff) -> SpecOpaque1FfffffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfffffInner> for SpecOpaque1Ffffff {
    open spec fn spec_from(m: SpecOpaque1FfffffInner) -> SpecOpaque1Ffffff {
        let (l, data) = m;
        SpecOpaque1Ffffff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque1Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}

impl View for Opaque1Ffffff<'_> {
    type V = SpecOpaque1Ffffff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque1FfffffInner<'a> = (u24, &'a [u8]);
impl<'a> From<Opaque1Ffffff<'a>> for Opaque1FfffffInner<'a> {
    fn ex_from(m: Opaque1Ffffff) -> Opaque1FfffffInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffffInner<'a>> for Opaque1Ffffff<'a> {
    fn ex_from(m: Opaque1FfffffInner) -> Opaque1Ffffff {
        let (l, data) = m;
        Opaque1Ffffff { l, data }
    }
}

pub struct Opaque1FfffffMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffffMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque1FfffffMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque1FfffffMapper(PhantomData)
    }
}
impl View for Opaque1FfffffMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffffMapper<'_> {
    type Src = SpecOpaque1FfffffInner;
    type Dst = SpecOpaque1Ffffff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque1FfffffMapper<'a> {
    type Src = Opaque1FfffffInner<'a>;
    type Dst = Opaque1Ffffff<'a>;
}

pub struct SpecOpaque1FfffffCombinator(SpecOpaque1FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffffCombinator {
    type SpecResult = SpecOpaque1Ffffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfffffCombinatorAlias = Mapped<SpecDepend<Refined<U24Be, Predicate15036445817960576151>, Bytes>, Opaque1FfffffMapper<'static>>;
pub struct Predicate15036445817960576151;
impl View for Predicate15036445817960576151 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate15036445817960576151 {
    type Input = u24;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i).as_u32();
        (i >= 1 && i <= 16777215)
    }
}
impl SpecPred for Predicate15036445817960576151 {
    type Input = u24;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i).spec_as_u32();
        (i >= 1 && i <= 16777215)
    }
}

pub struct Opaque1FfffffCombinator<'a>(Opaque1FfffffCombinatorAlias<'a>);

impl<'a> View for Opaque1FfffffCombinator<'a> {
    type V = SpecOpaque1FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque1FfffffCombinator<'a> {
    type Result = Opaque1Ffffff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque1FfffffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U24Be, Predicate15036445817960576151>, Bytes, Opaque1FfffffCont0<'a>>, Opaque1FfffffMapper<'a>>;


pub closed spec fn spec_opaque_1_ffffff() -> SpecOpaque1FfffffCombinator {
    SpecOpaque1FfffffCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U24Be, predicate: Predicate15036445817960576151 }, snd: |deps| spec_opaque1_ffffff_cont0(deps) },
        mapper: Opaque1FfffffMapper::spec_new(),
    })
}

pub open spec fn spec_opaque1_ffffff_cont0(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_1_ffffff<'a>() -> (o: Opaque1FfffffCombinator<'a>)
    ensures o@ == spec_opaque_1_ffffff(),
{
    Opaque1FfffffCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U24Be, predicate: Predicate15036445817960576151 }, snd: Opaque1FfffffCont0::new(), spec_snd: Ghost(|deps| spec_opaque1_ffffff_cont0(deps)) },
        mapper: Opaque1FfffffMapper::new(),
    })
}

pub struct Opaque1FfffffCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffffCont0<'a> {
    pub fn new() -> Self {
        Opaque1FfffffCont0(PhantomData)
    }
}
impl<'a> Continuation<&u24> for Opaque1FfffffCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &u24) -> bool { true }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffffff_cont0(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                
pub type SpecOcspResponse = SpecOpaque1Ffffff;
pub type OcspResponse<'a> = Opaque1Ffffff<'a>;


pub struct SpecOcspResponseCombinator(SpecOcspResponseCombinatorAlias);

impl SpecCombinator for SpecOcspResponseCombinator {
    type SpecResult = SpecOcspResponse;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOcspResponseCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspResponseCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOcspResponseCombinatorAlias = SpecOpaque1FfffffCombinator;

pub struct OcspResponseCombinator<'a>(OcspResponseCombinatorAlias<'a>);

impl<'a> View for OcspResponseCombinator<'a> {
    type V = SpecOcspResponseCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspResponseCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OcspResponseCombinator<'a> {
    type Result = OcspResponse<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OcspResponseCombinatorAlias<'a> = Opaque1FfffffCombinator<'a>;


pub closed spec fn spec_ocsp_response() -> SpecOcspResponseCombinator {
    SpecOcspResponseCombinator(spec_opaque_1_ffffff())
}

                
pub fn ocsp_response<'a>() -> (o: OcspResponseCombinator<'a>)
    ensures o@ == spec_ocsp_response(),
{
    OcspResponseCombinator(opaque_1_ffffff())
}

                

pub struct SpecCertificateStatus {
    pub status_type: u8,
    pub response: SpecOcspResponse,
}

pub type SpecCertificateStatusInner = (u8, SpecOcspResponse);
impl SpecFrom<SpecCertificateStatus> for SpecCertificateStatusInner {
    open spec fn spec_from(m: SpecCertificateStatus) -> SpecCertificateStatusInner {
        (m.status_type, m.response)
    }
}
impl SpecFrom<SpecCertificateStatusInner> for SpecCertificateStatus {
    open spec fn spec_from(m: SpecCertificateStatusInner) -> SpecCertificateStatus {
        let (status_type, response) = m;
        SpecCertificateStatus { status_type, response }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateStatus<'a> {
    pub status_type: u8,
    pub response: OcspResponse<'a>,
}

impl View for CertificateStatus<'_> {
    type V = SpecCertificateStatus;

    open spec fn view(&self) -> Self::V {
        SpecCertificateStatus {
            status_type: self.status_type@,
            response: self.response@,
        }
    }
}
pub type CertificateStatusInner<'a> = (u8, OcspResponse<'a>);
impl<'a> From<CertificateStatus<'a>> for CertificateStatusInner<'a> {
    fn ex_from(m: CertificateStatus) -> CertificateStatusInner {
        (m.status_type, m.response)
    }
}
impl<'a> From<CertificateStatusInner<'a>> for CertificateStatus<'a> {
    fn ex_from(m: CertificateStatusInner) -> CertificateStatus {
        let (status_type, response) = m;
        CertificateStatus { status_type, response }
    }
}

pub struct CertificateStatusMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateStatusMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateStatusMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateStatusMapper(PhantomData)
    }
}
impl View for CertificateStatusMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusMapper<'_> {
    type Src = SpecCertificateStatusInner;
    type Dst = SpecCertificateStatus;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateStatusMapper<'a> {
    type Src = CertificateStatusInner<'a>;
    type Dst = CertificateStatus<'a>;
}
pub const CERTIFICATESTATUS_STATUS_TYPE: u8 = 1;

pub struct SpecCertificateStatusCombinator(SpecCertificateStatusCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusCombinator {
    type SpecResult = SpecCertificateStatus;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateStatusCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateStatusCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, SpecOcspResponseCombinator), CertificateStatusMapper<'static>>;

pub struct CertificateStatusCombinator<'a>(CertificateStatusCombinatorAlias<'a>);

impl<'a> View for CertificateStatusCombinator<'a> {
    type V = SpecCertificateStatusCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateStatusCombinator<'a> {
    type Result = CertificateStatus<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateStatusCombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, OcspResponseCombinator<'a>), CertificateStatusMapper<'a>>;


pub closed spec fn spec_certificate_status() -> SpecCertificateStatusCombinator {
    SpecCertificateStatusCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, spec_ocsp_response()),
        mapper: CertificateStatusMapper::spec_new(),
    })
}

                
pub fn certificate_status<'a>() -> (o: CertificateStatusCombinator<'a>)
    ensures o@ == spec_certificate_status(),
{
    CertificateStatusCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, ocsp_response()),
        mapper: CertificateStatusMapper::new(),
    })
}

                

pub struct SpecUncompressedPointRepresentation48 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}

pub type SpecUncompressedPointRepresentation48Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation48> for SpecUncompressedPointRepresentation48Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation48) -> SpecUncompressedPointRepresentation48Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation48Inner> for SpecUncompressedPointRepresentation48 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation48Inner) -> SpecUncompressedPointRepresentation48 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation48 { legacy_form, x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct UncompressedPointRepresentation48<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}

impl View for UncompressedPointRepresentation48<'_> {
    type V = SpecUncompressedPointRepresentation48;

    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation48 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type UncompressedPointRepresentation48Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl<'a> From<UncompressedPointRepresentation48<'a>> for UncompressedPointRepresentation48Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation48) -> UncompressedPointRepresentation48Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation48Inner<'a>> for UncompressedPointRepresentation48<'a> {
    fn ex_from(m: UncompressedPointRepresentation48Inner) -> UncompressedPointRepresentation48 {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation48 { legacy_form, x, y }
    }
}

pub struct UncompressedPointRepresentation48Mapper<'a>(PhantomData<&'a ()>);
impl<'a> UncompressedPointRepresentation48Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        UncompressedPointRepresentation48Mapper(PhantomData)
    }
    pub fn new() -> Self {
        UncompressedPointRepresentation48Mapper(PhantomData)
    }
}
impl View for UncompressedPointRepresentation48Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation48Mapper<'_> {
    type Src = SpecUncompressedPointRepresentation48Inner;
    type Dst = SpecUncompressedPointRepresentation48;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for UncompressedPointRepresentation48Mapper<'a> {
    type Src = UncompressedPointRepresentation48Inner<'a>;
    type Dst = UncompressedPointRepresentation48<'a>;
}
pub const UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation48Combinator(SpecUncompressedPointRepresentation48CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation48Combinator {
    type SpecResult = SpecUncompressedPointRepresentation48;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation48Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation48CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation48CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<48>, BytesN<48>)), UncompressedPointRepresentation48Mapper<'static>>;

pub struct UncompressedPointRepresentation48Combinator<'a>(UncompressedPointRepresentation48CombinatorAlias<'a>);

impl<'a> View for UncompressedPointRepresentation48Combinator<'a> {
    type V = SpecUncompressedPointRepresentation48Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation48Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UncompressedPointRepresentation48Combinator<'a> {
    type Result = UncompressedPointRepresentation48<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UncompressedPointRepresentation48CombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<48>, BytesN<48>)), UncompressedPointRepresentation48Mapper<'a>>;


pub closed spec fn spec_uncompressed_point_representation48() -> SpecUncompressedPointRepresentation48Combinator {
    SpecUncompressedPointRepresentation48Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)),
        mapper: UncompressedPointRepresentation48Mapper::spec_new(),
    })
}

                
pub fn uncompressed_point_representation48<'a>() -> (o: UncompressedPointRepresentation48Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation48(),
{
    UncompressedPointRepresentation48Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)),
        mapper: UncompressedPointRepresentation48Mapper::new(),
    })
}

                

pub struct SpecEarlyDataIndicationNewSessionTicket {
    pub max_early_data_size: u32,
}

pub type SpecEarlyDataIndicationNewSessionTicketInner = u32;
impl SpecFrom<SpecEarlyDataIndicationNewSessionTicket> for SpecEarlyDataIndicationNewSessionTicketInner {
    open spec fn spec_from(m: SpecEarlyDataIndicationNewSessionTicket) -> SpecEarlyDataIndicationNewSessionTicketInner {
        m.max_early_data_size
    }
}
impl SpecFrom<SpecEarlyDataIndicationNewSessionTicketInner> for SpecEarlyDataIndicationNewSessionTicket {
    open spec fn spec_from(m: SpecEarlyDataIndicationNewSessionTicketInner) -> SpecEarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        SpecEarlyDataIndicationNewSessionTicket { max_early_data_size }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EarlyDataIndicationNewSessionTicket {
    pub max_early_data_size: u32,
}

impl View for EarlyDataIndicationNewSessionTicket {
    type V = SpecEarlyDataIndicationNewSessionTicket;

    open spec fn view(&self) -> Self::V {
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size: self.max_early_data_size@,
        }
    }
}
pub type EarlyDataIndicationNewSessionTicketInner = u32;
impl From<EarlyDataIndicationNewSessionTicket> for EarlyDataIndicationNewSessionTicketInner {
    fn ex_from(m: EarlyDataIndicationNewSessionTicket) -> EarlyDataIndicationNewSessionTicketInner {
        m.max_early_data_size
    }
}
impl From<EarlyDataIndicationNewSessionTicketInner> for EarlyDataIndicationNewSessionTicket {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketInner) -> EarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        EarlyDataIndicationNewSessionTicket { max_early_data_size }
    }
}

pub struct EarlyDataIndicationNewSessionTicketMapper;
impl EarlyDataIndicationNewSessionTicketMapper {
    pub closed spec fn spec_new() -> Self {
        EarlyDataIndicationNewSessionTicketMapper
    }
    pub fn new() -> Self {
        EarlyDataIndicationNewSessionTicketMapper
    }
}
impl View for EarlyDataIndicationNewSessionTicketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EarlyDataIndicationNewSessionTicketMapper {
    type Src = SpecEarlyDataIndicationNewSessionTicketInner;
    type Dst = SpecEarlyDataIndicationNewSessionTicket;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for EarlyDataIndicationNewSessionTicketMapper {
    type Src = EarlyDataIndicationNewSessionTicketInner;
    type Dst = EarlyDataIndicationNewSessionTicket;
}

pub struct SpecEarlyDataIndicationNewSessionTicketCombinator(SpecEarlyDataIndicationNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    type SpecResult = SpecEarlyDataIndicationNewSessionTicket;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEarlyDataIndicationNewSessionTicketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;

pub struct EarlyDataIndicationNewSessionTicketCombinator(EarlyDataIndicationNewSessionTicketCombinatorAlias);

impl View for EarlyDataIndicationNewSessionTicketCombinator {
    type V = SpecEarlyDataIndicationNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecEarlyDataIndicationNewSessionTicketCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EarlyDataIndicationNewSessionTicketCombinator {
    type Result = EarlyDataIndicationNewSessionTicket;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;


pub closed spec fn spec_early_data_indication_new_session_ticket() -> SpecEarlyDataIndicationNewSessionTicketCombinator {
    SpecEarlyDataIndicationNewSessionTicketCombinator(
    Mapped {
        inner: U32Be,
        mapper: EarlyDataIndicationNewSessionTicketMapper::spec_new(),
    })
}

                
pub fn early_data_indication_new_session_ticket() -> (o: EarlyDataIndicationNewSessionTicketCombinator)
    ensures o@ == spec_early_data_indication_new_session_ticket(),
{
    EarlyDataIndicationNewSessionTicketCombinator(
    Mapped {
        inner: U32Be,
        mapper: EarlyDataIndicationNewSessionTicketMapper::new(),
    })
}

                

pub enum SpecNewSessionTicketExtensionExtensionData {
    EarlyData(SpecEarlyDataIndicationNewSessionTicket),
    Unrecognized(Seq<u8>),
}

pub type SpecNewSessionTicketExtensionExtensionDataInner = Either<SpecEarlyDataIndicationNewSessionTicket, Seq<u8>>;



impl SpecFrom<SpecNewSessionTicketExtensionExtensionData> for SpecNewSessionTicketExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionExtensionData) -> SpecNewSessionTicketExtensionExtensionDataInner {
        match m {
            SpecNewSessionTicketExtensionExtensionData::EarlyData(m) => Either::Left(m),
            SpecNewSessionTicketExtensionExtensionData::Unrecognized(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecNewSessionTicketExtensionExtensionDataInner> for SpecNewSessionTicketExtensionExtensionData {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionExtensionDataInner) -> SpecNewSessionTicketExtensionExtensionData {
        match m {
            Either::Left(m) => SpecNewSessionTicketExtensionExtensionData::EarlyData(m),
            Either::Right(m) => SpecNewSessionTicketExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NewSessionTicketExtensionExtensionData<'a> {
    EarlyData(EarlyDataIndicationNewSessionTicket),
    Unrecognized(&'a [u8]),
}

pub type NewSessionTicketExtensionExtensionDataInner<'a> = Either<EarlyDataIndicationNewSessionTicket, &'a [u8]>;


impl<'a> View for NewSessionTicketExtensionExtensionData<'a> {
    type V = SpecNewSessionTicketExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            NewSessionTicketExtensionExtensionData::EarlyData(m) => SpecNewSessionTicketExtensionExtensionData::EarlyData(m@),
            NewSessionTicketExtensionExtensionData::Unrecognized(m) => SpecNewSessionTicketExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<NewSessionTicketExtensionExtensionData<'a>> for NewSessionTicketExtensionExtensionDataInner<'a> {
    fn ex_from(m: NewSessionTicketExtensionExtensionData<'a>) -> NewSessionTicketExtensionExtensionDataInner<'a> {
        match m {
            NewSessionTicketExtensionExtensionData::EarlyData(m) => Either::Left(m),
            NewSessionTicketExtensionExtensionData::Unrecognized(m) => Either::Right(m),
        }
    }

}

impl<'a> From<NewSessionTicketExtensionExtensionDataInner<'a>> for NewSessionTicketExtensionExtensionData<'a> {
    fn ex_from(m: NewSessionTicketExtensionExtensionDataInner<'a>) -> NewSessionTicketExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => NewSessionTicketExtensionExtensionData::EarlyData(m),
            Either::Right(m) => NewSessionTicketExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct NewSessionTicketExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        NewSessionTicketExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        NewSessionTicketExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for NewSessionTicketExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionExtensionDataMapper<'_> {
    type Src = SpecNewSessionTicketExtensionExtensionDataInner;
    type Dst = SpecNewSessionTicketExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for NewSessionTicketExtensionExtensionDataMapper<'a> {
    type Src = NewSessionTicketExtensionExtensionDataInner<'a>;
    type Dst = NewSessionTicketExtensionExtensionData<'a>;
}


pub struct SpecNewSessionTicketExtensionExtensionDataCombinator(SpecNewSessionTicketExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionExtensionDataCombinator {
    type SpecResult = SpecNewSessionTicketExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecEarlyDataIndicationNewSessionTicketCombinator>, Cond<Bytes>>, NewSessionTicketExtensionExtensionDataMapper<'static>>>;

pub struct NewSessionTicketExtensionExtensionDataCombinator<'a>(NewSessionTicketExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for NewSessionTicketExtensionExtensionDataCombinator<'a> {
    type V = SpecNewSessionTicketExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NewSessionTicketExtensionExtensionDataCombinator<'a> {
    type Result = NewSessionTicketExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NewSessionTicketExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<EarlyDataIndicationNewSessionTicketCombinator>, Cond<Bytes>>, NewSessionTicketExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_new_session_ticket_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecNewSessionTicketExtensionExtensionDataCombinator {
    SpecNewSessionTicketExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 42, inner: spec_early_data_indication_new_session_ticket() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) }), mapper: NewSessionTicketExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn new_session_ticket_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: NewSessionTicketExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extension_extension_data(ext_len@, extension_type@),
{
    NewSessionTicketExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 42, inner: early_data_indication_new_session_ticket() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) }), mapper: NewSessionTicketExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecNewSessionTicketExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecNewSessionTicketExtensionExtensionData,
}

pub type SpecNewSessionTicketExtensionInner = ((SpecExtensionType, u16), SpecNewSessionTicketExtensionExtensionData);
impl SpecFrom<SpecNewSessionTicketExtension> for SpecNewSessionTicketExtensionInner {
    open spec fn spec_from(m: SpecNewSessionTicketExtension) -> SpecNewSessionTicketExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecNewSessionTicketExtensionInner> for SpecNewSessionTicketExtension {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionInner) -> SpecNewSessionTicketExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecNewSessionTicketExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NewSessionTicketExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: NewSessionTicketExtensionExtensionData<'a>,
}

impl View for NewSessionTicketExtension<'_> {
    type V = SpecNewSessionTicketExtension;

    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type NewSessionTicketExtensionInner<'a> = ((ExtensionType, u16), NewSessionTicketExtensionExtensionData<'a>);
impl<'a> From<NewSessionTicketExtension<'a>> for NewSessionTicketExtensionInner<'a> {
    fn ex_from(m: NewSessionTicketExtension) -> NewSessionTicketExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<NewSessionTicketExtensionInner<'a>> for NewSessionTicketExtension<'a> {
    fn ex_from(m: NewSessionTicketExtensionInner) -> NewSessionTicketExtension {
        let ((extension_type, ext_len), extension_data) = m;
        NewSessionTicketExtension { extension_type, ext_len, extension_data }
    }
}

pub struct NewSessionTicketExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        NewSessionTicketExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        NewSessionTicketExtensionMapper(PhantomData)
    }
}
impl View for NewSessionTicketExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionMapper<'_> {
    type Src = SpecNewSessionTicketExtensionInner;
    type Dst = SpecNewSessionTicketExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for NewSessionTicketExtensionMapper<'a> {
    type Src = NewSessionTicketExtensionInner<'a>;
    type Dst = NewSessionTicketExtension<'a>;
}

pub struct SpecNewSessionTicketExtensionCombinator(SpecNewSessionTicketExtensionCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionCombinator {
    type SpecResult = SpecNewSessionTicketExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecNewSessionTicketExtensionExtensionDataCombinator>, NewSessionTicketExtensionMapper<'static>>;

pub struct NewSessionTicketExtensionCombinator<'a>(NewSessionTicketExtensionCombinatorAlias<'a>);

impl<'a> View for NewSessionTicketExtensionCombinator<'a> {
    type V = SpecNewSessionTicketExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NewSessionTicketExtensionCombinator<'a> {
    type Result = NewSessionTicketExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NewSessionTicketExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, NewSessionTicketExtensionCont1<'a>>, NewSessionTicketExtensionExtensionDataCombinator<'a>, NewSessionTicketExtensionCont0<'a>>, NewSessionTicketExtensionMapper<'a>>;


pub closed spec fn spec_new_session_ticket_extension() -> SpecNewSessionTicketExtensionCombinator {
    SpecNewSessionTicketExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_new_session_ticket_extension_cont1(deps) }, snd: |deps| spec_new_session_ticket_extension_cont0(deps) },
        mapper: NewSessionTicketExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_new_session_ticket_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_new_session_ticket_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecNewSessionTicketExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_new_session_ticket_extension_extension_data(ext_len, extension_type)
}
                
pub fn new_session_ticket_extension<'a>() -> (o: NewSessionTicketExtensionCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extension(),
{
    NewSessionTicketExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: NewSessionTicketExtensionCont1::new(), spec_snd: Ghost(|deps| spec_new_session_ticket_extension_cont1(deps)) }, snd: NewSessionTicketExtensionCont0::new(), spec_snd: Ghost(|deps| spec_new_session_ticket_extension_cont0(deps)) },
        mapper: NewSessionTicketExtensionMapper::new(),
    })
}

pub struct NewSessionTicketExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionCont1<'a> {
    pub fn new() -> Self {
        NewSessionTicketExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for NewSessionTicketExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct NewSessionTicketExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionCont0<'a> {
    pub fn new() -> Self {
        NewSessionTicketExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for NewSessionTicketExtensionCont0<'a> {
    type Output = NewSessionTicketExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        new_session_ticket_extension_extension_data(ext_len, extension_type)
    }
}
                
pub type SpecNewSessionTicketExtensionsExtensions = Seq<SpecNewSessionTicketExtension>;
pub type NewSessionTicketExtensionsExtensions<'a> = RepeatResult<NewSessionTicketExtension<'a>>;


pub struct SpecNewSessionTicketExtensionsExtensionsCombinator(SpecNewSessionTicketExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionsExtensionsCombinator {
    type SpecResult = SpecNewSessionTicketExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecNewSessionTicketExtensionCombinator>>;

pub struct NewSessionTicketExtensionsExtensionsCombinator<'a>(NewSessionTicketExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for NewSessionTicketExtensionsExtensionsCombinator<'a> {
    type V = SpecNewSessionTicketExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NewSessionTicketExtensionsExtensionsCombinator<'a> {
    type Result = NewSessionTicketExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NewSessionTicketExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<NewSessionTicketExtensionCombinator<'a>>>;


pub closed spec fn spec_new_session_ticket_extensions_extensions(l: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    SpecNewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_new_session_ticket_extension())))
}

                
pub fn new_session_ticket_extensions_extensions<'a>(l: Uint0Fffe) -> (o: NewSessionTicketExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extensions_extensions(l@),
{
    NewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(new_session_ticket_extension())))
}

                

pub struct SpecExtension {
    pub extension_type: SpecExtensionType,
    pub extension_data: SpecOpaque0Ffff,
}

pub type SpecExtensionInner = (SpecExtensionType, SpecOpaque0Ffff);
impl SpecFrom<SpecExtension> for SpecExtensionInner {
    open spec fn spec_from(m: SpecExtension) -> SpecExtensionInner {
        (m.extension_type, m.extension_data)
    }
}
impl SpecFrom<SpecExtensionInner> for SpecExtension {
    open spec fn spec_from(m: SpecExtensionInner) -> SpecExtension {
        let (extension_type, extension_data) = m;
        SpecExtension { extension_type, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Extension<'a> {
    pub extension_type: ExtensionType,
    pub extension_data: Opaque0Ffff<'a>,
}

impl View for Extension<'_> {
    type V = SpecExtension;

    open spec fn view(&self) -> Self::V {
        SpecExtension {
            extension_type: self.extension_type@,
            extension_data: self.extension_data@,
        }
    }
}
pub type ExtensionInner<'a> = (ExtensionType, Opaque0Ffff<'a>);
impl<'a> From<Extension<'a>> for ExtensionInner<'a> {
    fn ex_from(m: Extension) -> ExtensionInner {
        (m.extension_type, m.extension_data)
    }
}
impl<'a> From<ExtensionInner<'a>> for Extension<'a> {
    fn ex_from(m: ExtensionInner) -> Extension {
        let (extension_type, extension_data) = m;
        Extension { extension_type, extension_data }
    }
}

pub struct ExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> ExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        ExtensionMapper(PhantomData)
    }
}
impl View for ExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExtensionMapper<'_> {
    type Src = SpecExtensionInner;
    type Dst = SpecExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ExtensionMapper<'a> {
    type Src = ExtensionInner<'a>;
    type Dst = Extension<'a>;
}

pub struct SpecExtensionCombinator(SpecExtensionCombinatorAlias);

impl SpecCombinator for SpecExtensionCombinator {
    type SpecResult = SpecExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecExtensionCombinatorAlias = Mapped<(SpecExtensionTypeCombinator, SpecOpaque0FfffCombinator), ExtensionMapper<'static>>;

pub struct ExtensionCombinator<'a>(ExtensionCombinatorAlias<'a>);

impl<'a> View for ExtensionCombinator<'a> {
    type V = SpecExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ExtensionCombinator<'a> {
    type Result = Extension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ExtensionCombinatorAlias<'a> = Mapped<(ExtensionTypeCombinator, Opaque0FfffCombinator<'a>), ExtensionMapper<'a>>;


pub closed spec fn spec_extension() -> SpecExtensionCombinator {
    SpecExtensionCombinator(
    Mapped {
        inner: (spec_extension_type(), spec_opaque_0_ffff()),
        mapper: ExtensionMapper::spec_new(),
    })
}

                
pub fn extension<'a>() -> (o: ExtensionCombinator<'a>)
    ensures o@ == spec_extension(),
{
    ExtensionCombinator(
    Mapped {
        inner: (extension_type(), opaque_0_ffff()),
        mapper: ExtensionMapper::new(),
    })
}

                
pub type SpecCipherSuiteListList = Seq<SpecCipherSuite>;
pub type CipherSuiteListList = RepeatResult<CipherSuite>;


pub struct SpecCipherSuiteListListCombinator(SpecCipherSuiteListListCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteListListCombinator {
    type SpecResult = SpecCipherSuiteListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteListListCombinatorAlias = AndThen<Bytes, Repeat<SpecCipherSuiteCombinator>>;

pub struct CipherSuiteListListCombinator(CipherSuiteListListCombinatorAlias);

impl View for CipherSuiteListListCombinator {
    type V = SpecCipherSuiteListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CipherSuiteListListCombinator {
    type Result = CipherSuiteListList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CipherSuiteListListCombinatorAlias = AndThen<Bytes, Repeat<CipherSuiteCombinator>>;


pub closed spec fn spec_cipher_suite_list_list(l: SpecUint2Fffe) -> SpecCipherSuiteListListCombinator {
    SpecCipherSuiteListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_cipher_suite())))
}

                
pub fn cipher_suite_list_list<'a>(l: Uint2Fffe) -> (o: CipherSuiteListListCombinator)
    ensures o@ == spec_cipher_suite_list_list(l@),
{
    CipherSuiteListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(cipher_suite())))
}

                

pub struct SpecCipherSuiteList {
    pub l: SpecUint2Fffe,
    pub list: SpecCipherSuiteListList,
}

pub type SpecCipherSuiteListInner = (SpecUint2Fffe, SpecCipherSuiteListList);
impl SpecFrom<SpecCipherSuiteList> for SpecCipherSuiteListInner {
    open spec fn spec_from(m: SpecCipherSuiteList) -> SpecCipherSuiteListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecCipherSuiteListInner> for SpecCipherSuiteList {
    open spec fn spec_from(m: SpecCipherSuiteListInner) -> SpecCipherSuiteList {
        let (l, list) = m;
        SpecCipherSuiteList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CipherSuiteList {
    pub l: Uint2Fffe,
    pub list: CipherSuiteListList,
}

impl View for CipherSuiteList {
    type V = SpecCipherSuiteList;

    open spec fn view(&self) -> Self::V {
        SpecCipherSuiteList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type CipherSuiteListInner = (Uint2Fffe, CipherSuiteListList);
impl From<CipherSuiteList> for CipherSuiteListInner {
    fn ex_from(m: CipherSuiteList) -> CipherSuiteListInner {
        (m.l, m.list)
    }
}
impl From<CipherSuiteListInner> for CipherSuiteList {
    fn ex_from(m: CipherSuiteListInner) -> CipherSuiteList {
        let (l, list) = m;
        CipherSuiteList { l, list }
    }
}

pub struct CipherSuiteListMapper;
impl CipherSuiteListMapper {
    pub closed spec fn spec_new() -> Self {
        CipherSuiteListMapper
    }
    pub fn new() -> Self {
        CipherSuiteListMapper
    }
}
impl View for CipherSuiteListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CipherSuiteListMapper {
    type Src = SpecCipherSuiteListInner;
    type Dst = SpecCipherSuiteList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for CipherSuiteListMapper {
    type Src = CipherSuiteListInner;
    type Dst = CipherSuiteList;
}

pub struct SpecCipherSuiteListCombinator(SpecCipherSuiteListCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteListCombinator {
    type SpecResult = SpecCipherSuiteList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteListCombinatorAlias = Mapped<SpecDepend<SpecUint2FffeCombinator, SpecCipherSuiteListListCombinator>, CipherSuiteListMapper>;

pub struct CipherSuiteListCombinator<'a>(CipherSuiteListCombinatorAlias<'a>);

impl<'a> View for CipherSuiteListCombinator<'a> {
    type V = SpecCipherSuiteListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CipherSuiteListCombinator<'a> {
    type Result = CipherSuiteList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CipherSuiteListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FffeCombinator, CipherSuiteListListCombinator, CipherSuiteListCont0<'a>>, CipherSuiteListMapper>;


pub closed spec fn spec_cipher_suite_list() -> SpecCipherSuiteListCombinator {
    SpecCipherSuiteListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_fffe(), snd: |deps| spec_cipher_suite_list_cont0(deps) },
        mapper: CipherSuiteListMapper::spec_new(),
    })
}

pub open spec fn spec_cipher_suite_list_cont0(deps: SpecUint2Fffe) -> SpecCipherSuiteListListCombinator {
    let l = deps;
    spec_cipher_suite_list_list(l)
}
                
pub fn cipher_suite_list<'a>() -> (o: CipherSuiteListCombinator<'a>)
    ensures o@ == spec_cipher_suite_list(),
{
    CipherSuiteListCombinator(
    Mapped {
        inner: Depend { fst: uint_2_fffe(), snd: CipherSuiteListCont0::new(), spec_snd: Ghost(|deps| spec_cipher_suite_list_cont0(deps)) },
        mapper: CipherSuiteListMapper::new(),
    })
}

pub struct CipherSuiteListCont0<'a>(PhantomData<&'a ()>);
impl<'a> CipherSuiteListCont0<'a> {
    pub fn new() -> Self {
        CipherSuiteListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Fffe> for CipherSuiteListCont0<'a> {
    type Output = CipherSuiteListListCombinator;

    open spec fn requires(&self, deps: &Uint2Fffe) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_cipher_suite_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Fffe) -> Self::Output {
        let l = *deps;
        cipher_suite_list_list(l)
    }
}
                
pub type SpecNameType = u8;
pub type NameType = u8;


pub struct SpecNameTypeCombinator(SpecNameTypeCombinatorAlias);

impl SpecCombinator for SpecNameTypeCombinator {
    type SpecResult = SpecNameType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNameTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNameTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNameTypeCombinatorAlias = U8;

pub struct NameTypeCombinator(NameTypeCombinatorAlias);

impl View for NameTypeCombinator {
    type V = SpecNameTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecNameTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NameTypeCombinator {
    type Result = NameType;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NameTypeCombinatorAlias = U8;


pub closed spec fn spec_name_type() -> SpecNameTypeCombinator {
    SpecNameTypeCombinator(U8)
}

                
pub fn name_type() -> (o: NameTypeCombinator)
    ensures o@ == spec_name_type(),
{
    NameTypeCombinator(U8)
}

                
pub type SpecHostName = SpecOpaque1Ffff;
pub type HostName<'a> = Opaque1Ffff<'a>;


pub struct SpecHostNameCombinator(SpecHostNameCombinatorAlias);

impl SpecCombinator for SpecHostNameCombinator {
    type SpecResult = SpecHostName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHostNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHostNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHostNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct HostNameCombinator<'a>(HostNameCombinatorAlias<'a>);

impl<'a> View for HostNameCombinator<'a> {
    type V = SpecHostNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecHostNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HostNameCombinator<'a> {
    type Result = HostName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HostNameCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_host_name() -> SpecHostNameCombinator {
    SpecHostNameCombinator(spec_opaque_1_ffff())
}

                
pub fn host_name<'a>() -> (o: HostNameCombinator<'a>)
    ensures o@ == spec_host_name(),
{
    HostNameCombinator(opaque_1_ffff())
}

                
pub type SpecUnknownName = SpecOpaque1Ffff;
pub type UnknownName<'a> = Opaque1Ffff<'a>;


pub struct SpecUnknownNameCombinator(SpecUnknownNameCombinatorAlias);

impl SpecCombinator for SpecUnknownNameCombinator {
    type SpecResult = SpecUnknownName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUnknownNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUnknownNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct UnknownNameCombinator<'a>(UnknownNameCombinatorAlias<'a>);

impl<'a> View for UnknownNameCombinator<'a> {
    type V = SpecUnknownNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UnknownNameCombinator<'a> {
    type Result = UnknownName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UnknownNameCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_unknown_name() -> SpecUnknownNameCombinator {
    SpecUnknownNameCombinator(spec_opaque_1_ffff())
}

                
pub fn unknown_name<'a>() -> (o: UnknownNameCombinator<'a>)
    ensures o@ == spec_unknown_name(),
{
    UnknownNameCombinator(opaque_1_ffff())
}

                

pub enum SpecServerNameName {
    HostName(SpecHostName),
    Unrecognized(SpecUnknownName),
}

pub type SpecServerNameNameInner = Either<SpecHostName, SpecUnknownName>;



impl SpecFrom<SpecServerNameName> for SpecServerNameNameInner {
    open spec fn spec_from(m: SpecServerNameName) -> SpecServerNameNameInner {
        match m {
            SpecServerNameName::HostName(m) => Either::Left(m),
            SpecServerNameName::Unrecognized(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecServerNameNameInner> for SpecServerNameName {
    open spec fn spec_from(m: SpecServerNameNameInner) -> SpecServerNameName {
        match m {
            Either::Left(m) => SpecServerNameName::HostName(m),
            Either::Right(m) => SpecServerNameName::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ServerNameName<'a> {
    HostName(HostName<'a>),
    Unrecognized(UnknownName<'a>),
}

pub type ServerNameNameInner<'a> = Either<HostName<'a>, UnknownName<'a>>;


impl<'a> View for ServerNameName<'a> {
    type V = SpecServerNameName;
    open spec fn view(&self) -> Self::V {
        match self {
            ServerNameName::HostName(m) => SpecServerNameName::HostName(m@),
            ServerNameName::Unrecognized(m) => SpecServerNameName::Unrecognized(m@),
        }
    }
}


impl<'a> From<ServerNameName<'a>> for ServerNameNameInner<'a> {
    fn ex_from(m: ServerNameName<'a>) -> ServerNameNameInner<'a> {
        match m {
            ServerNameName::HostName(m) => Either::Left(m),
            ServerNameName::Unrecognized(m) => Either::Right(m),
        }
    }

}

impl<'a> From<ServerNameNameInner<'a>> for ServerNameName<'a> {
    fn ex_from(m: ServerNameNameInner<'a>) -> ServerNameName<'a> {
        match m {
            Either::Left(m) => ServerNameName::HostName(m),
            Either::Right(m) => ServerNameName::Unrecognized(m),
        }
    }
    
}


pub struct ServerNameNameMapper<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameNameMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ServerNameNameMapper(PhantomData)
    }
    pub fn new() -> Self {
        ServerNameNameMapper(PhantomData)
    }
}
impl View for ServerNameNameMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameNameMapper<'_> {
    type Src = SpecServerNameNameInner;
    type Dst = SpecServerNameName;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ServerNameNameMapper<'a> {
    type Src = ServerNameNameInner<'a>;
    type Dst = ServerNameName<'a>;
}


pub struct SpecServerNameNameCombinator(SpecServerNameNameCombinatorAlias);

impl SpecCombinator for SpecServerNameNameCombinator {
    type SpecResult = SpecServerNameName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameNameCombinatorAlias = Mapped<OrdChoice<Cond<SpecHostNameCombinator>, Cond<SpecUnknownNameCombinator>>, ServerNameNameMapper<'static>>;

pub struct ServerNameNameCombinator<'a>(ServerNameNameCombinatorAlias<'a>);

impl<'a> View for ServerNameNameCombinator<'a> {
    type V = SpecServerNameNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerNameNameCombinator<'a> {
    type Result = ServerNameName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerNameNameCombinatorAlias<'a> = Mapped<OrdChoice<Cond<HostNameCombinator<'a>>, Cond<UnknownNameCombinator<'a>>>, ServerNameNameMapper<'a>>;


pub closed spec fn spec_server_name_name(name_type: SpecNameType) -> SpecServerNameNameCombinator {
    SpecServerNameNameCombinator(Mapped { inner: OrdChoice(Cond { cond: name_type == 0, inner: spec_host_name() }, Cond { cond: !(name_type == 0), inner: spec_unknown_name() }), mapper: ServerNameNameMapper::spec_new() })
}

                
pub fn server_name_name<'a>(name_type: NameType) -> (o: ServerNameNameCombinator<'a>)
    ensures o@ == spec_server_name_name(name_type@),
{
    ServerNameNameCombinator(Mapped { inner: OrdChoice::new(Cond { cond: name_type == 0, inner: host_name() }, Cond { cond: !(name_type == 0), inner: unknown_name() }), mapper: ServerNameNameMapper::new() })
}

                

pub struct SpecServerName {
    pub name_type: SpecNameType,
    pub name: SpecServerNameName,
}

pub type SpecServerNameInner = (SpecNameType, SpecServerNameName);
impl SpecFrom<SpecServerName> for SpecServerNameInner {
    open spec fn spec_from(m: SpecServerName) -> SpecServerNameInner {
        (m.name_type, m.name)
    }
}
impl SpecFrom<SpecServerNameInner> for SpecServerName {
    open spec fn spec_from(m: SpecServerNameInner) -> SpecServerName {
        let (name_type, name) = m;
        SpecServerName { name_type, name }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerName<'a> {
    pub name_type: NameType,
    pub name: ServerNameName<'a>,
}

impl View for ServerName<'_> {
    type V = SpecServerName;

    open spec fn view(&self) -> Self::V {
        SpecServerName {
            name_type: self.name_type@,
            name: self.name@,
        }
    }
}
pub type ServerNameInner<'a> = (NameType, ServerNameName<'a>);
impl<'a> From<ServerName<'a>> for ServerNameInner<'a> {
    fn ex_from(m: ServerName) -> ServerNameInner {
        (m.name_type, m.name)
    }
}
impl<'a> From<ServerNameInner<'a>> for ServerName<'a> {
    fn ex_from(m: ServerNameInner) -> ServerName {
        let (name_type, name) = m;
        ServerName { name_type, name }
    }
}

pub struct ServerNameMapper<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ServerNameMapper(PhantomData)
    }
    pub fn new() -> Self {
        ServerNameMapper(PhantomData)
    }
}
impl View for ServerNameMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameMapper<'_> {
    type Src = SpecServerNameInner;
    type Dst = SpecServerName;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ServerNameMapper<'a> {
    type Src = ServerNameInner<'a>;
    type Dst = ServerName<'a>;
}

pub struct SpecServerNameCombinator(SpecServerNameCombinatorAlias);

impl SpecCombinator for SpecServerNameCombinator {
    type SpecResult = SpecServerName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameCombinatorAlias = Mapped<SpecDepend<SpecNameTypeCombinator, SpecServerNameNameCombinator>, ServerNameMapper<'static>>;

pub struct ServerNameCombinator<'a>(ServerNameCombinatorAlias<'a>);

impl<'a> View for ServerNameCombinator<'a> {
    type V = SpecServerNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerNameCombinator<'a> {
    type Result = ServerName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerNameCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, NameTypeCombinator, ServerNameNameCombinator<'a>, ServerNameCont0<'a>>, ServerNameMapper<'a>>;


pub closed spec fn spec_server_name() -> SpecServerNameCombinator {
    SpecServerNameCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_name_type(), snd: |deps| spec_server_name_cont0(deps) },
        mapper: ServerNameMapper::spec_new(),
    })
}

pub open spec fn spec_server_name_cont0(deps: SpecNameType) -> SpecServerNameNameCombinator {
    let name_type = deps;
    spec_server_name_name(name_type)
}
                
pub fn server_name<'a>() -> (o: ServerNameCombinator<'a>)
    ensures o@ == spec_server_name(),
{
    ServerNameCombinator(
    Mapped {
        inner: Depend { fst: name_type(), snd: ServerNameCont0::new(), spec_snd: Ghost(|deps| spec_server_name_cont0(deps)) },
        mapper: ServerNameMapper::new(),
    })
}

pub struct ServerNameCont0<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameCont0<'a> {
    pub fn new() -> Self {
        ServerNameCont0(PhantomData)
    }
}
impl<'a> Continuation<&NameType> for ServerNameCont0<'a> {
    type Output = ServerNameNameCombinator<'a>;

    open spec fn requires(&self, deps: &NameType) -> bool { true }

    open spec fn ensures(&self, deps: &NameType, o: Self::Output) -> bool {
        o@ == spec_server_name_cont0(deps@)
    }

    fn apply(&self, deps: &NameType) -> Self::Output {
        let name_type = *deps;
        server_name_name(name_type)
    }
}
                
pub type SpecServerNameListList = Seq<SpecServerName>;
pub type ServerNameListList<'a> = RepeatResult<ServerName<'a>>;


pub struct SpecServerNameListListCombinator(SpecServerNameListListCombinatorAlias);

impl SpecCombinator for SpecServerNameListListCombinator {
    type SpecResult = SpecServerNameListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameListListCombinatorAlias = AndThen<Bytes, Repeat<SpecServerNameCombinator>>;

pub struct ServerNameListListCombinator<'a>(ServerNameListListCombinatorAlias<'a>);

impl<'a> View for ServerNameListListCombinator<'a> {
    type V = SpecServerNameListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerNameListListCombinator<'a> {
    type Result = ServerNameListList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerNameListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<ServerNameCombinator<'a>>>;


pub closed spec fn spec_server_name_list_list(l: SpecUint1Ffff) -> SpecServerNameListListCombinator {
    SpecServerNameListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_server_name())))
}

                
pub fn server_name_list_list<'a>(l: Uint1Ffff) -> (o: ServerNameListListCombinator<'a>)
    ensures o@ == spec_server_name_list_list(l@),
{
    ServerNameListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(server_name())))
}

                

pub struct SpecServerNameList {
    pub l: SpecUint1Ffff,
    pub list: SpecServerNameListList,
}

pub type SpecServerNameListInner = (SpecUint1Ffff, SpecServerNameListList);
impl SpecFrom<SpecServerNameList> for SpecServerNameListInner {
    open spec fn spec_from(m: SpecServerNameList) -> SpecServerNameListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecServerNameListInner> for SpecServerNameList {
    open spec fn spec_from(m: SpecServerNameListInner) -> SpecServerNameList {
        let (l, list) = m;
        SpecServerNameList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerNameList<'a> {
    pub l: Uint1Ffff,
    pub list: ServerNameListList<'a>,
}

impl View for ServerNameList<'_> {
    type V = SpecServerNameList;

    open spec fn view(&self) -> Self::V {
        SpecServerNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ServerNameListInner<'a> = (Uint1Ffff, ServerNameListList<'a>);
impl<'a> From<ServerNameList<'a>> for ServerNameListInner<'a> {
    fn ex_from(m: ServerNameList) -> ServerNameListInner {
        (m.l, m.list)
    }
}
impl<'a> From<ServerNameListInner<'a>> for ServerNameList<'a> {
    fn ex_from(m: ServerNameListInner) -> ServerNameList {
        let (l, list) = m;
        ServerNameList { l, list }
    }
}

pub struct ServerNameListMapper<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameListMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ServerNameListMapper(PhantomData)
    }
    pub fn new() -> Self {
        ServerNameListMapper(PhantomData)
    }
}
impl View for ServerNameListMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameListMapper<'_> {
    type Src = SpecServerNameListInner;
    type Dst = SpecServerNameList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ServerNameListMapper<'a> {
    type Src = ServerNameListInner<'a>;
    type Dst = ServerNameList<'a>;
}

pub struct SpecServerNameListCombinator(SpecServerNameListCombinatorAlias);

impl SpecCombinator for SpecServerNameListCombinator {
    type SpecResult = SpecServerNameList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, SpecServerNameListListCombinator>, ServerNameListMapper<'static>>;

pub struct ServerNameListCombinator<'a>(ServerNameListCombinatorAlias<'a>);

impl<'a> View for ServerNameListCombinator<'a> {
    type V = SpecServerNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerNameListCombinator<'a> {
    type Result = ServerNameList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerNameListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, ServerNameListListCombinator<'a>, ServerNameListCont0<'a>>, ServerNameListMapper<'a>>;


pub closed spec fn spec_server_name_list() -> SpecServerNameListCombinator {
    SpecServerNameListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ffff(), snd: |deps| spec_server_name_list_cont0(deps) },
        mapper: ServerNameListMapper::spec_new(),
    })
}

pub open spec fn spec_server_name_list_cont0(deps: SpecUint1Ffff) -> SpecServerNameListListCombinator {
    let l = deps;
    spec_server_name_list_list(l)
}
                
pub fn server_name_list<'a>() -> (o: ServerNameListCombinator<'a>)
    ensures o@ == spec_server_name_list(),
{
    ServerNameListCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ffff(), snd: ServerNameListCont0::new(), spec_snd: Ghost(|deps| spec_server_name_list_cont0(deps)) },
        mapper: ServerNameListMapper::new(),
    })
}

pub struct ServerNameListCont0<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameListCont0<'a> {
    pub fn new() -> Self {
        ServerNameListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ffff> for ServerNameListCont0<'a> {
    type Output = ServerNameListListCombinator<'a>;

    open spec fn requires(&self, deps: &Uint1Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_server_name_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ffff) -> Self::Output {
        let l = *deps;
        server_name_list_list(l)
    }
}
                
pub type SpecMaxFragmentLength = u8;
pub type MaxFragmentLength = u8;


pub struct SpecMaxFragmentLengthCombinator(SpecMaxFragmentLengthCombinatorAlias);

impl SpecCombinator for SpecMaxFragmentLengthCombinator {
    type SpecResult = SpecMaxFragmentLength;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMaxFragmentLengthCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMaxFragmentLengthCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMaxFragmentLengthCombinatorAlias = U8;

pub struct MaxFragmentLengthCombinator(MaxFragmentLengthCombinatorAlias);

impl View for MaxFragmentLengthCombinator {
    type V = SpecMaxFragmentLengthCombinator;
    closed spec fn view(&self) -> Self::V { SpecMaxFragmentLengthCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MaxFragmentLengthCombinator {
    type Result = MaxFragmentLength;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MaxFragmentLengthCombinatorAlias = U8;


pub closed spec fn spec_max_fragment_length() -> SpecMaxFragmentLengthCombinator {
    SpecMaxFragmentLengthCombinator(U8)
}

                
pub fn max_fragment_length() -> (o: MaxFragmentLengthCombinator)
    ensures o@ == spec_max_fragment_length(),
{
    MaxFragmentLengthCombinator(U8)
}

                
pub type SpecResponderId = SpecOpaque1Ffff;
pub type ResponderId<'a> = Opaque1Ffff<'a>;


pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type SpecResult = SpecResponderId;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct ResponderIdCombinator<'a>(ResponderIdCombinatorAlias<'a>);

impl<'a> View for ResponderIdCombinator<'a> {
    type V = SpecResponderIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdCombinator<'a> {
    type Result = ResponderId<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ResponderIdCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_1_ffff())
}

                
pub fn responder_id<'a>() -> (o: ResponderIdCombinator<'a>)
    ensures o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_1_ffff())
}

                
pub type SpecResponderIdListList = Seq<SpecResponderId>;
pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;


pub struct SpecResponderIdListListCombinator(SpecResponderIdListListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListListCombinator {
    type SpecResult = SpecResponderIdListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdListListCombinatorAlias = AndThen<Bytes, Repeat<SpecResponderIdCombinator>>;

pub struct ResponderIdListListCombinator<'a>(ResponderIdListListCombinatorAlias<'a>);

impl<'a> View for ResponderIdListListCombinator<'a> {
    type V = SpecResponderIdListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdListListCombinator<'a> {
    type Result = ResponderIdListList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ResponderIdListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<ResponderIdCombinator<'a>>>;


pub closed spec fn spec_responder_id_list_list(l: SpecUint0Ffff) -> SpecResponderIdListListCombinator {
    SpecResponderIdListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id())))
}

                
pub fn responder_id_list_list<'a>(l: Uint0Ffff) -> (o: ResponderIdListListCombinator<'a>)
    ensures o@ == spec_responder_id_list_list(l@),
{
    ResponderIdListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(responder_id())))
}

                

pub struct SpecResponderIdList {
    pub l: SpecUint0Ffff,
    pub list: SpecResponderIdListList,
}

pub type SpecResponderIdListInner = (SpecUint0Ffff, SpecResponderIdListList);
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
    pub l: Uint0Ffff,
    pub list: ResponderIdListList<'a>,
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
pub type ResponderIdListInner<'a> = (Uint0Ffff, ResponderIdListList<'a>);
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
    type SpecResult = SpecResponderIdList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdListCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecResponderIdListListCombinator>, ResponderIdListMapper<'static>>;

pub struct ResponderIdListCombinator<'a>(ResponderIdListCombinatorAlias<'a>);

impl<'a> View for ResponderIdListCombinator<'a> {
    type V = SpecResponderIdListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ResponderIdListCombinator<'a> {
    type Result = ResponderIdList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ResponderIdListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, ResponderIdListListCombinator<'a>, ResponderIdListCont0<'a>>, ResponderIdListMapper<'a>>;


pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_responder_id_list_cont0(deps) },
        mapper: ResponderIdListMapper::spec_new(),
    })
}

pub open spec fn spec_responder_id_list_cont0(deps: SpecUint0Ffff) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}
                
pub fn responder_id_list<'a>() -> (o: ResponderIdListCombinator<'a>)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: ResponderIdListCont0::new(), spec_snd: Ghost(|deps| spec_responder_id_list_cont0(deps)) },
        mapper: ResponderIdListMapper::new(),
    })
}

pub struct ResponderIdListCont0<'a>(PhantomData<&'a ()>);
impl<'a> ResponderIdListCont0<'a> {
    pub fn new() -> Self {
        ResponderIdListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for ResponderIdListCont0<'a> {
    type Output = ResponderIdListListCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        responder_id_list_list(l)
    }
}
                
pub type SpecOcspExtensions = SpecOpaque0Ffff;
pub type OcspExtensions<'a> = Opaque0Ffff<'a>;


pub struct SpecOcspExtensionsCombinator(SpecOcspExtensionsCombinatorAlias);

impl SpecCombinator for SpecOcspExtensionsCombinator {
    type SpecResult = SpecOcspExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOcspExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOcspExtensionsCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct OcspExtensionsCombinator<'a>(OcspExtensionsCombinatorAlias<'a>);

impl<'a> View for OcspExtensionsCombinator<'a> {
    type V = SpecOcspExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OcspExtensionsCombinator<'a> {
    type Result = OcspExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OcspExtensionsCombinatorAlias<'a> = Opaque0FfffCombinator<'a>;


pub closed spec fn spec_ocsp_extensions() -> SpecOcspExtensionsCombinator {
    SpecOcspExtensionsCombinator(spec_opaque_0_ffff())
}

                
pub fn ocsp_extensions<'a>() -> (o: OcspExtensionsCombinator<'a>)
    ensures o@ == spec_ocsp_extensions(),
{
    OcspExtensionsCombinator(opaque_0_ffff())
}

                

pub struct SpecOscpStatusRequest {
    pub responder_id_list: SpecResponderIdList,
    pub extensions: SpecOcspExtensions,
}

pub type SpecOscpStatusRequestInner = (SpecResponderIdList, SpecOcspExtensions);
impl SpecFrom<SpecOscpStatusRequest> for SpecOscpStatusRequestInner {
    open spec fn spec_from(m: SpecOscpStatusRequest) -> SpecOscpStatusRequestInner {
        (m.responder_id_list, m.extensions)
    }
}
impl SpecFrom<SpecOscpStatusRequestInner> for SpecOscpStatusRequest {
    open spec fn spec_from(m: SpecOscpStatusRequestInner) -> SpecOscpStatusRequest {
        let (responder_id_list, extensions) = m;
        SpecOscpStatusRequest { responder_id_list, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OscpStatusRequest<'a> {
    pub responder_id_list: ResponderIdList<'a>,
    pub extensions: OcspExtensions<'a>,
}

impl View for OscpStatusRequest<'_> {
    type V = SpecOscpStatusRequest;

    open spec fn view(&self) -> Self::V {
        SpecOscpStatusRequest {
            responder_id_list: self.responder_id_list@,
            extensions: self.extensions@,
        }
    }
}
pub type OscpStatusRequestInner<'a> = (ResponderIdList<'a>, OcspExtensions<'a>);
impl<'a> From<OscpStatusRequest<'a>> for OscpStatusRequestInner<'a> {
    fn ex_from(m: OscpStatusRequest) -> OscpStatusRequestInner {
        (m.responder_id_list, m.extensions)
    }
}
impl<'a> From<OscpStatusRequestInner<'a>> for OscpStatusRequest<'a> {
    fn ex_from(m: OscpStatusRequestInner) -> OscpStatusRequest {
        let (responder_id_list, extensions) = m;
        OscpStatusRequest { responder_id_list, extensions }
    }
}

pub struct OscpStatusRequestMapper<'a>(PhantomData<&'a ()>);
impl<'a> OscpStatusRequestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OscpStatusRequestMapper(PhantomData)
    }
    pub fn new() -> Self {
        OscpStatusRequestMapper(PhantomData)
    }
}
impl View for OscpStatusRequestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OscpStatusRequestMapper<'_> {
    type Src = SpecOscpStatusRequestInner;
    type Dst = SpecOscpStatusRequest;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OscpStatusRequestMapper<'a> {
    type Src = OscpStatusRequestInner<'a>;
    type Dst = OscpStatusRequest<'a>;
}

pub struct SpecOscpStatusRequestCombinator(SpecOscpStatusRequestCombinatorAlias);

impl SpecCombinator for SpecOscpStatusRequestCombinator {
    type SpecResult = SpecOscpStatusRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOscpStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOscpStatusRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOscpStatusRequestCombinatorAlias = Mapped<(SpecResponderIdListCombinator, SpecOcspExtensionsCombinator), OscpStatusRequestMapper<'static>>;

pub struct OscpStatusRequestCombinator<'a>(OscpStatusRequestCombinatorAlias<'a>);

impl<'a> View for OscpStatusRequestCombinator<'a> {
    type V = SpecOscpStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecOscpStatusRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OscpStatusRequestCombinator<'a> {
    type Result = OscpStatusRequest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OscpStatusRequestCombinatorAlias<'a> = Mapped<(ResponderIdListCombinator<'a>, OcspExtensionsCombinator<'a>), OscpStatusRequestMapper<'a>>;


pub closed spec fn spec_oscp_status_request() -> SpecOscpStatusRequestCombinator {
    SpecOscpStatusRequestCombinator(
    Mapped {
        inner: (spec_responder_id_list(), spec_ocsp_extensions()),
        mapper: OscpStatusRequestMapper::spec_new(),
    })
}

                
pub fn oscp_status_request<'a>() -> (o: OscpStatusRequestCombinator<'a>)
    ensures o@ == spec_oscp_status_request(),
{
    OscpStatusRequestCombinator(
    Mapped {
        inner: (responder_id_list(), ocsp_extensions()),
        mapper: OscpStatusRequestMapper::new(),
    })
}

                

pub struct SpecCertificateStatusRequest {
    pub status_type: u8,
    pub request: SpecOscpStatusRequest,
}

pub type SpecCertificateStatusRequestInner = (u8, SpecOscpStatusRequest);
impl SpecFrom<SpecCertificateStatusRequest> for SpecCertificateStatusRequestInner {
    open spec fn spec_from(m: SpecCertificateStatusRequest) -> SpecCertificateStatusRequestInner {
        (m.status_type, m.request)
    }
}
impl SpecFrom<SpecCertificateStatusRequestInner> for SpecCertificateStatusRequest {
    open spec fn spec_from(m: SpecCertificateStatusRequestInner) -> SpecCertificateStatusRequest {
        let (status_type, request) = m;
        SpecCertificateStatusRequest { status_type, request }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateStatusRequest<'a> {
    pub status_type: u8,
    pub request: OscpStatusRequest<'a>,
}

impl View for CertificateStatusRequest<'_> {
    type V = SpecCertificateStatusRequest;

    open spec fn view(&self) -> Self::V {
        SpecCertificateStatusRequest {
            status_type: self.status_type@,
            request: self.request@,
        }
    }
}
pub type CertificateStatusRequestInner<'a> = (u8, OscpStatusRequest<'a>);
impl<'a> From<CertificateStatusRequest<'a>> for CertificateStatusRequestInner<'a> {
    fn ex_from(m: CertificateStatusRequest) -> CertificateStatusRequestInner {
        (m.status_type, m.request)
    }
}
impl<'a> From<CertificateStatusRequestInner<'a>> for CertificateStatusRequest<'a> {
    fn ex_from(m: CertificateStatusRequestInner) -> CertificateStatusRequest {
        let (status_type, request) = m;
        CertificateStatusRequest { status_type, request }
    }
}

pub struct CertificateStatusRequestMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateStatusRequestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateStatusRequestMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateStatusRequestMapper(PhantomData)
    }
}
impl View for CertificateStatusRequestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusRequestMapper<'_> {
    type Src = SpecCertificateStatusRequestInner;
    type Dst = SpecCertificateStatusRequest;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateStatusRequestMapper<'a> {
    type Src = CertificateStatusRequestInner<'a>;
    type Dst = CertificateStatusRequest<'a>;
}
pub const CERTIFICATESTATUSREQUEST_STATUS_TYPE: u8 = 1;

pub struct SpecCertificateStatusRequestCombinator(SpecCertificateStatusRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusRequestCombinator {
    type SpecResult = SpecCertificateStatusRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateStatusRequestCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, SpecOscpStatusRequestCombinator), CertificateStatusRequestMapper<'static>>;

pub struct CertificateStatusRequestCombinator<'a>(CertificateStatusRequestCombinatorAlias<'a>);

impl<'a> View for CertificateStatusRequestCombinator<'a> {
    type V = SpecCertificateStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateStatusRequestCombinator<'a> {
    type Result = CertificateStatusRequest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateStatusRequestCombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, OscpStatusRequestCombinator<'a>), CertificateStatusRequestMapper<'a>>;


pub closed spec fn spec_certificate_status_request() -> SpecCertificateStatusRequestCombinator {
    SpecCertificateStatusRequestCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, spec_oscp_status_request()),
        mapper: CertificateStatusRequestMapper::spec_new(),
    })
}

                
pub fn certificate_status_request<'a>() -> (o: CertificateStatusRequestCombinator<'a>)
    ensures o@ == spec_certificate_status_request(),
{
    CertificateStatusRequestCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, oscp_status_request()),
        mapper: CertificateStatusRequestMapper::new(),
    })
}

                
pub type SpecNamedGroupListList = Seq<SpecNamedGroup>;
pub type NamedGroupListList = RepeatResult<NamedGroup>;


pub struct SpecNamedGroupListListCombinator(SpecNamedGroupListListCombinatorAlias);

impl SpecCombinator for SpecNamedGroupListListCombinator {
    type SpecResult = SpecNamedGroupListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupListListCombinatorAlias = AndThen<Bytes, Repeat<SpecNamedGroupCombinator>>;

pub struct NamedGroupListListCombinator(NamedGroupListListCombinatorAlias);

impl View for NamedGroupListListCombinator {
    type V = SpecNamedGroupListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NamedGroupListListCombinator {
    type Result = NamedGroupListList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NamedGroupListListCombinatorAlias = AndThen<Bytes, Repeat<NamedGroupCombinator>>;


pub closed spec fn spec_named_group_list_list(l: SpecUint2Ffff) -> SpecNamedGroupListListCombinator {
    SpecNamedGroupListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_named_group())))
}

                
pub fn named_group_list_list<'a>(l: Uint2Ffff) -> (o: NamedGroupListListCombinator)
    ensures o@ == spec_named_group_list_list(l@),
{
    NamedGroupListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(named_group())))
}

                

pub struct SpecNamedGroupList {
    pub l: SpecUint2Ffff,
    pub list: SpecNamedGroupListList,
}

pub type SpecNamedGroupListInner = (SpecUint2Ffff, SpecNamedGroupListList);
impl SpecFrom<SpecNamedGroupList> for SpecNamedGroupListInner {
    open spec fn spec_from(m: SpecNamedGroupList) -> SpecNamedGroupListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecNamedGroupListInner> for SpecNamedGroupList {
    open spec fn spec_from(m: SpecNamedGroupListInner) -> SpecNamedGroupList {
        let (l, list) = m;
        SpecNamedGroupList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NamedGroupList {
    pub l: Uint2Ffff,
    pub list: NamedGroupListList,
}

impl View for NamedGroupList {
    type V = SpecNamedGroupList;

    open spec fn view(&self) -> Self::V {
        SpecNamedGroupList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type NamedGroupListInner = (Uint2Ffff, NamedGroupListList);
impl From<NamedGroupList> for NamedGroupListInner {
    fn ex_from(m: NamedGroupList) -> NamedGroupListInner {
        (m.l, m.list)
    }
}
impl From<NamedGroupListInner> for NamedGroupList {
    fn ex_from(m: NamedGroupListInner) -> NamedGroupList {
        let (l, list) = m;
        NamedGroupList { l, list }
    }
}

pub struct NamedGroupListMapper;
impl NamedGroupListMapper {
    pub closed spec fn spec_new() -> Self {
        NamedGroupListMapper
    }
    pub fn new() -> Self {
        NamedGroupListMapper
    }
}
impl View for NamedGroupListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NamedGroupListMapper {
    type Src = SpecNamedGroupListInner;
    type Dst = SpecNamedGroupList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for NamedGroupListMapper {
    type Src = NamedGroupListInner;
    type Dst = NamedGroupList;
}

pub struct SpecNamedGroupListCombinator(SpecNamedGroupListCombinatorAlias);

impl SpecCombinator for SpecNamedGroupListCombinator {
    type SpecResult = SpecNamedGroupList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupListCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecNamedGroupListListCombinator>, NamedGroupListMapper>;

pub struct NamedGroupListCombinator<'a>(NamedGroupListCombinatorAlias<'a>);

impl<'a> View for NamedGroupListCombinator<'a> {
    type V = SpecNamedGroupListCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NamedGroupListCombinator<'a> {
    type Result = NamedGroupList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NamedGroupListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, NamedGroupListListCombinator, NamedGroupListCont0<'a>>, NamedGroupListMapper>;


pub closed spec fn spec_named_group_list() -> SpecNamedGroupListCombinator {
    SpecNamedGroupListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_ffff(), snd: |deps| spec_named_group_list_cont0(deps) },
        mapper: NamedGroupListMapper::spec_new(),
    })
}

pub open spec fn spec_named_group_list_cont0(deps: SpecUint2Ffff) -> SpecNamedGroupListListCombinator {
    let l = deps;
    spec_named_group_list_list(l)
}
                
pub fn named_group_list<'a>() -> (o: NamedGroupListCombinator<'a>)
    ensures o@ == spec_named_group_list(),
{
    NamedGroupListCombinator(
    Mapped {
        inner: Depend { fst: uint_2_ffff(), snd: NamedGroupListCont0::new(), spec_snd: Ghost(|deps| spec_named_group_list_cont0(deps)) },
        mapper: NamedGroupListMapper::new(),
    })
}

pub struct NamedGroupListCont0<'a>(PhantomData<&'a ()>);
impl<'a> NamedGroupListCont0<'a> {
    pub fn new() -> Self {
        NamedGroupListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Ffff> for NamedGroupListCont0<'a> {
    type Output = NamedGroupListListCombinator;

    open spec fn requires(&self, deps: &Uint2Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_named_group_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Ffff) -> Self::Output {
        let l = *deps;
        named_group_list_list(l)
    }
}
                

pub struct SpecEcPointFormatList {
    pub l: SpecUint1Ff,
    pub list: SpecEcPointFormatListList,
}

pub type SpecEcPointFormatListInner = (SpecUint1Ff, SpecEcPointFormatListList);
impl SpecFrom<SpecEcPointFormatList> for SpecEcPointFormatListInner {
    open spec fn spec_from(m: SpecEcPointFormatList) -> SpecEcPointFormatListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecEcPointFormatListInner> for SpecEcPointFormatList {
    open spec fn spec_from(m: SpecEcPointFormatListInner) -> SpecEcPointFormatList {
        let (l, list) = m;
        SpecEcPointFormatList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EcPointFormatList {
    pub l: Uint1Ff,
    pub list: EcPointFormatListList,
}

impl View for EcPointFormatList {
    type V = SpecEcPointFormatList;

    open spec fn view(&self) -> Self::V {
        SpecEcPointFormatList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type EcPointFormatListInner = (Uint1Ff, EcPointFormatListList);
impl From<EcPointFormatList> for EcPointFormatListInner {
    fn ex_from(m: EcPointFormatList) -> EcPointFormatListInner {
        (m.l, m.list)
    }
}
impl From<EcPointFormatListInner> for EcPointFormatList {
    fn ex_from(m: EcPointFormatListInner) -> EcPointFormatList {
        let (l, list) = m;
        EcPointFormatList { l, list }
    }
}

pub struct EcPointFormatListMapper;
impl EcPointFormatListMapper {
    pub closed spec fn spec_new() -> Self {
        EcPointFormatListMapper
    }
    pub fn new() -> Self {
        EcPointFormatListMapper
    }
}
impl View for EcPointFormatListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EcPointFormatListMapper {
    type Src = SpecEcPointFormatListInner;
    type Dst = SpecEcPointFormatList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for EcPointFormatListMapper {
    type Src = EcPointFormatListInner;
    type Dst = EcPointFormatList;
}

pub struct SpecEcPointFormatListCombinator(SpecEcPointFormatListCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatListCombinator {
    type SpecResult = SpecEcPointFormatList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecEcPointFormatListListCombinator>, EcPointFormatListMapper>;

pub struct EcPointFormatListCombinator<'a>(EcPointFormatListCombinatorAlias<'a>);

impl<'a> View for EcPointFormatListCombinator<'a> {
    type V = SpecEcPointFormatListCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EcPointFormatListCombinator<'a> {
    type Result = EcPointFormatList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EcPointFormatListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, EcPointFormatListListCombinator, EcPointFormatListCont0<'a>>, EcPointFormatListMapper>;


pub closed spec fn spec_ec_point_format_list() -> SpecEcPointFormatListCombinator {
    SpecEcPointFormatListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ff(), snd: |deps| spec_ec_point_format_list_cont0(deps) },
        mapper: EcPointFormatListMapper::spec_new(),
    })
}

pub open spec fn spec_ec_point_format_list_cont0(deps: SpecUint1Ff) -> SpecEcPointFormatListListCombinator {
    let l = deps;
    spec_ec_point_format_list_list(l)
}
                
pub fn ec_point_format_list<'a>() -> (o: EcPointFormatListCombinator<'a>)
    ensures o@ == spec_ec_point_format_list(),
{
    EcPointFormatListCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ff(), snd: EcPointFormatListCont0::new(), spec_snd: Ghost(|deps| spec_ec_point_format_list_cont0(deps)) },
        mapper: EcPointFormatListMapper::new(),
    })
}

pub struct EcPointFormatListCont0<'a>(PhantomData<&'a ()>);
impl<'a> EcPointFormatListCont0<'a> {
    pub fn new() -> Self {
        EcPointFormatListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ff> for EcPointFormatListCont0<'a> {
    type Output = EcPointFormatListListCombinator;

    open spec fn requires(&self, deps: &Uint1Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_ec_point_format_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ff) -> Self::Output {
        let l = *deps;
        ec_point_format_list_list(l)
    }
}
                
pub type SpecSignatureSchemeListList = Seq<SpecSignatureScheme>;
pub type SignatureSchemeListList = RepeatResult<SignatureScheme>;


pub struct SpecSignatureSchemeListListCombinator(SpecSignatureSchemeListListCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeListListCombinator {
    type SpecResult = SpecSignatureSchemeListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeListListCombinatorAlias = AndThen<Bytes, Repeat<SpecSignatureSchemeCombinator>>;

pub struct SignatureSchemeListListCombinator(SignatureSchemeListListCombinatorAlias);

impl View for SignatureSchemeListListCombinator {
    type V = SpecSignatureSchemeListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SignatureSchemeListListCombinator {
    type Result = SignatureSchemeListList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SignatureSchemeListListCombinatorAlias = AndThen<Bytes, Repeat<SignatureSchemeCombinator>>;


pub closed spec fn spec_signature_scheme_list_list(l: SpecUint2Fffe) -> SpecSignatureSchemeListListCombinator {
    SpecSignatureSchemeListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_signature_scheme())))
}

                
pub fn signature_scheme_list_list<'a>(l: Uint2Fffe) -> (o: SignatureSchemeListListCombinator)
    ensures o@ == spec_signature_scheme_list_list(l@),
{
    SignatureSchemeListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(signature_scheme())))
}

                

pub struct SpecSignatureSchemeList {
    pub l: SpecUint2Fffe,
    pub list: SpecSignatureSchemeListList,
}

pub type SpecSignatureSchemeListInner = (SpecUint2Fffe, SpecSignatureSchemeListList);
impl SpecFrom<SpecSignatureSchemeList> for SpecSignatureSchemeListInner {
    open spec fn spec_from(m: SpecSignatureSchemeList) -> SpecSignatureSchemeListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSignatureSchemeListInner> for SpecSignatureSchemeList {
    open spec fn spec_from(m: SpecSignatureSchemeListInner) -> SpecSignatureSchemeList {
        let (l, list) = m;
        SpecSignatureSchemeList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SignatureSchemeList {
    pub l: Uint2Fffe,
    pub list: SignatureSchemeListList,
}

impl View for SignatureSchemeList {
    type V = SpecSignatureSchemeList;

    open spec fn view(&self) -> Self::V {
        SpecSignatureSchemeList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type SignatureSchemeListInner = (Uint2Fffe, SignatureSchemeListList);
impl From<SignatureSchemeList> for SignatureSchemeListInner {
    fn ex_from(m: SignatureSchemeList) -> SignatureSchemeListInner {
        (m.l, m.list)
    }
}
impl From<SignatureSchemeListInner> for SignatureSchemeList {
    fn ex_from(m: SignatureSchemeListInner) -> SignatureSchemeList {
        let (l, list) = m;
        SignatureSchemeList { l, list }
    }
}

pub struct SignatureSchemeListMapper;
impl SignatureSchemeListMapper {
    pub closed spec fn spec_new() -> Self {
        SignatureSchemeListMapper
    }
    pub fn new() -> Self {
        SignatureSchemeListMapper
    }
}
impl View for SignatureSchemeListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignatureSchemeListMapper {
    type Src = SpecSignatureSchemeListInner;
    type Dst = SpecSignatureSchemeList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for SignatureSchemeListMapper {
    type Src = SignatureSchemeListInner;
    type Dst = SignatureSchemeList;
}

pub struct SpecSignatureSchemeListCombinator(SpecSignatureSchemeListCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeListCombinator {
    type SpecResult = SpecSignatureSchemeList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeListCombinatorAlias = Mapped<SpecDepend<SpecUint2FffeCombinator, SpecSignatureSchemeListListCombinator>, SignatureSchemeListMapper>;

pub struct SignatureSchemeListCombinator<'a>(SignatureSchemeListCombinatorAlias<'a>);

impl<'a> View for SignatureSchemeListCombinator<'a> {
    type V = SpecSignatureSchemeListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SignatureSchemeListCombinator<'a> {
    type Result = SignatureSchemeList;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SignatureSchemeListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FffeCombinator, SignatureSchemeListListCombinator, SignatureSchemeListCont0<'a>>, SignatureSchemeListMapper>;


pub closed spec fn spec_signature_scheme_list() -> SpecSignatureSchemeListCombinator {
    SpecSignatureSchemeListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_fffe(), snd: |deps| spec_signature_scheme_list_cont0(deps) },
        mapper: SignatureSchemeListMapper::spec_new(),
    })
}

pub open spec fn spec_signature_scheme_list_cont0(deps: SpecUint2Fffe) -> SpecSignatureSchemeListListCombinator {
    let l = deps;
    spec_signature_scheme_list_list(l)
}
                
pub fn signature_scheme_list<'a>() -> (o: SignatureSchemeListCombinator<'a>)
    ensures o@ == spec_signature_scheme_list(),
{
    SignatureSchemeListCombinator(
    Mapped {
        inner: Depend { fst: uint_2_fffe(), snd: SignatureSchemeListCont0::new(), spec_snd: Ghost(|deps| spec_signature_scheme_list_cont0(deps)) },
        mapper: SignatureSchemeListMapper::new(),
    })
}

pub struct SignatureSchemeListCont0<'a>(PhantomData<&'a ()>);
impl<'a> SignatureSchemeListCont0<'a> {
    pub fn new() -> Self {
        SignatureSchemeListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Fffe> for SignatureSchemeListCont0<'a> {
    type Output = SignatureSchemeListListCombinator;

    open spec fn requires(&self, deps: &Uint2Fffe) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_signature_scheme_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Fffe) -> Self::Output {
        let l = *deps;
        signature_scheme_list_list(l)
    }
}
                
pub type SpecHeartbeatMode = u8;
pub type HeartbeatMode = u8;


pub struct SpecHeartbeatModeCombinator(SpecHeartbeatModeCombinatorAlias);

impl SpecCombinator for SpecHeartbeatModeCombinator {
    type SpecResult = SpecHeartbeatMode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHeartbeatModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatModeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHeartbeatModeCombinatorAlias = U8;

pub struct HeartbeatModeCombinator(HeartbeatModeCombinatorAlias);

impl View for HeartbeatModeCombinator {
    type V = SpecHeartbeatModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatModeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HeartbeatModeCombinator {
    type Result = HeartbeatMode;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HeartbeatModeCombinatorAlias = U8;


pub closed spec fn spec_heartbeat_mode() -> SpecHeartbeatModeCombinator {
    SpecHeartbeatModeCombinator(U8)
}

                
pub fn heartbeat_mode() -> (o: HeartbeatModeCombinator)
    ensures o@ == spec_heartbeat_mode(),
{
    HeartbeatModeCombinator(U8)
}

                

pub struct SpecProtocolNameList {
    pub l: SpecUint2Ffff,
    pub list: SpecProtocolNameListList,
}

pub type SpecProtocolNameListInner = (SpecUint2Ffff, SpecProtocolNameListList);
impl SpecFrom<SpecProtocolNameList> for SpecProtocolNameListInner {
    open spec fn spec_from(m: SpecProtocolNameList) -> SpecProtocolNameListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecProtocolNameListInner> for SpecProtocolNameList {
    open spec fn spec_from(m: SpecProtocolNameListInner) -> SpecProtocolNameList {
        let (l, list) = m;
        SpecProtocolNameList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ProtocolNameList<'a> {
    pub l: Uint2Ffff,
    pub list: ProtocolNameListList<'a>,
}

impl View for ProtocolNameList<'_> {
    type V = SpecProtocolNameList;

    open spec fn view(&self) -> Self::V {
        SpecProtocolNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ProtocolNameListInner<'a> = (Uint2Ffff, ProtocolNameListList<'a>);
impl<'a> From<ProtocolNameList<'a>> for ProtocolNameListInner<'a> {
    fn ex_from(m: ProtocolNameList) -> ProtocolNameListInner {
        (m.l, m.list)
    }
}
impl<'a> From<ProtocolNameListInner<'a>> for ProtocolNameList<'a> {
    fn ex_from(m: ProtocolNameListInner) -> ProtocolNameList {
        let (l, list) = m;
        ProtocolNameList { l, list }
    }
}

pub struct ProtocolNameListMapper<'a>(PhantomData<&'a ()>);
impl<'a> ProtocolNameListMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ProtocolNameListMapper(PhantomData)
    }
    pub fn new() -> Self {
        ProtocolNameListMapper(PhantomData)
    }
}
impl View for ProtocolNameListMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProtocolNameListMapper<'_> {
    type Src = SpecProtocolNameListInner;
    type Dst = SpecProtocolNameList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ProtocolNameListMapper<'a> {
    type Src = ProtocolNameListInner<'a>;
    type Dst = ProtocolNameList<'a>;
}

pub struct SpecProtocolNameListCombinator(SpecProtocolNameListCombinatorAlias);

impl SpecCombinator for SpecProtocolNameListCombinator {
    type SpecResult = SpecProtocolNameList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameListCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecProtocolNameListListCombinator>, ProtocolNameListMapper<'static>>;

pub struct ProtocolNameListCombinator<'a>(ProtocolNameListCombinatorAlias<'a>);

impl<'a> View for ProtocolNameListCombinator<'a> {
    type V = SpecProtocolNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ProtocolNameListCombinator<'a> {
    type Result = ProtocolNameList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ProtocolNameListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, ProtocolNameListListCombinator<'a>, ProtocolNameListCont0<'a>>, ProtocolNameListMapper<'a>>;


pub closed spec fn spec_protocol_name_list() -> SpecProtocolNameListCombinator {
    SpecProtocolNameListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_ffff(), snd: |deps| spec_protocol_name_list_cont0(deps) },
        mapper: ProtocolNameListMapper::spec_new(),
    })
}

pub open spec fn spec_protocol_name_list_cont0(deps: SpecUint2Ffff) -> SpecProtocolNameListListCombinator {
    let l = deps;
    spec_protocol_name_list_list(l)
}
                
pub fn protocol_name_list<'a>() -> (o: ProtocolNameListCombinator<'a>)
    ensures o@ == spec_protocol_name_list(),
{
    ProtocolNameListCombinator(
    Mapped {
        inner: Depend { fst: uint_2_ffff(), snd: ProtocolNameListCont0::new(), spec_snd: Ghost(|deps| spec_protocol_name_list_cont0(deps)) },
        mapper: ProtocolNameListMapper::new(),
    })
}

pub struct ProtocolNameListCont0<'a>(PhantomData<&'a ()>);
impl<'a> ProtocolNameListCont0<'a> {
    pub fn new() -> Self {
        ProtocolNameListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Ffff> for ProtocolNameListCont0<'a> {
    type Output = ProtocolNameListListCombinator<'a>;

    open spec fn requires(&self, deps: &Uint2Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_protocol_name_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Ffff) -> Self::Output {
        let l = *deps;
        protocol_name_list_list(l)
    }
}
                
pub type SpecSerializedSct = SpecOpaque1Ffff;
pub type SerializedSct<'a> = Opaque1Ffff<'a>;


pub struct SpecSerializedSctCombinator(SpecSerializedSctCombinatorAlias);

impl SpecCombinator for SpecSerializedSctCombinator {
    type SpecResult = SpecSerializedSct;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSerializedSctCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSerializedSctCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSerializedSctCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct SerializedSctCombinator<'a>(SerializedSctCombinatorAlias<'a>);

impl<'a> View for SerializedSctCombinator<'a> {
    type V = SpecSerializedSctCombinator;
    closed spec fn view(&self) -> Self::V { SpecSerializedSctCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SerializedSctCombinator<'a> {
    type Result = SerializedSct<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SerializedSctCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_serialized_sct() -> SpecSerializedSctCombinator {
    SpecSerializedSctCombinator(spec_opaque_1_ffff())
}

                
pub fn serialized_sct<'a>() -> (o: SerializedSctCombinator<'a>)
    ensures o@ == spec_serialized_sct(),
{
    SerializedSctCombinator(opaque_1_ffff())
}

                
pub type SpecSignedCertificateTimestampListList = Seq<SpecSerializedSct>;
pub type SignedCertificateTimestampListList<'a> = RepeatResult<SerializedSct<'a>>;


pub struct SpecSignedCertificateTimestampListListCombinator(SpecSignedCertificateTimestampListListCombinatorAlias);

impl SpecCombinator for SpecSignedCertificateTimestampListListCombinator {
    type SpecResult = SpecSignedCertificateTimestampListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignedCertificateTimestampListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignedCertificateTimestampListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignedCertificateTimestampListListCombinatorAlias = AndThen<Bytes, Repeat<SpecSerializedSctCombinator>>;

pub struct SignedCertificateTimestampListListCombinator<'a>(SignedCertificateTimestampListListCombinatorAlias<'a>);

impl<'a> View for SignedCertificateTimestampListListCombinator<'a> {
    type V = SpecSignedCertificateTimestampListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignedCertificateTimestampListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SignedCertificateTimestampListListCombinator<'a> {
    type Result = SignedCertificateTimestampListList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SignedCertificateTimestampListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<SerializedSctCombinator<'a>>>;


pub closed spec fn spec_signed_certificate_timestamp_list_list(l: SpecUint1Ffff) -> SpecSignedCertificateTimestampListListCombinator {
    SpecSignedCertificateTimestampListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_serialized_sct())))
}

                
pub fn signed_certificate_timestamp_list_list<'a>(l: Uint1Ffff) -> (o: SignedCertificateTimestampListListCombinator<'a>)
    ensures o@ == spec_signed_certificate_timestamp_list_list(l@),
{
    SignedCertificateTimestampListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(serialized_sct())))
}

                

pub struct SpecSignedCertificateTimestampList {
    pub l: SpecUint1Ffff,
    pub list: SpecSignedCertificateTimestampListList,
}

pub type SpecSignedCertificateTimestampListInner = (SpecUint1Ffff, SpecSignedCertificateTimestampListList);
impl SpecFrom<SpecSignedCertificateTimestampList> for SpecSignedCertificateTimestampListInner {
    open spec fn spec_from(m: SpecSignedCertificateTimestampList) -> SpecSignedCertificateTimestampListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSignedCertificateTimestampListInner> for SpecSignedCertificateTimestampList {
    open spec fn spec_from(m: SpecSignedCertificateTimestampListInner) -> SpecSignedCertificateTimestampList {
        let (l, list) = m;
        SpecSignedCertificateTimestampList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SignedCertificateTimestampList<'a> {
    pub l: Uint1Ffff,
    pub list: SignedCertificateTimestampListList<'a>,
}

impl View for SignedCertificateTimestampList<'_> {
    type V = SpecSignedCertificateTimestampList;

    open spec fn view(&self) -> Self::V {
        SpecSignedCertificateTimestampList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type SignedCertificateTimestampListInner<'a> = (Uint1Ffff, SignedCertificateTimestampListList<'a>);
impl<'a> From<SignedCertificateTimestampList<'a>> for SignedCertificateTimestampListInner<'a> {
    fn ex_from(m: SignedCertificateTimestampList) -> SignedCertificateTimestampListInner {
        (m.l, m.list)
    }
}
impl<'a> From<SignedCertificateTimestampListInner<'a>> for SignedCertificateTimestampList<'a> {
    fn ex_from(m: SignedCertificateTimestampListInner) -> SignedCertificateTimestampList {
        let (l, list) = m;
        SignedCertificateTimestampList { l, list }
    }
}

pub struct SignedCertificateTimestampListMapper<'a>(PhantomData<&'a ()>);
impl<'a> SignedCertificateTimestampListMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SignedCertificateTimestampListMapper(PhantomData)
    }
    pub fn new() -> Self {
        SignedCertificateTimestampListMapper(PhantomData)
    }
}
impl View for SignedCertificateTimestampListMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignedCertificateTimestampListMapper<'_> {
    type Src = SpecSignedCertificateTimestampListInner;
    type Dst = SpecSignedCertificateTimestampList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SignedCertificateTimestampListMapper<'a> {
    type Src = SignedCertificateTimestampListInner<'a>;
    type Dst = SignedCertificateTimestampList<'a>;
}

pub struct SpecSignedCertificateTimestampListCombinator(SpecSignedCertificateTimestampListCombinatorAlias);

impl SpecCombinator for SpecSignedCertificateTimestampListCombinator {
    type SpecResult = SpecSignedCertificateTimestampList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignedCertificateTimestampListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignedCertificateTimestampListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignedCertificateTimestampListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, SpecSignedCertificateTimestampListListCombinator>, SignedCertificateTimestampListMapper<'static>>;

pub struct SignedCertificateTimestampListCombinator<'a>(SignedCertificateTimestampListCombinatorAlias<'a>);

impl<'a> View for SignedCertificateTimestampListCombinator<'a> {
    type V = SpecSignedCertificateTimestampListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignedCertificateTimestampListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SignedCertificateTimestampListCombinator<'a> {
    type Result = SignedCertificateTimestampList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SignedCertificateTimestampListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, SignedCertificateTimestampListListCombinator<'a>, SignedCertificateTimestampListCont0<'a>>, SignedCertificateTimestampListMapper<'a>>;


pub closed spec fn spec_signed_certificate_timestamp_list() -> SpecSignedCertificateTimestampListCombinator {
    SpecSignedCertificateTimestampListCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ffff(), snd: |deps| spec_signed_certificate_timestamp_list_cont0(deps) },
        mapper: SignedCertificateTimestampListMapper::spec_new(),
    })
}

pub open spec fn spec_signed_certificate_timestamp_list_cont0(deps: SpecUint1Ffff) -> SpecSignedCertificateTimestampListListCombinator {
    let l = deps;
    spec_signed_certificate_timestamp_list_list(l)
}
                
pub fn signed_certificate_timestamp_list<'a>() -> (o: SignedCertificateTimestampListCombinator<'a>)
    ensures o@ == spec_signed_certificate_timestamp_list(),
{
    SignedCertificateTimestampListCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ffff(), snd: SignedCertificateTimestampListCont0::new(), spec_snd: Ghost(|deps| spec_signed_certificate_timestamp_list_cont0(deps)) },
        mapper: SignedCertificateTimestampListMapper::new(),
    })
}

pub struct SignedCertificateTimestampListCont0<'a>(PhantomData<&'a ()>);
impl<'a> SignedCertificateTimestampListCont0<'a> {
    pub fn new() -> Self {
        SignedCertificateTimestampListCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ffff> for SignedCertificateTimestampListCont0<'a> {
    type Output = SignedCertificateTimestampListListCombinator<'a>;

    open spec fn requires(&self, deps: &Uint1Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_signed_certificate_timestamp_list_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ffff) -> Self::Output {
        let l = *deps;
        signed_certificate_timestamp_list_list(l)
    }
}
                
pub type SpecClientCertTypeClientExtensionTypes = Seq<SpecCertificateType>;
pub type ClientCertTypeClientExtensionTypes = RepeatResult<CertificateType>;


pub struct SpecClientCertTypeClientExtensionTypesCombinator(SpecClientCertTypeClientExtensionTypesCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeClientExtensionTypesCombinator {
    type SpecResult = SpecClientCertTypeClientExtensionTypes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeClientExtensionTypesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeClientExtensionTypesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateTypeCombinator>>;

pub struct ClientCertTypeClientExtensionTypesCombinator(ClientCertTypeClientExtensionTypesCombinatorAlias);

impl View for ClientCertTypeClientExtensionTypesCombinator {
    type V = SpecClientCertTypeClientExtensionTypesCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeClientExtensionTypesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientCertTypeClientExtensionTypesCombinator {
    type Result = ClientCertTypeClientExtensionTypes;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<CertificateTypeCombinator>>;


pub closed spec fn spec_client_cert_type_client_extension_types(l: SpecUint1Ff) -> SpecClientCertTypeClientExtensionTypesCombinator {
    SpecClientCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_type())))
}

                
pub fn client_cert_type_client_extension_types<'a>(l: Uint1Ff) -> (o: ClientCertTypeClientExtensionTypesCombinator)
    ensures o@ == spec_client_cert_type_client_extension_types(l@),
{
    ClientCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_type())))
}

                

pub struct SpecClientCertTypeClientExtension {
    pub l: SpecUint1Ff,
    pub types: SpecClientCertTypeClientExtensionTypes,
}

pub type SpecClientCertTypeClientExtensionInner = (SpecUint1Ff, SpecClientCertTypeClientExtensionTypes);
impl SpecFrom<SpecClientCertTypeClientExtension> for SpecClientCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecClientCertTypeClientExtension) -> SpecClientCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl SpecFrom<SpecClientCertTypeClientExtensionInner> for SpecClientCertTypeClientExtension {
    open spec fn spec_from(m: SpecClientCertTypeClientExtensionInner) -> SpecClientCertTypeClientExtension {
        let (l, types) = m;
        SpecClientCertTypeClientExtension { l, types }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ClientCertTypeClientExtensionTypes,
}

impl View for ClientCertTypeClientExtension {
    type V = SpecClientCertTypeClientExtension;

    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
pub type ClientCertTypeClientExtensionInner = (Uint1Ff, ClientCertTypeClientExtensionTypes);
impl From<ClientCertTypeClientExtension> for ClientCertTypeClientExtensionInner {
    fn ex_from(m: ClientCertTypeClientExtension) -> ClientCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ClientCertTypeClientExtensionInner> for ClientCertTypeClientExtension {
    fn ex_from(m: ClientCertTypeClientExtensionInner) -> ClientCertTypeClientExtension {
        let (l, types) = m;
        ClientCertTypeClientExtension { l, types }
    }
}

pub struct ClientCertTypeClientExtensionMapper;
impl ClientCertTypeClientExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        ClientCertTypeClientExtensionMapper
    }
    pub fn new() -> Self {
        ClientCertTypeClientExtensionMapper
    }
}
impl View for ClientCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeClientExtensionMapper {
    type Src = SpecClientCertTypeClientExtensionInner;
    type Dst = SpecClientCertTypeClientExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ClientCertTypeClientExtensionMapper {
    type Src = ClientCertTypeClientExtensionInner;
    type Dst = ClientCertTypeClientExtension;
}

pub struct SpecClientCertTypeClientExtensionCombinator(SpecClientCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    type SpecResult = SpecClientCertTypeClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeClientExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecClientCertTypeClientExtensionTypesCombinator>, ClientCertTypeClientExtensionMapper>;

pub struct ClientCertTypeClientExtensionCombinator<'a>(ClientCertTypeClientExtensionCombinatorAlias<'a>);

impl<'a> View for ClientCertTypeClientExtensionCombinator<'a> {
    type V = SpecClientCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientCertTypeClientExtensionCombinator<'a> {
    type Result = ClientCertTypeClientExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientCertTypeClientExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, ClientCertTypeClientExtensionTypesCombinator, ClientCertTypeClientExtensionCont0<'a>>, ClientCertTypeClientExtensionMapper>;


pub closed spec fn spec_client_cert_type_client_extension() -> SpecClientCertTypeClientExtensionCombinator {
    SpecClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ff(), snd: |deps| spec_client_cert_type_client_extension_cont0(deps) },
        mapper: ClientCertTypeClientExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_client_cert_type_client_extension_cont0(deps: SpecUint1Ff) -> SpecClientCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_client_cert_type_client_extension_types(l)
}
                
pub fn client_cert_type_client_extension<'a>() -> (o: ClientCertTypeClientExtensionCombinator<'a>)
    ensures o@ == spec_client_cert_type_client_extension(),
{
    ClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ff(), snd: ClientCertTypeClientExtensionCont0::new(), spec_snd: Ghost(|deps| spec_client_cert_type_client_extension_cont0(deps)) },
        mapper: ClientCertTypeClientExtensionMapper::new(),
    })
}

pub struct ClientCertTypeClientExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> ClientCertTypeClientExtensionCont0<'a> {
    pub fn new() -> Self {
        ClientCertTypeClientExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ff> for ClientCertTypeClientExtensionCont0<'a> {
    type Output = ClientCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: &Uint1Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_client_cert_type_client_extension_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ff) -> Self::Output {
        let l = *deps;
        client_cert_type_client_extension_types(l)
    }
}
                

pub struct SpecServerCertTypeClientExtension {
    pub l: SpecUint1Ff,
    pub types: SpecServerCertTypeClientExtensionTypes,
}

pub type SpecServerCertTypeClientExtensionInner = (SpecUint1Ff, SpecServerCertTypeClientExtensionTypes);
impl SpecFrom<SpecServerCertTypeClientExtension> for SpecServerCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecServerCertTypeClientExtension) -> SpecServerCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl SpecFrom<SpecServerCertTypeClientExtensionInner> for SpecServerCertTypeClientExtension {
    open spec fn spec_from(m: SpecServerCertTypeClientExtensionInner) -> SpecServerCertTypeClientExtension {
        let (l, types) = m;
        SpecServerCertTypeClientExtension { l, types }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ServerCertTypeClientExtensionTypes,
}

impl View for ServerCertTypeClientExtension {
    type V = SpecServerCertTypeClientExtension;

    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
pub type ServerCertTypeClientExtensionInner = (Uint1Ff, ServerCertTypeClientExtensionTypes);
impl From<ServerCertTypeClientExtension> for ServerCertTypeClientExtensionInner {
    fn ex_from(m: ServerCertTypeClientExtension) -> ServerCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ServerCertTypeClientExtensionInner> for ServerCertTypeClientExtension {
    fn ex_from(m: ServerCertTypeClientExtensionInner) -> ServerCertTypeClientExtension {
        let (l, types) = m;
        ServerCertTypeClientExtension { l, types }
    }
}

pub struct ServerCertTypeClientExtensionMapper;
impl ServerCertTypeClientExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        ServerCertTypeClientExtensionMapper
    }
    pub fn new() -> Self {
        ServerCertTypeClientExtensionMapper
    }
}
impl View for ServerCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeClientExtensionMapper {
    type Src = SpecServerCertTypeClientExtensionInner;
    type Dst = SpecServerCertTypeClientExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ServerCertTypeClientExtensionMapper {
    type Src = ServerCertTypeClientExtensionInner;
    type Dst = ServerCertTypeClientExtension;
}

pub struct SpecServerCertTypeClientExtensionCombinator(SpecServerCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    type SpecResult = SpecServerCertTypeClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeClientExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecServerCertTypeClientExtensionTypesCombinator>, ServerCertTypeClientExtensionMapper>;

pub struct ServerCertTypeClientExtensionCombinator<'a>(ServerCertTypeClientExtensionCombinatorAlias<'a>);

impl<'a> View for ServerCertTypeClientExtensionCombinator<'a> {
    type V = SpecServerCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerCertTypeClientExtensionCombinator<'a> {
    type Result = ServerCertTypeClientExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerCertTypeClientExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, ServerCertTypeClientExtensionTypesCombinator, ServerCertTypeClientExtensionCont0<'a>>, ServerCertTypeClientExtensionMapper>;


pub closed spec fn spec_server_cert_type_client_extension() -> SpecServerCertTypeClientExtensionCombinator {
    SpecServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ff(), snd: |deps| spec_server_cert_type_client_extension_cont0(deps) },
        mapper: ServerCertTypeClientExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_server_cert_type_client_extension_cont0(deps: SpecUint1Ff) -> SpecServerCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_server_cert_type_client_extension_types(l)
}
                
pub fn server_cert_type_client_extension<'a>() -> (o: ServerCertTypeClientExtensionCombinator<'a>)
    ensures o@ == spec_server_cert_type_client_extension(),
{
    ServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ff(), snd: ServerCertTypeClientExtensionCont0::new(), spec_snd: Ghost(|deps| spec_server_cert_type_client_extension_cont0(deps)) },
        mapper: ServerCertTypeClientExtensionMapper::new(),
    })
}

pub struct ServerCertTypeClientExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> ServerCertTypeClientExtensionCont0<'a> {
    pub fn new() -> Self {
        ServerCertTypeClientExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ff> for ServerCertTypeClientExtensionCont0<'a> {
    type Output = ServerCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: &Uint1Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_server_cert_type_client_extension_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ff) -> Self::Output {
        let l = *deps;
        server_cert_type_client_extension_types(l)
    }
}
                
pub type SpecEmpty = Seq<u8>;
pub type Empty<'a> = &'a [u8];


pub struct SpecEmptyCombinator(SpecEmptyCombinatorAlias);

impl SpecCombinator for SpecEmptyCombinator {
    type SpecResult = SpecEmpty;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEmptyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEmptyCombinatorAlias = BytesN<0>;

pub struct EmptyCombinator(EmptyCombinatorAlias);

impl View for EmptyCombinator {
    type V = SpecEmptyCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EmptyCombinator {
    type Result = Empty<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EmptyCombinatorAlias = BytesN<0>;


pub closed spec fn spec_empty() -> SpecEmptyCombinator {
    SpecEmptyCombinator(BytesN::<0>)
}

                
pub fn empty() -> (o: EmptyCombinator)
    ensures o@ == spec_empty(),
{
    EmptyCombinator(BytesN::<0>)
}

                

pub struct SpecPskBinderEntry {
    pub l: u8,
    pub entries: Seq<u8>,
}

pub type SpecPskBinderEntryInner = (u8, Seq<u8>);
impl SpecFrom<SpecPskBinderEntry> for SpecPskBinderEntryInner {
    open spec fn spec_from(m: SpecPskBinderEntry) -> SpecPskBinderEntryInner {
        (m.l, m.entries)
    }
}
impl SpecFrom<SpecPskBinderEntryInner> for SpecPskBinderEntry {
    open spec fn spec_from(m: SpecPskBinderEntryInner) -> SpecPskBinderEntry {
        let (l, entries) = m;
        SpecPskBinderEntry { l, entries }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskBinderEntry<'a> {
    pub l: u8,
    pub entries: &'a [u8],
}

impl View for PskBinderEntry<'_> {
    type V = SpecPskBinderEntry;

    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntry {
            l: self.l@,
            entries: self.entries@,
        }
    }
}
pub type PskBinderEntryInner<'a> = (u8, &'a [u8]);
impl<'a> From<PskBinderEntry<'a>> for PskBinderEntryInner<'a> {
    fn ex_from(m: PskBinderEntry) -> PskBinderEntryInner {
        (m.l, m.entries)
    }
}
impl<'a> From<PskBinderEntryInner<'a>> for PskBinderEntry<'a> {
    fn ex_from(m: PskBinderEntryInner) -> PskBinderEntry {
        let (l, entries) = m;
        PskBinderEntry { l, entries }
    }
}

pub struct PskBinderEntryMapper<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntryMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        PskBinderEntryMapper(PhantomData)
    }
    pub fn new() -> Self {
        PskBinderEntryMapper(PhantomData)
    }
}
impl View for PskBinderEntryMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntryMapper<'_> {
    type Src = SpecPskBinderEntryInner;
    type Dst = SpecPskBinderEntry;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for PskBinderEntryMapper<'a> {
    type Src = PskBinderEntryInner<'a>;
    type Dst = PskBinderEntry<'a>;
}

pub struct SpecPskBinderEntryCombinator(SpecPskBinderEntryCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntryCombinator {
    type SpecResult = SpecPskBinderEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntryCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate12415296748708102903>, Bytes>, PskBinderEntryMapper<'static>>;
pub struct Predicate12415296748708102903;
impl View for Predicate12415296748708102903 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate12415296748708102903 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 32 && i <= 255)
    }
}
impl SpecPred for Predicate12415296748708102903 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 32 && i <= 255)
    }
}

pub struct PskBinderEntryCombinator<'a>(PskBinderEntryCombinatorAlias<'a>);

impl<'a> View for PskBinderEntryCombinator<'a> {
    type V = SpecPskBinderEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntryCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskBinderEntryCombinator<'a> {
    type Result = PskBinderEntry<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskBinderEntryCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate12415296748708102903>, Bytes, PskBinderEntryCont0<'a>>, PskBinderEntryMapper<'a>>;


pub closed spec fn spec_psk_binder_entry() -> SpecPskBinderEntryCombinator {
    SpecPskBinderEntryCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U8, predicate: Predicate12415296748708102903 }, snd: |deps| spec_psk_binder_entry_cont0(deps) },
        mapper: PskBinderEntryMapper::spec_new(),
    })
}

pub open spec fn spec_psk_binder_entry_cont0(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn psk_binder_entry<'a>() -> (o: PskBinderEntryCombinator<'a>)
    ensures o@ == spec_psk_binder_entry(),
{
    PskBinderEntryCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U8, predicate: Predicate12415296748708102903 }, snd: PskBinderEntryCont0::new(), spec_snd: Ghost(|deps| spec_psk_binder_entry_cont0(deps)) },
        mapper: PskBinderEntryMapper::new(),
    })
}

pub struct PskBinderEntryCont0<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntryCont0<'a> {
    pub fn new() -> Self {
        PskBinderEntryCont0(PhantomData)
    }
}
impl<'a> Continuation<&u8> for PskBinderEntryCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &u8) -> bool { true }

    open spec fn ensures(&self, deps: &u8, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entry_cont0(deps@)
    }

    fn apply(&self, deps: &u8) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                
pub type SpecPskBinderEntriesBinders = Seq<SpecPskBinderEntry>;
pub type PskBinderEntriesBinders<'a> = RepeatResult<PskBinderEntry<'a>>;


pub struct SpecPskBinderEntriesBindersCombinator(SpecPskBinderEntriesBindersCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntriesBindersCombinator {
    type SpecResult = SpecPskBinderEntriesBinders;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntriesBindersCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntriesBindersCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntriesBindersCombinatorAlias = AndThen<Bytes, Repeat<SpecPskBinderEntryCombinator>>;

pub struct PskBinderEntriesBindersCombinator<'a>(PskBinderEntriesBindersCombinatorAlias<'a>);

impl<'a> View for PskBinderEntriesBindersCombinator<'a> {
    type V = SpecPskBinderEntriesBindersCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntriesBindersCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskBinderEntriesBindersCombinator<'a> {
    type Result = PskBinderEntriesBinders<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskBinderEntriesBindersCombinatorAlias<'a> = AndThen<Bytes, Repeat<PskBinderEntryCombinator<'a>>>;


pub closed spec fn spec_psk_binder_entries_binders(l: u16) -> SpecPskBinderEntriesBindersCombinator {
    SpecPskBinderEntriesBindersCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_binder_entry())))
}

                
pub fn psk_binder_entries_binders<'a>(l: u16) -> (o: PskBinderEntriesBindersCombinator<'a>)
    ensures o@ == spec_psk_binder_entries_binders(l@),
{
    PskBinderEntriesBindersCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_binder_entry())))
}

                

pub struct SpecPskBinderEntries {
    pub l: u16,
    pub binders: SpecPskBinderEntriesBinders,
}

pub type SpecPskBinderEntriesInner = (u16, SpecPskBinderEntriesBinders);
impl SpecFrom<SpecPskBinderEntries> for SpecPskBinderEntriesInner {
    open spec fn spec_from(m: SpecPskBinderEntries) -> SpecPskBinderEntriesInner {
        (m.l, m.binders)
    }
}
impl SpecFrom<SpecPskBinderEntriesInner> for SpecPskBinderEntries {
    open spec fn spec_from(m: SpecPskBinderEntriesInner) -> SpecPskBinderEntries {
        let (l, binders) = m;
        SpecPskBinderEntries { l, binders }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskBinderEntries<'a> {
    pub l: u16,
    pub binders: PskBinderEntriesBinders<'a>,
}

impl View for PskBinderEntries<'_> {
    type V = SpecPskBinderEntries;

    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntries {
            l: self.l@,
            binders: self.binders@,
        }
    }
}
pub type PskBinderEntriesInner<'a> = (u16, PskBinderEntriesBinders<'a>);
impl<'a> From<PskBinderEntries<'a>> for PskBinderEntriesInner<'a> {
    fn ex_from(m: PskBinderEntries) -> PskBinderEntriesInner {
        (m.l, m.binders)
    }
}
impl<'a> From<PskBinderEntriesInner<'a>> for PskBinderEntries<'a> {
    fn ex_from(m: PskBinderEntriesInner) -> PskBinderEntries {
        let (l, binders) = m;
        PskBinderEntries { l, binders }
    }
}

pub struct PskBinderEntriesMapper<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntriesMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        PskBinderEntriesMapper(PhantomData)
    }
    pub fn new() -> Self {
        PskBinderEntriesMapper(PhantomData)
    }
}
impl View for PskBinderEntriesMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntriesMapper<'_> {
    type Src = SpecPskBinderEntriesInner;
    type Dst = SpecPskBinderEntries;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for PskBinderEntriesMapper<'a> {
    type Src = PskBinderEntriesInner<'a>;
    type Dst = PskBinderEntries<'a>;
}

pub struct SpecPskBinderEntriesCombinator(SpecPskBinderEntriesCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntriesCombinator {
    type SpecResult = SpecPskBinderEntries;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntriesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntriesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntriesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate14373960394449908011>, SpecPskBinderEntriesBindersCombinator>, PskBinderEntriesMapper<'static>>;
pub struct Predicate14373960394449908011;
impl View for Predicate14373960394449908011 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14373960394449908011 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 33 && i <= 65535)
    }
}
impl SpecPred for Predicate14373960394449908011 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 33 && i <= 65535)
    }
}

pub struct PskBinderEntriesCombinator<'a>(PskBinderEntriesCombinatorAlias<'a>);

impl<'a> View for PskBinderEntriesCombinator<'a> {
    type V = SpecPskBinderEntriesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntriesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskBinderEntriesCombinator<'a> {
    type Result = PskBinderEntries<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskBinderEntriesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate14373960394449908011>, PskBinderEntriesBindersCombinator<'a>, PskBinderEntriesCont0<'a>>, PskBinderEntriesMapper<'a>>;


pub closed spec fn spec_psk_binder_entries() -> SpecPskBinderEntriesCombinator {
    SpecPskBinderEntriesCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate14373960394449908011 }, snd: |deps| spec_psk_binder_entries_cont0(deps) },
        mapper: PskBinderEntriesMapper::spec_new(),
    })
}

pub open spec fn spec_psk_binder_entries_cont0(deps: u16) -> SpecPskBinderEntriesBindersCombinator {
    let l = deps;
    spec_psk_binder_entries_binders(l)
}
                
pub fn psk_binder_entries<'a>() -> (o: PskBinderEntriesCombinator<'a>)
    ensures o@ == spec_psk_binder_entries(),
{
    PskBinderEntriesCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate14373960394449908011 }, snd: PskBinderEntriesCont0::new(), spec_snd: Ghost(|deps| spec_psk_binder_entries_cont0(deps)) },
        mapper: PskBinderEntriesMapper::new(),
    })
}

pub struct PskBinderEntriesCont0<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntriesCont0<'a> {
    pub fn new() -> Self {
        PskBinderEntriesCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for PskBinderEntriesCont0<'a> {
    type Output = PskBinderEntriesBindersCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entries_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        psk_binder_entries_binders(l)
    }
}
                

pub struct SpecOfferedPsks {
    pub identities: SpecPskIdentities,
    pub binders: SpecPskBinderEntries,
}

pub type SpecOfferedPsksInner = (SpecPskIdentities, SpecPskBinderEntries);
impl SpecFrom<SpecOfferedPsks> for SpecOfferedPsksInner {
    open spec fn spec_from(m: SpecOfferedPsks) -> SpecOfferedPsksInner {
        (m.identities, m.binders)
    }
}
impl SpecFrom<SpecOfferedPsksInner> for SpecOfferedPsks {
    open spec fn spec_from(m: SpecOfferedPsksInner) -> SpecOfferedPsks {
        let (identities, binders) = m;
        SpecOfferedPsks { identities, binders }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OfferedPsks<'a> {
    pub identities: PskIdentities<'a>,
    pub binders: PskBinderEntries<'a>,
}

impl View for OfferedPsks<'_> {
    type V = SpecOfferedPsks;

    open spec fn view(&self) -> Self::V {
        SpecOfferedPsks {
            identities: self.identities@,
            binders: self.binders@,
        }
    }
}
pub type OfferedPsksInner<'a> = (PskIdentities<'a>, PskBinderEntries<'a>);
impl<'a> From<OfferedPsks<'a>> for OfferedPsksInner<'a> {
    fn ex_from(m: OfferedPsks) -> OfferedPsksInner {
        (m.identities, m.binders)
    }
}
impl<'a> From<OfferedPsksInner<'a>> for OfferedPsks<'a> {
    fn ex_from(m: OfferedPsksInner) -> OfferedPsks {
        let (identities, binders) = m;
        OfferedPsks { identities, binders }
    }
}

pub struct OfferedPsksMapper<'a>(PhantomData<&'a ()>);
impl<'a> OfferedPsksMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        OfferedPsksMapper(PhantomData)
    }
    pub fn new() -> Self {
        OfferedPsksMapper(PhantomData)
    }
}
impl View for OfferedPsksMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OfferedPsksMapper<'_> {
    type Src = SpecOfferedPsksInner;
    type Dst = SpecOfferedPsks;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for OfferedPsksMapper<'a> {
    type Src = OfferedPsksInner<'a>;
    type Dst = OfferedPsks<'a>;
}

pub struct SpecOfferedPsksCombinator(SpecOfferedPsksCombinatorAlias);

impl SpecCombinator for SpecOfferedPsksCombinator {
    type SpecResult = SpecOfferedPsks;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOfferedPsksCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOfferedPsksCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOfferedPsksCombinatorAlias = Mapped<(SpecPskIdentitiesCombinator, SpecPskBinderEntriesCombinator), OfferedPsksMapper<'static>>;

pub struct OfferedPsksCombinator<'a>(OfferedPsksCombinatorAlias<'a>);

impl<'a> View for OfferedPsksCombinator<'a> {
    type V = SpecOfferedPsksCombinator;
    closed spec fn view(&self) -> Self::V { SpecOfferedPsksCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for OfferedPsksCombinator<'a> {
    type Result = OfferedPsks<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type OfferedPsksCombinatorAlias<'a> = Mapped<(PskIdentitiesCombinator<'a>, PskBinderEntriesCombinator<'a>), OfferedPsksMapper<'a>>;


pub closed spec fn spec_offered_psks() -> SpecOfferedPsksCombinator {
    SpecOfferedPsksCombinator(
    Mapped {
        inner: (spec_psk_identities(), spec_psk_binder_entries()),
        mapper: OfferedPsksMapper::spec_new(),
    })
}

                
pub fn offered_psks<'a>() -> (o: OfferedPsksCombinator<'a>)
    ensures o@ == spec_offered_psks(),
{
    OfferedPsksCombinator(
    Mapped {
        inner: (psk_identities(), psk_binder_entries()),
        mapper: OfferedPsksMapper::new(),
    })
}

                

pub struct SpecPreSharedKeyClientExtension {
    pub offers: SpecOfferedPsks,
}

pub type SpecPreSharedKeyClientExtensionInner = SpecOfferedPsks;
impl SpecFrom<SpecPreSharedKeyClientExtension> for SpecPreSharedKeyClientExtensionInner {
    open spec fn spec_from(m: SpecPreSharedKeyClientExtension) -> SpecPreSharedKeyClientExtensionInner {
        m.offers
    }
}
impl SpecFrom<SpecPreSharedKeyClientExtensionInner> for SpecPreSharedKeyClientExtension {
    open spec fn spec_from(m: SpecPreSharedKeyClientExtensionInner) -> SpecPreSharedKeyClientExtension {
        let offers = m;
        SpecPreSharedKeyClientExtension { offers }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PreSharedKeyClientExtension<'a> {
    pub offers: OfferedPsks<'a>,
}

impl View for PreSharedKeyClientExtension<'_> {
    type V = SpecPreSharedKeyClientExtension;

    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyClientExtension {
            offers: self.offers@,
        }
    }
}
pub type PreSharedKeyClientExtensionInner<'a> = OfferedPsks<'a>;
impl<'a> From<PreSharedKeyClientExtension<'a>> for PreSharedKeyClientExtensionInner<'a> {
    fn ex_from(m: PreSharedKeyClientExtension) -> PreSharedKeyClientExtensionInner {
        m.offers
    }
}
impl<'a> From<PreSharedKeyClientExtensionInner<'a>> for PreSharedKeyClientExtension<'a> {
    fn ex_from(m: PreSharedKeyClientExtensionInner) -> PreSharedKeyClientExtension {
        let offers = m;
        PreSharedKeyClientExtension { offers }
    }
}

pub struct PreSharedKeyClientExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> PreSharedKeyClientExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        PreSharedKeyClientExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        PreSharedKeyClientExtensionMapper(PhantomData)
    }
}
impl View for PreSharedKeyClientExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyClientExtensionMapper<'_> {
    type Src = SpecPreSharedKeyClientExtensionInner;
    type Dst = SpecPreSharedKeyClientExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for PreSharedKeyClientExtensionMapper<'a> {
    type Src = PreSharedKeyClientExtensionInner<'a>;
    type Dst = PreSharedKeyClientExtension<'a>;
}

pub struct SpecPreSharedKeyClientExtensionCombinator(SpecPreSharedKeyClientExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    type SpecResult = SpecPreSharedKeyClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPreSharedKeyClientExtensionCombinatorAlias = Mapped<SpecOfferedPsksCombinator, PreSharedKeyClientExtensionMapper<'static>>;

pub struct PreSharedKeyClientExtensionCombinator<'a>(PreSharedKeyClientExtensionCombinatorAlias<'a>);

impl<'a> View for PreSharedKeyClientExtensionCombinator<'a> {
    type V = SpecPreSharedKeyClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PreSharedKeyClientExtensionCombinator<'a> {
    type Result = PreSharedKeyClientExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PreSharedKeyClientExtensionCombinatorAlias<'a> = Mapped<OfferedPsksCombinator<'a>, PreSharedKeyClientExtensionMapper<'a>>;


pub closed spec fn spec_pre_shared_key_client_extension() -> SpecPreSharedKeyClientExtensionCombinator {
    SpecPreSharedKeyClientExtensionCombinator(
    Mapped {
        inner: spec_offered_psks(),
        mapper: PreSharedKeyClientExtensionMapper::spec_new(),
    })
}

                
pub fn pre_shared_key_client_extension<'a>() -> (o: PreSharedKeyClientExtensionCombinator<'a>)
    ensures o@ == spec_pre_shared_key_client_extension(),
{
    PreSharedKeyClientExtensionCombinator(
    Mapped {
        inner: offered_psks(),
        mapper: PreSharedKeyClientExtensionMapper::new(),
    })
}

                
pub type SpecKeyShareClientHelloClientShares = Seq<SpecKeyShareEntry>;
pub type KeyShareClientHelloClientShares<'a> = RepeatResult<KeyShareEntry<'a>>;


pub struct SpecKeyShareClientHelloClientSharesCombinator(SpecKeyShareClientHelloClientSharesCombinatorAlias);

impl SpecCombinator for SpecKeyShareClientHelloClientSharesCombinator {
    type SpecResult = SpecKeyShareClientHelloClientShares;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareClientHelloClientSharesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareClientHelloClientSharesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareClientHelloClientSharesCombinatorAlias = AndThen<Bytes, Repeat<SpecKeyShareEntryCombinator>>;

pub struct KeyShareClientHelloClientSharesCombinator<'a>(KeyShareClientHelloClientSharesCombinatorAlias<'a>);

impl<'a> View for KeyShareClientHelloClientSharesCombinator<'a> {
    type V = SpecKeyShareClientHelloClientSharesCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareClientHelloClientSharesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyShareClientHelloClientSharesCombinator<'a> {
    type Result = KeyShareClientHelloClientShares<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyShareClientHelloClientSharesCombinatorAlias<'a> = AndThen<Bytes, Repeat<KeyShareEntryCombinator<'a>>>;


pub closed spec fn spec_key_share_client_hello_client_shares(l: SpecUint0Ffff) -> SpecKeyShareClientHelloClientSharesCombinator {
    SpecKeyShareClientHelloClientSharesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_key_share_entry())))
}

                
pub fn key_share_client_hello_client_shares<'a>(l: Uint0Ffff) -> (o: KeyShareClientHelloClientSharesCombinator<'a>)
    ensures o@ == spec_key_share_client_hello_client_shares(l@),
{
    KeyShareClientHelloClientSharesCombinator(AndThen(Bytes(l.ex_into()), Repeat(key_share_entry())))
}

                

pub struct SpecKeyShareClientHello {
    pub l: SpecUint0Ffff,
    pub client_shares: SpecKeyShareClientHelloClientShares,
}

pub type SpecKeyShareClientHelloInner = (SpecUint0Ffff, SpecKeyShareClientHelloClientShares);
impl SpecFrom<SpecKeyShareClientHello> for SpecKeyShareClientHelloInner {
    open spec fn spec_from(m: SpecKeyShareClientHello) -> SpecKeyShareClientHelloInner {
        (m.l, m.client_shares)
    }
}
impl SpecFrom<SpecKeyShareClientHelloInner> for SpecKeyShareClientHello {
    open spec fn spec_from(m: SpecKeyShareClientHelloInner) -> SpecKeyShareClientHello {
        let (l, client_shares) = m;
        SpecKeyShareClientHello { l, client_shares }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct KeyShareClientHello<'a> {
    pub l: Uint0Ffff,
    pub client_shares: KeyShareClientHelloClientShares<'a>,
}

impl View for KeyShareClientHello<'_> {
    type V = SpecKeyShareClientHello;

    open spec fn view(&self) -> Self::V {
        SpecKeyShareClientHello {
            l: self.l@,
            client_shares: self.client_shares@,
        }
    }
}
pub type KeyShareClientHelloInner<'a> = (Uint0Ffff, KeyShareClientHelloClientShares<'a>);
impl<'a> From<KeyShareClientHello<'a>> for KeyShareClientHelloInner<'a> {
    fn ex_from(m: KeyShareClientHello) -> KeyShareClientHelloInner {
        (m.l, m.client_shares)
    }
}
impl<'a> From<KeyShareClientHelloInner<'a>> for KeyShareClientHello<'a> {
    fn ex_from(m: KeyShareClientHelloInner) -> KeyShareClientHello {
        let (l, client_shares) = m;
        KeyShareClientHello { l, client_shares }
    }
}

pub struct KeyShareClientHelloMapper<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareClientHelloMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        KeyShareClientHelloMapper(PhantomData)
    }
    pub fn new() -> Self {
        KeyShareClientHelloMapper(PhantomData)
    }
}
impl View for KeyShareClientHelloMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareClientHelloMapper<'_> {
    type Src = SpecKeyShareClientHelloInner;
    type Dst = SpecKeyShareClientHello;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for KeyShareClientHelloMapper<'a> {
    type Src = KeyShareClientHelloInner<'a>;
    type Dst = KeyShareClientHello<'a>;
}

pub struct SpecKeyShareClientHelloCombinator(SpecKeyShareClientHelloCombinatorAlias);

impl SpecCombinator for SpecKeyShareClientHelloCombinator {
    type SpecResult = SpecKeyShareClientHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareClientHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareClientHelloCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecKeyShareClientHelloClientSharesCombinator>, KeyShareClientHelloMapper<'static>>;

pub struct KeyShareClientHelloCombinator<'a>(KeyShareClientHelloCombinatorAlias<'a>);

impl<'a> View for KeyShareClientHelloCombinator<'a> {
    type V = SpecKeyShareClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareClientHelloCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyShareClientHelloCombinator<'a> {
    type Result = KeyShareClientHello<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyShareClientHelloCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, KeyShareClientHelloClientSharesCombinator<'a>, KeyShareClientHelloCont0<'a>>, KeyShareClientHelloMapper<'a>>;


pub closed spec fn spec_key_share_client_hello() -> SpecKeyShareClientHelloCombinator {
    SpecKeyShareClientHelloCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_key_share_client_hello_cont0(deps) },
        mapper: KeyShareClientHelloMapper::spec_new(),
    })
}

pub open spec fn spec_key_share_client_hello_cont0(deps: SpecUint0Ffff) -> SpecKeyShareClientHelloClientSharesCombinator {
    let l = deps;
    spec_key_share_client_hello_client_shares(l)
}
                
pub fn key_share_client_hello<'a>() -> (o: KeyShareClientHelloCombinator<'a>)
    ensures o@ == spec_key_share_client_hello(),
{
    KeyShareClientHelloCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: KeyShareClientHelloCont0::new(), spec_snd: Ghost(|deps| spec_key_share_client_hello_cont0(deps)) },
        mapper: KeyShareClientHelloMapper::new(),
    })
}

pub struct KeyShareClientHelloCont0<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareClientHelloCont0<'a> {
    pub fn new() -> Self {
        KeyShareClientHelloCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for KeyShareClientHelloCont0<'a> {
    type Output = KeyShareClientHelloClientSharesCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_key_share_client_hello_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        key_share_client_hello_client_shares(l)
    }
}
                

pub struct SpecPskKeyExchangeModes {
    pub l: SpecUint1Ff,
    pub modes: SpecPskKeyExchangeModesModes,
}

pub type SpecPskKeyExchangeModesInner = (SpecUint1Ff, SpecPskKeyExchangeModesModes);
impl SpecFrom<SpecPskKeyExchangeModes> for SpecPskKeyExchangeModesInner {
    open spec fn spec_from(m: SpecPskKeyExchangeModes) -> SpecPskKeyExchangeModesInner {
        (m.l, m.modes)
    }
}
impl SpecFrom<SpecPskKeyExchangeModesInner> for SpecPskKeyExchangeModes {
    open spec fn spec_from(m: SpecPskKeyExchangeModesInner) -> SpecPskKeyExchangeModes {
        let (l, modes) = m;
        SpecPskKeyExchangeModes { l, modes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskKeyExchangeModes {
    pub l: Uint1Ff,
    pub modes: PskKeyExchangeModesModes,
}

impl View for PskKeyExchangeModes {
    type V = SpecPskKeyExchangeModes;

    open spec fn view(&self) -> Self::V {
        SpecPskKeyExchangeModes {
            l: self.l@,
            modes: self.modes@,
        }
    }
}
pub type PskKeyExchangeModesInner = (Uint1Ff, PskKeyExchangeModesModes);
impl From<PskKeyExchangeModes> for PskKeyExchangeModesInner {
    fn ex_from(m: PskKeyExchangeModes) -> PskKeyExchangeModesInner {
        (m.l, m.modes)
    }
}
impl From<PskKeyExchangeModesInner> for PskKeyExchangeModes {
    fn ex_from(m: PskKeyExchangeModesInner) -> PskKeyExchangeModes {
        let (l, modes) = m;
        PskKeyExchangeModes { l, modes }
    }
}

pub struct PskKeyExchangeModesMapper;
impl PskKeyExchangeModesMapper {
    pub closed spec fn spec_new() -> Self {
        PskKeyExchangeModesMapper
    }
    pub fn new() -> Self {
        PskKeyExchangeModesMapper
    }
}
impl View for PskKeyExchangeModesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskKeyExchangeModesMapper {
    type Src = SpecPskKeyExchangeModesInner;
    type Dst = SpecPskKeyExchangeModes;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for PskKeyExchangeModesMapper {
    type Src = PskKeyExchangeModesInner;
    type Dst = PskKeyExchangeModes;
}

pub struct SpecPskKeyExchangeModesCombinator(SpecPskKeyExchangeModesCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModesCombinator {
    type SpecResult = SpecPskKeyExchangeModes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModesCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecPskKeyExchangeModesModesCombinator>, PskKeyExchangeModesMapper>;

pub struct PskKeyExchangeModesCombinator<'a>(PskKeyExchangeModesCombinatorAlias<'a>);

impl<'a> View for PskKeyExchangeModesCombinator<'a> {
    type V = SpecPskKeyExchangeModesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for PskKeyExchangeModesCombinator<'a> {
    type Result = PskKeyExchangeModes;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type PskKeyExchangeModesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, PskKeyExchangeModesModesCombinator, PskKeyExchangeModesCont0<'a>>, PskKeyExchangeModesMapper>;


pub closed spec fn spec_psk_key_exchange_modes() -> SpecPskKeyExchangeModesCombinator {
    SpecPskKeyExchangeModesCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_1_ff(), snd: |deps| spec_psk_key_exchange_modes_cont0(deps) },
        mapper: PskKeyExchangeModesMapper::spec_new(),
    })
}

pub open spec fn spec_psk_key_exchange_modes_cont0(deps: SpecUint1Ff) -> SpecPskKeyExchangeModesModesCombinator {
    let l = deps;
    spec_psk_key_exchange_modes_modes(l)
}
                
pub fn psk_key_exchange_modes<'a>() -> (o: PskKeyExchangeModesCombinator<'a>)
    ensures o@ == spec_psk_key_exchange_modes(),
{
    PskKeyExchangeModesCombinator(
    Mapped {
        inner: Depend { fst: uint_1_ff(), snd: PskKeyExchangeModesCont0::new(), spec_snd: Ghost(|deps| spec_psk_key_exchange_modes_cont0(deps)) },
        mapper: PskKeyExchangeModesMapper::new(),
    })
}

pub struct PskKeyExchangeModesCont0<'a>(PhantomData<&'a ()>);
impl<'a> PskKeyExchangeModesCont0<'a> {
    pub fn new() -> Self {
        PskKeyExchangeModesCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint1Ff> for PskKeyExchangeModesCont0<'a> {
    type Output = PskKeyExchangeModesModesCombinator;

    open spec fn requires(&self, deps: &Uint1Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_psk_key_exchange_modes_cont0(deps@)
    }

    fn apply(&self, deps: &Uint1Ff) -> Self::Output {
        let l = *deps;
        psk_key_exchange_modes_modes(l)
    }
}
                
pub type SpecSupportedVersionsClientVersions = Seq<SpecProtocolVersion>;
pub type SupportedVersionsClientVersions = RepeatResult<ProtocolVersion>;


pub struct SpecSupportedVersionsClientVersionsCombinator(SpecSupportedVersionsClientVersionsCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsClientVersionsCombinator {
    type SpecResult = SpecSupportedVersionsClientVersions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsClientVersionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsClientVersionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsClientVersionsCombinatorAlias = AndThen<Bytes, Repeat<SpecProtocolVersionCombinator>>;

pub struct SupportedVersionsClientVersionsCombinator(SupportedVersionsClientVersionsCombinatorAlias);

impl View for SupportedVersionsClientVersionsCombinator {
    type V = SpecSupportedVersionsClientVersionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsClientVersionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SupportedVersionsClientVersionsCombinator {
    type Result = SupportedVersionsClientVersions;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SupportedVersionsClientVersionsCombinatorAlias = AndThen<Bytes, Repeat<ProtocolVersionCombinator>>;


pub closed spec fn spec_supported_versions_client_versions(l: u8) -> SpecSupportedVersionsClientVersionsCombinator {
    SpecSupportedVersionsClientVersionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_protocol_version())))
}

                
pub fn supported_versions_client_versions<'a>(l: u8) -> (o: SupportedVersionsClientVersionsCombinator)
    ensures o@ == spec_supported_versions_client_versions(l@),
{
    SupportedVersionsClientVersionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(protocol_version())))
}

                

pub struct SpecSupportedVersionsClient {
    pub l: u8,
    pub versions: SpecSupportedVersionsClientVersions,
}

pub type SpecSupportedVersionsClientInner = (u8, SpecSupportedVersionsClientVersions);
impl SpecFrom<SpecSupportedVersionsClient> for SpecSupportedVersionsClientInner {
    open spec fn spec_from(m: SpecSupportedVersionsClient) -> SpecSupportedVersionsClientInner {
        (m.l, m.versions)
    }
}
impl SpecFrom<SpecSupportedVersionsClientInner> for SpecSupportedVersionsClient {
    open spec fn spec_from(m: SpecSupportedVersionsClientInner) -> SpecSupportedVersionsClient {
        let (l, versions) = m;
        SpecSupportedVersionsClient { l, versions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SupportedVersionsClient {
    pub l: u8,
    pub versions: SupportedVersionsClientVersions,
}

impl View for SupportedVersionsClient {
    type V = SpecSupportedVersionsClient;

    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsClient {
            l: self.l@,
            versions: self.versions@,
        }
    }
}
pub type SupportedVersionsClientInner = (u8, SupportedVersionsClientVersions);
impl From<SupportedVersionsClient> for SupportedVersionsClientInner {
    fn ex_from(m: SupportedVersionsClient) -> SupportedVersionsClientInner {
        (m.l, m.versions)
    }
}
impl From<SupportedVersionsClientInner> for SupportedVersionsClient {
    fn ex_from(m: SupportedVersionsClientInner) -> SupportedVersionsClient {
        let (l, versions) = m;
        SupportedVersionsClient { l, versions }
    }
}

pub struct SupportedVersionsClientMapper;
impl SupportedVersionsClientMapper {
    pub closed spec fn spec_new() -> Self {
        SupportedVersionsClientMapper
    }
    pub fn new() -> Self {
        SupportedVersionsClientMapper
    }
}
impl View for SupportedVersionsClientMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SupportedVersionsClientMapper {
    type Src = SpecSupportedVersionsClientInner;
    type Dst = SpecSupportedVersionsClient;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for SupportedVersionsClientMapper {
    type Src = SupportedVersionsClientInner;
    type Dst = SupportedVersionsClient;
}

pub struct SpecSupportedVersionsClientCombinator(SpecSupportedVersionsClientCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsClientCombinator {
    type SpecResult = SpecSupportedVersionsClient;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsClientCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsClientCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsClientCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate7700940249185834031>, SpecSupportedVersionsClientVersionsCombinator>, SupportedVersionsClientMapper>;
pub struct Predicate7700940249185834031;
impl View for Predicate7700940249185834031 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate7700940249185834031 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 254)
    }
}
impl SpecPred for Predicate7700940249185834031 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 2 && i <= 254)
    }
}

pub struct SupportedVersionsClientCombinator<'a>(SupportedVersionsClientCombinatorAlias<'a>);

impl<'a> View for SupportedVersionsClientCombinator<'a> {
    type V = SpecSupportedVersionsClientCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsClientCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SupportedVersionsClientCombinator<'a> {
    type Result = SupportedVersionsClient;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SupportedVersionsClientCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate7700940249185834031>, SupportedVersionsClientVersionsCombinator, SupportedVersionsClientCont0<'a>>, SupportedVersionsClientMapper>;


pub closed spec fn spec_supported_versions_client() -> SpecSupportedVersionsClientCombinator {
    SpecSupportedVersionsClientCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U8, predicate: Predicate7700940249185834031 }, snd: |deps| spec_supported_versions_client_cont0(deps) },
        mapper: SupportedVersionsClientMapper::spec_new(),
    })
}

pub open spec fn spec_supported_versions_client_cont0(deps: u8) -> SpecSupportedVersionsClientVersionsCombinator {
    let l = deps;
    spec_supported_versions_client_versions(l)
}
                
pub fn supported_versions_client<'a>() -> (o: SupportedVersionsClientCombinator<'a>)
    ensures o@ == spec_supported_versions_client(),
{
    SupportedVersionsClientCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U8, predicate: Predicate7700940249185834031 }, snd: SupportedVersionsClientCont0::new(), spec_snd: Ghost(|deps| spec_supported_versions_client_cont0(deps)) },
        mapper: SupportedVersionsClientMapper::new(),
    })
}

pub struct SupportedVersionsClientCont0<'a>(PhantomData<&'a ()>);
impl<'a> SupportedVersionsClientCont0<'a> {
    pub fn new() -> Self {
        SupportedVersionsClientCont0(PhantomData)
    }
}
impl<'a> Continuation<&u8> for SupportedVersionsClientCont0<'a> {
    type Output = SupportedVersionsClientVersionsCombinator;

    open spec fn requires(&self, deps: &u8) -> bool { true }

    open spec fn ensures(&self, deps: &u8, o: Self::Output) -> bool {
        o@ == spec_supported_versions_client_cont0(deps@)
    }

    fn apply(&self, deps: &u8) -> Self::Output {
        let l = *deps;
        supported_versions_client_versions(l)
    }
}
                
pub type SpecDistinguishedName = SpecOpaque1Ffff;
pub type DistinguishedName<'a> = Opaque1Ffff<'a>;


pub struct SpecDistinguishedNameCombinator(SpecDistinguishedNameCombinatorAlias);

impl SpecCombinator for SpecDistinguishedNameCombinator {
    type SpecResult = SpecDistinguishedName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecDistinguishedNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDistinguishedNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecDistinguishedNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct DistinguishedNameCombinator<'a>(DistinguishedNameCombinatorAlias<'a>);

impl<'a> View for DistinguishedNameCombinator<'a> {
    type V = SpecDistinguishedNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecDistinguishedNameCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for DistinguishedNameCombinator<'a> {
    type Result = DistinguishedName<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DistinguishedNameCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_distinguished_name() -> SpecDistinguishedNameCombinator {
    SpecDistinguishedNameCombinator(spec_opaque_1_ffff())
}

                
pub fn distinguished_name<'a>() -> (o: DistinguishedNameCombinator<'a>)
    ensures o@ == spec_distinguished_name(),
{
    DistinguishedNameCombinator(opaque_1_ffff())
}

                
pub type SpecCertificateAuthoritiesExtensionAuthorities = Seq<SpecDistinguishedName>;
pub type CertificateAuthoritiesExtensionAuthorities<'a> = RepeatResult<DistinguishedName<'a>>;


pub struct SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias);

impl SpecCombinator for SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    type SpecResult = SpecCertificateAuthoritiesExtensionAuthorities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias = AndThen<Bytes, Repeat<SpecDistinguishedNameCombinator>>;

pub struct CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>(CertificateAuthoritiesExtensionAuthoritiesCombinatorAlias<'a>);

impl<'a> View for CertificateAuthoritiesExtensionAuthoritiesCombinator<'a> {
    type V = SpecCertificateAuthoritiesExtensionAuthoritiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateAuthoritiesExtensionAuthoritiesCombinator<'a> {
    type Result = CertificateAuthoritiesExtensionAuthorities<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateAuthoritiesExtensionAuthoritiesCombinatorAlias<'a> = AndThen<Bytes, Repeat<DistinguishedNameCombinator<'a>>>;


pub closed spec fn spec_certificate_authorities_extension_authorities(l: u16) -> SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_distinguished_name())))
}

                
pub fn certificate_authorities_extension_authorities<'a>(l: u16) -> (o: CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>)
    ensures o@ == spec_certificate_authorities_extension_authorities(l@),
{
    CertificateAuthoritiesExtensionAuthoritiesCombinator(AndThen(Bytes(l.ex_into()), Repeat(distinguished_name())))
}

                

pub struct SpecCertificateAuthoritiesExtension {
    pub l: u16,
    pub authorities: SpecCertificateAuthoritiesExtensionAuthorities,
}

pub type SpecCertificateAuthoritiesExtensionInner = (u16, SpecCertificateAuthoritiesExtensionAuthorities);
impl SpecFrom<SpecCertificateAuthoritiesExtension> for SpecCertificateAuthoritiesExtensionInner {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtension) -> SpecCertificateAuthoritiesExtensionInner {
        (m.l, m.authorities)
    }
}
impl SpecFrom<SpecCertificateAuthoritiesExtensionInner> for SpecCertificateAuthoritiesExtension {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtensionInner) -> SpecCertificateAuthoritiesExtension {
        let (l, authorities) = m;
        SpecCertificateAuthoritiesExtension { l, authorities }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateAuthoritiesExtension<'a> {
    pub l: u16,
    pub authorities: CertificateAuthoritiesExtensionAuthorities<'a>,
}

impl View for CertificateAuthoritiesExtension<'_> {
    type V = SpecCertificateAuthoritiesExtension;

    open spec fn view(&self) -> Self::V {
        SpecCertificateAuthoritiesExtension {
            l: self.l@,
            authorities: self.authorities@,
        }
    }
}
pub type CertificateAuthoritiesExtensionInner<'a> = (u16, CertificateAuthoritiesExtensionAuthorities<'a>);
impl<'a> From<CertificateAuthoritiesExtension<'a>> for CertificateAuthoritiesExtensionInner<'a> {
    fn ex_from(m: CertificateAuthoritiesExtension) -> CertificateAuthoritiesExtensionInner {
        (m.l, m.authorities)
    }
}
impl<'a> From<CertificateAuthoritiesExtensionInner<'a>> for CertificateAuthoritiesExtension<'a> {
    fn ex_from(m: CertificateAuthoritiesExtensionInner) -> CertificateAuthoritiesExtension {
        let (l, authorities) = m;
        CertificateAuthoritiesExtension { l, authorities }
    }
}

pub struct CertificateAuthoritiesExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateAuthoritiesExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateAuthoritiesExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateAuthoritiesExtensionMapper(PhantomData)
    }
}
impl View for CertificateAuthoritiesExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateAuthoritiesExtensionMapper<'_> {
    type Src = SpecCertificateAuthoritiesExtensionInner;
    type Dst = SpecCertificateAuthoritiesExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateAuthoritiesExtensionMapper<'a> {
    type Src = CertificateAuthoritiesExtensionInner<'a>;
    type Dst = CertificateAuthoritiesExtension<'a>;
}

pub struct SpecCertificateAuthoritiesExtensionCombinator(SpecCertificateAuthoritiesExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    type SpecResult = SpecCertificateAuthoritiesExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateAuthoritiesExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateAuthoritiesExtensionCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate12905524399844557818>, SpecCertificateAuthoritiesExtensionAuthoritiesCombinator>, CertificateAuthoritiesExtensionMapper<'static>>;
pub struct Predicate12905524399844557818;
impl View for Predicate12905524399844557818 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate12905524399844557818 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}
impl SpecPred for Predicate12905524399844557818 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}

pub struct CertificateAuthoritiesExtensionCombinator<'a>(CertificateAuthoritiesExtensionCombinatorAlias<'a>);

impl<'a> View for CertificateAuthoritiesExtensionCombinator<'a> {
    type V = SpecCertificateAuthoritiesExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateAuthoritiesExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateAuthoritiesExtensionCombinator<'a> {
    type Result = CertificateAuthoritiesExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateAuthoritiesExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate12905524399844557818>, CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>, CertificateAuthoritiesExtensionCont0<'a>>, CertificateAuthoritiesExtensionMapper<'a>>;


pub closed spec fn spec_certificate_authorities_extension() -> SpecCertificateAuthoritiesExtensionCombinator {
    SpecCertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate12905524399844557818 }, snd: |deps| spec_certificate_authorities_extension_cont0(deps) },
        mapper: CertificateAuthoritiesExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_authorities_extension_cont0(deps: u16) -> SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    let l = deps;
    spec_certificate_authorities_extension_authorities(l)
}
                
pub fn certificate_authorities_extension<'a>() -> (o: CertificateAuthoritiesExtensionCombinator<'a>)
    ensures o@ == spec_certificate_authorities_extension(),
{
    CertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate12905524399844557818 }, snd: CertificateAuthoritiesExtensionCont0::new(), spec_snd: Ghost(|deps| spec_certificate_authorities_extension_cont0(deps)) },
        mapper: CertificateAuthoritiesExtensionMapper::new(),
    })
}

pub struct CertificateAuthoritiesExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateAuthoritiesExtensionCont0<'a> {
    pub fn new() -> Self {
        CertificateAuthoritiesExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for CertificateAuthoritiesExtensionCont0<'a> {
    type Output = CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_certificate_authorities_extension_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        certificate_authorities_extension_authorities(l)
    }
}
                

pub enum SpecClientHelloExtensionExtensionData {
    ServerName(SpecServerNameList),
    MaxFragmentLength(SpecMaxFragmentLength),
    StatusRequest(SpecCertificateStatusRequest),
    SupportedGroups(SpecNamedGroupList),
    ECPointFormats(SpecEcPointFormatList),
    SignatureAlgorithms(SpecSignatureSchemeList),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SignedCertificateTimeStamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(SpecPaddingExtension),
    EncryptThenMac(SpecEmpty),
    ExtendedMasterSecret(SpecEmpty),
    SessionTicket(Seq<u8>),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    KeyShare(SpecKeyShareClientHello),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    EarlyData(SpecEmpty),
    SupportedVersions(SpecSupportedVersionsClient),
    Cookie(SpecCookie),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    PostHandshakeAuth(SpecEmpty),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    Unrecognized(Seq<u8>),
}

pub type SpecClientHelloExtensionExtensionDataInner = Either<SpecServerNameList, Either<SpecMaxFragmentLength, Either<SpecCertificateStatusRequest, Either<SpecNamedGroupList, Either<SpecEcPointFormatList, Either<SpecSignatureSchemeList, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecPaddingExtension, Either<SpecEmpty, Either<SpecEmpty, Either<Seq<u8>, Either<SpecPreSharedKeyClientExtension, Either<SpecKeyShareClientHello, Either<SpecPskKeyExchangeModes, Either<SpecEmpty, Either<SpecSupportedVersionsClient, Either<SpecCookie, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecEmpty, Either<SpecSignatureSchemeList, Seq<u8>>>>>>>>>>>>>>>>>>>>>>>>>>;



impl SpecFrom<SpecClientHelloExtensionExtensionData> for SpecClientHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionData) -> SpecClientHelloExtensionExtensionDataInner {
        match m {
            SpecClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecClientHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))),
        }
    }

}

impl SpecFrom<SpecClientHelloExtensionExtensionDataInner> for SpecClientHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionDataInner) -> SpecClientHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClientHelloExtensionExtensionData<'a> {
    ServerName(ServerNameList<'a>),
    MaxFragmentLength(MaxFragmentLength),
    StatusRequest(CertificateStatusRequest<'a>),
    SupportedGroups(NamedGroupList),
    ECPointFormats(EcPointFormatList),
    SignatureAlgorithms(SignatureSchemeList),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SignedCertificateTimeStamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(PaddingExtension),
    EncryptThenMac(Empty<'a>),
    ExtendedMasterSecret(Empty<'a>),
    SessionTicket(&'a [u8]),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    KeyShare(KeyShareClientHello<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    EarlyData(Empty<'a>),
    SupportedVersions(SupportedVersionsClient),
    Cookie(Cookie<'a>),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    PostHandshakeAuth(Empty<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    Unrecognized(&'a [u8]),
}

pub type ClientHelloExtensionExtensionDataInner<'a> = Either<ServerNameList<'a>, Either<MaxFragmentLength, Either<CertificateStatusRequest<'a>, Either<NamedGroupList, Either<EcPointFormatList, Either<SignatureSchemeList, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<PaddingExtension, Either<Empty<'a>, Either<Empty<'a>, Either<&'a [u8], Either<PreSharedKeyClientExtension<'a>, Either<KeyShareClientHello<'a>, Either<PskKeyExchangeModes, Either<Empty<'a>, Either<SupportedVersionsClient, Either<Cookie<'a>, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<Empty<'a>, Either<SignatureSchemeList, &'a [u8]>>>>>>>>>>>>>>>>>>>>>>>>>;


impl<'a> View for ClientHelloExtensionExtensionData<'a> {
    type V = SpecClientHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionExtensionData::ServerName(m) => SpecClientHelloExtensionExtensionData::ServerName(m@),
            ClientHelloExtensionExtensionData::MaxFragmentLength(m) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m@),
            ClientHelloExtensionExtensionData::StatusRequest(m) => SpecClientHelloExtensionExtensionData::StatusRequest(m@),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => SpecClientHelloExtensionExtensionData::SupportedGroups(m@),
            ClientHelloExtensionExtensionData::ECPointFormats(m) => SpecClientHelloExtensionExtensionData::ECPointFormats(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m@),
            ClientHelloExtensionExtensionData::Heartbeat(m) => SpecClientHelloExtensionExtensionData::Heartbeat(m@),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            ClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m) => SpecClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m@),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m@),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m@),
            ClientHelloExtensionExtensionData::Padding(m) => SpecClientHelloExtensionExtensionData::Padding(m@),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m@),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            ClientHelloExtensionExtensionData::SessionTicket(m) => SpecClientHelloExtensionExtensionData::SessionTicket(m@),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => SpecClientHelloExtensionExtensionData::PreSharedKey(m@),
            ClientHelloExtensionExtensionData::KeyShare(m) => SpecClientHelloExtensionExtensionData::KeyShare(m@),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            ClientHelloExtensionExtensionData::EarlyData(m) => SpecClientHelloExtensionExtensionData::EarlyData(m@),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => SpecClientHelloExtensionExtensionData::SupportedVersions(m@),
            ClientHelloExtensionExtensionData::Cookie(m) => SpecClientHelloExtensionExtensionData::Cookie(m@),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m@),
            ClientHelloExtensionExtensionData::OidFilters(m) => SpecClientHelloExtensionExtensionData::OidFilters(m@),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            ClientHelloExtensionExtensionData::Unrecognized(m) => SpecClientHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<ClientHelloExtensionExtensionData<'a>> for ClientHelloExtensionExtensionDataInner<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionData<'a>) -> ClientHelloExtensionExtensionDataInner<'a> {
        match m {
            ClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            ClientHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            ClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))),
        }
    }

}

impl<'a> From<ClientHelloExtensionExtensionDataInner<'a>> for ClientHelloExtensionExtensionData<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionDataInner<'a>) -> ClientHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => ClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))) => ClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct ClientHelloExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ClientHelloExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        ClientHelloExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for ClientHelloExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionExtensionDataMapper<'_> {
    type Src = SpecClientHelloExtensionExtensionDataInner;
    type Dst = SpecClientHelloExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ClientHelloExtensionExtensionDataMapper<'a> {
    type Src = ClientHelloExtensionExtensionDataInner<'a>;
    type Dst = ClientHelloExtensionExtensionData<'a>;
}


pub struct SpecClientHelloExtensionExtensionDataCombinator(SpecClientHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    type SpecResult = SpecClientHelloExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecServerNameListCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecCertificateStatusRequestCombinator>, OrdChoice<Cond<SpecNamedGroupListCombinator>, OrdChoice<Cond<SpecEcPointFormatListCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecPaddingExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<Bytes>, OrdChoice<Cond<SpecPreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<SpecKeyShareClientHelloCombinator>, OrdChoice<Cond<SpecPskKeyExchangeModesCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSupportedVersionsClientCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper<'static>>>;

pub struct ClientHelloExtensionExtensionDataCombinator<'a>(ClientHelloExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for ClientHelloExtensionExtensionDataCombinator<'a> {
    type V = SpecClientHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientHelloExtensionExtensionDataCombinator<'a> {
    type Result = ClientHelloExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientHelloExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<ServerNameListCombinator<'a>>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<CertificateStatusRequestCombinator<'a>>, OrdChoice<Cond<NamedGroupListCombinator<'a>>, OrdChoice<Cond<EcPointFormatListCombinator<'a>>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator<'a>>, OrdChoice<Cond<SignedCertificateTimestampListCombinator<'a>>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<PaddingExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<Bytes>, OrdChoice<Cond<PreSharedKeyClientExtensionCombinator<'a>>, OrdChoice<Cond<KeyShareClientHelloCombinator<'a>>, OrdChoice<Cond<PskKeyExchangeModesCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SupportedVersionsClientCombinator<'a>>, OrdChoice<Cond<CookieCombinator<'a>>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator<'a>>, OrdChoice<Cond<OidFilterExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_client_hello_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecClientHelloExtensionExtensionDataCombinator {
    SpecClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: spec_ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: spec_padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: Bytes(ext_len.spec_into()) }, OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, OrdChoice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) }))))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn client_hello_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: ClientHelloExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_client_hello_extension_extension_data(extension_type@, ext_len@),
{
    ClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 0, inner: server_name_list() }, OrdChoice::new(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice::new(Cond { cond: extension_type == 5, inner: certificate_status_request() }, OrdChoice::new(Cond { cond: extension_type == 10, inner: named_group_list() }, OrdChoice::new(Cond { cond: extension_type == 11, inner: ec_point_format_list() }, OrdChoice::new(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, OrdChoice::new(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice::new(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice::new(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice::new(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice::new(Cond { cond: extension_type == 21, inner: padding_extension() }, OrdChoice::new(Cond { cond: extension_type == 22, inner: empty() }, OrdChoice::new(Cond { cond: extension_type == 23, inner: empty() }, OrdChoice::new(Cond { cond: extension_type == 35, inner: Bytes(ext_len.ex_into()) }, OrdChoice::new(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, OrdChoice::new(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, OrdChoice::new(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, OrdChoice::new(Cond { cond: extension_type == 42, inner: empty() }, OrdChoice::new(Cond { cond: extension_type == 43, inner: supported_versions_client() }, OrdChoice::new(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice::new(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice::new(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, OrdChoice::new(Cond { cond: extension_type == 49, inner: empty() }, OrdChoice::new(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) }))))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecClientHelloExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecClientHelloExtensionExtensionData,
}

pub type SpecClientHelloExtensionInner = ((SpecExtensionType, u16), SpecClientHelloExtensionExtensionData);
impl SpecFrom<SpecClientHelloExtension> for SpecClientHelloExtensionInner {
    open spec fn spec_from(m: SpecClientHelloExtension) -> SpecClientHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecClientHelloExtensionInner> for SpecClientHelloExtension {
    open spec fn spec_from(m: SpecClientHelloExtensionInner) -> SpecClientHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecClientHelloExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: ClientHelloExtensionExtensionData<'a>,
}

impl View for ClientHelloExtension<'_> {
    type V = SpecClientHelloExtension;

    open spec fn view(&self) -> Self::V {
        SpecClientHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type ClientHelloExtensionInner<'a> = ((ExtensionType, u16), ClientHelloExtensionExtensionData<'a>);
impl<'a> From<ClientHelloExtension<'a>> for ClientHelloExtensionInner<'a> {
    fn ex_from(m: ClientHelloExtension) -> ClientHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<ClientHelloExtensionInner<'a>> for ClientHelloExtension<'a> {
    fn ex_from(m: ClientHelloExtensionInner) -> ClientHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        ClientHelloExtension { extension_type, ext_len, extension_data }
    }
}

pub struct ClientHelloExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ClientHelloExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        ClientHelloExtensionMapper(PhantomData)
    }
}
impl View for ClientHelloExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionMapper<'_> {
    type Src = SpecClientHelloExtensionInner;
    type Dst = SpecClientHelloExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ClientHelloExtensionMapper<'a> {
    type Src = ClientHelloExtensionInner<'a>;
    type Dst = ClientHelloExtension<'a>;
}

pub struct SpecClientHelloExtensionCombinator(SpecClientHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionCombinator {
    type SpecResult = SpecClientHelloExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecClientHelloExtensionExtensionDataCombinator>, ClientHelloExtensionMapper<'static>>;

pub struct ClientHelloExtensionCombinator<'a>(ClientHelloExtensionCombinatorAlias<'a>);

impl<'a> View for ClientHelloExtensionCombinator<'a> {
    type V = SpecClientHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientHelloExtensionCombinator<'a> {
    type Result = ClientHelloExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientHelloExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, ClientHelloExtensionCont1<'a>>, ClientHelloExtensionExtensionDataCombinator<'a>, ClientHelloExtensionCont0<'a>>, ClientHelloExtensionMapper<'a>>;


pub closed spec fn spec_client_hello_extension() -> SpecClientHelloExtensionCombinator {
    SpecClientHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_client_hello_extension_cont1(deps) }, snd: |deps| spec_client_hello_extension_cont0(deps) },
        mapper: ClientHelloExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_client_hello_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_client_hello_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecClientHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_client_hello_extension_extension_data(extension_type, ext_len)
}
                
pub fn client_hello_extension<'a>() -> (o: ClientHelloExtensionCombinator<'a>)
    ensures o@ == spec_client_hello_extension(),
{
    ClientHelloExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: ClientHelloExtensionCont1::new(), spec_snd: Ghost(|deps| spec_client_hello_extension_cont1(deps)) }, snd: ClientHelloExtensionCont0::new(), spec_snd: Ghost(|deps| spec_client_hello_extension_cont0(deps)) },
        mapper: ClientHelloExtensionMapper::new(),
    })
}

pub struct ClientHelloExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloExtensionCont1<'a> {
    pub fn new() -> Self {
        ClientHelloExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for ClientHelloExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct ClientHelloExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloExtensionCont0<'a> {
    pub fn new() -> Self {
        ClientHelloExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for ClientHelloExtensionCont0<'a> {
    type Output = ClientHelloExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        client_hello_extension_extension_data(extension_type, ext_len)
    }
}
                
pub type SpecClientExtensionsExtensions = Seq<SpecClientHelloExtension>;
pub type ClientExtensionsExtensions<'a> = RepeatResult<ClientHelloExtension<'a>>;


pub struct SpecClientExtensionsExtensionsCombinator(SpecClientExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecClientExtensionsExtensionsCombinator {
    type SpecResult = SpecClientExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecClientHelloExtensionCombinator>>;

pub struct ClientExtensionsExtensionsCombinator<'a>(ClientExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for ClientExtensionsExtensionsCombinator<'a> {
    type V = SpecClientExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientExtensionsExtensionsCombinator<'a> {
    type Result = ClientExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<ClientHelloExtensionCombinator<'a>>>;


pub closed spec fn spec_client_extensions_extensions(l: u16) -> SpecClientExtensionsExtensionsCombinator {
    SpecClientExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_client_hello_extension())))
}

                
pub fn client_extensions_extensions<'a>(l: u16) -> (o: ClientExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_client_extensions_extensions(l@),
{
    ClientExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(client_hello_extension())))
}

                

pub struct SpecClientExtensions {
    pub l: u16,
    pub extensions: SpecClientExtensionsExtensions,
}

pub type SpecClientExtensionsInner = (u16, SpecClientExtensionsExtensions);
impl SpecFrom<SpecClientExtensions> for SpecClientExtensionsInner {
    open spec fn spec_from(m: SpecClientExtensions) -> SpecClientExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecClientExtensionsInner> for SpecClientExtensions {
    open spec fn spec_from(m: SpecClientExtensionsInner) -> SpecClientExtensions {
        let (l, extensions) = m;
        SpecClientExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientExtensions<'a> {
    pub l: u16,
    pub extensions: ClientExtensionsExtensions<'a>,
}

impl View for ClientExtensions<'_> {
    type V = SpecClientExtensions;

    open spec fn view(&self) -> Self::V {
        SpecClientExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type ClientExtensionsInner<'a> = (u16, ClientExtensionsExtensions<'a>);
impl<'a> From<ClientExtensions<'a>> for ClientExtensionsInner<'a> {
    fn ex_from(m: ClientExtensions) -> ClientExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<ClientExtensionsInner<'a>> for ClientExtensions<'a> {
    fn ex_from(m: ClientExtensionsInner) -> ClientExtensions {
        let (l, extensions) = m;
        ClientExtensions { l, extensions }
    }
}

pub struct ClientExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> ClientExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ClientExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        ClientExtensionsMapper(PhantomData)
    }
}
impl View for ClientExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientExtensionsMapper<'_> {
    type Src = SpecClientExtensionsInner;
    type Dst = SpecClientExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ClientExtensionsMapper<'a> {
    type Src = ClientExtensionsInner<'a>;
    type Dst = ClientExtensions<'a>;
}

pub struct SpecClientExtensionsCombinator(SpecClientExtensionsCombinatorAlias);

impl SpecCombinator for SpecClientExtensionsCombinator {
    type SpecResult = SpecClientExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate18193225726552524852>, SpecClientExtensionsExtensionsCombinator>, ClientExtensionsMapper<'static>>;
pub struct Predicate18193225726552524852;
impl View for Predicate18193225726552524852 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate18193225726552524852 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}
impl SpecPred for Predicate18193225726552524852 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}

pub struct ClientExtensionsCombinator<'a>(ClientExtensionsCombinatorAlias<'a>);

impl<'a> View for ClientExtensionsCombinator<'a> {
    type V = SpecClientExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientExtensionsCombinator<'a> {
    type Result = ClientExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate18193225726552524852>, ClientExtensionsExtensionsCombinator<'a>, ClientExtensionsCont0<'a>>, ClientExtensionsMapper<'a>>;


pub closed spec fn spec_client_extensions() -> SpecClientExtensionsCombinator {
    SpecClientExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate18193225726552524852 }, snd: |deps| spec_client_extensions_cont0(deps) },
        mapper: ClientExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_client_extensions_cont0(deps: u16) -> SpecClientExtensionsExtensionsCombinator {
    let l = deps;
    spec_client_extensions_extensions(l)
}
                
pub fn client_extensions<'a>() -> (o: ClientExtensionsCombinator<'a>)
    ensures o@ == spec_client_extensions(),
{
    ClientExtensionsCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate18193225726552524852 }, snd: ClientExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_client_extensions_cont0(deps)) },
        mapper: ClientExtensionsMapper::new(),
    })
}

pub struct ClientExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> ClientExtensionsCont0<'a> {
    pub fn new() -> Self {
        ClientExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for ClientExtensionsCont0<'a> {
    type Output = ClientExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_client_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        client_extensions_extensions(l)
    }
}
                

pub struct SpecClientHello {
    pub legacy_version: u16,
    pub random: Seq<u8>,
    pub legacy_session_id: SpecSessionId,
    pub cipher_suites: SpecCipherSuiteList,
    pub legacy_compression_methods: SpecOpaque1Ff,
    pub extensions: SpecClientExtensions,
}

pub type SpecClientHelloInner = (u16, (Seq<u8>, (SpecSessionId, (SpecCipherSuiteList, (SpecOpaque1Ff, SpecClientExtensions)))));
impl SpecFrom<SpecClientHello> for SpecClientHelloInner {
    open spec fn spec_from(m: SpecClientHello) -> SpecClientHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl SpecFrom<SpecClientHelloInner> for SpecClientHello {
    open spec fn spec_from(m: SpecClientHelloInner) -> SpecClientHello {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        SpecClientHello { legacy_version, random, legacy_session_id, cipher_suites, legacy_compression_methods, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientHello<'a> {
    pub legacy_version: u16,
    pub random: &'a [u8],
    pub legacy_session_id: SessionId<'a>,
    pub cipher_suites: CipherSuiteList,
    pub legacy_compression_methods: Opaque1Ff<'a>,
    pub extensions: ClientExtensions<'a>,
}

impl View for ClientHello<'_> {
    type V = SpecClientHello;

    open spec fn view(&self) -> Self::V {
        SpecClientHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id: self.legacy_session_id@,
            cipher_suites: self.cipher_suites@,
            legacy_compression_methods: self.legacy_compression_methods@,
            extensions: self.extensions@,
        }
    }
}
pub type ClientHelloInner<'a> = (u16, (&'a [u8], (SessionId<'a>, (CipherSuiteList, (Opaque1Ff<'a>, ClientExtensions<'a>)))));
impl<'a> From<ClientHello<'a>> for ClientHelloInner<'a> {
    fn ex_from(m: ClientHello) -> ClientHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl<'a> From<ClientHelloInner<'a>> for ClientHello<'a> {
    fn ex_from(m: ClientHelloInner) -> ClientHello {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        ClientHello { legacy_version, random, legacy_session_id, cipher_suites, legacy_compression_methods, extensions }
    }
}

pub struct ClientHelloMapper<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ClientHelloMapper(PhantomData)
    }
    pub fn new() -> Self {
        ClientHelloMapper(PhantomData)
    }
}
impl View for ClientHelloMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloMapper<'_> {
    type Src = SpecClientHelloInner;
    type Dst = SpecClientHello;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ClientHelloMapper<'a> {
    type Src = ClientHelloInner<'a>;
    type Dst = ClientHello<'a>;
}
pub const CLIENTHELLO_LEGACY_VERSION: u16 = 771;

pub struct SpecClientHelloCombinator(SpecClientHelloCombinatorAlias);

impl SpecCombinator for SpecClientHelloCombinator {
    type SpecResult = SpecClientHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloCombinatorAlias = Mapped<(Refined<U16Be, TagPred<u16>>, (BytesN<32>, (SpecSessionIdCombinator, (SpecCipherSuiteListCombinator, (SpecOpaque1FfCombinator, SpecClientExtensionsCombinator))))), ClientHelloMapper<'static>>;

pub struct ClientHelloCombinator<'a>(ClientHelloCombinatorAlias<'a>);

impl<'a> View for ClientHelloCombinator<'a> {
    type V = SpecClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientHelloCombinator<'a> {
    type Result = ClientHello<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientHelloCombinatorAlias<'a> = Mapped<(Refined<U16Be, TagPred<u16>>, (BytesN<32>, (SessionIdCombinator<'a>, (CipherSuiteListCombinator<'a>, (Opaque1FfCombinator<'a>, ClientExtensionsCombinator<'a>))))), ClientHelloMapper<'a>>;


pub closed spec fn spec_client_hello() -> SpecClientHelloCombinator {
    SpecClientHelloCombinator(
    Mapped {
        inner: (Refined { inner: U16Be, predicate: TagPred(CLIENTHELLO_LEGACY_VERSION) }, (BytesN::<32>, (spec_session_id(), (spec_cipher_suite_list(), (spec_opaque_1_ff(), spec_client_extensions()))))),
        mapper: ClientHelloMapper::spec_new(),
    })
}

                
pub fn client_hello<'a>() -> (o: ClientHelloCombinator<'a>)
    ensures o@ == spec_client_hello(),
{
    ClientHelloCombinator(
    Mapped {
        inner: (Refined { inner: U16Be, predicate: TagPred(CLIENTHELLO_LEGACY_VERSION) }, (BytesN::<32>, (session_id(), (cipher_suite_list(), (opaque_1_ff(), client_extensions()))))),
        mapper: ClientHelloMapper::new(),
    })
}

                
pub type SpecServerExtensionsExtensions = Seq<SpecSeverHelloExtension>;
pub type ServerExtensionsExtensions<'a> = RepeatResult<SeverHelloExtension<'a>>;


pub struct SpecServerExtensionsExtensionsCombinator(SpecServerExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecServerExtensionsExtensionsCombinator {
    type SpecResult = SpecServerExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecSeverHelloExtensionCombinator>>;

pub struct ServerExtensionsExtensionsCombinator<'a>(ServerExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for ServerExtensionsExtensionsCombinator<'a> {
    type V = SpecServerExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerExtensionsExtensionsCombinator<'a> {
    type Result = ServerExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<SeverHelloExtensionCombinator<'a>>>;


pub closed spec fn spec_server_extensions_extensions(l: u16) -> SpecServerExtensionsExtensionsCombinator {
    SpecServerExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_sever_hello_extension())))
}

                
pub fn server_extensions_extensions<'a>(l: u16) -> (o: ServerExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_server_extensions_extensions(l@),
{
    ServerExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(sever_hello_extension())))
}

                

pub struct SpecServerExtensions {
    pub l: u16,
    pub extensions: SpecServerExtensionsExtensions,
}

pub type SpecServerExtensionsInner = (u16, SpecServerExtensionsExtensions);
impl SpecFrom<SpecServerExtensions> for SpecServerExtensionsInner {
    open spec fn spec_from(m: SpecServerExtensions) -> SpecServerExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecServerExtensionsInner> for SpecServerExtensions {
    open spec fn spec_from(m: SpecServerExtensionsInner) -> SpecServerExtensions {
        let (l, extensions) = m;
        SpecServerExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerExtensions<'a> {
    pub l: u16,
    pub extensions: ServerExtensionsExtensions<'a>,
}

impl View for ServerExtensions<'_> {
    type V = SpecServerExtensions;

    open spec fn view(&self) -> Self::V {
        SpecServerExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type ServerExtensionsInner<'a> = (u16, ServerExtensionsExtensions<'a>);
impl<'a> From<ServerExtensions<'a>> for ServerExtensionsInner<'a> {
    fn ex_from(m: ServerExtensions) -> ServerExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<ServerExtensionsInner<'a>> for ServerExtensions<'a> {
    fn ex_from(m: ServerExtensionsInner) -> ServerExtensions {
        let (l, extensions) = m;
        ServerExtensions { l, extensions }
    }
}

pub struct ServerExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> ServerExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ServerExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        ServerExtensionsMapper(PhantomData)
    }
}
impl View for ServerExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerExtensionsMapper<'_> {
    type Src = SpecServerExtensionsInner;
    type Dst = SpecServerExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ServerExtensionsMapper<'a> {
    type Src = ServerExtensionsInner<'a>;
    type Dst = ServerExtensions<'a>;
}

pub struct SpecServerExtensionsCombinator(SpecServerExtensionsCombinatorAlias);

impl SpecCombinator for SpecServerExtensionsCombinator {
    type SpecResult = SpecServerExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate3289024863945113924>, SpecServerExtensionsExtensionsCombinator>, ServerExtensionsMapper<'static>>;

pub struct ServerExtensionsCombinator<'a>(ServerExtensionsCombinatorAlias<'a>);

impl<'a> View for ServerExtensionsCombinator<'a> {
    type V = SpecServerExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerExtensionsCombinator<'a> {
    type Result = ServerExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate3289024863945113924>, ServerExtensionsExtensionsCombinator<'a>, ServerExtensionsCont0<'a>>, ServerExtensionsMapper<'a>>;


pub closed spec fn spec_server_extensions() -> SpecServerExtensionsCombinator {
    SpecServerExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: Refined { inner: U16Be, predicate: Predicate3289024863945113924 }, snd: |deps| spec_server_extensions_cont0(deps) },
        mapper: ServerExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_server_extensions_cont0(deps: u16) -> SpecServerExtensionsExtensionsCombinator {
    let l = deps;
    spec_server_extensions_extensions(l)
}
                
pub fn server_extensions<'a>() -> (o: ServerExtensionsCombinator<'a>)
    ensures o@ == spec_server_extensions(),
{
    ServerExtensionsCombinator(
    Mapped {
        inner: Depend { fst: Refined { inner: U16Be, predicate: Predicate3289024863945113924 }, snd: ServerExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_server_extensions_cont0(deps)) },
        mapper: ServerExtensionsMapper::new(),
    })
}

pub struct ServerExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> ServerExtensionsCont0<'a> {
    pub fn new() -> Self {
        ServerExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&u16> for ServerExtensionsCont0<'a> {
    type Output = ServerExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &u16) -> bool { true }

    open spec fn ensures(&self, deps: &u16, o: Self::Output) -> bool {
        o@ == spec_server_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &u16) -> Self::Output {
        let l = *deps;
        server_extensions_extensions(l)
    }
}
                

pub struct SpecServerHello {
    pub legacy_session_id_echo: SpecSessionId,
    pub cipher_suite: SpecCipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: SpecServerExtensions,
}

pub type SpecServerHelloInner = (SpecSessionId, (SpecCipherSuite, (u8, SpecServerExtensions)));
impl SpecFrom<SpecServerHello> for SpecServerHelloInner {
    open spec fn spec_from(m: SpecServerHello) -> SpecServerHelloInner {
        (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))
    }
}
impl SpecFrom<SpecServerHelloInner> for SpecServerHello {
    open spec fn spec_from(m: SpecServerHelloInner) -> SpecServerHello {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        SpecServerHello { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerHello<'a> {
    pub legacy_session_id_echo: SessionId<'a>,
    pub cipher_suite: CipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: ServerExtensions<'a>,
}

impl View for ServerHello<'_> {
    type V = SpecServerHello;

    open spec fn view(&self) -> Self::V {
        SpecServerHello {
            legacy_session_id_echo: self.legacy_session_id_echo@,
            cipher_suite: self.cipher_suite@,
            legacy_compression_method: self.legacy_compression_method@,
            extensions: self.extensions@,
        }
    }
}
pub type ServerHelloInner<'a> = (SessionId<'a>, (CipherSuite, (u8, ServerExtensions<'a>)));
impl<'a> From<ServerHello<'a>> for ServerHelloInner<'a> {
    fn ex_from(m: ServerHello) -> ServerHelloInner {
        (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))
    }
}
impl<'a> From<ServerHelloInner<'a>> for ServerHello<'a> {
    fn ex_from(m: ServerHelloInner) -> ServerHello {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        ServerHello { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}

pub struct ServerHelloMapper<'a>(PhantomData<&'a ()>);
impl<'a> ServerHelloMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ServerHelloMapper(PhantomData)
    }
    pub fn new() -> Self {
        ServerHelloMapper(PhantomData)
    }
}
impl View for ServerHelloMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerHelloMapper<'_> {
    type Src = SpecServerHelloInner;
    type Dst = SpecServerHello;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ServerHelloMapper<'a> {
    type Src = ServerHelloInner<'a>;
    type Dst = ServerHello<'a>;
}
pub const SERVERHELLO_LEGACY_COMPRESSION_METHOD: u8 = 0;

pub struct SpecServerHelloCombinator(SpecServerHelloCombinatorAlias);

impl SpecCombinator for SpecServerHelloCombinator {
    type SpecResult = SpecServerHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerHelloCombinatorAlias = Mapped<(SpecSessionIdCombinator, (SpecCipherSuiteCombinator, (Refined<U8, TagPred<u8>>, SpecServerExtensionsCombinator))), ServerHelloMapper<'static>>;

pub struct ServerHelloCombinator<'a>(ServerHelloCombinatorAlias<'a>);

impl<'a> View for ServerHelloCombinator<'a> {
    type V = SpecServerHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerHelloCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerHelloCombinator<'a> {
    type Result = ServerHello<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerHelloCombinatorAlias<'a> = Mapped<(SessionIdCombinator<'a>, (CipherSuiteCombinator, (Refined<U8, TagPred<u8>>, ServerExtensionsCombinator<'a>))), ServerHelloMapper<'a>>;


pub closed spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(
    Mapped {
        inner: (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, spec_server_extensions()))),
        mapper: ServerHelloMapper::spec_new(),
    })
}

                
pub fn server_hello<'a>() -> (o: ServerHelloCombinator<'a>)
    ensures o@ == spec_server_hello(),
{
    ServerHelloCombinator(
    Mapped {
        inner: (session_id(), (cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, server_extensions()))),
        mapper: ServerHelloMapper::new(),
    })
}

                

pub enum SpecShOrHrrPayload {
    Variant0(SpecHelloRetryRequest),
    Variant1(SpecServerHello),
}

pub type SpecShOrHrrPayloadInner = Either<SpecHelloRetryRequest, SpecServerHello>;



impl SpecFrom<SpecShOrHrrPayload> for SpecShOrHrrPayloadInner {
    open spec fn spec_from(m: SpecShOrHrrPayload) -> SpecShOrHrrPayloadInner {
        match m {
            SpecShOrHrrPayload::Variant0(m) => Either::Left(m),
            SpecShOrHrrPayload::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecShOrHrrPayloadInner> for SpecShOrHrrPayload {
    open spec fn spec_from(m: SpecShOrHrrPayloadInner) -> SpecShOrHrrPayload {
        match m {
            Either::Left(m) => SpecShOrHrrPayload::Variant0(m),
            Either::Right(m) => SpecShOrHrrPayload::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShOrHrrPayload<'a> {
    Variant0(HelloRetryRequest<'a>),
    Variant1(ServerHello<'a>),
}

pub type ShOrHrrPayloadInner<'a> = Either<HelloRetryRequest<'a>, ServerHello<'a>>;


impl<'a> View for ShOrHrrPayload<'a> {
    type V = SpecShOrHrrPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            ShOrHrrPayload::Variant0(m) => SpecShOrHrrPayload::Variant0(m@),
            ShOrHrrPayload::Variant1(m) => SpecShOrHrrPayload::Variant1(m@),
        }
    }
}


impl<'a> From<ShOrHrrPayload<'a>> for ShOrHrrPayloadInner<'a> {
    fn ex_from(m: ShOrHrrPayload<'a>) -> ShOrHrrPayloadInner<'a> {
        match m {
            ShOrHrrPayload::Variant0(m) => Either::Left(m),
            ShOrHrrPayload::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<ShOrHrrPayloadInner<'a>> for ShOrHrrPayload<'a> {
    fn ex_from(m: ShOrHrrPayloadInner<'a>) -> ShOrHrrPayload<'a> {
        match m {
            Either::Left(m) => ShOrHrrPayload::Variant0(m),
            Either::Right(m) => ShOrHrrPayload::Variant1(m),
        }
    }
    
}


pub struct ShOrHrrPayloadMapper<'a>(PhantomData<&'a ()>);
impl<'a> ShOrHrrPayloadMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ShOrHrrPayloadMapper(PhantomData)
    }
    pub fn new() -> Self {
        ShOrHrrPayloadMapper(PhantomData)
    }
}
impl View for ShOrHrrPayloadMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ShOrHrrPayloadMapper<'_> {
    type Src = SpecShOrHrrPayloadInner;
    type Dst = SpecShOrHrrPayload;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ShOrHrrPayloadMapper<'a> {
    type Src = ShOrHrrPayloadInner<'a>;
    type Dst = ShOrHrrPayload<'a>;
}


pub struct SpecShOrHrrPayloadCombinator(SpecShOrHrrPayloadCombinatorAlias);

impl SpecCombinator for SpecShOrHrrPayloadCombinator {
    type SpecResult = SpecShOrHrrPayload;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecShOrHrrPayloadCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShOrHrrPayloadCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecShOrHrrPayloadCombinatorAlias = Mapped<OrdChoice<Cond<SpecHelloRetryRequestCombinator>, Cond<SpecServerHelloCombinator>>, ShOrHrrPayloadMapper<'static>>;

pub struct ShOrHrrPayloadCombinator<'a>(ShOrHrrPayloadCombinatorAlias<'a>);

impl<'a> View for ShOrHrrPayloadCombinator<'a> {
    type V = SpecShOrHrrPayloadCombinator;
    closed spec fn view(&self) -> Self::V { SpecShOrHrrPayloadCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ShOrHrrPayloadCombinator<'a> {
    type Result = ShOrHrrPayload<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ShOrHrrPayloadCombinatorAlias<'a> = Mapped<OrdChoice<Cond<HelloRetryRequestCombinator<'a>>, Cond<ServerHelloCombinator<'a>>>, ShOrHrrPayloadMapper<'a>>;


pub closed spec fn spec_sh_or_hrr_payload(random: Seq<u8>) -> SpecShOrHrrPayloadCombinator {
    SpecShOrHrrPayloadCombinator(Mapped { inner: OrdChoice(Cond { cond: random == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8], inner: spec_hello_retry_request() }, Cond { cond: !(random == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8]), inner: spec_server_hello() }), mapper: ShOrHrrPayloadMapper::spec_new() })
}

                
pub fn sh_or_hrr_payload<'a>(random: &'a [u8]) -> (o: ShOrHrrPayloadCombinator<'a>)
    ensures o@ == spec_sh_or_hrr_payload(random@),
{
    ShOrHrrPayloadCombinator(Mapped { inner: OrdChoice::new(Cond { cond: compare_slice(random, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice()), inner: hello_retry_request() }, Cond { cond: !(compare_slice(random, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice())), inner: server_hello() }), mapper: ShOrHrrPayloadMapper::new() })
}

                

pub struct SpecShOrHrr {
    pub legacy_version: u16,
    pub random: Seq<u8>,
    pub payload: SpecShOrHrrPayload,
}

pub type SpecShOrHrrInner = ((u16, Seq<u8>), SpecShOrHrrPayload);
impl SpecFrom<SpecShOrHrr> for SpecShOrHrrInner {
    open spec fn spec_from(m: SpecShOrHrr) -> SpecShOrHrrInner {
        ((m.legacy_version, m.random), m.payload)
    }
}
impl SpecFrom<SpecShOrHrrInner> for SpecShOrHrr {
    open spec fn spec_from(m: SpecShOrHrrInner) -> SpecShOrHrr {
        let ((legacy_version, random), payload) = m;
        SpecShOrHrr { legacy_version, random, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ShOrHrr<'a> {
    pub legacy_version: u16,
    pub random: &'a [u8],
    pub payload: ShOrHrrPayload<'a>,
}

impl View for ShOrHrr<'_> {
    type V = SpecShOrHrr;

    open spec fn view(&self) -> Self::V {
        SpecShOrHrr {
            legacy_version: self.legacy_version@,
            random: self.random@,
            payload: self.payload@,
        }
    }
}
pub type ShOrHrrInner<'a> = ((u16, &'a [u8]), ShOrHrrPayload<'a>);
impl<'a> From<ShOrHrr<'a>> for ShOrHrrInner<'a> {
    fn ex_from(m: ShOrHrr) -> ShOrHrrInner {
        ((m.legacy_version, m.random), m.payload)
    }
}
impl<'a> From<ShOrHrrInner<'a>> for ShOrHrr<'a> {
    fn ex_from(m: ShOrHrrInner) -> ShOrHrr {
        let ((legacy_version, random), payload) = m;
        ShOrHrr { legacy_version, random, payload }
    }
}

pub struct ShOrHrrMapper<'a>(PhantomData<&'a ()>);
impl<'a> ShOrHrrMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        ShOrHrrMapper(PhantomData)
    }
    pub fn new() -> Self {
        ShOrHrrMapper(PhantomData)
    }
}
impl View for ShOrHrrMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ShOrHrrMapper<'_> {
    type Src = SpecShOrHrrInner;
    type Dst = SpecShOrHrr;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for ShOrHrrMapper<'a> {
    type Src = ShOrHrrInner<'a>;
    type Dst = ShOrHrr<'a>;
}
pub const SHORHRR_LEGACY_VERSION: u16 = 771;

pub struct SpecShOrHrrCombinator(SpecShOrHrrCombinatorAlias);

impl SpecCombinator for SpecShOrHrrCombinator {
    type SpecResult = SpecShOrHrr;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecShOrHrrCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShOrHrrCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecShOrHrrCombinatorAlias = Mapped<SpecDepend<(Refined<U16Be, TagPred<u16>>, BytesN<32>), SpecShOrHrrPayloadCombinator>, ShOrHrrMapper<'static>>;

pub struct ShOrHrrCombinator<'a>(ShOrHrrCombinatorAlias<'a>);

impl<'a> View for ShOrHrrCombinator<'a> {
    type V = SpecShOrHrrCombinator;
    closed spec fn view(&self) -> Self::V { SpecShOrHrrCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ShOrHrrCombinator<'a> {
    type Result = ShOrHrr<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ShOrHrrCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (Refined<U16Be, TagPred<u16>>, BytesN<32>), ShOrHrrPayloadCombinator<'a>, ShOrHrrCont0<'a>>, ShOrHrrMapper<'a>>;


pub closed spec fn spec_sh_or_hrr() -> SpecShOrHrrCombinator {
    SpecShOrHrrCombinator(
    Mapped {
        inner: SpecDepend { fst: (Refined { inner: U16Be, predicate: TagPred(SHORHRR_LEGACY_VERSION) }, BytesN::<32>), snd: |deps| spec_sh_or_hrr_cont0(deps) },
        mapper: ShOrHrrMapper::spec_new(),
    })
}

pub open spec fn spec_sh_or_hrr_cont0(deps: (u16, Seq<u8>)) -> SpecShOrHrrPayloadCombinator {
    let (_, random) = deps;
    spec_sh_or_hrr_payload(random)
}
                
pub fn sh_or_hrr<'a>() -> (o: ShOrHrrCombinator<'a>)
    ensures o@ == spec_sh_or_hrr(),
{
    ShOrHrrCombinator(
    Mapped {
        inner: Depend { fst: (Refined { inner: U16Be, predicate: TagPred(SHORHRR_LEGACY_VERSION) }, BytesN::<32>), snd: ShOrHrrCont0::new(), spec_snd: Ghost(|deps| spec_sh_or_hrr_cont0(deps)) },
        mapper: ShOrHrrMapper::new(),
    })
}

pub struct ShOrHrrCont0<'a>(PhantomData<&'a ()>);
impl<'a> ShOrHrrCont0<'a> {
    pub fn new() -> Self {
        ShOrHrrCont0(PhantomData)
    }
}
impl<'a> Continuation<&(u16, &'a [u8])> for ShOrHrrCont0<'a> {
    type Output = ShOrHrrPayloadCombinator<'a>;

    open spec fn requires(&self, deps: &(u16, &'a [u8])) -> bool { true }

    open spec fn ensures(&self, deps: &(u16, &'a [u8]), o: Self::Output) -> bool {
        o@ == spec_sh_or_hrr_cont0(deps@)
    }

    fn apply(&self, deps: &(u16, &'a [u8])) -> Self::Output {
        let (_, random) = *deps;
        sh_or_hrr_payload(random)
    }
}
                
pub type SpecUint0Ff = u8;
pub type Uint0Ff = u8;


pub struct SpecUint0FfCombinator(SpecUint0FfCombinatorAlias);

impl SpecCombinator for SpecUint0FfCombinator {
    type SpecResult = SpecUint0Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FfCombinatorAlias = U8;

pub struct Uint0FfCombinator(Uint0FfCombinatorAlias);

impl View for Uint0FfCombinator {
    type V = SpecUint0FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FfCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Uint0FfCombinator {
    type Result = Uint0Ff;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Uint0FfCombinatorAlias = U8;


pub closed spec fn spec_uint_0_ff() -> SpecUint0FfCombinator {
    SpecUint0FfCombinator(U8)
}

                
pub fn uint_0_ff() -> (o: Uint0FfCombinator)
    ensures o@ == spec_uint_0_ff(),
{
    Uint0FfCombinator(U8)
}

                

pub struct SpecOpaque0Ff {
    pub l: SpecUint0Ff,
    pub data: Seq<u8>,
}

pub type SpecOpaque0FfInner = (SpecUint0Ff, Seq<u8>);
impl SpecFrom<SpecOpaque0Ff> for SpecOpaque0FfInner {
    open spec fn spec_from(m: SpecOpaque0Ff) -> SpecOpaque0FfInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfInner> for SpecOpaque0Ff {
    open spec fn spec_from(m: SpecOpaque0FfInner) -> SpecOpaque0Ff {
        let (l, data) = m;
        SpecOpaque0Ff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque0Ff<'a> {
    pub l: Uint0Ff,
    pub data: &'a [u8],
}

impl View for Opaque0Ff<'_> {
    type V = SpecOpaque0Ff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque0FfInner<'a> = (Uint0Ff, &'a [u8]);
impl<'a> From<Opaque0Ff<'a>> for Opaque0FfInner<'a> {
    fn ex_from(m: Opaque0Ff) -> Opaque0FfInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfInner<'a>> for Opaque0Ff<'a> {
    fn ex_from(m: Opaque0FfInner) -> Opaque0Ff {
        let (l, data) = m;
        Opaque0Ff { l, data }
    }
}

pub struct Opaque0FfMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque0FfMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque0FfMapper(PhantomData)
    }
}
impl View for Opaque0FfMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfMapper<'_> {
    type Src = SpecOpaque0FfInner;
    type Dst = SpecOpaque0Ff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque0FfMapper<'a> {
    type Src = Opaque0FfInner<'a>;
    type Dst = Opaque0Ff<'a>;
}

pub struct SpecOpaque0FfCombinator(SpecOpaque0FfCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfCombinator {
    type SpecResult = SpecOpaque0Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfCombinatorAlias = Mapped<SpecDepend<SpecUint0FfCombinator, Bytes>, Opaque0FfMapper<'static>>;

pub struct Opaque0FfCombinator<'a>(Opaque0FfCombinatorAlias<'a>);

impl<'a> View for Opaque0FfCombinator<'a> {
    type V = SpecOpaque0FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque0FfCombinator<'a> {
    type Result = Opaque0Ff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque0FfCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfCombinator, Bytes, Opaque0FfCont0<'a>>, Opaque0FfMapper<'a>>;


pub closed spec fn spec_opaque_0_ff() -> SpecOpaque0FfCombinator {
    SpecOpaque0FfCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ff(), snd: |deps| spec_opaque0_ff_cont0(deps) },
        mapper: Opaque0FfMapper::spec_new(),
    })
}

pub open spec fn spec_opaque0_ff_cont0(deps: SpecUint0Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_0_ff<'a>() -> (o: Opaque0FfCombinator<'a>)
    ensures o@ == spec_opaque_0_ff(),
{
    Opaque0FfCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ff(), snd: Opaque0FfCont0::new(), spec_snd: Ghost(|deps| spec_opaque0_ff_cont0(deps)) },
        mapper: Opaque0FfMapper::new(),
    })
}

pub struct Opaque0FfCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfCont0<'a> {
    pub fn new() -> Self {
        Opaque0FfCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ff> for Opaque0FfCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &Uint0Ff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ff_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ff) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecNewSessionTicketExtensions {
    pub l: SpecUint0Fffe,
    pub extensions: SpecNewSessionTicketExtensionsExtensions,
}

pub type SpecNewSessionTicketExtensionsInner = (SpecUint0Fffe, SpecNewSessionTicketExtensionsExtensions);
impl SpecFrom<SpecNewSessionTicketExtensions> for SpecNewSessionTicketExtensionsInner {
    open spec fn spec_from(m: SpecNewSessionTicketExtensions) -> SpecNewSessionTicketExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecNewSessionTicketExtensionsInner> for SpecNewSessionTicketExtensions {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionsInner) -> SpecNewSessionTicketExtensions {
        let (l, extensions) = m;
        SpecNewSessionTicketExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NewSessionTicketExtensions<'a> {
    pub l: Uint0Fffe,
    pub extensions: NewSessionTicketExtensionsExtensions<'a>,
}

impl View for NewSessionTicketExtensions<'_> {
    type V = SpecNewSessionTicketExtensions;

    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type NewSessionTicketExtensionsInner<'a> = (Uint0Fffe, NewSessionTicketExtensionsExtensions<'a>);
impl<'a> From<NewSessionTicketExtensions<'a>> for NewSessionTicketExtensionsInner<'a> {
    fn ex_from(m: NewSessionTicketExtensions) -> NewSessionTicketExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<NewSessionTicketExtensionsInner<'a>> for NewSessionTicketExtensions<'a> {
    fn ex_from(m: NewSessionTicketExtensionsInner) -> NewSessionTicketExtensions {
        let (l, extensions) = m;
        NewSessionTicketExtensions { l, extensions }
    }
}

pub struct NewSessionTicketExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        NewSessionTicketExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        NewSessionTicketExtensionsMapper(PhantomData)
    }
}
impl View for NewSessionTicketExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionsMapper<'_> {
    type Src = SpecNewSessionTicketExtensionsInner;
    type Dst = SpecNewSessionTicketExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for NewSessionTicketExtensionsMapper<'a> {
    type Src = NewSessionTicketExtensionsInner<'a>;
    type Dst = NewSessionTicketExtensions<'a>;
}

pub struct SpecNewSessionTicketExtensionsCombinator(SpecNewSessionTicketExtensionsCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    type SpecResult = SpecNewSessionTicketExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint0FffeCombinator, SpecNewSessionTicketExtensionsExtensionsCombinator>, NewSessionTicketExtensionsMapper<'static>>;

pub struct NewSessionTicketExtensionsCombinator<'a>(NewSessionTicketExtensionsCombinatorAlias<'a>);

impl<'a> View for NewSessionTicketExtensionsCombinator<'a> {
    type V = SpecNewSessionTicketExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NewSessionTicketExtensionsCombinator<'a> {
    type Result = NewSessionTicketExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NewSessionTicketExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FffeCombinator, NewSessionTicketExtensionsExtensionsCombinator<'a>, NewSessionTicketExtensionsCont0<'a>>, NewSessionTicketExtensionsMapper<'a>>;


pub closed spec fn spec_new_session_ticket_extensions() -> SpecNewSessionTicketExtensionsCombinator {
    SpecNewSessionTicketExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_fffe(), snd: |deps| spec_new_session_ticket_extensions_cont0(deps) },
        mapper: NewSessionTicketExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_new_session_ticket_extensions_cont0(deps: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    let l = deps;
    spec_new_session_ticket_extensions_extensions(l)
}
                
pub fn new_session_ticket_extensions<'a>() -> (o: NewSessionTicketExtensionsCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extensions(),
{
    NewSessionTicketExtensionsCombinator(
    Mapped {
        inner: Depend { fst: uint_0_fffe(), snd: NewSessionTicketExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_new_session_ticket_extensions_cont0(deps)) },
        mapper: NewSessionTicketExtensionsMapper::new(),
    })
}

pub struct NewSessionTicketExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionsCont0<'a> {
    pub fn new() -> Self {
        NewSessionTicketExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Fffe> for NewSessionTicketExtensionsCont0<'a> {
    type Output = NewSessionTicketExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Fffe) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Fffe, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Fffe) -> Self::Output {
        let l = *deps;
        new_session_ticket_extensions_extensions(l)
    }
}
                

pub struct SpecNewSessionTicket {
    pub ticket_lifetime: u32,
    pub ticket_age_add: u32,
    pub ticket_nonce: SpecOpaque0Ff,
    pub ticket: SpecOpaque1Ffff,
    pub extensions: SpecNewSessionTicketExtensions,
}

pub type SpecNewSessionTicketInner = (u32, (u32, (SpecOpaque0Ff, (SpecOpaque1Ffff, SpecNewSessionTicketExtensions))));
impl SpecFrom<SpecNewSessionTicket> for SpecNewSessionTicketInner {
    open spec fn spec_from(m: SpecNewSessionTicket) -> SpecNewSessionTicketInner {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl SpecFrom<SpecNewSessionTicketInner> for SpecNewSessionTicket {
    open spec fn spec_from(m: SpecNewSessionTicketInner) -> SpecNewSessionTicket {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        SpecNewSessionTicket { ticket_lifetime, ticket_age_add, ticket_nonce, ticket, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NewSessionTicket<'a> {
    pub ticket_lifetime: u32,
    pub ticket_age_add: u32,
    pub ticket_nonce: Opaque0Ff<'a>,
    pub ticket: Opaque1Ffff<'a>,
    pub extensions: NewSessionTicketExtensions<'a>,
}

impl View for NewSessionTicket<'_> {
    type V = SpecNewSessionTicket;

    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicket {
            ticket_lifetime: self.ticket_lifetime@,
            ticket_age_add: self.ticket_age_add@,
            ticket_nonce: self.ticket_nonce@,
            ticket: self.ticket@,
            extensions: self.extensions@,
        }
    }
}
pub type NewSessionTicketInner<'a> = (u32, (u32, (Opaque0Ff<'a>, (Opaque1Ffff<'a>, NewSessionTicketExtensions<'a>))));
impl<'a> From<NewSessionTicket<'a>> for NewSessionTicketInner<'a> {
    fn ex_from(m: NewSessionTicket) -> NewSessionTicketInner {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl<'a> From<NewSessionTicketInner<'a>> for NewSessionTicket<'a> {
    fn ex_from(m: NewSessionTicketInner) -> NewSessionTicket {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        NewSessionTicket { ticket_lifetime, ticket_age_add, ticket_nonce, ticket, extensions }
    }
}

pub struct NewSessionTicketMapper<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        NewSessionTicketMapper(PhantomData)
    }
    pub fn new() -> Self {
        NewSessionTicketMapper(PhantomData)
    }
}
impl View for NewSessionTicketMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketMapper<'_> {
    type Src = SpecNewSessionTicketInner;
    type Dst = SpecNewSessionTicket;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for NewSessionTicketMapper<'a> {
    type Src = NewSessionTicketInner<'a>;
    type Dst = NewSessionTicket<'a>;
}

pub struct SpecNewSessionTicketCombinator(SpecNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketCombinator {
    type SpecResult = SpecNewSessionTicket;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketCombinatorAlias = Mapped<(U32Be, (U32Be, (SpecOpaque0FfCombinator, (SpecOpaque1FfffCombinator, SpecNewSessionTicketExtensionsCombinator)))), NewSessionTicketMapper<'static>>;

pub struct NewSessionTicketCombinator<'a>(NewSessionTicketCombinatorAlias<'a>);

impl<'a> View for NewSessionTicketCombinator<'a> {
    type V = SpecNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for NewSessionTicketCombinator<'a> {
    type Result = NewSessionTicket<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type NewSessionTicketCombinatorAlias<'a> = Mapped<(U32Be, (U32Be, (Opaque0FfCombinator<'a>, (Opaque1FfffCombinator<'a>, NewSessionTicketExtensionsCombinator<'a>)))), NewSessionTicketMapper<'a>>;


pub closed spec fn spec_new_session_ticket() -> SpecNewSessionTicketCombinator {
    SpecNewSessionTicketCombinator(
    Mapped {
        inner: (U32Be, (U32Be, (spec_opaque_0_ff(), (spec_opaque_1_ffff(), spec_new_session_ticket_extensions())))),
        mapper: NewSessionTicketMapper::spec_new(),
    })
}

                
pub fn new_session_ticket<'a>() -> (o: NewSessionTicketCombinator<'a>)
    ensures o@ == spec_new_session_ticket(),
{
    NewSessionTicketCombinator(
    Mapped {
        inner: (U32Be, (U32Be, (opaque_0_ff(), (opaque_1_ffff(), new_session_ticket_extensions())))),
        mapper: NewSessionTicketMapper::new(),
    })
}

                

pub enum SpecEncryptedExtensionExtensionData {
    ServerName(SpecEmpty),
    MaxFragmentLength(SpecMaxFragmentLength),
    SupportedGroups(SpecNamedGroupList),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    EarlyData(SpecEmpty),
    Unrecognized(Seq<u8>),
}

pub type SpecEncryptedExtensionExtensionDataInner = Either<SpecEmpty, Either<SpecMaxFragmentLength, Either<SpecNamedGroupList, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecEmpty, Seq<u8>>>>>>>>>;



impl SpecFrom<SpecEncryptedExtensionExtensionData> for SpecEncryptedExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecEncryptedExtensionExtensionData) -> SpecEncryptedExtensionExtensionDataInner {
        match m {
            SpecEncryptedExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecEncryptedExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecEncryptedExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecEncryptedExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecEncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecEncryptedExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecEncryptedExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecEncryptedExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecEncryptedExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))),
        }
    }

}

impl SpecFrom<SpecEncryptedExtensionExtensionDataInner> for SpecEncryptedExtensionExtensionData {
    open spec fn spec_from(m: SpecEncryptedExtensionExtensionDataInner) -> SpecEncryptedExtensionExtensionData {
        match m {
            Either::Left(m) => SpecEncryptedExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecEncryptedExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecEncryptedExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecEncryptedExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecEncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecEncryptedExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecEncryptedExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecEncryptedExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))) => SpecEncryptedExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EncryptedExtensionExtensionData<'a> {
    ServerName(Empty<'a>),
    MaxFragmentLength(MaxFragmentLength),
    SupportedGroups(NamedGroupList),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    EarlyData(Empty<'a>),
    Unrecognized(&'a [u8]),
}

pub type EncryptedExtensionExtensionDataInner<'a> = Either<Empty<'a>, Either<MaxFragmentLength, Either<NamedGroupList, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<Empty<'a>, &'a [u8]>>>>>>>>;


impl<'a> View for EncryptedExtensionExtensionData<'a> {
    type V = SpecEncryptedExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            EncryptedExtensionExtensionData::ServerName(m) => SpecEncryptedExtensionExtensionData::ServerName(m@),
            EncryptedExtensionExtensionData::MaxFragmentLength(m) => SpecEncryptedExtensionExtensionData::MaxFragmentLength(m@),
            EncryptedExtensionExtensionData::SupportedGroups(m) => SpecEncryptedExtensionExtensionData::SupportedGroups(m@),
            EncryptedExtensionExtensionData::Heartbeat(m) => SpecEncryptedExtensionExtensionData::Heartbeat(m@),
            EncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecEncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            EncryptedExtensionExtensionData::ClientCertificateType(m) => SpecEncryptedExtensionExtensionData::ClientCertificateType(m@),
            EncryptedExtensionExtensionData::ServerCertificateType(m) => SpecEncryptedExtensionExtensionData::ServerCertificateType(m@),
            EncryptedExtensionExtensionData::EarlyData(m) => SpecEncryptedExtensionExtensionData::EarlyData(m@),
            EncryptedExtensionExtensionData::Unrecognized(m) => SpecEncryptedExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<EncryptedExtensionExtensionData<'a>> for EncryptedExtensionExtensionDataInner<'a> {
    fn ex_from(m: EncryptedExtensionExtensionData<'a>) -> EncryptedExtensionExtensionDataInner<'a> {
        match m {
            EncryptedExtensionExtensionData::ServerName(m) => Either::Left(m),
            EncryptedExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            EncryptedExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Left(m))),
            EncryptedExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            EncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            EncryptedExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            EncryptedExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            EncryptedExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            EncryptedExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))),
        }
    }

}

impl<'a> From<EncryptedExtensionExtensionDataInner<'a>> for EncryptedExtensionExtensionData<'a> {
    fn ex_from(m: EncryptedExtensionExtensionDataInner<'a>) -> EncryptedExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => EncryptedExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => EncryptedExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => EncryptedExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => EncryptedExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => EncryptedExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => EncryptedExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => EncryptedExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => EncryptedExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))) => EncryptedExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct EncryptedExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        EncryptedExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        EncryptedExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for EncryptedExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionExtensionDataMapper<'_> {
    type Src = SpecEncryptedExtensionExtensionDataInner;
    type Dst = SpecEncryptedExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for EncryptedExtensionExtensionDataMapper<'a> {
    type Src = EncryptedExtensionExtensionDataInner<'a>;
    type Dst = EncryptedExtensionExtensionData<'a>;
}


pub struct SpecEncryptedExtensionExtensionDataCombinator(SpecEncryptedExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionExtensionDataCombinator {
    type SpecResult = SpecEncryptedExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecNamedGroupListCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, Cond<Bytes>>>>>>>>>, EncryptedExtensionExtensionDataMapper<'static>>>;

pub struct EncryptedExtensionExtensionDataCombinator<'a>(EncryptedExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for EncryptedExtensionExtensionDataCombinator<'a> {
    type V = SpecEncryptedExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EncryptedExtensionExtensionDataCombinator<'a> {
    type Result = EncryptedExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EncryptedExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<NamedGroupListCombinator<'a>>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator<'a>>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, Cond<Bytes>>>>>>>>>, EncryptedExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_encrypted_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecEncryptedExtensionExtensionDataCombinator {
    SpecEncryptedExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) })))))))), mapper: EncryptedExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn encrypted_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: EncryptedExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_encrypted_extension_extension_data(ext_len@, extension_type@),
{
    EncryptedExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 0, inner: empty() }, OrdChoice::new(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice::new(Cond { cond: extension_type == 10, inner: named_group_list() }, OrdChoice::new(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice::new(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice::new(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice::new(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice::new(Cond { cond: extension_type == 42, inner: empty() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) })))))))), mapper: EncryptedExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecEncryptedExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecEncryptedExtensionExtensionData,
}

pub type SpecEncryptedExtensionInner = ((SpecExtensionType, u16), SpecEncryptedExtensionExtensionData);
impl SpecFrom<SpecEncryptedExtension> for SpecEncryptedExtensionInner {
    open spec fn spec_from(m: SpecEncryptedExtension) -> SpecEncryptedExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecEncryptedExtensionInner> for SpecEncryptedExtension {
    open spec fn spec_from(m: SpecEncryptedExtensionInner) -> SpecEncryptedExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecEncryptedExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EncryptedExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: EncryptedExtensionExtensionData<'a>,
}

impl View for EncryptedExtension<'_> {
    type V = SpecEncryptedExtension;

    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type EncryptedExtensionInner<'a> = ((ExtensionType, u16), EncryptedExtensionExtensionData<'a>);
impl<'a> From<EncryptedExtension<'a>> for EncryptedExtensionInner<'a> {
    fn ex_from(m: EncryptedExtension) -> EncryptedExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<EncryptedExtensionInner<'a>> for EncryptedExtension<'a> {
    fn ex_from(m: EncryptedExtensionInner) -> EncryptedExtension {
        let ((extension_type, ext_len), extension_data) = m;
        EncryptedExtension { extension_type, ext_len, extension_data }
    }
}

pub struct EncryptedExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        EncryptedExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        EncryptedExtensionMapper(PhantomData)
    }
}
impl View for EncryptedExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionMapper<'_> {
    type Src = SpecEncryptedExtensionInner;
    type Dst = SpecEncryptedExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for EncryptedExtensionMapper<'a> {
    type Src = EncryptedExtensionInner<'a>;
    type Dst = EncryptedExtension<'a>;
}

pub struct SpecEncryptedExtensionCombinator(SpecEncryptedExtensionCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionCombinator {
    type SpecResult = SpecEncryptedExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecEncryptedExtensionExtensionDataCombinator>, EncryptedExtensionMapper<'static>>;

pub struct EncryptedExtensionCombinator<'a>(EncryptedExtensionCombinatorAlias<'a>);

impl<'a> View for EncryptedExtensionCombinator<'a> {
    type V = SpecEncryptedExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EncryptedExtensionCombinator<'a> {
    type Result = EncryptedExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EncryptedExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, EncryptedExtensionCont1<'a>>, EncryptedExtensionExtensionDataCombinator<'a>, EncryptedExtensionCont0<'a>>, EncryptedExtensionMapper<'a>>;


pub closed spec fn spec_encrypted_extension() -> SpecEncryptedExtensionCombinator {
    SpecEncryptedExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_encrypted_extension_cont1(deps) }, snd: |deps| spec_encrypted_extension_cont0(deps) },
        mapper: EncryptedExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_encrypted_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_encrypted_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecEncryptedExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_encrypted_extension_extension_data(ext_len, extension_type)
}
                
pub fn encrypted_extension<'a>() -> (o: EncryptedExtensionCombinator<'a>)
    ensures o@ == spec_encrypted_extension(),
{
    EncryptedExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: EncryptedExtensionCont1::new(), spec_snd: Ghost(|deps| spec_encrypted_extension_cont1(deps)) }, snd: EncryptedExtensionCont0::new(), spec_snd: Ghost(|deps| spec_encrypted_extension_cont0(deps)) },
        mapper: EncryptedExtensionMapper::new(),
    })
}

pub struct EncryptedExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionCont1<'a> {
    pub fn new() -> Self {
        EncryptedExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for EncryptedExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_encrypted_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct EncryptedExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionCont0<'a> {
    pub fn new() -> Self {
        EncryptedExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for EncryptedExtensionCont0<'a> {
    type Output = EncryptedExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_encrypted_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        encrypted_extension_extension_data(ext_len, extension_type)
    }
}
                
pub type SpecEncryptedExtensionsExtensions = Seq<SpecEncryptedExtension>;
pub type EncryptedExtensionsExtensions<'a> = RepeatResult<EncryptedExtension<'a>>;


pub struct SpecEncryptedExtensionsExtensionsCombinator(SpecEncryptedExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionsExtensionsCombinator {
    type SpecResult = SpecEncryptedExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecEncryptedExtensionCombinator>>;

pub struct EncryptedExtensionsExtensionsCombinator<'a>(EncryptedExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for EncryptedExtensionsExtensionsCombinator<'a> {
    type V = SpecEncryptedExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EncryptedExtensionsExtensionsCombinator<'a> {
    type Result = EncryptedExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EncryptedExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<EncryptedExtensionCombinator<'a>>>;


pub closed spec fn spec_encrypted_extensions_extensions(l: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    SpecEncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_encrypted_extension())))
}

                
pub fn encrypted_extensions_extensions<'a>(l: Uint0Ffff) -> (o: EncryptedExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_encrypted_extensions_extensions(l@),
{
    EncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(encrypted_extension())))
}

                

pub struct SpecEncryptedExtensions {
    pub l: SpecUint0Ffff,
    pub extensions: SpecEncryptedExtensionsExtensions,
}

pub type SpecEncryptedExtensionsInner = (SpecUint0Ffff, SpecEncryptedExtensionsExtensions);
impl SpecFrom<SpecEncryptedExtensions> for SpecEncryptedExtensionsInner {
    open spec fn spec_from(m: SpecEncryptedExtensions) -> SpecEncryptedExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecEncryptedExtensionsInner> for SpecEncryptedExtensions {
    open spec fn spec_from(m: SpecEncryptedExtensionsInner) -> SpecEncryptedExtensions {
        let (l, extensions) = m;
        SpecEncryptedExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EncryptedExtensions<'a> {
    pub l: Uint0Ffff,
    pub extensions: EncryptedExtensionsExtensions<'a>,
}

impl View for EncryptedExtensions<'_> {
    type V = SpecEncryptedExtensions;

    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type EncryptedExtensionsInner<'a> = (Uint0Ffff, EncryptedExtensionsExtensions<'a>);
impl<'a> From<EncryptedExtensions<'a>> for EncryptedExtensionsInner<'a> {
    fn ex_from(m: EncryptedExtensions) -> EncryptedExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<EncryptedExtensionsInner<'a>> for EncryptedExtensions<'a> {
    fn ex_from(m: EncryptedExtensionsInner) -> EncryptedExtensions {
        let (l, extensions) = m;
        EncryptedExtensions { l, extensions }
    }
}

pub struct EncryptedExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        EncryptedExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        EncryptedExtensionsMapper(PhantomData)
    }
}
impl View for EncryptedExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionsMapper<'_> {
    type Src = SpecEncryptedExtensionsInner;
    type Dst = SpecEncryptedExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for EncryptedExtensionsMapper<'a> {
    type Src = EncryptedExtensionsInner<'a>;
    type Dst = EncryptedExtensions<'a>;
}

pub struct SpecEncryptedExtensionsCombinator(SpecEncryptedExtensionsCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionsCombinator {
    type SpecResult = SpecEncryptedExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecEncryptedExtensionsExtensionsCombinator>, EncryptedExtensionsMapper<'static>>;

pub struct EncryptedExtensionsCombinator<'a>(EncryptedExtensionsCombinatorAlias<'a>);

impl<'a> View for EncryptedExtensionsCombinator<'a> {
    type V = SpecEncryptedExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for EncryptedExtensionsCombinator<'a> {
    type Result = EncryptedExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type EncryptedExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, EncryptedExtensionsExtensionsCombinator<'a>, EncryptedExtensionsCont0<'a>>, EncryptedExtensionsMapper<'a>>;


pub closed spec fn spec_encrypted_extensions() -> SpecEncryptedExtensionsCombinator {
    SpecEncryptedExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_encrypted_extensions_cont0(deps) },
        mapper: EncryptedExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_encrypted_extensions_cont0(deps: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    let l = deps;
    spec_encrypted_extensions_extensions(l)
}
                
pub fn encrypted_extensions<'a>() -> (o: EncryptedExtensionsCombinator<'a>)
    ensures o@ == spec_encrypted_extensions(),
{
    EncryptedExtensionsCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: EncryptedExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_encrypted_extensions_cont0(deps)) },
        mapper: EncryptedExtensionsMapper::new(),
    })
}

pub struct EncryptedExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionsCont0<'a> {
    pub fn new() -> Self {
        EncryptedExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for EncryptedExtensionsCont0<'a> {
    type Output = EncryptedExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_encrypted_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        encrypted_extensions_extensions(l)
    }
}
                

pub enum SpecCertificateExtensionExtensionData {
    StatusRequest(SpecCertificateStatus),
    SignedCertificateTimeStamp(SpecSignedCertificateTimestampList),
    Unrecognized(Seq<u8>),
}

pub type SpecCertificateExtensionExtensionDataInner = Either<SpecCertificateStatus, Either<SpecSignedCertificateTimestampList, Seq<u8>>>;



impl SpecFrom<SpecCertificateExtensionExtensionData> for SpecCertificateExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecCertificateExtensionExtensionData) -> SpecCertificateExtensionExtensionDataInner {
        match m {
            SpecCertificateExtensionExtensionData::StatusRequest(m) => Either::Left(m),
            SpecCertificateExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Left(m)),
            SpecCertificateExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl SpecFrom<SpecCertificateExtensionExtensionDataInner> for SpecCertificateExtensionExtensionData {
    open spec fn spec_from(m: SpecCertificateExtensionExtensionDataInner) -> SpecCertificateExtensionExtensionData {
        match m {
            Either::Left(m) => SpecCertificateExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Left(m)) => SpecCertificateExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(m)) => SpecCertificateExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateExtensionExtensionData<'a> {
    StatusRequest(CertificateStatus<'a>),
    SignedCertificateTimeStamp(SignedCertificateTimestampList<'a>),
    Unrecognized(&'a [u8]),
}

pub type CertificateExtensionExtensionDataInner<'a> = Either<CertificateStatus<'a>, Either<SignedCertificateTimestampList<'a>, &'a [u8]>>;


impl<'a> View for CertificateExtensionExtensionData<'a> {
    type V = SpecCertificateExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            CertificateExtensionExtensionData::StatusRequest(m) => SpecCertificateExtensionExtensionData::StatusRequest(m@),
            CertificateExtensionExtensionData::SignedCertificateTimeStamp(m) => SpecCertificateExtensionExtensionData::SignedCertificateTimeStamp(m@),
            CertificateExtensionExtensionData::Unrecognized(m) => SpecCertificateExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<CertificateExtensionExtensionData<'a>> for CertificateExtensionExtensionDataInner<'a> {
    fn ex_from(m: CertificateExtensionExtensionData<'a>) -> CertificateExtensionExtensionDataInner<'a> {
        match m {
            CertificateExtensionExtensionData::StatusRequest(m) => Either::Left(m),
            CertificateExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Left(m)),
            CertificateExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<CertificateExtensionExtensionDataInner<'a>> for CertificateExtensionExtensionData<'a> {
    fn ex_from(m: CertificateExtensionExtensionDataInner<'a>) -> CertificateExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => CertificateExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Left(m)) => CertificateExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(m)) => CertificateExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct CertificateExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for CertificateExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionExtensionDataMapper<'_> {
    type Src = SpecCertificateExtensionExtensionDataInner;
    type Dst = SpecCertificateExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateExtensionExtensionDataMapper<'a> {
    type Src = CertificateExtensionExtensionDataInner<'a>;
    type Dst = CertificateExtensionExtensionData<'a>;
}


pub struct SpecCertificateExtensionExtensionDataCombinator(SpecCertificateExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionExtensionDataCombinator {
    type SpecResult = SpecCertificateExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecCertificateStatusCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, Cond<Bytes>>>, CertificateExtensionExtensionDataMapper<'static>>>;

pub struct CertificateExtensionExtensionDataCombinator<'a>(CertificateExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for CertificateExtensionExtensionDataCombinator<'a> {
    type V = SpecCertificateExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateExtensionExtensionDataCombinator<'a> {
    type Result = CertificateExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<CertificateStatusCombinator<'a>>, OrdChoice<Cond<SignedCertificateTimestampListCombinator<'a>>, Cond<Bytes>>>, CertificateExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_certificate_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecCertificateExtensionExtensionDataCombinator {
    SpecCertificateExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) })), mapper: CertificateExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn certificate_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: CertificateExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_certificate_extension_extension_data(extension_type@, ext_len@),
{
    CertificateExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 5, inner: certificate_status() }, OrdChoice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) })), mapper: CertificateExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecCertificateExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecCertificateExtensionExtensionData,
}

pub type SpecCertificateExtensionInner = ((SpecExtensionType, u16), SpecCertificateExtensionExtensionData);
impl SpecFrom<SpecCertificateExtension> for SpecCertificateExtensionInner {
    open spec fn spec_from(m: SpecCertificateExtension) -> SpecCertificateExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecCertificateExtensionInner> for SpecCertificateExtension {
    open spec fn spec_from(m: SpecCertificateExtensionInner) -> SpecCertificateExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecCertificateExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: CertificateExtensionExtensionData<'a>,
}

impl View for CertificateExtension<'_> {
    type V = SpecCertificateExtension;

    open spec fn view(&self) -> Self::V {
        SpecCertificateExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type CertificateExtensionInner<'a> = ((ExtensionType, u16), CertificateExtensionExtensionData<'a>);
impl<'a> From<CertificateExtension<'a>> for CertificateExtensionInner<'a> {
    fn ex_from(m: CertificateExtension) -> CertificateExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<CertificateExtensionInner<'a>> for CertificateExtension<'a> {
    fn ex_from(m: CertificateExtensionInner) -> CertificateExtension {
        let ((extension_type, ext_len), extension_data) = m;
        CertificateExtension { extension_type, ext_len, extension_data }
    }
}

pub struct CertificateExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateExtensionMapper(PhantomData)
    }
}
impl View for CertificateExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionMapper<'_> {
    type Src = SpecCertificateExtensionInner;
    type Dst = SpecCertificateExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateExtensionMapper<'a> {
    type Src = CertificateExtensionInner<'a>;
    type Dst = CertificateExtension<'a>;
}

pub struct SpecCertificateExtensionCombinator(SpecCertificateExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionCombinator {
    type SpecResult = SpecCertificateExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecCertificateExtensionExtensionDataCombinator>, CertificateExtensionMapper<'static>>;

pub struct CertificateExtensionCombinator<'a>(CertificateExtensionCombinatorAlias<'a>);

impl<'a> View for CertificateExtensionCombinator<'a> {
    type V = SpecCertificateExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateExtensionCombinator<'a> {
    type Result = CertificateExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, CertificateExtensionCont1<'a>>, CertificateExtensionExtensionDataCombinator<'a>, CertificateExtensionCont0<'a>>, CertificateExtensionMapper<'a>>;


pub closed spec fn spec_certificate_extension() -> SpecCertificateExtensionCombinator {
    SpecCertificateExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_certificate_extension_cont1(deps) }, snd: |deps| spec_certificate_extension_cont0(deps) },
        mapper: CertificateExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_certificate_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecCertificateExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_certificate_extension_extension_data(extension_type, ext_len)
}
                
pub fn certificate_extension<'a>() -> (o: CertificateExtensionCombinator<'a>)
    ensures o@ == spec_certificate_extension(),
{
    CertificateExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: CertificateExtensionCont1::new(), spec_snd: Ghost(|deps| spec_certificate_extension_cont1(deps)) }, snd: CertificateExtensionCont0::new(), spec_snd: Ghost(|deps| spec_certificate_extension_cont0(deps)) },
        mapper: CertificateExtensionMapper::new(),
    })
}

pub struct CertificateExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionCont1<'a> {
    pub fn new() -> Self {
        CertificateExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for CertificateExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_certificate_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct CertificateExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionCont0<'a> {
    pub fn new() -> Self {
        CertificateExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for CertificateExtensionCont0<'a> {
    type Output = CertificateExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_certificate_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        certificate_extension_extension_data(extension_type, ext_len)
    }
}
                
pub type SpecCertificateExtensionsExtensions = Seq<SpecCertificateExtension>;
pub type CertificateExtensionsExtensions<'a> = RepeatResult<CertificateExtension<'a>>;


pub struct SpecCertificateExtensionsExtensionsCombinator(SpecCertificateExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionsExtensionsCombinator {
    type SpecResult = SpecCertificateExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateExtensionCombinator>>;

pub struct CertificateExtensionsExtensionsCombinator<'a>(CertificateExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for CertificateExtensionsExtensionsCombinator<'a> {
    type V = SpecCertificateExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateExtensionsExtensionsCombinator<'a> {
    type Result = CertificateExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<CertificateExtensionCombinator<'a>>>;


pub closed spec fn spec_certificate_extensions_extensions(l: SpecUint0Ffff) -> SpecCertificateExtensionsExtensionsCombinator {
    SpecCertificateExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_extension())))
}

                
pub fn certificate_extensions_extensions<'a>(l: Uint0Ffff) -> (o: CertificateExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_extensions_extensions(l@),
{
    CertificateExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_extension())))
}

                

pub struct SpecCertificateExtensions {
    pub l: SpecUint0Ffff,
    pub extensions: SpecCertificateExtensionsExtensions,
}

pub type SpecCertificateExtensionsInner = (SpecUint0Ffff, SpecCertificateExtensionsExtensions);
impl SpecFrom<SpecCertificateExtensions> for SpecCertificateExtensionsInner {
    open spec fn spec_from(m: SpecCertificateExtensions) -> SpecCertificateExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecCertificateExtensionsInner> for SpecCertificateExtensions {
    open spec fn spec_from(m: SpecCertificateExtensionsInner) -> SpecCertificateExtensions {
        let (l, extensions) = m;
        SpecCertificateExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateExtensions<'a> {
    pub l: Uint0Ffff,
    pub extensions: CertificateExtensionsExtensions<'a>,
}

impl View for CertificateExtensions<'_> {
    type V = SpecCertificateExtensions;

    open spec fn view(&self) -> Self::V {
        SpecCertificateExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateExtensionsInner<'a> = (Uint0Ffff, CertificateExtensionsExtensions<'a>);
impl<'a> From<CertificateExtensions<'a>> for CertificateExtensionsInner<'a> {
    fn ex_from(m: CertificateExtensions) -> CertificateExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<CertificateExtensionsInner<'a>> for CertificateExtensions<'a> {
    fn ex_from(m: CertificateExtensionsInner) -> CertificateExtensions {
        let (l, extensions) = m;
        CertificateExtensions { l, extensions }
    }
}

pub struct CertificateExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateExtensionsMapper(PhantomData)
    }
}
impl View for CertificateExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionsMapper<'_> {
    type Src = SpecCertificateExtensionsInner;
    type Dst = SpecCertificateExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateExtensionsMapper<'a> {
    type Src = CertificateExtensionsInner<'a>;
    type Dst = CertificateExtensions<'a>;
}

pub struct SpecCertificateExtensionsCombinator(SpecCertificateExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionsCombinator {
    type SpecResult = SpecCertificateExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecCertificateExtensionsExtensionsCombinator>, CertificateExtensionsMapper<'static>>;

pub struct CertificateExtensionsCombinator<'a>(CertificateExtensionsCombinatorAlias<'a>);

impl<'a> View for CertificateExtensionsCombinator<'a> {
    type V = SpecCertificateExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateExtensionsCombinator<'a> {
    type Result = CertificateExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, CertificateExtensionsExtensionsCombinator<'a>, CertificateExtensionsCont0<'a>>, CertificateExtensionsMapper<'a>>;


pub closed spec fn spec_certificate_extensions() -> SpecCertificateExtensionsCombinator {
    SpecCertificateExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_0_ffff(), snd: |deps| spec_certificate_extensions_cont0(deps) },
        mapper: CertificateExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_extensions_cont0(deps: SpecUint0Ffff) -> SpecCertificateExtensionsExtensionsCombinator {
    let l = deps;
    spec_certificate_extensions_extensions(l)
}
                
pub fn certificate_extensions<'a>() -> (o: CertificateExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_extensions(),
{
    CertificateExtensionsCombinator(
    Mapped {
        inner: Depend { fst: uint_0_ffff(), snd: CertificateExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_certificate_extensions_cont0(deps)) },
        mapper: CertificateExtensionsMapper::new(),
    })
}

pub struct CertificateExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateExtensionsCont0<'a> {
    pub fn new() -> Self {
        CertificateExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint0Ffff> for CertificateExtensionsCont0<'a> {
    type Output = CertificateExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &Uint0Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_certificate_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &Uint0Ffff) -> Self::Output {
        let l = *deps;
        certificate_extensions_extensions(l)
    }
}
                

pub struct SpecCertificateEntry {
    pub cert_data: SpecOpaque1Ffffff,
    pub extensions: SpecCertificateExtensions,
}

pub type SpecCertificateEntryInner = (SpecOpaque1Ffffff, SpecCertificateExtensions);
impl SpecFrom<SpecCertificateEntry> for SpecCertificateEntryInner {
    open spec fn spec_from(m: SpecCertificateEntry) -> SpecCertificateEntryInner {
        (m.cert_data, m.extensions)
    }
}
impl SpecFrom<SpecCertificateEntryInner> for SpecCertificateEntry {
    open spec fn spec_from(m: SpecCertificateEntryInner) -> SpecCertificateEntry {
        let (cert_data, extensions) = m;
        SpecCertificateEntry { cert_data, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateEntry<'a> {
    pub cert_data: Opaque1Ffffff<'a>,
    pub extensions: CertificateExtensions<'a>,
}

impl View for CertificateEntry<'_> {
    type V = SpecCertificateEntry;

    open spec fn view(&self) -> Self::V {
        SpecCertificateEntry {
            cert_data: self.cert_data@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateEntryInner<'a> = (Opaque1Ffffff<'a>, CertificateExtensions<'a>);
impl<'a> From<CertificateEntry<'a>> for CertificateEntryInner<'a> {
    fn ex_from(m: CertificateEntry) -> CertificateEntryInner {
        (m.cert_data, m.extensions)
    }
}
impl<'a> From<CertificateEntryInner<'a>> for CertificateEntry<'a> {
    fn ex_from(m: CertificateEntryInner) -> CertificateEntry {
        let (cert_data, extensions) = m;
        CertificateEntry { cert_data, extensions }
    }
}

pub struct CertificateEntryMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateEntryMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateEntryMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateEntryMapper(PhantomData)
    }
}
impl View for CertificateEntryMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateEntryMapper<'_> {
    type Src = SpecCertificateEntryInner;
    type Dst = SpecCertificateEntry;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateEntryMapper<'a> {
    type Src = CertificateEntryInner<'a>;
    type Dst = CertificateEntry<'a>;
}

pub struct SpecCertificateEntryCombinator(SpecCertificateEntryCombinatorAlias);

impl SpecCombinator for SpecCertificateEntryCombinator {
    type SpecResult = SpecCertificateEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateEntryCombinatorAlias = Mapped<(SpecOpaque1FfffffCombinator, SpecCertificateExtensionsCombinator), CertificateEntryMapper<'static>>;

pub struct CertificateEntryCombinator<'a>(CertificateEntryCombinatorAlias<'a>);

impl<'a> View for CertificateEntryCombinator<'a> {
    type V = SpecCertificateEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateEntryCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateEntryCombinator<'a> {
    type Result = CertificateEntry<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateEntryCombinatorAlias<'a> = Mapped<(Opaque1FfffffCombinator<'a>, CertificateExtensionsCombinator<'a>), CertificateEntryMapper<'a>>;


pub closed spec fn spec_certificate_entry() -> SpecCertificateEntryCombinator {
    SpecCertificateEntryCombinator(
    Mapped {
        inner: (spec_opaque_1_ffffff(), spec_certificate_extensions()),
        mapper: CertificateEntryMapper::spec_new(),
    })
}

                
pub fn certificate_entry<'a>() -> (o: CertificateEntryCombinator<'a>)
    ensures o@ == spec_certificate_entry(),
{
    CertificateEntryCombinator(
    Mapped {
        inner: (opaque_1_ffffff(), certificate_extensions()),
        mapper: CertificateEntryMapper::new(),
    })
}

                
pub type SpecCertificateListList = Seq<SpecCertificateEntry>;
pub type CertificateListList<'a> = RepeatResult<CertificateEntry<'a>>;


pub struct SpecCertificateListListCombinator(SpecCertificateListListCombinatorAlias);

impl SpecCombinator for SpecCertificateListListCombinator {
    type SpecResult = SpecCertificateListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateListListCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateEntryCombinator>>;

pub struct CertificateListListCombinator<'a>(CertificateListListCombinatorAlias<'a>);

impl<'a> View for CertificateListListCombinator<'a> {
    type V = SpecCertificateListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateListListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateListListCombinator<'a> {
    type Result = CertificateListList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateListListCombinatorAlias<'a> = AndThen<Bytes, Repeat<CertificateEntryCombinator<'a>>>;


pub closed spec fn spec_certificate_list_list(l: u24) -> SpecCertificateListListCombinator {
    SpecCertificateListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_entry())))
}

                
pub fn certificate_list_list<'a>(l: u24) -> (o: CertificateListListCombinator<'a>)
    ensures o@ == spec_certificate_list_list(l@),
{
    CertificateListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_entry())))
}

                

pub struct SpecCertificateList {
    pub l: u24,
    pub list: SpecCertificateListList,
}

pub type SpecCertificateListInner = (u24, SpecCertificateListList);
impl SpecFrom<SpecCertificateList> for SpecCertificateListInner {
    open spec fn spec_from(m: SpecCertificateList) -> SpecCertificateListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecCertificateListInner> for SpecCertificateList {
    open spec fn spec_from(m: SpecCertificateListInner) -> SpecCertificateList {
        let (l, list) = m;
        SpecCertificateList { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateList<'a> {
    pub l: u24,
    pub list: CertificateListList<'a>,
}

impl View for CertificateList<'_> {
    type V = SpecCertificateList;

    open spec fn view(&self) -> Self::V {
        SpecCertificateList {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type CertificateListInner<'a> = (u24, CertificateListList<'a>);
impl<'a> From<CertificateList<'a>> for CertificateListInner<'a> {
    fn ex_from(m: CertificateList) -> CertificateListInner {
        (m.l, m.list)
    }
}
impl<'a> From<CertificateListInner<'a>> for CertificateList<'a> {
    fn ex_from(m: CertificateListInner) -> CertificateList {
        let (l, list) = m;
        CertificateList { l, list }
    }
}

pub struct CertificateListMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateListMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateListMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateListMapper(PhantomData)
    }
}
impl View for CertificateListMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateListMapper<'_> {
    type Src = SpecCertificateListInner;
    type Dst = SpecCertificateList;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateListMapper<'a> {
    type Src = CertificateListInner<'a>;
    type Dst = CertificateList<'a>;
}

pub struct SpecCertificateListCombinator(SpecCertificateListCombinatorAlias);

impl SpecCombinator for SpecCertificateListCombinator {
    type SpecResult = SpecCertificateList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateListCombinatorAlias = Mapped<SpecDepend<U24Be, SpecCertificateListListCombinator>, CertificateListMapper<'static>>;

pub struct CertificateListCombinator<'a>(CertificateListCombinatorAlias<'a>);

impl<'a> View for CertificateListCombinator<'a> {
    type V = SpecCertificateListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateListCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateListCombinator<'a> {
    type Result = CertificateList<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U24Be, CertificateListListCombinator<'a>, CertificateListCont0<'a>>, CertificateListMapper<'a>>;


pub closed spec fn spec_certificate_list() -> SpecCertificateListCombinator {
    SpecCertificateListCombinator(
    Mapped {
        inner: SpecDepend { fst: U24Be, snd: |deps| spec_certificate_list_cont0(deps) },
        mapper: CertificateListMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_list_cont0(deps: u24) -> SpecCertificateListListCombinator {
    let l = deps;
    spec_certificate_list_list(l)
}
                
pub fn certificate_list<'a>() -> (o: CertificateListCombinator<'a>)
    ensures o@ == spec_certificate_list(),
{
    CertificateListCombinator(
    Mapped {
        inner: Depend { fst: U24Be, snd: CertificateListCont0::new(), spec_snd: Ghost(|deps| spec_certificate_list_cont0(deps)) },
        mapper: CertificateListMapper::new(),
    })
}

pub struct CertificateListCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateListCont0<'a> {
    pub fn new() -> Self {
        CertificateListCont0(PhantomData)
    }
}
impl<'a> Continuation<&u24> for CertificateListCont0<'a> {
    type Output = CertificateListListCombinator<'a>;

    open spec fn requires(&self, deps: &u24) -> bool { true }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_certificate_list_cont0(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let l = *deps;
        certificate_list_list(l)
    }
}
                

pub struct SpecCertificate {
    pub certificate_request_context: SpecOpaque0Ff,
    pub certificate_list: SpecCertificateList,
}

pub type SpecCertificateInner = (SpecOpaque0Ff, SpecCertificateList);
impl SpecFrom<SpecCertificate> for SpecCertificateInner {
    open spec fn spec_from(m: SpecCertificate) -> SpecCertificateInner {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl SpecFrom<SpecCertificateInner> for SpecCertificate {
    open spec fn spec_from(m: SpecCertificateInner) -> SpecCertificate {
        let (certificate_request_context, certificate_list) = m;
        SpecCertificate { certificate_request_context, certificate_list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Certificate<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub certificate_list: CertificateList<'a>,
}

impl View for Certificate<'_> {
    type V = SpecCertificate;

    open spec fn view(&self) -> Self::V {
        SpecCertificate {
            certificate_request_context: self.certificate_request_context@,
            certificate_list: self.certificate_list@,
        }
    }
}
pub type CertificateInner<'a> = (Opaque0Ff<'a>, CertificateList<'a>);
impl<'a> From<Certificate<'a>> for CertificateInner<'a> {
    fn ex_from(m: Certificate) -> CertificateInner {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl<'a> From<CertificateInner<'a>> for Certificate<'a> {
    fn ex_from(m: CertificateInner) -> Certificate {
        let (certificate_request_context, certificate_list) = m;
        Certificate { certificate_request_context, certificate_list }
    }
}

pub struct CertificateMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateMapper(PhantomData)
    }
}
impl View for CertificateMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateMapper<'_> {
    type Src = SpecCertificateInner;
    type Dst = SpecCertificate;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateMapper<'a> {
    type Src = CertificateInner<'a>;
    type Dst = Certificate<'a>;
}

pub struct SpecCertificateCombinator(SpecCertificateCombinatorAlias);

impl SpecCombinator for SpecCertificateCombinator {
    type SpecResult = SpecCertificate;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateCombinatorAlias = Mapped<(SpecOpaque0FfCombinator, SpecCertificateListCombinator), CertificateMapper<'static>>;

pub struct CertificateCombinator<'a>(CertificateCombinatorAlias<'a>);

impl<'a> View for CertificateCombinator<'a> {
    type V = SpecCertificateCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateCombinator<'a> {
    type Result = Certificate<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateCombinatorAlias<'a> = Mapped<(Opaque0FfCombinator<'a>, CertificateListCombinator<'a>), CertificateMapper<'a>>;


pub closed spec fn spec_certificate() -> SpecCertificateCombinator {
    SpecCertificateCombinator(
    Mapped {
        inner: (spec_opaque_0_ff(), spec_certificate_list()),
        mapper: CertificateMapper::spec_new(),
    })
}

                
pub fn certificate<'a>() -> (o: CertificateCombinator<'a>)
    ensures o@ == spec_certificate(),
{
    CertificateCombinator(
    Mapped {
        inner: (opaque_0_ff(), certificate_list()),
        mapper: CertificateMapper::new(),
    })
}

                

pub enum SpecCertificateRequestExtensionExtensionData {
    SignatureAlgorithms(SpecSignatureSchemeList),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    StatusRequest(SpecCertificateStatusRequest),
    SignedCertificateTimeStamp(SpecSignedCertificateTimestampList),
    OidFilters(SpecOidFilterExtension),
    Unrecognized(Seq<u8>),
}

pub type SpecCertificateRequestExtensionExtensionDataInner = Either<SpecSignatureSchemeList, Either<SpecCertificateAuthoritiesExtension, Either<SpecSignatureSchemeList, Either<SpecCertificateStatusRequest, Either<SpecSignedCertificateTimestampList, Either<SpecOidFilterExtension, Seq<u8>>>>>>>;



impl SpecFrom<SpecCertificateRequestExtensionExtensionData> for SpecCertificateRequestExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecCertificateRequestExtensionExtensionData) -> SpecCertificateRequestExtensionExtensionDataInner {
        match m {
            SpecCertificateRequestExtensionExtensionData::SignatureAlgorithms(m) => Either::Left(m),
            SpecCertificateRequestExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Left(m)),
            SpecCertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecCertificateRequestExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecCertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecCertificateRequestExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecCertificateRequestExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

impl SpecFrom<SpecCertificateRequestExtensionExtensionDataInner> for SpecCertificateRequestExtensionExtensionData {
    open spec fn spec_from(m: SpecCertificateRequestExtensionExtensionDataInner) -> SpecCertificateRequestExtensionExtensionData {
        match m {
            Either::Left(m) => SpecCertificateRequestExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Left(m)) => SpecCertificateRequestExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecCertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecCertificateRequestExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecCertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecCertificateRequestExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => SpecCertificateRequestExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateRequestExtensionExtensionData<'a> {
    SignatureAlgorithms(SignatureSchemeList),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    StatusRequest(CertificateStatusRequest<'a>),
    SignedCertificateTimeStamp(SignedCertificateTimestampList<'a>),
    OidFilters(OidFilterExtension<'a>),
    Unrecognized(&'a [u8]),
}

pub type CertificateRequestExtensionExtensionDataInner<'a> = Either<SignatureSchemeList, Either<CertificateAuthoritiesExtension<'a>, Either<SignatureSchemeList, Either<CertificateStatusRequest<'a>, Either<SignedCertificateTimestampList<'a>, Either<OidFilterExtension<'a>, &'a [u8]>>>>>>;


impl<'a> View for CertificateRequestExtensionExtensionData<'a> {
    type V = SpecCertificateRequestExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            CertificateRequestExtensionExtensionData::SignatureAlgorithms(m) => SpecCertificateRequestExtensionExtensionData::SignatureAlgorithms(m@),
            CertificateRequestExtensionExtensionData::CertificateAuthorities(m) => SpecCertificateRequestExtensionExtensionData::CertificateAuthorities(m@),
            CertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecCertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m@),
            CertificateRequestExtensionExtensionData::StatusRequest(m) => SpecCertificateRequestExtensionExtensionData::StatusRequest(m@),
            CertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m) => SpecCertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m@),
            CertificateRequestExtensionExtensionData::OidFilters(m) => SpecCertificateRequestExtensionExtensionData::OidFilters(m@),
            CertificateRequestExtensionExtensionData::Unrecognized(m) => SpecCertificateRequestExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<CertificateRequestExtensionExtensionData<'a>> for CertificateRequestExtensionExtensionDataInner<'a> {
    fn ex_from(m: CertificateRequestExtensionExtensionData<'a>) -> CertificateRequestExtensionExtensionDataInner<'a> {
        match m {
            CertificateRequestExtensionExtensionData::SignatureAlgorithms(m) => Either::Left(m),
            CertificateRequestExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Left(m)),
            CertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Left(m))),
            CertificateRequestExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            CertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            CertificateRequestExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            CertificateRequestExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

impl<'a> From<CertificateRequestExtensionExtensionDataInner<'a>> for CertificateRequestExtensionExtensionData<'a> {
    fn ex_from(m: CertificateRequestExtensionExtensionDataInner<'a>) -> CertificateRequestExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => CertificateRequestExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Left(m)) => CertificateRequestExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Left(m))) => CertificateRequestExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => CertificateRequestExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => CertificateRequestExtensionExtensionData::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => CertificateRequestExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => CertificateRequestExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct CertificateRequestExtensionExtensionDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionExtensionDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateRequestExtensionExtensionDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateRequestExtensionExtensionDataMapper(PhantomData)
    }
}
impl View for CertificateRequestExtensionExtensionDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionExtensionDataMapper<'_> {
    type Src = SpecCertificateRequestExtensionExtensionDataInner;
    type Dst = SpecCertificateRequestExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateRequestExtensionExtensionDataMapper<'a> {
    type Src = CertificateRequestExtensionExtensionDataInner<'a>;
    type Dst = CertificateRequestExtensionExtensionData<'a>;
}


pub struct SpecCertificateRequestExtensionExtensionDataCombinator(SpecCertificateRequestExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionExtensionDataCombinator {
    type SpecResult = SpecCertificateRequestExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecCertificateStatusRequestCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, Cond<Bytes>>>>>>>, CertificateRequestExtensionExtensionDataMapper<'static>>>;

pub struct CertificateRequestExtensionExtensionDataCombinator<'a>(CertificateRequestExtensionExtensionDataCombinatorAlias<'a>);

impl<'a> View for CertificateRequestExtensionExtensionDataCombinator<'a> {
    type V = SpecCertificateRequestExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateRequestExtensionExtensionDataCombinator<'a> {
    type Result = CertificateRequestExtensionExtensionData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateRequestExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator<'a>>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<CertificateStatusRequestCombinator<'a>>, OrdChoice<Cond<SignedCertificateTimestampListCombinator<'a>>, OrdChoice<Cond<OidFilterExtensionCombinator<'a>>, Cond<Bytes>>>>>>>, CertificateRequestExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_certificate_request_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecCertificateRequestExtensionExtensionDataCombinator {
    SpecCertificateRequestExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) })))))), mapper: CertificateRequestExtensionExtensionDataMapper::spec_new() }))
}

                
pub fn certificate_request_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: CertificateRequestExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_certificate_request_extension_extension_data(ext_len@, extension_type@),
{
    CertificateRequestExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, OrdChoice::new(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice::new(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, OrdChoice::new(Cond { cond: extension_type == 5, inner: certificate_status_request() }, OrdChoice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice::new(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) })))))), mapper: CertificateRequestExtensionExtensionDataMapper::new() }))
}

                

pub struct SpecCertificateRequestExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecCertificateRequestExtensionExtensionData,
}

pub type SpecCertificateRequestExtensionInner = ((SpecExtensionType, u16), SpecCertificateRequestExtensionExtensionData);
impl SpecFrom<SpecCertificateRequestExtension> for SpecCertificateRequestExtensionInner {
    open spec fn spec_from(m: SpecCertificateRequestExtension) -> SpecCertificateRequestExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecCertificateRequestExtensionInner> for SpecCertificateRequestExtension {
    open spec fn spec_from(m: SpecCertificateRequestExtensionInner) -> SpecCertificateRequestExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecCertificateRequestExtension { extension_type, ext_len, extension_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateRequestExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: CertificateRequestExtensionExtensionData<'a>,
}

impl View for CertificateRequestExtension<'_> {
    type V = SpecCertificateRequestExtension;

    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
pub type CertificateRequestExtensionInner<'a> = ((ExtensionType, u16), CertificateRequestExtensionExtensionData<'a>);
impl<'a> From<CertificateRequestExtension<'a>> for CertificateRequestExtensionInner<'a> {
    fn ex_from(m: CertificateRequestExtension) -> CertificateRequestExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<CertificateRequestExtensionInner<'a>> for CertificateRequestExtension<'a> {
    fn ex_from(m: CertificateRequestExtensionInner) -> CertificateRequestExtension {
        let ((extension_type, ext_len), extension_data) = m;
        CertificateRequestExtension { extension_type, ext_len, extension_data }
    }
}

pub struct CertificateRequestExtensionMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateRequestExtensionMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateRequestExtensionMapper(PhantomData)
    }
}
impl View for CertificateRequestExtensionMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionMapper<'_> {
    type Src = SpecCertificateRequestExtensionInner;
    type Dst = SpecCertificateRequestExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateRequestExtensionMapper<'a> {
    type Src = CertificateRequestExtensionInner<'a>;
    type Dst = CertificateRequestExtension<'a>;
}

pub struct SpecCertificateRequestExtensionCombinator(SpecCertificateRequestExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionCombinator {
    type SpecResult = SpecCertificateRequestExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecExtensionTypeCombinator, U16Be>, SpecCertificateRequestExtensionExtensionDataCombinator>, CertificateRequestExtensionMapper<'static>>;

pub struct CertificateRequestExtensionCombinator<'a>(CertificateRequestExtensionCombinatorAlias<'a>);

impl<'a> View for CertificateRequestExtensionCombinator<'a> {
    type V = SpecCertificateRequestExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateRequestExtensionCombinator<'a> {
    type Result = CertificateRequestExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateRequestExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, ExtensionTypeCombinator, U16Be, CertificateRequestExtensionCont1<'a>>, CertificateRequestExtensionExtensionDataCombinator<'a>, CertificateRequestExtensionCont0<'a>>, CertificateRequestExtensionMapper<'a>>;


pub closed spec fn spec_certificate_request_extension() -> SpecCertificateRequestExtensionCombinator {
    SpecCertificateRequestExtensionCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_extension_type(), snd: |deps| spec_certificate_request_extension_cont1(deps) }, snd: |deps| spec_certificate_request_extension_cont0(deps) },
        mapper: CertificateRequestExtensionMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_request_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}
pub open spec fn spec_certificate_request_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecCertificateRequestExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_certificate_request_extension_extension_data(ext_len, extension_type)
}
                
pub fn certificate_request_extension<'a>() -> (o: CertificateRequestExtensionCombinator<'a>)
    ensures o@ == spec_certificate_request_extension(),
{
    CertificateRequestExtensionCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: extension_type(), snd: CertificateRequestExtensionCont1::new(), spec_snd: Ghost(|deps| spec_certificate_request_extension_cont1(deps)) }, snd: CertificateRequestExtensionCont0::new(), spec_snd: Ghost(|deps| spec_certificate_request_extension_cont0(deps)) },
        mapper: CertificateRequestExtensionMapper::new(),
    })
}

pub struct CertificateRequestExtensionCont1<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionCont1<'a> {
    pub fn new() -> Self {
        CertificateRequestExtensionCont1(PhantomData)
    }
}
impl<'a> Continuation<&ExtensionType> for CertificateRequestExtensionCont1<'a> {
    type Output = U16Be;

    open spec fn requires(&self, deps: &ExtensionType) -> bool { true }

    open spec fn ensures(&self, deps: &ExtensionType, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extension_cont1(deps@)
    }

    fn apply(&self, deps: &ExtensionType) -> Self::Output {
        let extension_type = *deps;
        U16Be
    }
}
pub struct CertificateRequestExtensionCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionCont0<'a> {
    pub fn new() -> Self {
        CertificateRequestExtensionCont0(PhantomData)
    }
}
impl<'a> Continuation<&(ExtensionType, u16)> for CertificateRequestExtensionCont0<'a> {
    type Output = CertificateRequestExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: &(ExtensionType, u16)) -> bool { true }

    open spec fn ensures(&self, deps: &(ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_certificate_request_extension_cont0(deps@)
    }

    fn apply(&self, deps: &(ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = *deps;
        certificate_request_extension_extension_data(ext_len, extension_type)
    }
}
                
pub type SpecCertificateRequestExtensionsExtensions = Seq<SpecCertificateRequestExtension>;
pub type CertificateRequestExtensionsExtensions<'a> = RepeatResult<CertificateRequestExtension<'a>>;


pub struct SpecCertificateRequestExtensionsExtensionsCombinator(SpecCertificateRequestExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionsExtensionsCombinator {
    type SpecResult = SpecCertificateRequestExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateRequestExtensionCombinator>>;

pub struct CertificateRequestExtensionsExtensionsCombinator<'a>(CertificateRequestExtensionsExtensionsCombinatorAlias<'a>);

impl<'a> View for CertificateRequestExtensionsExtensionsCombinator<'a> {
    type V = SpecCertificateRequestExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionsExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateRequestExtensionsExtensionsCombinator<'a> {
    type Result = CertificateRequestExtensionsExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateRequestExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<CertificateRequestExtensionCombinator<'a>>>;


pub closed spec fn spec_certificate_request_extensions_extensions(l: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    SpecCertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_request_extension())))
}

                
pub fn certificate_request_extensions_extensions<'a>(l: Uint2Ffff) -> (o: CertificateRequestExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_request_extensions_extensions(l@),
{
    CertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_request_extension())))
}

                

pub struct SpecCertificateRequestExtensions {
    pub l: SpecUint2Ffff,
    pub extensions: SpecCertificateRequestExtensionsExtensions,
}

pub type SpecCertificateRequestExtensionsInner = (SpecUint2Ffff, SpecCertificateRequestExtensionsExtensions);
impl SpecFrom<SpecCertificateRequestExtensions> for SpecCertificateRequestExtensionsInner {
    open spec fn spec_from(m: SpecCertificateRequestExtensions) -> SpecCertificateRequestExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecCertificateRequestExtensionsInner> for SpecCertificateRequestExtensions {
    open spec fn spec_from(m: SpecCertificateRequestExtensionsInner) -> SpecCertificateRequestExtensions {
        let (l, extensions) = m;
        SpecCertificateRequestExtensions { l, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateRequestExtensions<'a> {
    pub l: Uint2Ffff,
    pub extensions: CertificateRequestExtensionsExtensions<'a>,
}

impl View for CertificateRequestExtensions<'_> {
    type V = SpecCertificateRequestExtensions;

    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateRequestExtensionsInner<'a> = (Uint2Ffff, CertificateRequestExtensionsExtensions<'a>);
impl<'a> From<CertificateRequestExtensions<'a>> for CertificateRequestExtensionsInner<'a> {
    fn ex_from(m: CertificateRequestExtensions) -> CertificateRequestExtensionsInner {
        (m.l, m.extensions)
    }
}
impl<'a> From<CertificateRequestExtensionsInner<'a>> for CertificateRequestExtensions<'a> {
    fn ex_from(m: CertificateRequestExtensionsInner) -> CertificateRequestExtensions {
        let (l, extensions) = m;
        CertificateRequestExtensions { l, extensions }
    }
}

pub struct CertificateRequestExtensionsMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateRequestExtensionsMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateRequestExtensionsMapper(PhantomData)
    }
}
impl View for CertificateRequestExtensionsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionsMapper<'_> {
    type Src = SpecCertificateRequestExtensionsInner;
    type Dst = SpecCertificateRequestExtensions;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateRequestExtensionsMapper<'a> {
    type Src = CertificateRequestExtensionsInner<'a>;
    type Dst = CertificateRequestExtensions<'a>;
}

pub struct SpecCertificateRequestExtensionsCombinator(SpecCertificateRequestExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionsCombinator {
    type SpecResult = SpecCertificateRequestExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecCertificateRequestExtensionsExtensionsCombinator>, CertificateRequestExtensionsMapper<'static>>;

pub struct CertificateRequestExtensionsCombinator<'a>(CertificateRequestExtensionsCombinatorAlias<'a>);

impl<'a> View for CertificateRequestExtensionsCombinator<'a> {
    type V = SpecCertificateRequestExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateRequestExtensionsCombinator<'a> {
    type Result = CertificateRequestExtensions<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateRequestExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, CertificateRequestExtensionsExtensionsCombinator<'a>, CertificateRequestExtensionsCont0<'a>>, CertificateRequestExtensionsMapper<'a>>;


pub closed spec fn spec_certificate_request_extensions() -> SpecCertificateRequestExtensionsCombinator {
    SpecCertificateRequestExtensionsCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_ffff(), snd: |deps| spec_certificate_request_extensions_cont0(deps) },
        mapper: CertificateRequestExtensionsMapper::spec_new(),
    })
}

pub open spec fn spec_certificate_request_extensions_cont0(deps: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    let l = deps;
    spec_certificate_request_extensions_extensions(l)
}
                
pub fn certificate_request_extensions<'a>() -> (o: CertificateRequestExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_request_extensions(),
{
    CertificateRequestExtensionsCombinator(
    Mapped {
        inner: Depend { fst: uint_2_ffff(), snd: CertificateRequestExtensionsCont0::new(), spec_snd: Ghost(|deps| spec_certificate_request_extensions_cont0(deps)) },
        mapper: CertificateRequestExtensionsMapper::new(),
    })
}

pub struct CertificateRequestExtensionsCont0<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionsCont0<'a> {
    pub fn new() -> Self {
        CertificateRequestExtensionsCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Ffff> for CertificateRequestExtensionsCont0<'a> {
    type Output = CertificateRequestExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: &Uint2Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extensions_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Ffff) -> Self::Output {
        let l = *deps;
        certificate_request_extensions_extensions(l)
    }
}
                

pub struct SpecCertificateRequest {
    pub certificate_request_context: SpecOpaque0Ff,
    pub extensions: SpecCertificateRequestExtensions,
}

pub type SpecCertificateRequestInner = (SpecOpaque0Ff, SpecCertificateRequestExtensions);
impl SpecFrom<SpecCertificateRequest> for SpecCertificateRequestInner {
    open spec fn spec_from(m: SpecCertificateRequest) -> SpecCertificateRequestInner {
        (m.certificate_request_context, m.extensions)
    }
}
impl SpecFrom<SpecCertificateRequestInner> for SpecCertificateRequest {
    open spec fn spec_from(m: SpecCertificateRequestInner) -> SpecCertificateRequest {
        let (certificate_request_context, extensions) = m;
        SpecCertificateRequest { certificate_request_context, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateRequest<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub extensions: CertificateRequestExtensions<'a>,
}

impl View for CertificateRequest<'_> {
    type V = SpecCertificateRequest;

    open spec fn view(&self) -> Self::V {
        SpecCertificateRequest {
            certificate_request_context: self.certificate_request_context@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateRequestInner<'a> = (Opaque0Ff<'a>, CertificateRequestExtensions<'a>);
impl<'a> From<CertificateRequest<'a>> for CertificateRequestInner<'a> {
    fn ex_from(m: CertificateRequest) -> CertificateRequestInner {
        (m.certificate_request_context, m.extensions)
    }
}
impl<'a> From<CertificateRequestInner<'a>> for CertificateRequest<'a> {
    fn ex_from(m: CertificateRequestInner) -> CertificateRequest {
        let (certificate_request_context, extensions) = m;
        CertificateRequest { certificate_request_context, extensions }
    }
}

pub struct CertificateRequestMapper<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        CertificateRequestMapper(PhantomData)
    }
    pub fn new() -> Self {
        CertificateRequestMapper(PhantomData)
    }
}
impl View for CertificateRequestMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestMapper<'_> {
    type Src = SpecCertificateRequestInner;
    type Dst = SpecCertificateRequest;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for CertificateRequestMapper<'a> {
    type Src = CertificateRequestInner<'a>;
    type Dst = CertificateRequest<'a>;
}

pub struct SpecCertificateRequestCombinator(SpecCertificateRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestCombinator {
    type SpecResult = SpecCertificateRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestCombinatorAlias = Mapped<(SpecOpaque0FfCombinator, SpecCertificateRequestExtensionsCombinator), CertificateRequestMapper<'static>>;

pub struct CertificateRequestCombinator<'a>(CertificateRequestCombinatorAlias<'a>);

impl<'a> View for CertificateRequestCombinator<'a> {
    type V = SpecCertificateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for CertificateRequestCombinator<'a> {
    type Result = CertificateRequest<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type CertificateRequestCombinatorAlias<'a> = Mapped<(Opaque0FfCombinator<'a>, CertificateRequestExtensionsCombinator<'a>), CertificateRequestMapper<'a>>;


pub closed spec fn spec_certificate_request() -> SpecCertificateRequestCombinator {
    SpecCertificateRequestCombinator(
    Mapped {
        inner: (spec_opaque_0_ff(), spec_certificate_request_extensions()),
        mapper: CertificateRequestMapper::spec_new(),
    })
}

                
pub fn certificate_request<'a>() -> (o: CertificateRequestCombinator<'a>)
    ensures o@ == spec_certificate_request(),
{
    CertificateRequestCombinator(
    Mapped {
        inner: (opaque_0_ff(), certificate_request_extensions()),
        mapper: CertificateRequestMapper::new(),
    })
}

                
pub type SpecFinished = Seq<u8>;
pub type Finished<'a> = &'a [u8];


pub struct SpecFinishedCombinator(SpecFinishedCombinatorAlias);

impl SpecCombinator for SpecFinishedCombinator {
    type SpecResult = SpecFinished;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecFinishedCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFinishedCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecFinishedCombinatorAlias = Bytes;

pub struct FinishedCombinator(FinishedCombinatorAlias);

impl View for FinishedCombinator {
    type V = SpecFinishedCombinator;
    closed spec fn view(&self) -> Self::V { SpecFinishedCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for FinishedCombinator {
    type Result = Finished<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type FinishedCombinatorAlias = Bytes;


pub closed spec fn spec_finished(digest_size: u24) -> SpecFinishedCombinator {
    SpecFinishedCombinator(Bytes(digest_size.spec_into()))
}

                
pub fn finished<'a>(digest_size: u24) -> (o: FinishedCombinator)
    ensures o@ == spec_finished(digest_size@),
{
    FinishedCombinator(Bytes(digest_size.ex_into()))
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum KeyUpdateRequest {
    UpdateNotRequested = 0,
UpdateRequested = 1
}
pub type SpecKeyUpdateRequest = KeyUpdateRequest;

pub type KeyUpdateRequestInner = u8;

impl View for KeyUpdateRequest {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<KeyUpdateRequestInner> for KeyUpdateRequest {
    type Error = ();

    open spec fn spec_try_from(v: KeyUpdateRequestInner) -> Result<KeyUpdateRequest, ()> {
        match v {
            0u8 => Ok(KeyUpdateRequest::UpdateNotRequested),
            1u8 => Ok(KeyUpdateRequest::UpdateRequested),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<KeyUpdateRequest> for KeyUpdateRequestInner {
    type Error = ();

    open spec fn spec_try_from(v: KeyUpdateRequest) -> Result<KeyUpdateRequestInner, ()> {
        match v {
            KeyUpdateRequest::UpdateNotRequested => Ok(0u8),
            KeyUpdateRequest::UpdateRequested => Ok(1u8),
        }
    }
}

impl TryFrom<KeyUpdateRequestInner> for KeyUpdateRequest {
    type Error = ();

    fn ex_try_from(v: KeyUpdateRequestInner) -> Result<KeyUpdateRequest, ()> {
        match v {
            0u8 => Ok(KeyUpdateRequest::UpdateNotRequested),
            1u8 => Ok(KeyUpdateRequest::UpdateRequested),
            _ => Err(()),
        }
    }
}

impl TryFrom<KeyUpdateRequest> for KeyUpdateRequestInner {
    type Error = ();

    fn ex_try_from(v: KeyUpdateRequest) -> Result<KeyUpdateRequestInner, ()> {
        match v {
            KeyUpdateRequest::UpdateNotRequested => Ok(0u8),
            KeyUpdateRequest::UpdateRequested => Ok(1u8),
        }
    }
}

pub struct KeyUpdateRequestMapper;

impl View for KeyUpdateRequestMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for KeyUpdateRequestMapper {
    type Src = KeyUpdateRequestInner;
    type Dst = KeyUpdateRequest;

    proof fn spec_iso(s: Self::Src) { }

    proof fn spec_iso_rev(s: Self::Dst) { }
}

impl TryFromInto for KeyUpdateRequestMapper {
    type Src = KeyUpdateRequestInner;
    type Dst = KeyUpdateRequest;
}


pub struct SpecKeyUpdateRequestCombinator(SpecKeyUpdateRequestCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateRequestCombinator {
    type SpecResult = SpecKeyUpdateRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyUpdateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyUpdateRequestCombinatorAlias = TryMap<U8, KeyUpdateRequestMapper>;

pub struct KeyUpdateRequestCombinator(KeyUpdateRequestCombinatorAlias);

impl View for KeyUpdateRequestCombinator {
    type V = SpecKeyUpdateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyUpdateRequestCombinator {
    type Result = KeyUpdateRequest;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyUpdateRequestCombinatorAlias = TryMap<U8, KeyUpdateRequestMapper>;


pub closed spec fn spec_key_update_request() -> SpecKeyUpdateRequestCombinator {
    SpecKeyUpdateRequestCombinator(TryMap { inner: U8, mapper: KeyUpdateRequestMapper })
}

                
pub fn key_update_request() -> (o: KeyUpdateRequestCombinator)
    ensures o@ == spec_key_update_request(),
{
    KeyUpdateRequestCombinator(TryMap { inner: U8, mapper: KeyUpdateRequestMapper })
}

                

pub struct SpecKeyUpdate {
    pub request_update: SpecKeyUpdateRequest,
}

pub type SpecKeyUpdateInner = SpecKeyUpdateRequest;
impl SpecFrom<SpecKeyUpdate> for SpecKeyUpdateInner {
    open spec fn spec_from(m: SpecKeyUpdate) -> SpecKeyUpdateInner {
        m.request_update
    }
}
impl SpecFrom<SpecKeyUpdateInner> for SpecKeyUpdate {
    open spec fn spec_from(m: SpecKeyUpdateInner) -> SpecKeyUpdate {
        let request_update = m;
        SpecKeyUpdate { request_update }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct KeyUpdate {
    pub request_update: KeyUpdateRequest,
}

impl View for KeyUpdate {
    type V = SpecKeyUpdate;

    open spec fn view(&self) -> Self::V {
        SpecKeyUpdate {
            request_update: self.request_update@,
        }
    }
}
pub type KeyUpdateInner = KeyUpdateRequest;
impl From<KeyUpdate> for KeyUpdateInner {
    fn ex_from(m: KeyUpdate) -> KeyUpdateInner {
        m.request_update
    }
}
impl From<KeyUpdateInner> for KeyUpdate {
    fn ex_from(m: KeyUpdateInner) -> KeyUpdate {
        let request_update = m;
        KeyUpdate { request_update }
    }
}

pub struct KeyUpdateMapper;
impl KeyUpdateMapper {
    pub closed spec fn spec_new() -> Self {
        KeyUpdateMapper
    }
    pub fn new() -> Self {
        KeyUpdateMapper
    }
}
impl View for KeyUpdateMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyUpdateMapper {
    type Src = SpecKeyUpdateInner;
    type Dst = SpecKeyUpdate;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for KeyUpdateMapper {
    type Src = KeyUpdateInner;
    type Dst = KeyUpdate;
}

pub struct SpecKeyUpdateCombinator(SpecKeyUpdateCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateCombinator {
    type SpecResult = SpecKeyUpdate;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyUpdateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyUpdateCombinatorAlias = Mapped<SpecKeyUpdateRequestCombinator, KeyUpdateMapper>;

pub struct KeyUpdateCombinator(KeyUpdateCombinatorAlias);

impl View for KeyUpdateCombinator {
    type V = SpecKeyUpdateCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyUpdateCombinator {
    type Result = KeyUpdate;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyUpdateCombinatorAlias = Mapped<KeyUpdateRequestCombinator, KeyUpdateMapper>;


pub closed spec fn spec_key_update() -> SpecKeyUpdateCombinator {
    SpecKeyUpdateCombinator(
    Mapped {
        inner: spec_key_update_request(),
        mapper: KeyUpdateMapper::spec_new(),
    })
}

                
pub fn key_update() -> (o: KeyUpdateCombinator)
    ensures o@ == spec_key_update(),
{
    KeyUpdateCombinator(
    Mapped {
        inner: key_update_request(),
        mapper: KeyUpdateMapper::new(),
    })
}

                

pub enum SpecHandshakeMsg {
    ClientHello(SpecClientHello),
    ServerHello(SpecShOrHrr),
    NewSessionTicket(SpecNewSessionTicket),
    EndOfEarlyData(SpecEmpty),
    EncryptedExtensions(SpecEncryptedExtensions),
    Certificate(SpecCertificate),
    CertificateRequest(SpecCertificateRequest),
    CertificateVerify(SpecCertificateVerify),
    Finished(SpecFinished),
    KeyUpdate(SpecKeyUpdate),
}

pub type SpecHandshakeMsgInner = Either<SpecClientHello, Either<SpecShOrHrr, Either<SpecNewSessionTicket, Either<SpecEmpty, Either<SpecEncryptedExtensions, Either<SpecCertificate, Either<SpecCertificateRequest, Either<SpecCertificateVerify, Either<SpecFinished, SpecKeyUpdate>>>>>>>>>;



impl SpecFrom<SpecHandshakeMsg> for SpecHandshakeMsgInner {
    open spec fn spec_from(m: SpecHandshakeMsg) -> SpecHandshakeMsgInner {
        match m {
            SpecHandshakeMsg::ClientHello(m) => Either::Left(m),
            SpecHandshakeMsg::ServerHello(m) => Either::Right(Either::Left(m)),
            SpecHandshakeMsg::NewSessionTicket(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecHandshakeMsg::EndOfEarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecHandshakeMsg::EncryptedExtensions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecHandshakeMsg::Certificate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecHandshakeMsg::CertificateRequest(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecHandshakeMsg::CertificateVerify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecHandshakeMsg::Finished(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecHandshakeMsg::KeyUpdate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }

}

impl SpecFrom<SpecHandshakeMsgInner> for SpecHandshakeMsg {
    open spec fn spec_from(m: SpecHandshakeMsgInner) -> SpecHandshakeMsg {
        match m {
            Either::Left(m) => SpecHandshakeMsg::ClientHello(m),
            Either::Right(Either::Left(m)) => SpecHandshakeMsg::ServerHello(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecHandshakeMsg::NewSessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecHandshakeMsg::EndOfEarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecHandshakeMsg::EncryptedExtensions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecHandshakeMsg::Certificate(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecHandshakeMsg::CertificateRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecHandshakeMsg::CertificateVerify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecHandshakeMsg::Finished(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => SpecHandshakeMsg::KeyUpdate(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandshakeMsg<'a> {
    ClientHello(ClientHello<'a>),
    ServerHello(ShOrHrr<'a>),
    NewSessionTicket(NewSessionTicket<'a>),
    EndOfEarlyData(Empty<'a>),
    EncryptedExtensions(EncryptedExtensions<'a>),
    Certificate(Certificate<'a>),
    CertificateRequest(CertificateRequest<'a>),
    CertificateVerify(CertificateVerify<'a>),
    Finished(Finished<'a>),
    KeyUpdate(KeyUpdate),
}

pub type HandshakeMsgInner<'a> = Either<ClientHello<'a>, Either<ShOrHrr<'a>, Either<NewSessionTicket<'a>, Either<Empty<'a>, Either<EncryptedExtensions<'a>, Either<Certificate<'a>, Either<CertificateRequest<'a>, Either<CertificateVerify<'a>, Either<Finished<'a>, KeyUpdate>>>>>>>>>;


impl<'a> View for HandshakeMsg<'a> {
    type V = SpecHandshakeMsg;
    open spec fn view(&self) -> Self::V {
        match self {
            HandshakeMsg::ClientHello(m) => SpecHandshakeMsg::ClientHello(m@),
            HandshakeMsg::ServerHello(m) => SpecHandshakeMsg::ServerHello(m@),
            HandshakeMsg::NewSessionTicket(m) => SpecHandshakeMsg::NewSessionTicket(m@),
            HandshakeMsg::EndOfEarlyData(m) => SpecHandshakeMsg::EndOfEarlyData(m@),
            HandshakeMsg::EncryptedExtensions(m) => SpecHandshakeMsg::EncryptedExtensions(m@),
            HandshakeMsg::Certificate(m) => SpecHandshakeMsg::Certificate(m@),
            HandshakeMsg::CertificateRequest(m) => SpecHandshakeMsg::CertificateRequest(m@),
            HandshakeMsg::CertificateVerify(m) => SpecHandshakeMsg::CertificateVerify(m@),
            HandshakeMsg::Finished(m) => SpecHandshakeMsg::Finished(m@),
            HandshakeMsg::KeyUpdate(m) => SpecHandshakeMsg::KeyUpdate(m@),
        }
    }
}


impl<'a> From<HandshakeMsg<'a>> for HandshakeMsgInner<'a> {
    fn ex_from(m: HandshakeMsg<'a>) -> HandshakeMsgInner<'a> {
        match m {
            HandshakeMsg::ClientHello(m) => Either::Left(m),
            HandshakeMsg::ServerHello(m) => Either::Right(Either::Left(m)),
            HandshakeMsg::NewSessionTicket(m) => Either::Right(Either::Right(Either::Left(m))),
            HandshakeMsg::EndOfEarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            HandshakeMsg::EncryptedExtensions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            HandshakeMsg::Certificate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            HandshakeMsg::CertificateRequest(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            HandshakeMsg::CertificateVerify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            HandshakeMsg::Finished(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            HandshakeMsg::KeyUpdate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }

}

impl<'a> From<HandshakeMsgInner<'a>> for HandshakeMsg<'a> {
    fn ex_from(m: HandshakeMsgInner<'a>) -> HandshakeMsg<'a> {
        match m {
            Either::Left(m) => HandshakeMsg::ClientHello(m),
            Either::Right(Either::Left(m)) => HandshakeMsg::ServerHello(m),
            Either::Right(Either::Right(Either::Left(m))) => HandshakeMsg::NewSessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => HandshakeMsg::EndOfEarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => HandshakeMsg::EncryptedExtensions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => HandshakeMsg::Certificate(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => HandshakeMsg::CertificateRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => HandshakeMsg::CertificateVerify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => HandshakeMsg::Finished(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => HandshakeMsg::KeyUpdate(m),
        }
    }
    
}


pub struct HandshakeMsgMapper<'a>(PhantomData<&'a ()>);
impl<'a> HandshakeMsgMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HandshakeMsgMapper(PhantomData)
    }
    pub fn new() -> Self {
        HandshakeMsgMapper(PhantomData)
    }
}
impl View for HandshakeMsgMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMsgMapper<'_> {
    type Src = SpecHandshakeMsgInner;
    type Dst = SpecHandshakeMsg;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HandshakeMsgMapper<'a> {
    type Src = HandshakeMsgInner<'a>;
    type Dst = HandshakeMsg<'a>;
}


pub struct SpecHandshakeMsgCombinator(SpecHandshakeMsgCombinatorAlias);

impl SpecCombinator for SpecHandshakeMsgCombinator {
    type SpecResult = SpecHandshakeMsg;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeMsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeMsgCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeMsgCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecClientHelloCombinator>, OrdChoice<Cond<SpecShOrHrrCombinator>, OrdChoice<Cond<SpecNewSessionTicketCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEncryptedExtensionsCombinator>, OrdChoice<Cond<SpecCertificateCombinator>, OrdChoice<Cond<SpecCertificateRequestCombinator>, OrdChoice<Cond<SpecCertificateVerifyCombinator>, OrdChoice<Cond<SpecFinishedCombinator>, Cond<SpecKeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper<'static>>>;

pub struct HandshakeMsgCombinator<'a>(HandshakeMsgCombinatorAlias<'a>);

impl<'a> View for HandshakeMsgCombinator<'a> {
    type V = SpecHandshakeMsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeMsgCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HandshakeMsgCombinator<'a> {
    type Result = HandshakeMsg<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HandshakeMsgCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<ClientHelloCombinator<'a>>, OrdChoice<Cond<ShOrHrrCombinator<'a>>, OrdChoice<Cond<NewSessionTicketCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EncryptedExtensionsCombinator<'a>>, OrdChoice<Cond<CertificateCombinator<'a>>, OrdChoice<Cond<CertificateRequestCombinator<'a>>, OrdChoice<Cond<CertificateVerifyCombinator<'a>>, OrdChoice<Cond<FinishedCombinator>, Cond<KeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper<'a>>>;


pub closed spec fn spec_handshake_msg(length: u24, msg_type: SpecHandshakeType) -> SpecHandshakeMsgCombinator {
    SpecHandshakeMsgCombinator(AndThen(Bytes(length.spec_into()), Mapped { inner: OrdChoice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: spec_client_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: spec_sh_or_hrr() }, OrdChoice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: spec_new_session_ticket() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: spec_empty() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: spec_encrypted_extensions() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Certificate, inner: spec_certificate() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: spec_certificate_request() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: spec_certificate_verify() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Finished, inner: spec_finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: spec_key_update() }))))))))), mapper: HandshakeMsgMapper::spec_new() }))
}

                
pub fn handshake_msg<'a>(length: u24, msg_type: HandshakeType) -> (o: HandshakeMsgCombinator<'a>)
    ensures o@ == spec_handshake_msg(length@, msg_type@),
{
    HandshakeMsgCombinator(AndThen(Bytes(length.ex_into()), Mapped { inner: OrdChoice::new(Cond { cond: msg_type == HandshakeType::ClientHello, inner: client_hello() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::ServerHello, inner: sh_or_hrr() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: new_session_ticket() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: empty() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: encrypted_extensions() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::Certificate, inner: certificate() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: certificate_request() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: certificate_verify() }, OrdChoice::new(Cond { cond: msg_type == HandshakeType::Finished, inner: finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: key_update() }))))))))), mapper: HandshakeMsgMapper::new() }))
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContentType {
    Invalid = 0,
ChangeCipherSpec = 20,
Alert = 21,
Handshake = 22,
ApplicationData = 23
}
pub type SpecContentType = ContentType;

pub type ContentTypeInner = u8;

impl View for ContentType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ContentTypeInner> for ContentType {
    type Error = ();

    open spec fn spec_try_from(v: ContentTypeInner) -> Result<ContentType, ()> {
        match v {
            0u8 => Ok(ContentType::Invalid),
            20u8 => Ok(ContentType::ChangeCipherSpec),
            21u8 => Ok(ContentType::Alert),
            22u8 => Ok(ContentType::Handshake),
            23u8 => Ok(ContentType::ApplicationData),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<ContentType> for ContentTypeInner {
    type Error = ();

    open spec fn spec_try_from(v: ContentType) -> Result<ContentTypeInner, ()> {
        match v {
            ContentType::Invalid => Ok(0u8),
            ContentType::ChangeCipherSpec => Ok(20u8),
            ContentType::Alert => Ok(21u8),
            ContentType::Handshake => Ok(22u8),
            ContentType::ApplicationData => Ok(23u8),
        }
    }
}

impl TryFrom<ContentTypeInner> for ContentType {
    type Error = ();

    fn ex_try_from(v: ContentTypeInner) -> Result<ContentType, ()> {
        match v {
            0u8 => Ok(ContentType::Invalid),
            20u8 => Ok(ContentType::ChangeCipherSpec),
            21u8 => Ok(ContentType::Alert),
            22u8 => Ok(ContentType::Handshake),
            23u8 => Ok(ContentType::ApplicationData),
            _ => Err(()),
        }
    }
}

impl TryFrom<ContentType> for ContentTypeInner {
    type Error = ();

    fn ex_try_from(v: ContentType) -> Result<ContentTypeInner, ()> {
        match v {
            ContentType::Invalid => Ok(0u8),
            ContentType::ChangeCipherSpec => Ok(20u8),
            ContentType::Alert => Ok(21u8),
            ContentType::Handshake => Ok(22u8),
            ContentType::ApplicationData => Ok(23u8),
        }
    }
}

pub struct ContentTypeMapper;

impl View for ContentTypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for ContentTypeMapper {
    type Src = ContentTypeInner;
    type Dst = ContentType;

    proof fn spec_iso(s: Self::Src) { }

    proof fn spec_iso_rev(s: Self::Dst) { }
}

impl TryFromInto for ContentTypeMapper {
    type Src = ContentTypeInner;
    type Dst = ContentType;
}


pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type SpecResult = SpecContentType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecContentTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;

pub struct ContentTypeCombinator(ContentTypeCombinatorAlias);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecContentTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ContentTypeCombinator {
    type Result = ContentType;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;


pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}

                
pub fn content_type() -> (o: ContentTypeCombinator)
    ensures o@ == spec_content_type(),
{
    ContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}

                

pub struct SpecTlsPlaintext {
    pub content_type: SpecContentType,
    pub legacy_record_version: SpecProtocolVersion,
    pub fragment: SpecOpaque0Ffff,
}

pub type SpecTlsPlaintextInner = (SpecContentType, (SpecProtocolVersion, SpecOpaque0Ffff));
impl SpecFrom<SpecTlsPlaintext> for SpecTlsPlaintextInner {
    open spec fn spec_from(m: SpecTlsPlaintext) -> SpecTlsPlaintextInner {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl SpecFrom<SpecTlsPlaintextInner> for SpecTlsPlaintext {
    open spec fn spec_from(m: SpecTlsPlaintextInner) -> SpecTlsPlaintext {
        let (content_type, (legacy_record_version, fragment)) = m;
        SpecTlsPlaintext { content_type, legacy_record_version, fragment }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TlsPlaintext<'a> {
    pub content_type: ContentType,
    pub legacy_record_version: ProtocolVersion,
    pub fragment: Opaque0Ffff<'a>,
}

impl View for TlsPlaintext<'_> {
    type V = SpecTlsPlaintext;

    open spec fn view(&self) -> Self::V {
        SpecTlsPlaintext {
            content_type: self.content_type@,
            legacy_record_version: self.legacy_record_version@,
            fragment: self.fragment@,
        }
    }
}
pub type TlsPlaintextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
impl<'a> From<TlsPlaintext<'a>> for TlsPlaintextInner<'a> {
    fn ex_from(m: TlsPlaintext) -> TlsPlaintextInner {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl<'a> From<TlsPlaintextInner<'a>> for TlsPlaintext<'a> {
    fn ex_from(m: TlsPlaintextInner) -> TlsPlaintext {
        let (content_type, (legacy_record_version, fragment)) = m;
        TlsPlaintext { content_type, legacy_record_version, fragment }
    }
}

pub struct TlsPlaintextMapper<'a>(PhantomData<&'a ()>);
impl<'a> TlsPlaintextMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TlsPlaintextMapper(PhantomData)
    }
    pub fn new() -> Self {
        TlsPlaintextMapper(PhantomData)
    }
}
impl View for TlsPlaintextMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsPlaintextMapper<'_> {
    type Src = SpecTlsPlaintextInner;
    type Dst = SpecTlsPlaintext;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TlsPlaintextMapper<'a> {
    type Src = TlsPlaintextInner<'a>;
    type Dst = TlsPlaintext<'a>;
}

pub struct SpecTlsPlaintextCombinator(SpecTlsPlaintextCombinatorAlias);

impl SpecCombinator for SpecTlsPlaintextCombinator {
    type SpecResult = SpecTlsPlaintext;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTlsPlaintextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsPlaintextCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecTlsPlaintextCombinatorAlias = Mapped<(SpecContentTypeCombinator, (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator)), TlsPlaintextMapper<'static>>;

pub struct TlsPlaintextCombinator<'a>(TlsPlaintextCombinatorAlias<'a>);

impl<'a> View for TlsPlaintextCombinator<'a> {
    type V = SpecTlsPlaintextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsPlaintextCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TlsPlaintextCombinator<'a> {
    type Result = TlsPlaintext<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TlsPlaintextCombinatorAlias<'a> = Mapped<(ContentTypeCombinator, (ProtocolVersionCombinator, Opaque0FfffCombinator<'a>)), TlsPlaintextMapper<'a>>;


pub closed spec fn spec_tls_plaintext() -> SpecTlsPlaintextCombinator {
    SpecTlsPlaintextCombinator(
    Mapped {
        inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())),
        mapper: TlsPlaintextMapper::spec_new(),
    })
}

                
pub fn tls_plaintext<'a>() -> (o: TlsPlaintextCombinator<'a>)
    ensures o@ == spec_tls_plaintext(),
{
    TlsPlaintextCombinator(
    Mapped {
        inner: (content_type(), (protocol_version(), opaque_0_ffff())),
        mapper: TlsPlaintextMapper::new(),
    })
}

                
pub type SpecUnknownExtension = SpecOpaque0Ffff;
pub type UnknownExtension<'a> = Opaque0Ffff<'a>;


pub struct SpecUnknownExtensionCombinator(SpecUnknownExtensionCombinatorAlias);

impl SpecCombinator for SpecUnknownExtensionCombinator {
    type SpecResult = SpecUnknownExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUnknownExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUnknownExtensionCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct UnknownExtensionCombinator<'a>(UnknownExtensionCombinatorAlias<'a>);

impl<'a> View for UnknownExtensionCombinator<'a> {
    type V = SpecUnknownExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UnknownExtensionCombinator<'a> {
    type Result = UnknownExtension<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UnknownExtensionCombinatorAlias<'a> = Opaque0FfffCombinator<'a>;


pub closed spec fn spec_unknown_extension() -> SpecUnknownExtensionCombinator {
    SpecUnknownExtensionCombinator(spec_opaque_0_ffff())
}

                
pub fn unknown_extension<'a>() -> (o: UnknownExtensionCombinator<'a>)
    ensures o@ == spec_unknown_extension(),
{
    UnknownExtensionCombinator(opaque_0_ffff())
}

                

pub struct SpecTlsCiphertext {
    pub opaque_type: SpecContentType,
    pub version: SpecProtocolVersion,
    pub encrypted_record: SpecOpaque0Ffff,
}

pub type SpecTlsCiphertextInner = (SpecContentType, (SpecProtocolVersion, SpecOpaque0Ffff));
impl SpecFrom<SpecTlsCiphertext> for SpecTlsCiphertextInner {
    open spec fn spec_from(m: SpecTlsCiphertext) -> SpecTlsCiphertextInner {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl SpecFrom<SpecTlsCiphertextInner> for SpecTlsCiphertext {
    open spec fn spec_from(m: SpecTlsCiphertextInner) -> SpecTlsCiphertext {
        let (opaque_type, (version, encrypted_record)) = m;
        SpecTlsCiphertext { opaque_type, version, encrypted_record }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TlsCiphertext<'a> {
    pub opaque_type: ContentType,
    pub version: ProtocolVersion,
    pub encrypted_record: Opaque0Ffff<'a>,
}

impl View for TlsCiphertext<'_> {
    type V = SpecTlsCiphertext;

    open spec fn view(&self) -> Self::V {
        SpecTlsCiphertext {
            opaque_type: self.opaque_type@,
            version: self.version@,
            encrypted_record: self.encrypted_record@,
        }
    }
}
pub type TlsCiphertextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
impl<'a> From<TlsCiphertext<'a>> for TlsCiphertextInner<'a> {
    fn ex_from(m: TlsCiphertext) -> TlsCiphertextInner {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl<'a> From<TlsCiphertextInner<'a>> for TlsCiphertext<'a> {
    fn ex_from(m: TlsCiphertextInner) -> TlsCiphertext {
        let (opaque_type, (version, encrypted_record)) = m;
        TlsCiphertext { opaque_type, version, encrypted_record }
    }
}

pub struct TlsCiphertextMapper<'a>(PhantomData<&'a ()>);
impl<'a> TlsCiphertextMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TlsCiphertextMapper(PhantomData)
    }
    pub fn new() -> Self {
        TlsCiphertextMapper(PhantomData)
    }
}
impl View for TlsCiphertextMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsCiphertextMapper<'_> {
    type Src = SpecTlsCiphertextInner;
    type Dst = SpecTlsCiphertext;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for TlsCiphertextMapper<'a> {
    type Src = TlsCiphertextInner<'a>;
    type Dst = TlsCiphertext<'a>;
}

pub struct SpecTlsCiphertextCombinator(SpecTlsCiphertextCombinatorAlias);

impl SpecCombinator for SpecTlsCiphertextCombinator {
    type SpecResult = SpecTlsCiphertext;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTlsCiphertextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsCiphertextCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecTlsCiphertextCombinatorAlias = Mapped<(SpecContentTypeCombinator, (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator)), TlsCiphertextMapper<'static>>;

pub struct TlsCiphertextCombinator<'a>(TlsCiphertextCombinatorAlias<'a>);

impl<'a> View for TlsCiphertextCombinator<'a> {
    type V = SpecTlsCiphertextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsCiphertextCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for TlsCiphertextCombinator<'a> {
    type Result = TlsCiphertext<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type TlsCiphertextCombinatorAlias<'a> = Mapped<(ContentTypeCombinator, (ProtocolVersionCombinator, Opaque0FfffCombinator<'a>)), TlsCiphertextMapper<'a>>;


pub closed spec fn spec_tls_ciphertext() -> SpecTlsCiphertextCombinator {
    SpecTlsCiphertextCombinator(
    Mapped {
        inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())),
        mapper: TlsCiphertextMapper::spec_new(),
    })
}

                
pub fn tls_ciphertext<'a>() -> (o: TlsCiphertextCombinator<'a>)
    ensures o@ == spec_tls_ciphertext(),
{
    TlsCiphertextCombinator(
    Mapped {
        inner: (content_type(), (protocol_version(), opaque_0_ffff())),
        mapper: TlsCiphertextMapper::new(),
    })
}

                
pub type SpecKeyExchangeData = SpecOpaque1Ffff;
pub type KeyExchangeData<'a> = Opaque1Ffff<'a>;


pub struct SpecKeyExchangeDataCombinator(SpecKeyExchangeDataCombinatorAlias);

impl SpecCombinator for SpecKeyExchangeDataCombinator {
    type SpecResult = SpecKeyExchangeData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyExchangeDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyExchangeDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyExchangeDataCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct KeyExchangeDataCombinator<'a>(KeyExchangeDataCombinatorAlias<'a>);

impl<'a> View for KeyExchangeDataCombinator<'a> {
    type V = SpecKeyExchangeDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyExchangeDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyExchangeDataCombinator<'a> {
    type Result = KeyExchangeData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type KeyExchangeDataCombinatorAlias<'a> = Opaque1FfffCombinator<'a>;


pub closed spec fn spec_key_exchange_data() -> SpecKeyExchangeDataCombinator {
    SpecKeyExchangeDataCombinator(spec_opaque_1_ffff())
}

                
pub fn key_exchange_data<'a>() -> (o: KeyExchangeDataCombinator<'a>)
    ensures o@ == spec_key_exchange_data(),
{
    KeyExchangeDataCombinator(opaque_1_ffff())
}

                

pub struct SpecSeverDhParams {
    pub dh_p: SpecOpaque1Ffff,
    pub dh_g: SpecOpaque1Ffff,
    pub dh_ys: SpecOpaque1Ffff,
}

pub type SpecSeverDhParamsInner = (SpecOpaque1Ffff, (SpecOpaque1Ffff, SpecOpaque1Ffff));
impl SpecFrom<SpecSeverDhParams> for SpecSeverDhParamsInner {
    open spec fn spec_from(m: SpecSeverDhParams) -> SpecSeverDhParamsInner {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl SpecFrom<SpecSeverDhParamsInner> for SpecSeverDhParams {
    open spec fn spec_from(m: SpecSeverDhParamsInner) -> SpecSeverDhParams {
        let (dh_p, (dh_g, dh_ys)) = m;
        SpecSeverDhParams { dh_p, dh_g, dh_ys }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SeverDhParams<'a> {
    pub dh_p: Opaque1Ffff<'a>,
    pub dh_g: Opaque1Ffff<'a>,
    pub dh_ys: Opaque1Ffff<'a>,
}

impl View for SeverDhParams<'_> {
    type V = SpecSeverDhParams;

    open spec fn view(&self) -> Self::V {
        SpecSeverDhParams {
            dh_p: self.dh_p@,
            dh_g: self.dh_g@,
            dh_ys: self.dh_ys@,
        }
    }
}
pub type SeverDhParamsInner<'a> = (Opaque1Ffff<'a>, (Opaque1Ffff<'a>, Opaque1Ffff<'a>));
impl<'a> From<SeverDhParams<'a>> for SeverDhParamsInner<'a> {
    fn ex_from(m: SeverDhParams) -> SeverDhParamsInner {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl<'a> From<SeverDhParamsInner<'a>> for SeverDhParams<'a> {
    fn ex_from(m: SeverDhParamsInner) -> SeverDhParams {
        let (dh_p, (dh_g, dh_ys)) = m;
        SeverDhParams { dh_p, dh_g, dh_ys }
    }
}

pub struct SeverDhParamsMapper<'a>(PhantomData<&'a ()>);
impl<'a> SeverDhParamsMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        SeverDhParamsMapper(PhantomData)
    }
    pub fn new() -> Self {
        SeverDhParamsMapper(PhantomData)
    }
}
impl View for SeverDhParamsMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverDhParamsMapper<'_> {
    type Src = SpecSeverDhParamsInner;
    type Dst = SpecSeverDhParams;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for SeverDhParamsMapper<'a> {
    type Src = SeverDhParamsInner<'a>;
    type Dst = SeverDhParams<'a>;
}

pub struct SpecSeverDhParamsCombinator(SpecSeverDhParamsCombinatorAlias);

impl SpecCombinator for SpecSeverDhParamsCombinator {
    type SpecResult = SpecSeverDhParams;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverDhParamsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverDhParamsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverDhParamsCombinatorAlias = Mapped<(SpecOpaque1FfffCombinator, (SpecOpaque1FfffCombinator, SpecOpaque1FfffCombinator)), SeverDhParamsMapper<'static>>;

pub struct SeverDhParamsCombinator<'a>(SeverDhParamsCombinatorAlias<'a>);

impl<'a> View for SeverDhParamsCombinator<'a> {
    type V = SpecSeverDhParamsCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverDhParamsCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SeverDhParamsCombinator<'a> {
    type Result = SeverDhParams<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type SeverDhParamsCombinatorAlias<'a> = Mapped<(Opaque1FfffCombinator<'a>, (Opaque1FfffCombinator<'a>, Opaque1FfffCombinator<'a>)), SeverDhParamsMapper<'a>>;


pub closed spec fn spec_sever_dh_params() -> SpecSeverDhParamsCombinator {
    SpecSeverDhParamsCombinator(
    Mapped {
        inner: (spec_opaque_1_ffff(), (spec_opaque_1_ffff(), spec_opaque_1_ffff())),
        mapper: SeverDhParamsMapper::spec_new(),
    })
}

                
pub fn sever_dh_params<'a>() -> (o: SeverDhParamsCombinator<'a>)
    ensures o@ == spec_sever_dh_params(),
{
    SeverDhParamsCombinator(
    Mapped {
        inner: (opaque_1_ffff(), (opaque_1_ffff(), opaque_1_ffff())),
        mapper: SeverDhParamsMapper::new(),
    })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum HandshakeType {
    ClientHello = 1,
ServerHello = 2,
NewSessionTicket = 4,
EndOfEarlyData = 5,
EncryptedExtensions = 8,
Certificate = 11,
CertificateRequest = 13,
CertificateVerify = 15,
Finished = 20,
KeyUpdate = 24
}
pub type SpecHandshakeType = HandshakeType;

pub type HandshakeTypeInner = u8;

impl View for HandshakeType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<HandshakeTypeInner> for HandshakeType {
    type Error = ();

    open spec fn spec_try_from(v: HandshakeTypeInner) -> Result<HandshakeType, ()> {
        match v {
            1u8 => Ok(HandshakeType::ClientHello),
            2u8 => Ok(HandshakeType::ServerHello),
            4u8 => Ok(HandshakeType::NewSessionTicket),
            5u8 => Ok(HandshakeType::EndOfEarlyData),
            8u8 => Ok(HandshakeType::EncryptedExtensions),
            11u8 => Ok(HandshakeType::Certificate),
            13u8 => Ok(HandshakeType::CertificateRequest),
            15u8 => Ok(HandshakeType::CertificateVerify),
            20u8 => Ok(HandshakeType::Finished),
            24u8 => Ok(HandshakeType::KeyUpdate),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<HandshakeType> for HandshakeTypeInner {
    type Error = ();

    open spec fn spec_try_from(v: HandshakeType) -> Result<HandshakeTypeInner, ()> {
        match v {
            HandshakeType::ClientHello => Ok(1u8),
            HandshakeType::ServerHello => Ok(2u8),
            HandshakeType::NewSessionTicket => Ok(4u8),
            HandshakeType::EndOfEarlyData => Ok(5u8),
            HandshakeType::EncryptedExtensions => Ok(8u8),
            HandshakeType::Certificate => Ok(11u8),
            HandshakeType::CertificateRequest => Ok(13u8),
            HandshakeType::CertificateVerify => Ok(15u8),
            HandshakeType::Finished => Ok(20u8),
            HandshakeType::KeyUpdate => Ok(24u8),
        }
    }
}

impl TryFrom<HandshakeTypeInner> for HandshakeType {
    type Error = ();

    fn ex_try_from(v: HandshakeTypeInner) -> Result<HandshakeType, ()> {
        match v {
            1u8 => Ok(HandshakeType::ClientHello),
            2u8 => Ok(HandshakeType::ServerHello),
            4u8 => Ok(HandshakeType::NewSessionTicket),
            5u8 => Ok(HandshakeType::EndOfEarlyData),
            8u8 => Ok(HandshakeType::EncryptedExtensions),
            11u8 => Ok(HandshakeType::Certificate),
            13u8 => Ok(HandshakeType::CertificateRequest),
            15u8 => Ok(HandshakeType::CertificateVerify),
            20u8 => Ok(HandshakeType::Finished),
            24u8 => Ok(HandshakeType::KeyUpdate),
            _ => Err(()),
        }
    }
}

impl TryFrom<HandshakeType> for HandshakeTypeInner {
    type Error = ();

    fn ex_try_from(v: HandshakeType) -> Result<HandshakeTypeInner, ()> {
        match v {
            HandshakeType::ClientHello => Ok(1u8),
            HandshakeType::ServerHello => Ok(2u8),
            HandshakeType::NewSessionTicket => Ok(4u8),
            HandshakeType::EndOfEarlyData => Ok(5u8),
            HandshakeType::EncryptedExtensions => Ok(8u8),
            HandshakeType::Certificate => Ok(11u8),
            HandshakeType::CertificateRequest => Ok(13u8),
            HandshakeType::CertificateVerify => Ok(15u8),
            HandshakeType::Finished => Ok(20u8),
            HandshakeType::KeyUpdate => Ok(24u8),
        }
    }
}

pub struct HandshakeTypeMapper;

impl View for HandshakeTypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for HandshakeTypeMapper {
    type Src = HandshakeTypeInner;
    type Dst = HandshakeType;

    proof fn spec_iso(s: Self::Src) { }

    proof fn spec_iso_rev(s: Self::Dst) { }
}

impl TryFromInto for HandshakeTypeMapper {
    type Src = HandshakeTypeInner;
    type Dst = HandshakeType;
}


pub struct SpecHandshakeTypeCombinator(SpecHandshakeTypeCombinatorAlias);

impl SpecCombinator for SpecHandshakeTypeCombinator {
    type SpecResult = SpecHandshakeType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeTypeCombinatorAlias = TryMap<U8, HandshakeTypeMapper>;

pub struct HandshakeTypeCombinator(HandshakeTypeCombinatorAlias);

impl View for HandshakeTypeCombinator {
    type V = SpecHandshakeTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeTypeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HandshakeTypeCombinator {
    type Result = HandshakeType;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HandshakeTypeCombinatorAlias = TryMap<U8, HandshakeTypeMapper>;


pub closed spec fn spec_handshake_type() -> SpecHandshakeTypeCombinator {
    SpecHandshakeTypeCombinator(TryMap { inner: U8, mapper: HandshakeTypeMapper })
}

                
pub fn handshake_type() -> (o: HandshakeTypeCombinator)
    ensures o@ == spec_handshake_type(),
{
    HandshakeTypeCombinator(TryMap { inner: U8, mapper: HandshakeTypeMapper })
}

                

pub struct SpecHandshake {
    pub msg_type: SpecHandshakeType,
    pub length: u24,
    pub msg: SpecHandshakeMsg,
}

pub type SpecHandshakeInner = ((SpecHandshakeType, u24), SpecHandshakeMsg);
impl SpecFrom<SpecHandshake> for SpecHandshakeInner {
    open spec fn spec_from(m: SpecHandshake) -> SpecHandshakeInner {
        ((m.msg_type, m.length), m.msg)
    }
}
impl SpecFrom<SpecHandshakeInner> for SpecHandshake {
    open spec fn spec_from(m: SpecHandshakeInner) -> SpecHandshake {
        let ((msg_type, length), msg) = m;
        SpecHandshake { msg_type, length, msg }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Handshake<'a> {
    pub msg_type: HandshakeType,
    pub length: u24,
    pub msg: HandshakeMsg<'a>,
}

impl View for Handshake<'_> {
    type V = SpecHandshake;

    open spec fn view(&self) -> Self::V {
        SpecHandshake {
            msg_type: self.msg_type@,
            length: self.length@,
            msg: self.msg@,
        }
    }
}
pub type HandshakeInner<'a> = ((HandshakeType, u24), HandshakeMsg<'a>);
impl<'a> From<Handshake<'a>> for HandshakeInner<'a> {
    fn ex_from(m: Handshake) -> HandshakeInner {
        ((m.msg_type, m.length), m.msg)
    }
}
impl<'a> From<HandshakeInner<'a>> for Handshake<'a> {
    fn ex_from(m: HandshakeInner) -> Handshake {
        let ((msg_type, length), msg) = m;
        Handshake { msg_type, length, msg }
    }
}

pub struct HandshakeMapper<'a>(PhantomData<&'a ()>);
impl<'a> HandshakeMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        HandshakeMapper(PhantomData)
    }
    pub fn new() -> Self {
        HandshakeMapper(PhantomData)
    }
}
impl View for HandshakeMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMapper<'_> {
    type Src = SpecHandshakeInner;
    type Dst = SpecHandshake;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for HandshakeMapper<'a> {
    type Src = HandshakeInner<'a>;
    type Dst = Handshake<'a>;
}

pub struct SpecHandshakeCombinator(SpecHandshakeCombinatorAlias);

impl SpecCombinator for SpecHandshakeCombinator {
    type SpecResult = SpecHandshake;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeCombinatorAlias = Mapped<SpecDepend<SpecDepend<SpecHandshakeTypeCombinator, U24Be>, SpecHandshakeMsgCombinator>, HandshakeMapper<'static>>;

pub struct HandshakeCombinator<'a>(HandshakeCombinatorAlias<'a>);

impl<'a> View for HandshakeCombinator<'a> {
    type V = SpecHandshakeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HandshakeCombinator<'a> {
    type Result = Handshake<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HandshakeCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Depend<&'a [u8], Vec<u8>, HandshakeTypeCombinator, U24Be, HandshakeCont1<'a>>, HandshakeMsgCombinator<'a>, HandshakeCont0<'a>>, HandshakeMapper<'a>>;


pub closed spec fn spec_handshake() -> SpecHandshakeCombinator {
    SpecHandshakeCombinator(
    Mapped {
        inner: SpecDepend { fst: SpecDepend { fst: spec_handshake_type(), snd: |deps| spec_handshake_cont1(deps) }, snd: |deps| spec_handshake_cont0(deps) },
        mapper: HandshakeMapper::spec_new(),
    })
}

pub open spec fn spec_handshake_cont1(deps: SpecHandshakeType) -> U24Be {
    let msg_type = deps;
    U24Be
}
pub open spec fn spec_handshake_cont0(deps: (SpecHandshakeType, u24)) -> SpecHandshakeMsgCombinator {
    let (msg_type, length) = deps;
    spec_handshake_msg(length, msg_type)
}
                
pub fn handshake<'a>() -> (o: HandshakeCombinator<'a>)
    ensures o@ == spec_handshake(),
{
    HandshakeCombinator(
    Mapped {
        inner: Depend { fst: Depend { fst: handshake_type(), snd: HandshakeCont1::new(), spec_snd: Ghost(|deps| spec_handshake_cont1(deps)) }, snd: HandshakeCont0::new(), spec_snd: Ghost(|deps| spec_handshake_cont0(deps)) },
        mapper: HandshakeMapper::new(),
    })
}

pub struct HandshakeCont1<'a>(PhantomData<&'a ()>);
impl<'a> HandshakeCont1<'a> {
    pub fn new() -> Self {
        HandshakeCont1(PhantomData)
    }
}
impl<'a> Continuation<&HandshakeType> for HandshakeCont1<'a> {
    type Output = U24Be;

    open spec fn requires(&self, deps: &HandshakeType) -> bool { true }

    open spec fn ensures(&self, deps: &HandshakeType, o: Self::Output) -> bool {
        o@ == spec_handshake_cont1(deps@)
    }

    fn apply(&self, deps: &HandshakeType) -> Self::Output {
        let msg_type = *deps;
        U24Be
    }
}
pub struct HandshakeCont0<'a>(PhantomData<&'a ()>);
impl<'a> HandshakeCont0<'a> {
    pub fn new() -> Self {
        HandshakeCont0(PhantomData)
    }
}
impl<'a> Continuation<&(HandshakeType, u24)> for HandshakeCont0<'a> {
    type Output = HandshakeMsgCombinator<'a>;

    open spec fn requires(&self, deps: &(HandshakeType, u24)) -> bool { true }

    open spec fn ensures(&self, deps: &(HandshakeType, u24), o: Self::Output) -> bool {
        o@ == spec_handshake_cont0(deps@)
    }

    fn apply(&self, deps: &(HandshakeType, u24)) -> Self::Output {
        let (msg_type, length) = *deps;
        handshake_msg(length, msg_type)
    }
}
                

pub struct SpecUncompressedPointRepresentation32 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}

pub type SpecUncompressedPointRepresentation32Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation32> for SpecUncompressedPointRepresentation32Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation32) -> SpecUncompressedPointRepresentation32Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation32Inner> for SpecUncompressedPointRepresentation32 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation32Inner) -> SpecUncompressedPointRepresentation32 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation32 { legacy_form, x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct UncompressedPointRepresentation32<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}

impl View for UncompressedPointRepresentation32<'_> {
    type V = SpecUncompressedPointRepresentation32;

    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation32 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type UncompressedPointRepresentation32Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl<'a> From<UncompressedPointRepresentation32<'a>> for UncompressedPointRepresentation32Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation32) -> UncompressedPointRepresentation32Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation32Inner<'a>> for UncompressedPointRepresentation32<'a> {
    fn ex_from(m: UncompressedPointRepresentation32Inner) -> UncompressedPointRepresentation32 {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation32 { legacy_form, x, y }
    }
}

pub struct UncompressedPointRepresentation32Mapper<'a>(PhantomData<&'a ()>);
impl<'a> UncompressedPointRepresentation32Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        UncompressedPointRepresentation32Mapper(PhantomData)
    }
    pub fn new() -> Self {
        UncompressedPointRepresentation32Mapper(PhantomData)
    }
}
impl View for UncompressedPointRepresentation32Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation32Mapper<'_> {
    type Src = SpecUncompressedPointRepresentation32Inner;
    type Dst = SpecUncompressedPointRepresentation32;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for UncompressedPointRepresentation32Mapper<'a> {
    type Src = UncompressedPointRepresentation32Inner<'a>;
    type Dst = UncompressedPointRepresentation32<'a>;
}
pub const UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation32Combinator(SpecUncompressedPointRepresentation32CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation32Combinator {
    type SpecResult = SpecUncompressedPointRepresentation32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation32CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<32>, BytesN<32>)), UncompressedPointRepresentation32Mapper<'static>>;

pub struct UncompressedPointRepresentation32Combinator<'a>(UncompressedPointRepresentation32CombinatorAlias<'a>);

impl<'a> View for UncompressedPointRepresentation32Combinator<'a> {
    type V = SpecUncompressedPointRepresentation32Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation32Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UncompressedPointRepresentation32Combinator<'a> {
    type Result = UncompressedPointRepresentation32<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UncompressedPointRepresentation32CombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<32>, BytesN<32>)), UncompressedPointRepresentation32Mapper<'a>>;


pub closed spec fn spec_uncompressed_point_representation32() -> SpecUncompressedPointRepresentation32Combinator {
    SpecUncompressedPointRepresentation32Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)),
        mapper: UncompressedPointRepresentation32Mapper::spec_new(),
    })
}

                
pub fn uncompressed_point_representation32<'a>() -> (o: UncompressedPointRepresentation32Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation32(),
{
    UncompressedPointRepresentation32Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)),
        mapper: UncompressedPointRepresentation32Mapper::new(),
    })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AlertLevel {
    Warning = 1,
Fatal = 2
}
pub type SpecAlertLevel = AlertLevel;

pub type AlertLevelInner = u8;

impl View for AlertLevel {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AlertLevelInner> for AlertLevel {
    type Error = ();

    open spec fn spec_try_from(v: AlertLevelInner) -> Result<AlertLevel, ()> {
        match v {
            1u8 => Ok(AlertLevel::Warning),
            2u8 => Ok(AlertLevel::Fatal),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AlertLevel> for AlertLevelInner {
    type Error = ();

    open spec fn spec_try_from(v: AlertLevel) -> Result<AlertLevelInner, ()> {
        match v {
            AlertLevel::Warning => Ok(1u8),
            AlertLevel::Fatal => Ok(2u8),
        }
    }
}

impl TryFrom<AlertLevelInner> for AlertLevel {
    type Error = ();

    fn ex_try_from(v: AlertLevelInner) -> Result<AlertLevel, ()> {
        match v {
            1u8 => Ok(AlertLevel::Warning),
            2u8 => Ok(AlertLevel::Fatal),
            _ => Err(()),
        }
    }
}

impl TryFrom<AlertLevel> for AlertLevelInner {
    type Error = ();

    fn ex_try_from(v: AlertLevel) -> Result<AlertLevelInner, ()> {
        match v {
            AlertLevel::Warning => Ok(1u8),
            AlertLevel::Fatal => Ok(2u8),
        }
    }
}

pub struct AlertLevelMapper;

impl View for AlertLevelMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for AlertLevelMapper {
    type Src = AlertLevelInner;
    type Dst = AlertLevel;

    proof fn spec_iso(s: Self::Src) { }

    proof fn spec_iso_rev(s: Self::Dst) { }
}

impl TryFromInto for AlertLevelMapper {
    type Src = AlertLevelInner;
    type Dst = AlertLevel;
}


pub struct SpecAlertLevelCombinator(SpecAlertLevelCombinatorAlias);

impl SpecCombinator for SpecAlertLevelCombinator {
    type SpecResult = SpecAlertLevel;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertLevelCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertLevelCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;

pub struct AlertLevelCombinator(AlertLevelCombinatorAlias);

impl View for AlertLevelCombinator {
    type V = SpecAlertLevelCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertLevelCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for AlertLevelCombinator {
    type Result = AlertLevel;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type AlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;


pub closed spec fn spec_alert_level() -> SpecAlertLevelCombinator {
    SpecAlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}

                
pub fn alert_level() -> (o: AlertLevelCombinator)
    ensures o@ == spec_alert_level(),
{
    AlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}

                

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AlertDescription {
    CloseNotify = 0,
UnexpectedMessage = 10,
BadRecordMac = 20,
RecordOverflow = 22,
HandshakeFailure = 40,
BadCertificate = 42,
UnsupportedCertificate = 43,
CertificateRevoked = 44,
CertificateExpired = 45,
CertificateUnknown = 46,
IllegalParameter = 47,
UnknownCA = 48,
AccessDenied = 49,
DecodeError = 50,
DecryptError = 51,
ProtocolVersion = 70,
InsufficientSecurity = 71,
InternalError = 80,
InappropriateFallback = 86,
UserCanceled = 90,
MissingExtension = 109,
UnsupportedExtension = 110,
UnrecognizedName = 112,
BadCertificateStatusResponse = 113,
UnknownPSKIdentity = 115,
CertificateRequired = 116,
NoApplicationProtocol = 120
}
pub type SpecAlertDescription = AlertDescription;

pub type AlertDescriptionInner = u8;

impl View for AlertDescription {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AlertDescriptionInner> for AlertDescription {
    type Error = ();

    open spec fn spec_try_from(v: AlertDescriptionInner) -> Result<AlertDescription, ()> {
        match v {
            0u8 => Ok(AlertDescription::CloseNotify),
            10u8 => Ok(AlertDescription::UnexpectedMessage),
            20u8 => Ok(AlertDescription::BadRecordMac),
            22u8 => Ok(AlertDescription::RecordOverflow),
            40u8 => Ok(AlertDescription::HandshakeFailure),
            42u8 => Ok(AlertDescription::BadCertificate),
            43u8 => Ok(AlertDescription::UnsupportedCertificate),
            44u8 => Ok(AlertDescription::CertificateRevoked),
            45u8 => Ok(AlertDescription::CertificateExpired),
            46u8 => Ok(AlertDescription::CertificateUnknown),
            47u8 => Ok(AlertDescription::IllegalParameter),
            48u8 => Ok(AlertDescription::UnknownCA),
            49u8 => Ok(AlertDescription::AccessDenied),
            50u8 => Ok(AlertDescription::DecodeError),
            51u8 => Ok(AlertDescription::DecryptError),
            70u8 => Ok(AlertDescription::ProtocolVersion),
            71u8 => Ok(AlertDescription::InsufficientSecurity),
            80u8 => Ok(AlertDescription::InternalError),
            86u8 => Ok(AlertDescription::InappropriateFallback),
            90u8 => Ok(AlertDescription::UserCanceled),
            109u8 => Ok(AlertDescription::MissingExtension),
            110u8 => Ok(AlertDescription::UnsupportedExtension),
            112u8 => Ok(AlertDescription::UnrecognizedName),
            113u8 => Ok(AlertDescription::BadCertificateStatusResponse),
            115u8 => Ok(AlertDescription::UnknownPSKIdentity),
            116u8 => Ok(AlertDescription::CertificateRequired),
            120u8 => Ok(AlertDescription::NoApplicationProtocol),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AlertDescription> for AlertDescriptionInner {
    type Error = ();

    open spec fn spec_try_from(v: AlertDescription) -> Result<AlertDescriptionInner, ()> {
        match v {
            AlertDescription::CloseNotify => Ok(0u8),
            AlertDescription::UnexpectedMessage => Ok(10u8),
            AlertDescription::BadRecordMac => Ok(20u8),
            AlertDescription::RecordOverflow => Ok(22u8),
            AlertDescription::HandshakeFailure => Ok(40u8),
            AlertDescription::BadCertificate => Ok(42u8),
            AlertDescription::UnsupportedCertificate => Ok(43u8),
            AlertDescription::CertificateRevoked => Ok(44u8),
            AlertDescription::CertificateExpired => Ok(45u8),
            AlertDescription::CertificateUnknown => Ok(46u8),
            AlertDescription::IllegalParameter => Ok(47u8),
            AlertDescription::UnknownCA => Ok(48u8),
            AlertDescription::AccessDenied => Ok(49u8),
            AlertDescription::DecodeError => Ok(50u8),
            AlertDescription::DecryptError => Ok(51u8),
            AlertDescription::ProtocolVersion => Ok(70u8),
            AlertDescription::InsufficientSecurity => Ok(71u8),
            AlertDescription::InternalError => Ok(80u8),
            AlertDescription::InappropriateFallback => Ok(86u8),
            AlertDescription::UserCanceled => Ok(90u8),
            AlertDescription::MissingExtension => Ok(109u8),
            AlertDescription::UnsupportedExtension => Ok(110u8),
            AlertDescription::UnrecognizedName => Ok(112u8),
            AlertDescription::BadCertificateStatusResponse => Ok(113u8),
            AlertDescription::UnknownPSKIdentity => Ok(115u8),
            AlertDescription::CertificateRequired => Ok(116u8),
            AlertDescription::NoApplicationProtocol => Ok(120u8),
        }
    }
}

impl TryFrom<AlertDescriptionInner> for AlertDescription {
    type Error = ();

    fn ex_try_from(v: AlertDescriptionInner) -> Result<AlertDescription, ()> {
        match v {
            0u8 => Ok(AlertDescription::CloseNotify),
            10u8 => Ok(AlertDescription::UnexpectedMessage),
            20u8 => Ok(AlertDescription::BadRecordMac),
            22u8 => Ok(AlertDescription::RecordOverflow),
            40u8 => Ok(AlertDescription::HandshakeFailure),
            42u8 => Ok(AlertDescription::BadCertificate),
            43u8 => Ok(AlertDescription::UnsupportedCertificate),
            44u8 => Ok(AlertDescription::CertificateRevoked),
            45u8 => Ok(AlertDescription::CertificateExpired),
            46u8 => Ok(AlertDescription::CertificateUnknown),
            47u8 => Ok(AlertDescription::IllegalParameter),
            48u8 => Ok(AlertDescription::UnknownCA),
            49u8 => Ok(AlertDescription::AccessDenied),
            50u8 => Ok(AlertDescription::DecodeError),
            51u8 => Ok(AlertDescription::DecryptError),
            70u8 => Ok(AlertDescription::ProtocolVersion),
            71u8 => Ok(AlertDescription::InsufficientSecurity),
            80u8 => Ok(AlertDescription::InternalError),
            86u8 => Ok(AlertDescription::InappropriateFallback),
            90u8 => Ok(AlertDescription::UserCanceled),
            109u8 => Ok(AlertDescription::MissingExtension),
            110u8 => Ok(AlertDescription::UnsupportedExtension),
            112u8 => Ok(AlertDescription::UnrecognizedName),
            113u8 => Ok(AlertDescription::BadCertificateStatusResponse),
            115u8 => Ok(AlertDescription::UnknownPSKIdentity),
            116u8 => Ok(AlertDescription::CertificateRequired),
            120u8 => Ok(AlertDescription::NoApplicationProtocol),
            _ => Err(()),
        }
    }
}

impl TryFrom<AlertDescription> for AlertDescriptionInner {
    type Error = ();

    fn ex_try_from(v: AlertDescription) -> Result<AlertDescriptionInner, ()> {
        match v {
            AlertDescription::CloseNotify => Ok(0u8),
            AlertDescription::UnexpectedMessage => Ok(10u8),
            AlertDescription::BadRecordMac => Ok(20u8),
            AlertDescription::RecordOverflow => Ok(22u8),
            AlertDescription::HandshakeFailure => Ok(40u8),
            AlertDescription::BadCertificate => Ok(42u8),
            AlertDescription::UnsupportedCertificate => Ok(43u8),
            AlertDescription::CertificateRevoked => Ok(44u8),
            AlertDescription::CertificateExpired => Ok(45u8),
            AlertDescription::CertificateUnknown => Ok(46u8),
            AlertDescription::IllegalParameter => Ok(47u8),
            AlertDescription::UnknownCA => Ok(48u8),
            AlertDescription::AccessDenied => Ok(49u8),
            AlertDescription::DecodeError => Ok(50u8),
            AlertDescription::DecryptError => Ok(51u8),
            AlertDescription::ProtocolVersion => Ok(70u8),
            AlertDescription::InsufficientSecurity => Ok(71u8),
            AlertDescription::InternalError => Ok(80u8),
            AlertDescription::InappropriateFallback => Ok(86u8),
            AlertDescription::UserCanceled => Ok(90u8),
            AlertDescription::MissingExtension => Ok(109u8),
            AlertDescription::UnsupportedExtension => Ok(110u8),
            AlertDescription::UnrecognizedName => Ok(112u8),
            AlertDescription::BadCertificateStatusResponse => Ok(113u8),
            AlertDescription::UnknownPSKIdentity => Ok(115u8),
            AlertDescription::CertificateRequired => Ok(116u8),
            AlertDescription::NoApplicationProtocol => Ok(120u8),
        }
    }
}

pub struct AlertDescriptionMapper;

impl View for AlertDescriptionMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for AlertDescriptionMapper {
    type Src = AlertDescriptionInner;
    type Dst = AlertDescription;

    proof fn spec_iso(s: Self::Src) { }

    proof fn spec_iso_rev(s: Self::Dst) { }
}

impl TryFromInto for AlertDescriptionMapper {
    type Src = AlertDescriptionInner;
    type Dst = AlertDescription;
}


pub struct SpecAlertDescriptionCombinator(SpecAlertDescriptionCombinatorAlias);

impl SpecCombinator for SpecAlertDescriptionCombinator {
    type SpecResult = SpecAlertDescription;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertDescriptionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertDescriptionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertDescriptionCombinatorAlias = TryMap<U8, AlertDescriptionMapper>;

pub struct AlertDescriptionCombinator(AlertDescriptionCombinatorAlias);

impl View for AlertDescriptionCombinator {
    type V = SpecAlertDescriptionCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertDescriptionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for AlertDescriptionCombinator {
    type Result = AlertDescription;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type AlertDescriptionCombinatorAlias = TryMap<U8, AlertDescriptionMapper>;


pub closed spec fn spec_alert_description() -> SpecAlertDescriptionCombinator {
    SpecAlertDescriptionCombinator(TryMap { inner: U8, mapper: AlertDescriptionMapper })
}

                
pub fn alert_description() -> (o: AlertDescriptionCombinator)
    ensures o@ == spec_alert_description(),
{
    AlertDescriptionCombinator(TryMap { inner: U8, mapper: AlertDescriptionMapper })
}

                

pub struct SpecAlert {
    pub level: SpecAlertLevel,
    pub description: SpecAlertDescription,
}

pub type SpecAlertInner = (SpecAlertLevel, SpecAlertDescription);
impl SpecFrom<SpecAlert> for SpecAlertInner {
    open spec fn spec_from(m: SpecAlert) -> SpecAlertInner {
        (m.level, m.description)
    }
}
impl SpecFrom<SpecAlertInner> for SpecAlert {
    open spec fn spec_from(m: SpecAlertInner) -> SpecAlert {
        let (level, description) = m;
        SpecAlert { level, description }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Alert {
    pub level: AlertLevel,
    pub description: AlertDescription,
}

impl View for Alert {
    type V = SpecAlert;

    open spec fn view(&self) -> Self::V {
        SpecAlert {
            level: self.level@,
            description: self.description@,
        }
    }
}
pub type AlertInner = (AlertLevel, AlertDescription);
impl From<Alert> for AlertInner {
    fn ex_from(m: Alert) -> AlertInner {
        (m.level, m.description)
    }
}
impl From<AlertInner> for Alert {
    fn ex_from(m: AlertInner) -> Alert {
        let (level, description) = m;
        Alert { level, description }
    }
}

pub struct AlertMapper;
impl AlertMapper {
    pub closed spec fn spec_new() -> Self {
        AlertMapper
    }
    pub fn new() -> Self {
        AlertMapper
    }
}
impl View for AlertMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AlertMapper {
    type Src = SpecAlertInner;
    type Dst = SpecAlert;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for AlertMapper {
    type Src = AlertInner;
    type Dst = Alert;
}

pub struct SpecAlertCombinator(SpecAlertCombinatorAlias);

impl SpecCombinator for SpecAlertCombinator {
    type SpecResult = SpecAlert;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertCombinatorAlias = Mapped<(SpecAlertLevelCombinator, SpecAlertDescriptionCombinator), AlertMapper>;

pub struct AlertCombinator(AlertCombinatorAlias);

impl View for AlertCombinator {
    type V = SpecAlertCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for AlertCombinator {
    type Result = Alert;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type AlertCombinatorAlias = Mapped<(AlertLevelCombinator, AlertDescriptionCombinator), AlertMapper>;


pub closed spec fn spec_alert() -> SpecAlertCombinator {
    SpecAlertCombinator(
    Mapped {
        inner: (spec_alert_level(), spec_alert_description()),
        mapper: AlertMapper::spec_new(),
    })
}

                
pub fn alert() -> (o: AlertCombinator)
    ensures o@ == spec_alert(),
{
    AlertCombinator(
    Mapped {
        inner: (alert_level(), alert_description()),
        mapper: AlertMapper::new(),
    })
}

                

pub struct SpecServerCertTypeServerExtension {
    pub server_certificate_type: SpecCertificateType,
}

pub type SpecServerCertTypeServerExtensionInner = SpecCertificateType;
impl SpecFrom<SpecServerCertTypeServerExtension> for SpecServerCertTypeServerExtensionInner {
    open spec fn spec_from(m: SpecServerCertTypeServerExtension) -> SpecServerCertTypeServerExtensionInner {
        m.server_certificate_type
    }
}
impl SpecFrom<SpecServerCertTypeServerExtensionInner> for SpecServerCertTypeServerExtension {
    open spec fn spec_from(m: SpecServerCertTypeServerExtensionInner) -> SpecServerCertTypeServerExtension {
        let server_certificate_type = m;
        SpecServerCertTypeServerExtension { server_certificate_type }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerCertTypeServerExtension {
    pub server_certificate_type: CertificateType,
}

impl View for ServerCertTypeServerExtension {
    type V = SpecServerCertTypeServerExtension;

    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeServerExtension {
            server_certificate_type: self.server_certificate_type@,
        }
    }
}
pub type ServerCertTypeServerExtensionInner = CertificateType;
impl From<ServerCertTypeServerExtension> for ServerCertTypeServerExtensionInner {
    fn ex_from(m: ServerCertTypeServerExtension) -> ServerCertTypeServerExtensionInner {
        m.server_certificate_type
    }
}
impl From<ServerCertTypeServerExtensionInner> for ServerCertTypeServerExtension {
    fn ex_from(m: ServerCertTypeServerExtensionInner) -> ServerCertTypeServerExtension {
        let server_certificate_type = m;
        ServerCertTypeServerExtension { server_certificate_type }
    }
}

pub struct ServerCertTypeServerExtensionMapper;
impl ServerCertTypeServerExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        ServerCertTypeServerExtensionMapper
    }
    pub fn new() -> Self {
        ServerCertTypeServerExtensionMapper
    }
}
impl View for ServerCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeServerExtensionMapper {
    type Src = SpecServerCertTypeServerExtensionInner;
    type Dst = SpecServerCertTypeServerExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ServerCertTypeServerExtensionMapper {
    type Src = ServerCertTypeServerExtensionInner;
    type Dst = ServerCertTypeServerExtension;
}

pub struct SpecServerCertTypeServerExtensionCombinator(SpecServerCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    type SpecResult = SpecServerCertTypeServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;

pub struct ServerCertTypeServerExtensionCombinator(ServerCertTypeServerExtensionCombinatorAlias);

impl View for ServerCertTypeServerExtensionCombinator {
    type V = SpecServerCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerCertTypeServerExtensionCombinator {
    type Result = ServerCertTypeServerExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ServerCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;


pub closed spec fn spec_server_cert_type_server_extension() -> SpecServerCertTypeServerExtensionCombinator {
    SpecServerCertTypeServerExtensionCombinator(
    Mapped {
        inner: spec_certificate_type(),
        mapper: ServerCertTypeServerExtensionMapper::spec_new(),
    })
}

                
pub fn server_cert_type_server_extension() -> (o: ServerCertTypeServerExtensionCombinator)
    ensures o@ == spec_server_cert_type_server_extension(),
{
    ServerCertTypeServerExtensionCombinator(
    Mapped {
        inner: certificate_type(),
        mapper: ServerCertTypeServerExtensionMapper::new(),
    })
}

                

pub struct SpecOpaque2Ffff {
    pub l: SpecUint2Ffff,
    pub data: Seq<u8>,
}

pub type SpecOpaque2FfffInner = (SpecUint2Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque2Ffff> for SpecOpaque2FfffInner {
    open spec fn spec_from(m: SpecOpaque2Ffff) -> SpecOpaque2FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque2FfffInner> for SpecOpaque2Ffff {
    open spec fn spec_from(m: SpecOpaque2FfffInner) -> SpecOpaque2Ffff {
        let (l, data) = m;
        SpecOpaque2Ffff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque2Ffff<'a> {
    pub l: Uint2Ffff,
    pub data: &'a [u8],
}

impl View for Opaque2Ffff<'_> {
    type V = SpecOpaque2Ffff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque2Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque2FfffInner<'a> = (Uint2Ffff, &'a [u8]);
impl<'a> From<Opaque2Ffff<'a>> for Opaque2FfffInner<'a> {
    fn ex_from(m: Opaque2Ffff) -> Opaque2FfffInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque2FfffInner<'a>> for Opaque2Ffff<'a> {
    fn ex_from(m: Opaque2FfffInner) -> Opaque2Ffff {
        let (l, data) = m;
        Opaque2Ffff { l, data }
    }
}

pub struct Opaque2FfffMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque2FfffMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque2FfffMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque2FfffMapper(PhantomData)
    }
}
impl View for Opaque2FfffMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque2FfffMapper<'_> {
    type Src = SpecOpaque2FfffInner;
    type Dst = SpecOpaque2Ffff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque2FfffMapper<'a> {
    type Src = Opaque2FfffInner<'a>;
    type Dst = Opaque2Ffff<'a>;
}

pub struct SpecOpaque2FfffCombinator(SpecOpaque2FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque2FfffCombinator {
    type SpecResult = SpecOpaque2Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque2FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque2FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque2FfffCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, Bytes>, Opaque2FfffMapper<'static>>;

pub struct Opaque2FfffCombinator<'a>(Opaque2FfffCombinatorAlias<'a>);

impl<'a> View for Opaque2FfffCombinator<'a> {
    type V = SpecOpaque2FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque2FfffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque2FfffCombinator<'a> {
    type Result = Opaque2Ffff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque2FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, Bytes, Opaque2FfffCont0<'a>>, Opaque2FfffMapper<'a>>;


pub closed spec fn spec_opaque_2_ffff() -> SpecOpaque2FfffCombinator {
    SpecOpaque2FfffCombinator(
    Mapped {
        inner: SpecDepend { fst: spec_uint_2_ffff(), snd: |deps| spec_opaque2_ffff_cont0(deps) },
        mapper: Opaque2FfffMapper::spec_new(),
    })
}

pub open spec fn spec_opaque2_ffff_cont0(deps: SpecUint2Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_2_ffff<'a>() -> (o: Opaque2FfffCombinator<'a>)
    ensures o@ == spec_opaque_2_ffff(),
{
    Opaque2FfffCombinator(
    Mapped {
        inner: Depend { fst: uint_2_ffff(), snd: Opaque2FfffCont0::new(), spec_snd: Ghost(|deps| spec_opaque2_ffff_cont0(deps)) },
        mapper: Opaque2FfffMapper::new(),
    })
}

pub struct Opaque2FfffCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque2FfffCont0<'a> {
    pub fn new() -> Self {
        Opaque2FfffCont0(PhantomData)
    }
}
impl<'a> Continuation<&Uint2Ffff> for Opaque2FfffCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &Uint2Ffff) -> bool { true }

    open spec fn ensures(&self, deps: &Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque2_ffff_cont0(deps@)
    }

    fn apply(&self, deps: &Uint2Ffff) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                
pub type SpecMontgomeryPoint32 = Seq<u8>;
pub type MontgomeryPoint32<'a> = &'a [u8];


pub struct SpecMontgomeryPoint32Combinator(SpecMontgomeryPoint32CombinatorAlias);

impl SpecCombinator for SpecMontgomeryPoint32Combinator {
    type SpecResult = SpecMontgomeryPoint32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMontgomeryPoint32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMontgomeryPoint32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMontgomeryPoint32CombinatorAlias = BytesN<32>;

pub struct MontgomeryPoint32Combinator(MontgomeryPoint32CombinatorAlias);

impl View for MontgomeryPoint32Combinator {
    type V = SpecMontgomeryPoint32Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryPoint32Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MontgomeryPoint32Combinator {
    type Result = MontgomeryPoint32<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MontgomeryPoint32CombinatorAlias = BytesN<32>;


pub closed spec fn spec_montgomery_point32() -> SpecMontgomeryPoint32Combinator {
    SpecMontgomeryPoint32Combinator(BytesN::<32>)
}

                
pub fn montgomery_point32() -> (o: MontgomeryPoint32Combinator)
    ensures o@ == spec_montgomery_point32(),
{
    MontgomeryPoint32Combinator(BytesN::<32>)
}

                

pub struct SpecHeartbeatExtension {
    pub mode: SpecHeartbeatMode,
}

pub type SpecHeartbeatExtensionInner = SpecHeartbeatMode;
impl SpecFrom<SpecHeartbeatExtension> for SpecHeartbeatExtensionInner {
    open spec fn spec_from(m: SpecHeartbeatExtension) -> SpecHeartbeatExtensionInner {
        m.mode
    }
}
impl SpecFrom<SpecHeartbeatExtensionInner> for SpecHeartbeatExtension {
    open spec fn spec_from(m: SpecHeartbeatExtensionInner) -> SpecHeartbeatExtension {
        let mode = m;
        SpecHeartbeatExtension { mode }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct HeartbeatExtension {
    pub mode: HeartbeatMode,
}

impl View for HeartbeatExtension {
    type V = SpecHeartbeatExtension;

    open spec fn view(&self) -> Self::V {
        SpecHeartbeatExtension {
            mode: self.mode@,
        }
    }
}
pub type HeartbeatExtensionInner = HeartbeatMode;
impl From<HeartbeatExtension> for HeartbeatExtensionInner {
    fn ex_from(m: HeartbeatExtension) -> HeartbeatExtensionInner {
        m.mode
    }
}
impl From<HeartbeatExtensionInner> for HeartbeatExtension {
    fn ex_from(m: HeartbeatExtensionInner) -> HeartbeatExtension {
        let mode = m;
        HeartbeatExtension { mode }
    }
}

pub struct HeartbeatExtensionMapper;
impl HeartbeatExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        HeartbeatExtensionMapper
    }
    pub fn new() -> Self {
        HeartbeatExtensionMapper
    }
}
impl View for HeartbeatExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HeartbeatExtensionMapper {
    type Src = SpecHeartbeatExtensionInner;
    type Dst = SpecHeartbeatExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for HeartbeatExtensionMapper {
    type Src = HeartbeatExtensionInner;
    type Dst = HeartbeatExtension;
}

pub struct SpecHeartbeatExtensionCombinator(SpecHeartbeatExtensionCombinatorAlias);

impl SpecCombinator for SpecHeartbeatExtensionCombinator {
    type SpecResult = SpecHeartbeatExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHeartbeatExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHeartbeatExtensionCombinatorAlias = Mapped<SpecHeartbeatModeCombinator, HeartbeatExtensionMapper>;

pub struct HeartbeatExtensionCombinator(HeartbeatExtensionCombinatorAlias);

impl View for HeartbeatExtensionCombinator {
    type V = SpecHeartbeatExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HeartbeatExtensionCombinator {
    type Result = HeartbeatExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type HeartbeatExtensionCombinatorAlias = Mapped<HeartbeatModeCombinator, HeartbeatExtensionMapper>;


pub closed spec fn spec_heartbeat_extension() -> SpecHeartbeatExtensionCombinator {
    SpecHeartbeatExtensionCombinator(
    Mapped {
        inner: spec_heartbeat_mode(),
        mapper: HeartbeatExtensionMapper::spec_new(),
    })
}

                
pub fn heartbeat_extension() -> (o: HeartbeatExtensionCombinator)
    ensures o@ == spec_heartbeat_extension(),
{
    HeartbeatExtensionCombinator(
    Mapped {
        inner: heartbeat_mode(),
        mapper: HeartbeatExtensionMapper::new(),
    })
}

                
pub type SpecMontgomeryForm56 = Seq<u8>;
pub type MontgomeryForm56<'a> = &'a [u8];


pub struct SpecMontgomeryForm56Combinator(SpecMontgomeryForm56CombinatorAlias);

impl SpecCombinator for SpecMontgomeryForm56Combinator {
    type SpecResult = SpecMontgomeryForm56;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMontgomeryForm56Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMontgomeryForm56CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMontgomeryForm56CombinatorAlias = BytesN<56>;

pub struct MontgomeryForm56Combinator(MontgomeryForm56CombinatorAlias);

impl View for MontgomeryForm56Combinator {
    type V = SpecMontgomeryForm56Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryForm56Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MontgomeryForm56Combinator {
    type Result = MontgomeryForm56<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type MontgomeryForm56CombinatorAlias = BytesN<56>;


pub closed spec fn spec_montgomery_form56() -> SpecMontgomeryForm56Combinator {
    SpecMontgomeryForm56Combinator(BytesN::<56>)
}

                
pub fn montgomery_form56() -> (o: MontgomeryForm56Combinator)
    ensures o@ == spec_montgomery_form56(),
{
    MontgomeryForm56Combinator(BytesN::<56>)
}

                

pub struct SpecUncompressedPointRepresentation66 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}

pub type SpecUncompressedPointRepresentation66Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation66> for SpecUncompressedPointRepresentation66Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation66) -> SpecUncompressedPointRepresentation66Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation66Inner> for SpecUncompressedPointRepresentation66 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation66Inner) -> SpecUncompressedPointRepresentation66 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation66 { legacy_form, x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct UncompressedPointRepresentation66<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}

impl View for UncompressedPointRepresentation66<'_> {
    type V = SpecUncompressedPointRepresentation66;

    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation66 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type UncompressedPointRepresentation66Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl<'a> From<UncompressedPointRepresentation66<'a>> for UncompressedPointRepresentation66Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation66) -> UncompressedPointRepresentation66Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation66Inner<'a>> for UncompressedPointRepresentation66<'a> {
    fn ex_from(m: UncompressedPointRepresentation66Inner) -> UncompressedPointRepresentation66 {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation66 { legacy_form, x, y }
    }
}

pub struct UncompressedPointRepresentation66Mapper<'a>(PhantomData<&'a ()>);
impl<'a> UncompressedPointRepresentation66Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        UncompressedPointRepresentation66Mapper(PhantomData)
    }
    pub fn new() -> Self {
        UncompressedPointRepresentation66Mapper(PhantomData)
    }
}
impl View for UncompressedPointRepresentation66Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation66Mapper<'_> {
    type Src = SpecUncompressedPointRepresentation66Inner;
    type Dst = SpecUncompressedPointRepresentation66;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for UncompressedPointRepresentation66Mapper<'a> {
    type Src = UncompressedPointRepresentation66Inner<'a>;
    type Dst = UncompressedPointRepresentation66<'a>;
}
pub const UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation66Combinator(SpecUncompressedPointRepresentation66CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation66Combinator {
    type SpecResult = SpecUncompressedPointRepresentation66;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation66Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation66CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation66CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<66>, BytesN<66>)), UncompressedPointRepresentation66Mapper<'static>>;

pub struct UncompressedPointRepresentation66Combinator<'a>(UncompressedPointRepresentation66CombinatorAlias<'a>);

impl<'a> View for UncompressedPointRepresentation66Combinator<'a> {
    type V = SpecUncompressedPointRepresentation66Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation66Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UncompressedPointRepresentation66Combinator<'a> {
    type Result = UncompressedPointRepresentation66<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UncompressedPointRepresentation66CombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<66>, BytesN<66>)), UncompressedPointRepresentation66Mapper<'a>>;


pub closed spec fn spec_uncompressed_point_representation66() -> SpecUncompressedPointRepresentation66Combinator {
    SpecUncompressedPointRepresentation66Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)),
        mapper: UncompressedPointRepresentation66Mapper::spec_new(),
    })
}

                
pub fn uncompressed_point_representation66<'a>() -> (o: UncompressedPointRepresentation66Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation66(),
{
    UncompressedPointRepresentation66Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)),
        mapper: UncompressedPointRepresentation66Mapper::new(),
    })
}

                

pub struct SpecUseSrtpData {
    pub profiles: SpecSrtpProtectionProfiles,
    pub srtp_mki: SpecOpaque0Ff,
}

pub type SpecUseSrtpDataInner = (SpecSrtpProtectionProfiles, SpecOpaque0Ff);
impl SpecFrom<SpecUseSrtpData> for SpecUseSrtpDataInner {
    open spec fn spec_from(m: SpecUseSrtpData) -> SpecUseSrtpDataInner {
        (m.profiles, m.srtp_mki)
    }
}
impl SpecFrom<SpecUseSrtpDataInner> for SpecUseSrtpData {
    open spec fn spec_from(m: SpecUseSrtpDataInner) -> SpecUseSrtpData {
        let (profiles, srtp_mki) = m;
        SpecUseSrtpData { profiles, srtp_mki }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct UseSrtpData<'a> {
    pub profiles: SrtpProtectionProfiles<'a>,
    pub srtp_mki: Opaque0Ff<'a>,
}

impl View for UseSrtpData<'_> {
    type V = SpecUseSrtpData;

    open spec fn view(&self) -> Self::V {
        SpecUseSrtpData {
            profiles: self.profiles@,
            srtp_mki: self.srtp_mki@,
        }
    }
}
pub type UseSrtpDataInner<'a> = (SrtpProtectionProfiles<'a>, Opaque0Ff<'a>);
impl<'a> From<UseSrtpData<'a>> for UseSrtpDataInner<'a> {
    fn ex_from(m: UseSrtpData) -> UseSrtpDataInner {
        (m.profiles, m.srtp_mki)
    }
}
impl<'a> From<UseSrtpDataInner<'a>> for UseSrtpData<'a> {
    fn ex_from(m: UseSrtpDataInner) -> UseSrtpData {
        let (profiles, srtp_mki) = m;
        UseSrtpData { profiles, srtp_mki }
    }
}

pub struct UseSrtpDataMapper<'a>(PhantomData<&'a ()>);
impl<'a> UseSrtpDataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        UseSrtpDataMapper(PhantomData)
    }
    pub fn new() -> Self {
        UseSrtpDataMapper(PhantomData)
    }
}
impl View for UseSrtpDataMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UseSrtpDataMapper<'_> {
    type Src = SpecUseSrtpDataInner;
    type Dst = SpecUseSrtpData;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for UseSrtpDataMapper<'a> {
    type Src = UseSrtpDataInner<'a>;
    type Dst = UseSrtpData<'a>;
}

pub struct SpecUseSrtpDataCombinator(SpecUseSrtpDataCombinatorAlias);

impl SpecCombinator for SpecUseSrtpDataCombinator {
    type SpecResult = SpecUseSrtpData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUseSrtpDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUseSrtpDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUseSrtpDataCombinatorAlias = Mapped<(SpecSrtpProtectionProfilesCombinator, SpecOpaque0FfCombinator), UseSrtpDataMapper<'static>>;

pub struct UseSrtpDataCombinator<'a>(UseSrtpDataCombinatorAlias<'a>);

impl<'a> View for UseSrtpDataCombinator<'a> {
    type V = SpecUseSrtpDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecUseSrtpDataCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for UseSrtpDataCombinator<'a> {
    type Result = UseSrtpData<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type UseSrtpDataCombinatorAlias<'a> = Mapped<(SrtpProtectionProfilesCombinator<'a>, Opaque0FfCombinator<'a>), UseSrtpDataMapper<'a>>;


pub closed spec fn spec_use_srtp_data() -> SpecUseSrtpDataCombinator {
    SpecUseSrtpDataCombinator(
    Mapped {
        inner: (spec_srtp_protection_profiles(), spec_opaque_0_ff()),
        mapper: UseSrtpDataMapper::spec_new(),
    })
}

                
pub fn use_srtp_data<'a>() -> (o: UseSrtpDataCombinator<'a>)
    ensures o@ == spec_use_srtp_data(),
{
    UseSrtpDataCombinator(
    Mapped {
        inner: (srtp_protection_profiles(), opaque_0_ff()),
        mapper: UseSrtpDataMapper::new(),
    })
}

                

pub struct SpecOpaque0Ffffff {
    pub l: u24,
    pub data: Seq<u8>,
}

pub type SpecOpaque0FfffffInner = (u24, Seq<u8>);
impl SpecFrom<SpecOpaque0Ffffff> for SpecOpaque0FfffffInner {
    open spec fn spec_from(m: SpecOpaque0Ffffff) -> SpecOpaque0FfffffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfffffInner> for SpecOpaque0Ffffff {
    open spec fn spec_from(m: SpecOpaque0FfffffInner) -> SpecOpaque0Ffffff {
        let (l, data) = m;
        SpecOpaque0Ffffff { l, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Opaque0Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}

impl View for Opaque0Ffffff<'_> {
    type V = SpecOpaque0Ffffff;

    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
pub type Opaque0FfffffInner<'a> = (u24, &'a [u8]);
impl<'a> From<Opaque0Ffffff<'a>> for Opaque0FfffffInner<'a> {
    fn ex_from(m: Opaque0Ffffff) -> Opaque0FfffffInner {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffffInner<'a>> for Opaque0Ffffff<'a> {
    fn ex_from(m: Opaque0FfffffInner) -> Opaque0Ffffff {
        let (l, data) = m;
        Opaque0Ffffff { l, data }
    }
}

pub struct Opaque0FfffffMapper<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffffMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Opaque0FfffffMapper(PhantomData)
    }
    pub fn new() -> Self {
        Opaque0FfffffMapper(PhantomData)
    }
}
impl View for Opaque0FfffffMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffffMapper<'_> {
    type Src = SpecOpaque0FfffffInner;
    type Dst = SpecOpaque0Ffffff;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Opaque0FfffffMapper<'a> {
    type Src = Opaque0FfffffInner<'a>;
    type Dst = Opaque0Ffffff<'a>;
}

pub struct SpecOpaque0FfffffCombinator(SpecOpaque0FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffffCombinator {
    type SpecResult = SpecOpaque0Ffffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfffffCombinatorAlias = Mapped<SpecDepend<U24Be, Bytes>, Opaque0FfffffMapper<'static>>;

pub struct Opaque0FfffffCombinator<'a>(Opaque0FfffffCombinatorAlias<'a>);

impl<'a> View for Opaque0FfffffCombinator<'a> {
    type V = SpecOpaque0FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffffCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Opaque0FfffffCombinator<'a> {
    type Result = Opaque0Ffffff<'a>;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type Opaque0FfffffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U24Be, Bytes, Opaque0FfffffCont0<'a>>, Opaque0FfffffMapper<'a>>;


pub closed spec fn spec_opaque_0_ffffff() -> SpecOpaque0FfffffCombinator {
    SpecOpaque0FfffffCombinator(
    Mapped {
        inner: SpecDepend { fst: U24Be, snd: |deps| spec_opaque0_ffffff_cont0(deps) },
        mapper: Opaque0FfffffMapper::spec_new(),
    })
}

pub open spec fn spec_opaque0_ffffff_cont0(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
                
pub fn opaque_0_ffffff<'a>() -> (o: Opaque0FfffffCombinator<'a>)
    ensures o@ == spec_opaque_0_ffffff(),
{
    Opaque0FfffffCombinator(
    Mapped {
        inner: Depend { fst: U24Be, snd: Opaque0FfffffCont0::new(), spec_snd: Ghost(|deps| spec_opaque0_ffffff_cont0(deps)) },
        mapper: Opaque0FfffffMapper::new(),
    })
}

pub struct Opaque0FfffffCont0<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffffCont0<'a> {
    pub fn new() -> Self {
        Opaque0FfffffCont0(PhantomData)
    }
}
impl<'a> Continuation<&u24> for Opaque0FfffffCont0<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: &u24) -> bool { true }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffffff_cont0(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let l = *deps;
        Bytes(l.ex_into())
    }
}
                

pub struct SpecClientCertTypeServerExtension {
    pub client_certificate_type: SpecCertificateType,
}

pub type SpecClientCertTypeServerExtensionInner = SpecCertificateType;
impl SpecFrom<SpecClientCertTypeServerExtension> for SpecClientCertTypeServerExtensionInner {
    open spec fn spec_from(m: SpecClientCertTypeServerExtension) -> SpecClientCertTypeServerExtensionInner {
        m.client_certificate_type
    }
}
impl SpecFrom<SpecClientCertTypeServerExtensionInner> for SpecClientCertTypeServerExtension {
    open spec fn spec_from(m: SpecClientCertTypeServerExtensionInner) -> SpecClientCertTypeServerExtension {
        let client_certificate_type = m;
        SpecClientCertTypeServerExtension { client_certificate_type }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientCertTypeServerExtension {
    pub client_certificate_type: CertificateType,
}

impl View for ClientCertTypeServerExtension {
    type V = SpecClientCertTypeServerExtension;

    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeServerExtension {
            client_certificate_type: self.client_certificate_type@,
        }
    }
}
pub type ClientCertTypeServerExtensionInner = CertificateType;
impl From<ClientCertTypeServerExtension> for ClientCertTypeServerExtensionInner {
    fn ex_from(m: ClientCertTypeServerExtension) -> ClientCertTypeServerExtensionInner {
        m.client_certificate_type
    }
}
impl From<ClientCertTypeServerExtensionInner> for ClientCertTypeServerExtension {
    fn ex_from(m: ClientCertTypeServerExtensionInner) -> ClientCertTypeServerExtension {
        let client_certificate_type = m;
        ClientCertTypeServerExtension { client_certificate_type }
    }
}

pub struct ClientCertTypeServerExtensionMapper;
impl ClientCertTypeServerExtensionMapper {
    pub closed spec fn spec_new() -> Self {
        ClientCertTypeServerExtensionMapper
    }
    pub fn new() -> Self {
        ClientCertTypeServerExtensionMapper
    }
}
impl View for ClientCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeServerExtensionMapper {
    type Src = SpecClientCertTypeServerExtensionInner;
    type Dst = SpecClientCertTypeServerExtension;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for ClientCertTypeServerExtensionMapper {
    type Src = ClientCertTypeServerExtensionInner;
    type Dst = ClientCertTypeServerExtension;
}

pub struct SpecClientCertTypeServerExtensionCombinator(SpecClientCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    type SpecResult = SpecClientCertTypeServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;

pub struct ClientCertTypeServerExtensionCombinator(ClientCertTypeServerExtensionCombinatorAlias);

impl View for ClientCertTypeServerExtensionCombinator {
    type V = SpecClientCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ClientCertTypeServerExtensionCombinator {
    type Result = ClientCertTypeServerExtension;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0) }
    closed spec fn parse_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) 
    { <_ as Combinator<&[u8],Vec<u8>>>::parse(&self.0, s) }
    closed spec fn serialize_requires(&self) -> bool 
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0) }
    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type ClientCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;


pub closed spec fn spec_client_cert_type_server_extension() -> SpecClientCertTypeServerExtensionCombinator {
    SpecClientCertTypeServerExtensionCombinator(
    Mapped {
        inner: spec_certificate_type(),
        mapper: ClientCertTypeServerExtensionMapper::spec_new(),
    })
}

                
pub fn client_cert_type_server_extension() -> (o: ClientCertTypeServerExtensionCombinator)
    ensures o@ == spec_client_cert_type_server_extension(),
{
    ClientCertTypeServerExtensionCombinator(
    Mapped {
        inner: certificate_type(),
        mapper: ClientCertTypeServerExtensionMapper::new(),
    })
}

                

}
