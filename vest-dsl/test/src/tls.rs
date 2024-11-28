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
verus!{
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
        SpecOpaque1Ffffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}
pub type Opaque1FfffffInner<'a> = (u24, &'a [u8]);
impl View for Opaque1Ffffff<'_> {
    type V = SpecOpaque1Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ffffff<'a>> for Opaque1FfffffInner<'a> {
    fn ex_from(m: Opaque1Ffffff<'a>) -> Opaque1FfffffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffffInner<'a>> for Opaque1Ffffff<'a> {
    fn ex_from(m: Opaque1FfffffInner<'a>) -> Opaque1Ffffff<'a> {
        let (l, data) = m;
        Opaque1Ffffff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for Opaque1FfffffMapper<'a> {
    type Src = Opaque1FfffffInner<'a>;
    type Dst = Opaque1Ffffff<'a>;
}
    
impl SpecPred for Predicate10565972399076720534 {
    type Input = u24;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i).spec_as_u32();
        if (i >= 1 && i <= 16777215) {
            true
        } else {
            false
        }
    }
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
pub type SpecOpaque1FfffffCombinatorAlias = Mapped<SpecDepend<Refined<U24Be, Predicate10565972399076720534>, Bytes>, Opaque1FfffffMapper<'static>>;
pub struct Predicate10565972399076720534;
impl View for Predicate10565972399076720534 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate10565972399076720534 {
    type Input = u24;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i).as_u32();
        if (i >= 1 && i <= 16777215) {
            true
        } else {
            false
        }
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
pub type Opaque1FfffffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U24Be, Predicate10565972399076720534>, Bytes, Opaque1FfffffCont<'a>>, Opaque1FfffffMapper<'a>>;


pub closed spec fn spec_opaque_1_ffffff() -> SpecOpaque1FfffffCombinator {
    SpecOpaque1FfffffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U24Be, predicate: Predicate10565972399076720534 },
            snd: |deps| spec_opaque1_ffffff_cont(deps),
        },
        mapper: Opaque1FfffffMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque1_ffffff_cont(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_1_ffffff<'a>() -> (o: Opaque1FfffffCombinator<'a>)
    ensures o@ == spec_opaque_1_ffffff(),
{
    Opaque1FfffffCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U24Be, predicate: Predicate10565972399076720534 },
            snd: Opaque1FfffffCont::new(),
            spec_snd: Ghost(|deps| spec_opaque1_ffffff_cont(deps)),
        },
        mapper: Opaque1FfffffMapper::new(),
    }
)
}


pub struct Opaque1FfffffCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffffCont<'a> {
    pub fn new() -> Self {
        Opaque1FfffffCont(PhantomData)
    }
}
impl<'a> Continuation<u24> for Opaque1FfffffCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffffff_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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


                
pub type SpecExtensionType = u8;
pub type ExtensionType = u8;


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
pub type SpecExtensionTypeCombinatorAlias = U8;

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
pub type ExtensionTypeCombinatorAlias = U8;


pub closed spec fn spec_extension_type() -> SpecExtensionTypeCombinator {
    SpecExtensionTypeCombinator(U8)
}


                
pub fn extension_type() -> (o: ExtensionTypeCombinator)
    ensures o@ == spec_extension_type(),
{
    ExtensionTypeCombinator(U8)
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
        SpecOpaque0Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ffff<'a> {
    pub l: Uint0Ffff,
    pub data: &'a [u8],
}
pub type Opaque0FfffInner<'a> = (Uint0Ffff, &'a [u8]);
impl View for Opaque0Ffff<'_> {
    type V = SpecOpaque0Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ffff<'a>> for Opaque0FfffInner<'a> {
    fn ex_from(m: Opaque0Ffff<'a>) -> Opaque0FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffInner<'a>> for Opaque0Ffff<'a> {
    fn ex_from(m: Opaque0FfffInner<'a>) -> Opaque0Ffff<'a> {
        let (l, data) = m;
        Opaque0Ffff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque0FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, Bytes, Opaque0FfffCont<'a>>, Opaque0FfffMapper<'a>>;


pub closed spec fn spec_opaque_0_ffff() -> SpecOpaque0FfffCombinator {
    SpecOpaque0FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_opaque0_ffff_cont(deps),
        },
        mapper: Opaque0FfffMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque0_ffff_cont(deps: SpecUint0Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_0_ffff<'a>() -> (o: Opaque0FfffCombinator<'a>)
    ensures o@ == spec_opaque_0_ffff(),
{
    Opaque0FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: Opaque0FfffCont::new(),
            spec_snd: Ghost(|deps| spec_opaque0_ffff_cont(deps)),
        },
        mapper: Opaque0FfffMapper::new(),
    }
)
}


pub struct Opaque0FfffCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffCont<'a> {
    pub fn new() -> Self {
        Opaque0FfffCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for Opaque0FfffCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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
        SpecExtension {
            extension_type,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Extension<'a> {
    pub extension_type: ExtensionType,
    pub extension_data: Opaque0Ffff<'a>,
}
pub type ExtensionInner<'a> = (ExtensionType, Opaque0Ffff<'a>);
impl View for Extension<'_> {
    type V = SpecExtension;
    open spec fn view(&self) -> Self::V {
        SpecExtension {
            extension_type: self.extension_type@,
            extension_data: self.extension_data@,
        }
    }
}
impl<'a> From<Extension<'a>> for ExtensionInner<'a> {
    fn ex_from(m: Extension<'a>) -> ExtensionInner<'a> {
        (m.extension_type, m.extension_data)
    }
}
impl<'a> From<ExtensionInner<'a>> for Extension<'a> {
    fn ex_from(m: ExtensionInner<'a>) -> Extension<'a> {
        let (extension_type, extension_data) = m;
        Extension {
            extension_type,
            extension_data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecExtensionCombinator(Mapped { inner: (spec_extension_type(), spec_opaque_0_ffff()), mapper: ExtensionMapper::spec_new() })
}


                
pub fn extension<'a>() -> (o: ExtensionCombinator<'a>)
    ensures o@ == spec_extension(),
{
    ExtensionCombinator(Mapped { inner: (extension_type(), opaque_0_ffff()), mapper: ExtensionMapper::new() })
}


                
pub type SpecEncryptedExtensionsExtensions = Seq<SpecExtension>;
pub type EncryptedExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;


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
pub type SpecEncryptedExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

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
pub type EncryptedExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<ExtensionCombinator<'a>>>;


pub closed spec fn spec_encrypted_extensions_extensions(l: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    SpecEncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}


                
pub fn encrypted_extensions_extensions<'a>(l: Uint0Ffff) -> (o: EncryptedExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_encrypted_extensions_extensions(l@),
{
    EncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
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
        SpecEncryptedExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncryptedExtensions<'a> {
    pub l: Uint0Ffff,
    pub extensions: EncryptedExtensionsExtensions<'a>,
}
pub type EncryptedExtensionsInner<'a> = (Uint0Ffff, EncryptedExtensionsExtensions<'a>);
impl View for EncryptedExtensions<'_> {
    type V = SpecEncryptedExtensions;
    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<EncryptedExtensions<'a>> for EncryptedExtensionsInner<'a> {
    fn ex_from(m: EncryptedExtensions<'a>) -> EncryptedExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<EncryptedExtensionsInner<'a>> for EncryptedExtensions<'a> {
    fn ex_from(m: EncryptedExtensionsInner<'a>) -> EncryptedExtensions<'a> {
        let (l, extensions) = m;
        EncryptedExtensions {
            l,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type EncryptedExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, EncryptedExtensionsExtensionsCombinator<'a>, EncryptedExtensionsCont<'a>>, EncryptedExtensionsMapper<'a>>;


pub closed spec fn spec_encrypted_extensions() -> SpecEncryptedExtensionsCombinator {
    SpecEncryptedExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_encrypted_extensions_cont(deps),
        },
        mapper: EncryptedExtensionsMapper::spec_new(),
    }
)
}


pub open spec fn spec_encrypted_extensions_cont(deps: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    let l = deps;
    spec_encrypted_extensions_extensions(l)
}

                
pub fn encrypted_extensions<'a>() -> (o: EncryptedExtensionsCombinator<'a>)
    ensures o@ == spec_encrypted_extensions(),
{
    EncryptedExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: EncryptedExtensionsCont::new(),
            spec_snd: Ghost(|deps| spec_encrypted_extensions_cont(deps)),
        },
        mapper: EncryptedExtensionsMapper::new(),
    }
)
}


pub struct EncryptedExtensionsCont<'a>(PhantomData<&'a ()>);
impl<'a> EncryptedExtensionsCont<'a> {
    pub fn new() -> Self {
        EncryptedExtensionsCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for EncryptedExtensionsCont<'a> {
    type Output = EncryptedExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_encrypted_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        encrypted_extensions_extensions(l)
    }
}

                
pub type SpecCertificateExtensions = SpecEncryptedExtensions;
pub type CertificateExtensions<'a> = EncryptedExtensions<'a>;


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
pub type SpecCertificateExtensionsCombinatorAlias = SpecEncryptedExtensionsCombinator;

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
pub type CertificateExtensionsCombinatorAlias<'a> = EncryptedExtensionsCombinator<'a>;


pub closed spec fn spec_certificate_extensions() -> SpecCertificateExtensionsCombinator {
    SpecCertificateExtensionsCombinator(spec_encrypted_extensions())
}


                
pub fn certificate_extensions<'a>() -> (o: CertificateExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_extensions(),
{
    CertificateExtensionsCombinator(encrypted_extensions())
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
        SpecCertificateEntry {
            cert_data,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateEntry<'a> {
    pub cert_data: Opaque1Ffffff<'a>,
    pub extensions: CertificateExtensions<'a>,
}
pub type CertificateEntryInner<'a> = (Opaque1Ffffff<'a>, CertificateExtensions<'a>);
impl View for CertificateEntry<'_> {
    type V = SpecCertificateEntry;
    open spec fn view(&self) -> Self::V {
        SpecCertificateEntry {
            cert_data: self.cert_data@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateEntry<'a>> for CertificateEntryInner<'a> {
    fn ex_from(m: CertificateEntry<'a>) -> CertificateEntryInner<'a> {
        (m.cert_data, m.extensions)
    }
}
impl<'a> From<CertificateEntryInner<'a>> for CertificateEntry<'a> {
    fn ex_from(m: CertificateEntryInner<'a>) -> CertificateEntry<'a> {
        let (cert_data, extensions) = m;
        CertificateEntry {
            cert_data,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateEntryCombinator(Mapped { inner: (spec_opaque_1_ffffff(), spec_certificate_extensions()), mapper: CertificateEntryMapper::spec_new() })
}


                
pub fn certificate_entry<'a>() -> (o: CertificateEntryCombinator<'a>)
    ensures o@ == spec_certificate_entry(),
{
    CertificateEntryCombinator(Mapped { inner: (opaque_1_ffffff(), certificate_extensions()), mapper: CertificateEntryMapper::new() })
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
        SpecCertificateList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateList<'a> {
    pub l: u24,
    pub list: CertificateListList<'a>,
}
pub type CertificateListInner<'a> = (u24, CertificateListList<'a>);
impl View for CertificateList<'_> {
    type V = SpecCertificateList;
    open spec fn view(&self) -> Self::V {
        SpecCertificateList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<CertificateList<'a>> for CertificateListInner<'a> {
    fn ex_from(m: CertificateList<'a>) -> CertificateListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<CertificateListInner<'a>> for CertificateList<'a> {
    fn ex_from(m: CertificateListInner<'a>) -> CertificateList<'a> {
        let (l, list) = m;
        CertificateList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type CertificateListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U24Be, CertificateListListCombinator<'a>, CertificateListCont<'a>>, CertificateListMapper<'a>>;


pub closed spec fn spec_certificate_list() -> SpecCertificateListCombinator {
    SpecCertificateListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: U24Be,
            snd: |deps| spec_certificate_list_cont(deps),
        },
        mapper: CertificateListMapper::spec_new(),
    }
)
}


pub open spec fn spec_certificate_list_cont(deps: u24) -> SpecCertificateListListCombinator {
    let l = deps;
    spec_certificate_list_list(l)
}

                
pub fn certificate_list<'a>() -> (o: CertificateListCombinator<'a>)
    ensures o@ == spec_certificate_list(),
{
    CertificateListCombinator(
    Mapped {
        inner: Depend {
            fst: U24Be,
            snd: CertificateListCont::new(),
            spec_snd: Ghost(|deps| spec_certificate_list_cont(deps)),
        },
        mapper: CertificateListMapper::new(),
    }
)
}


pub struct CertificateListCont<'a>(PhantomData<&'a ()>);
impl<'a> CertificateListCont<'a> {
    pub fn new() -> Self {
        CertificateListCont(PhantomData)
    }
}
impl<'a> Continuation<u24> for CertificateListCont<'a> {
    type Output = CertificateListListCombinator<'a>;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_certificate_list_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        certificate_list_list(l)
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


                
pub type SpecUint1Ff = u8;
pub type Uint1Ff = u8;

impl SpecPred for Predicate13930216038658429813 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 255) {
            true
        } else {
            false
        }
    }
}

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
pub type SpecUint1FfCombinatorAlias = Refined<U8, Predicate13930216038658429813>;
pub struct Predicate13930216038658429813;
impl View for Predicate13930216038658429813 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate13930216038658429813 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 255) {
            true
        } else {
            false
        }
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
pub type Uint1FfCombinatorAlias = Refined<U8, Predicate13930216038658429813>;


pub closed spec fn spec_uint_1_ff() -> SpecUint1FfCombinator {
    SpecUint1FfCombinator(Refined { inner: U8, predicate: Predicate13930216038658429813 })
}


                
pub fn uint_1_ff() -> (o: Uint1FfCombinator)
    ensures o@ == spec_uint_1_ff(),
{
    Uint1FfCombinator(Refined { inner: U8, predicate: Predicate13930216038658429813 })
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


                
pub fn ec_point_format_list_list(l: Uint1Ff) -> (o: EcPointFormatListListCombinator)
    ensures o@ == spec_ec_point_format_list_list(l@),
{
    EcPointFormatListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(ec_point_format())))
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
        SpecEcPointFormatList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcPointFormatList {
    pub l: Uint1Ff,
    pub list: EcPointFormatListList,
}
pub type EcPointFormatListInner = (Uint1Ff, EcPointFormatListList);
impl View for EcPointFormatList {
    type V = SpecEcPointFormatList;
    open spec fn view(&self) -> Self::V {
        SpecEcPointFormatList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<EcPointFormatList> for EcPointFormatListInner {
    fn ex_from(m: EcPointFormatList) -> EcPointFormatListInner {
        (m.l, m.list)
    }
}
impl From<EcPointFormatListInner> for EcPointFormatList {
    fn ex_from(m: EcPointFormatListInner) -> EcPointFormatList {
        let (l, list) = m;
        EcPointFormatList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type EcPointFormatListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, EcPointFormatListListCombinator, EcPointFormatListCont<'a>>, EcPointFormatListMapper>;


pub closed spec fn spec_ec_point_format_list() -> SpecEcPointFormatListCombinator {
    SpecEcPointFormatListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_ec_point_format_list_cont(deps),
        },
        mapper: EcPointFormatListMapper::spec_new(),
    }
)
}


pub open spec fn spec_ec_point_format_list_cont(deps: SpecUint1Ff) -> SpecEcPointFormatListListCombinator {
    let l = deps;
    spec_ec_point_format_list_list(l)
}

                
pub fn ec_point_format_list<'a>() -> (o: EcPointFormatListCombinator<'a>)
    ensures o@ == spec_ec_point_format_list(),
{
    EcPointFormatListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: EcPointFormatListCont::new(),
            spec_snd: Ghost(|deps| spec_ec_point_format_list_cont(deps)),
        },
        mapper: EcPointFormatListMapper::new(),
    }
)
}


pub struct EcPointFormatListCont<'a>(PhantomData<&'a ()>);
impl<'a> EcPointFormatListCont<'a> {
    pub fn new() -> Self {
        EcPointFormatListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ff> for EcPointFormatListCont<'a> {
    type Output = EcPointFormatListListCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_ec_point_format_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        ec_point_format_list_list(l)
    }
}

                
pub type SpecUint2Ffff = u16;
pub type Uint2Ffff = u16;

impl SpecPred for Predicate5950696943328973166 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

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
pub type SpecUint2FfffCombinatorAlias = Refined<U16Be, Predicate5950696943328973166>;
pub struct Predicate5950696943328973166;
impl View for Predicate5950696943328973166 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate5950696943328973166 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65535) {
            true
        } else {
            false
        }
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
pub type Uint2FfffCombinatorAlias = Refined<U16Be, Predicate5950696943328973166>;


pub closed spec fn spec_uint_2_ffff() -> SpecUint2FfffCombinator {
    SpecUint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate5950696943328973166 })
}


                
pub fn uint_2_ffff() -> (o: Uint2FfffCombinator)
    ensures o@ == spec_uint_2_ffff(),
{
    Uint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate5950696943328973166 })
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


                
pub fn srtp_protection_profiles_list(l: Uint2Ffff) -> (o: SrtpProtectionProfilesListCombinator)
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
        SpecSrtpProtectionProfiles {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SrtpProtectionProfiles<'a> {
    pub l: Uint2Ffff,
    pub list: SrtpProtectionProfilesList<'a>,
}
pub type SrtpProtectionProfilesInner<'a> = (Uint2Ffff, SrtpProtectionProfilesList<'a>);
impl View for SrtpProtectionProfiles<'_> {
    type V = SpecSrtpProtectionProfiles;
    open spec fn view(&self) -> Self::V {
        SpecSrtpProtectionProfiles {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<SrtpProtectionProfiles<'a>> for SrtpProtectionProfilesInner<'a> {
    fn ex_from(m: SrtpProtectionProfiles<'a>) -> SrtpProtectionProfilesInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<SrtpProtectionProfilesInner<'a>> for SrtpProtectionProfiles<'a> {
    fn ex_from(m: SrtpProtectionProfilesInner<'a>) -> SrtpProtectionProfiles<'a> {
        let (l, list) = m;
        SrtpProtectionProfiles {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SrtpProtectionProfilesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, SrtpProtectionProfilesListCombinator, SrtpProtectionProfilesCont<'a>>, SrtpProtectionProfilesMapper<'a>>;


pub closed spec fn spec_srtp_protection_profiles() -> SpecSrtpProtectionProfilesCombinator {
    SpecSrtpProtectionProfilesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_srtp_protection_profiles_cont(deps),
        },
        mapper: SrtpProtectionProfilesMapper::spec_new(),
    }
)
}


pub open spec fn spec_srtp_protection_profiles_cont(deps: SpecUint2Ffff) -> SpecSrtpProtectionProfilesListCombinator {
    let l = deps;
    spec_srtp_protection_profiles_list(l)
}

                
pub fn srtp_protection_profiles<'a>() -> (o: SrtpProtectionProfilesCombinator<'a>)
    ensures o@ == spec_srtp_protection_profiles(),
{
    SrtpProtectionProfilesCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: SrtpProtectionProfilesCont::new(),
            spec_snd: Ghost(|deps| spec_srtp_protection_profiles_cont(deps)),
        },
        mapper: SrtpProtectionProfilesMapper::new(),
    }
)
}


pub struct SrtpProtectionProfilesCont<'a>(PhantomData<&'a ()>);
impl<'a> SrtpProtectionProfilesCont<'a> {
    pub fn new() -> Self {
        SrtpProtectionProfilesCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Ffff> for SrtpProtectionProfilesCont<'a> {
    type Output = SrtpProtectionProfilesListCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_srtp_protection_profiles_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        srtp_protection_profiles_list(l)
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
        SpecOpaque0Ff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ff<'a> {
    pub l: Uint0Ff,
    pub data: &'a [u8],
}
pub type Opaque0FfInner<'a> = (Uint0Ff, &'a [u8]);
impl View for Opaque0Ff<'_> {
    type V = SpecOpaque0Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ff<'a>> for Opaque0FfInner<'a> {
    fn ex_from(m: Opaque0Ff<'a>) -> Opaque0FfInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfInner<'a>> for Opaque0Ff<'a> {
    fn ex_from(m: Opaque0FfInner<'a>) -> Opaque0Ff<'a> {
        let (l, data) = m;
        Opaque0Ff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque0FfCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfCombinator, Bytes, Opaque0FfCont<'a>>, Opaque0FfMapper<'a>>;


pub closed spec fn spec_opaque_0_ff() -> SpecOpaque0FfCombinator {
    SpecOpaque0FfCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ff(),
            snd: |deps| spec_opaque0_ff_cont(deps),
        },
        mapper: Opaque0FfMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque0_ff_cont(deps: SpecUint0Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_0_ff<'a>() -> (o: Opaque0FfCombinator<'a>)
    ensures o@ == spec_opaque_0_ff(),
{
    Opaque0FfCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ff(),
            snd: Opaque0FfCont::new(),
            spec_snd: Ghost(|deps| spec_opaque0_ff_cont(deps)),
        },
        mapper: Opaque0FfMapper::new(),
    }
)
}


pub struct Opaque0FfCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfCont<'a> {
    pub fn new() -> Self {
        Opaque0FfCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ff> for Opaque0FfCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint0Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ff_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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
        SpecUseSrtpData {
            profiles,
            srtp_mki,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseSrtpData<'a> {
    pub profiles: SrtpProtectionProfiles<'a>,
    pub srtp_mki: Opaque0Ff<'a>,
}
pub type UseSrtpDataInner<'a> = (SrtpProtectionProfiles<'a>, Opaque0Ff<'a>);
impl View for UseSrtpData<'_> {
    type V = SpecUseSrtpData;
    open spec fn view(&self) -> Self::V {
        SpecUseSrtpData {
            profiles: self.profiles@,
            srtp_mki: self.srtp_mki@,
        }
    }
}
impl<'a> From<UseSrtpData<'a>> for UseSrtpDataInner<'a> {
    fn ex_from(m: UseSrtpData<'a>) -> UseSrtpDataInner<'a> {
        (m.profiles, m.srtp_mki)
    }
}
impl<'a> From<UseSrtpDataInner<'a>> for UseSrtpData<'a> {
    fn ex_from(m: UseSrtpDataInner<'a>) -> UseSrtpData<'a> {
        let (profiles, srtp_mki) = m;
        UseSrtpData {
            profiles,
            srtp_mki,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecUseSrtpDataCombinator(Mapped { inner: (spec_srtp_protection_profiles(), spec_opaque_0_ff()), mapper: UseSrtpDataMapper::spec_new() })
}


                
pub fn use_srtp_data<'a>() -> (o: UseSrtpDataCombinator<'a>)
    ensures o@ == spec_use_srtp_data(),
{
    UseSrtpDataCombinator(Mapped { inner: (srtp_protection_profiles(), opaque_0_ff()), mapper: UseSrtpDataMapper::new() })
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
        SpecOpaque1Ff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ff<'a> {
    pub l: Uint1Ff,
    pub data: &'a [u8],
}
pub type Opaque1FfInner<'a> = (Uint1Ff, &'a [u8]);
impl View for Opaque1Ff<'_> {
    type V = SpecOpaque1Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ff<'a>> for Opaque1FfInner<'a> {
    fn ex_from(m: Opaque1Ff<'a>) -> Opaque1FfInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfInner<'a>> for Opaque1Ff<'a> {
    fn ex_from(m: Opaque1FfInner<'a>) -> Opaque1Ff<'a> {
        let (l, data) = m;
        Opaque1Ff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque1FfCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, Bytes, Opaque1FfCont<'a>>, Opaque1FfMapper<'a>>;


pub closed spec fn spec_opaque_1_ff() -> SpecOpaque1FfCombinator {
    SpecOpaque1FfCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_opaque1_ff_cont(deps),
        },
        mapper: Opaque1FfMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque1_ff_cont(deps: SpecUint1Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_1_ff<'a>() -> (o: Opaque1FfCombinator<'a>)
    ensures o@ == spec_opaque_1_ff(),
{
    Opaque1FfCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: Opaque1FfCont::new(),
            spec_snd: Ghost(|deps| spec_opaque1_ff_cont(deps)),
        },
        mapper: Opaque1FfMapper::new(),
    }
)
}


pub struct Opaque1FfCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfCont<'a> {
    pub fn new() -> Self {
        Opaque1FfCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ff> for Opaque1FfCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ff_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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
        SpecProtocolNameList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolNameList<'a> {
    pub l: Uint2Ffff,
    pub list: ProtocolNameListList<'a>,
}
pub type ProtocolNameListInner<'a> = (Uint2Ffff, ProtocolNameListList<'a>);
impl View for ProtocolNameList<'_> {
    type V = SpecProtocolNameList;
    open spec fn view(&self) -> Self::V {
        SpecProtocolNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<ProtocolNameList<'a>> for ProtocolNameListInner<'a> {
    fn ex_from(m: ProtocolNameList<'a>) -> ProtocolNameListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<ProtocolNameListInner<'a>> for ProtocolNameList<'a> {
    fn ex_from(m: ProtocolNameListInner<'a>) -> ProtocolNameList<'a> {
        let (l, list) = m;
        ProtocolNameList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type ProtocolNameListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, ProtocolNameListListCombinator<'a>, ProtocolNameListCont<'a>>, ProtocolNameListMapper<'a>>;


pub closed spec fn spec_protocol_name_list() -> SpecProtocolNameListCombinator {
    SpecProtocolNameListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_protocol_name_list_cont(deps),
        },
        mapper: ProtocolNameListMapper::spec_new(),
    }
)
}


pub open spec fn spec_protocol_name_list_cont(deps: SpecUint2Ffff) -> SpecProtocolNameListListCombinator {
    let l = deps;
    spec_protocol_name_list_list(l)
}

                
pub fn protocol_name_list<'a>() -> (o: ProtocolNameListCombinator<'a>)
    ensures o@ == spec_protocol_name_list(),
{
    ProtocolNameListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: ProtocolNameListCont::new(),
            spec_snd: Ghost(|deps| spec_protocol_name_list_cont(deps)),
        },
        mapper: ProtocolNameListMapper::new(),
    }
)
}


pub struct ProtocolNameListCont<'a>(PhantomData<&'a ()>);
impl<'a> ProtocolNameListCont<'a> {
    pub fn new() -> Self {
        ProtocolNameListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Ffff> for ProtocolNameListCont<'a> {
    type Output = ProtocolNameListListCombinator<'a>;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_protocol_name_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        protocol_name_list_list(l)
    }
}

                
pub type SpecUint1Ffff = u16;
pub type Uint1Ffff = u16;

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
pub type SpecUint1FfffCombinatorAlias = Refined<U16Be, Predicate11955646336730306823>;
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
pub type Uint1FfffCombinatorAlias = Refined<U16Be, Predicate11955646336730306823>;


pub closed spec fn spec_uint_1_ffff() -> SpecUint1FfffCombinator {
    SpecUint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate11955646336730306823 })
}


                
pub fn uint_1_ffff() -> (o: Uint1FfffCombinator)
    ensures o@ == spec_uint_1_ffff(),
{
    Uint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate11955646336730306823 })
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
        SpecOpaque1Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ffff<'a> {
    pub l: Uint1Ffff,
    pub data: &'a [u8],
}
pub type Opaque1FfffInner<'a> = (Uint1Ffff, &'a [u8]);
impl View for Opaque1Ffff<'_> {
    type V = SpecOpaque1Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ffff<'a>> for Opaque1FfffInner<'a> {
    fn ex_from(m: Opaque1Ffff<'a>) -> Opaque1FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffInner<'a>> for Opaque1Ffff<'a> {
    fn ex_from(m: Opaque1FfffInner<'a>) -> Opaque1Ffff<'a> {
        let (l, data) = m;
        Opaque1Ffff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque1FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, Bytes, Opaque1FfffCont<'a>>, Opaque1FfffMapper<'a>>;


pub closed spec fn spec_opaque_1_ffff() -> SpecOpaque1FfffCombinator {
    SpecOpaque1FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_opaque1_ffff_cont(deps),
        },
        mapper: Opaque1FfffMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque1_ffff_cont(deps: SpecUint1Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_1_ffff<'a>() -> (o: Opaque1FfffCombinator<'a>)
    ensures o@ == spec_opaque_1_ffff(),
{
    Opaque1FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: Opaque1FfffCont::new(),
            spec_snd: Ghost(|deps| spec_opaque1_ffff_cont(deps)),
        },
        mapper: Opaque1FfffMapper::new(),
    }
)
}


pub struct Opaque1FfffCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque1FfffCont<'a> {
    pub fn new() -> Self {
        Opaque1FfffCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ffff> for Opaque1FfffCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
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
        SpecSignedCertificateTimestampList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedCertificateTimestampList<'a> {
    pub l: Uint1Ffff,
    pub list: SignedCertificateTimestampListList<'a>,
}
pub type SignedCertificateTimestampListInner<'a> = (Uint1Ffff, SignedCertificateTimestampListList<'a>);
impl View for SignedCertificateTimestampList<'_> {
    type V = SpecSignedCertificateTimestampList;
    open spec fn view(&self) -> Self::V {
        SpecSignedCertificateTimestampList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<SignedCertificateTimestampList<'a>> for SignedCertificateTimestampListInner<'a> {
    fn ex_from(m: SignedCertificateTimestampList<'a>) -> SignedCertificateTimestampListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<SignedCertificateTimestampListInner<'a>> for SignedCertificateTimestampList<'a> {
    fn ex_from(m: SignedCertificateTimestampListInner<'a>) -> SignedCertificateTimestampList<'a> {
        let (l, list) = m;
        SignedCertificateTimestampList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SignedCertificateTimestampListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, SignedCertificateTimestampListListCombinator<'a>, SignedCertificateTimestampListCont<'a>>, SignedCertificateTimestampListMapper<'a>>;


pub closed spec fn spec_signed_certificate_timestamp_list() -> SpecSignedCertificateTimestampListCombinator {
    SpecSignedCertificateTimestampListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_signed_certificate_timestamp_list_cont(deps),
        },
        mapper: SignedCertificateTimestampListMapper::spec_new(),
    }
)
}


pub open spec fn spec_signed_certificate_timestamp_list_cont(deps: SpecUint1Ffff) -> SpecSignedCertificateTimestampListListCombinator {
    let l = deps;
    spec_signed_certificate_timestamp_list_list(l)
}

                
pub fn signed_certificate_timestamp_list<'a>() -> (o: SignedCertificateTimestampListCombinator<'a>)
    ensures o@ == spec_signed_certificate_timestamp_list(),
{
    SignedCertificateTimestampListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: SignedCertificateTimestampListCont::new(),
            spec_snd: Ghost(|deps| spec_signed_certificate_timestamp_list_cont(deps)),
        },
        mapper: SignedCertificateTimestampListMapper::new(),
    }
)
}


pub struct SignedCertificateTimestampListCont<'a>(PhantomData<&'a ()>);
impl<'a> SignedCertificateTimestampListCont<'a> {
    pub fn new() -> Self {
        SignedCertificateTimestampListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ffff> for SignedCertificateTimestampListCont<'a> {
    type Output = SignedCertificateTimestampListListCombinator<'a>;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_signed_certificate_timestamp_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        signed_certificate_timestamp_list_list(l)
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


                
pub fn client_cert_type_client_extension_types(l: Uint1Ff) -> (o: ClientCertTypeClientExtensionTypesCombinator)
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
        SpecClientCertTypeClientExtension {
            l,
            types,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ClientCertTypeClientExtensionTypes,
}
pub type ClientCertTypeClientExtensionInner = (Uint1Ff, ClientCertTypeClientExtensionTypes);
impl View for ClientCertTypeClientExtension {
    type V = SpecClientCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ClientCertTypeClientExtension> for ClientCertTypeClientExtensionInner {
    fn ex_from(m: ClientCertTypeClientExtension) -> ClientCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ClientCertTypeClientExtensionInner> for ClientCertTypeClientExtension {
    fn ex_from(m: ClientCertTypeClientExtensionInner) -> ClientCertTypeClientExtension {
        let (l, types) = m;
        ClientCertTypeClientExtension {
            l,
            types,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type ClientCertTypeClientExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, ClientCertTypeClientExtensionTypesCombinator, ClientCertTypeClientExtensionCont<'a>>, ClientCertTypeClientExtensionMapper>;


pub closed spec fn spec_client_cert_type_client_extension() -> SpecClientCertTypeClientExtensionCombinator {
    SpecClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_client_cert_type_client_extension_cont(deps),
        },
        mapper: ClientCertTypeClientExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_client_cert_type_client_extension_cont(deps: SpecUint1Ff) -> SpecClientCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_client_cert_type_client_extension_types(l)
}

                
pub fn client_cert_type_client_extension<'a>() -> (o: ClientCertTypeClientExtensionCombinator<'a>)
    ensures o@ == spec_client_cert_type_client_extension(),
{
    ClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: ClientCertTypeClientExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_client_cert_type_client_extension_cont(deps)),
        },
        mapper: ClientCertTypeClientExtensionMapper::new(),
    }
)
}


pub struct ClientCertTypeClientExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> ClientCertTypeClientExtensionCont<'a> {
    pub fn new() -> Self {
        ClientCertTypeClientExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ff> for ClientCertTypeClientExtensionCont<'a> {
    type Output = ClientCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_client_cert_type_client_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        client_cert_type_client_extension_types(l)
    }
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


                
pub fn server_cert_type_client_extension_types(l: Uint1Ff) -> (o: ServerCertTypeClientExtensionTypesCombinator)
    ensures o@ == spec_server_cert_type_client_extension_types(l@),
{
    ServerCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_type())))
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
        SpecServerCertTypeClientExtension {
            l,
            types,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ServerCertTypeClientExtensionTypes,
}
pub type ServerCertTypeClientExtensionInner = (Uint1Ff, ServerCertTypeClientExtensionTypes);
impl View for ServerCertTypeClientExtension {
    type V = SpecServerCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ServerCertTypeClientExtension> for ServerCertTypeClientExtensionInner {
    fn ex_from(m: ServerCertTypeClientExtension) -> ServerCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ServerCertTypeClientExtensionInner> for ServerCertTypeClientExtension {
    fn ex_from(m: ServerCertTypeClientExtensionInner) -> ServerCertTypeClientExtension {
        let (l, types) = m;
        ServerCertTypeClientExtension {
            l,
            types,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type ServerCertTypeClientExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, ServerCertTypeClientExtensionTypesCombinator, ServerCertTypeClientExtensionCont<'a>>, ServerCertTypeClientExtensionMapper>;


pub closed spec fn spec_server_cert_type_client_extension() -> SpecServerCertTypeClientExtensionCombinator {
    SpecServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_server_cert_type_client_extension_cont(deps),
        },
        mapper: ServerCertTypeClientExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_server_cert_type_client_extension_cont(deps: SpecUint1Ff) -> SpecServerCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_server_cert_type_client_extension_types(l)
}

                
pub fn server_cert_type_client_extension<'a>() -> (o: ServerCertTypeClientExtensionCombinator<'a>)
    ensures o@ == spec_server_cert_type_client_extension(),
{
    ServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: ServerCertTypeClientExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_server_cert_type_client_extension_cont(deps)),
        },
        mapper: ServerCertTypeClientExtensionMapper::new(),
    }
)
}


pub struct ServerCertTypeClientExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> ServerCertTypeClientExtensionCont<'a> {
    pub fn new() -> Self {
        ServerCertTypeClientExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ff> for ServerCertTypeClientExtensionCont<'a> {
    type Output = ServerCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_server_cert_type_client_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        server_cert_type_client_extension_types(l)
    }
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
        SpecZeroByte {
            zero,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZeroByte {
    pub zero: u8,
}
pub type ZeroByteInner = u8;
impl View for ZeroByte {
    type V = SpecZeroByte;
    open spec fn view(&self) -> Self::V {
        SpecZeroByte {
            zero: self.zero@,
        }
    }
}
impl From<ZeroByte> for ZeroByteInner {
    fn ex_from(m: ZeroByte) -> ZeroByteInner {
        m.zero
    }
}
impl From<ZeroByteInner> for ZeroByte {
    fn ex_from(m: ZeroByteInner) -> ZeroByte {
        let zero = m;
        ZeroByte {
            zero,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecZeroByteCombinator(Mapped { inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) }, mapper: ZeroByteMapper::spec_new() })
}


                
pub fn zero_byte() -> (o: ZeroByteCombinator)
    ensures o@ == spec_zero_byte(),
{
    ZeroByteCombinator(Mapped { inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) }, mapper: ZeroByteMapper::new() })
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


                
pub fn padding_extension_padding(l: Uint0Ffff) -> (o: PaddingExtensionPaddingCombinator)
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
        SpecPaddingExtension {
            l,
            padding,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PaddingExtension {
    pub l: Uint0Ffff,
    pub padding: PaddingExtensionPadding,
}
pub type PaddingExtensionInner = (Uint0Ffff, PaddingExtensionPadding);
impl View for PaddingExtension {
    type V = SpecPaddingExtension;
    open spec fn view(&self) -> Self::V {
        SpecPaddingExtension {
            l: self.l@,
            padding: self.padding@,
        }
    }
}
impl From<PaddingExtension> for PaddingExtensionInner {
    fn ex_from(m: PaddingExtension) -> PaddingExtensionInner {
        (m.l, m.padding)
    }
}
impl From<PaddingExtensionInner> for PaddingExtension {
    fn ex_from(m: PaddingExtensionInner) -> PaddingExtension {
        let (l, padding) = m;
        PaddingExtension {
            l,
            padding,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type PaddingExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, PaddingExtensionPaddingCombinator, PaddingExtensionCont<'a>>, PaddingExtensionMapper>;


pub closed spec fn spec_padding_extension() -> SpecPaddingExtensionCombinator {
    SpecPaddingExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_padding_extension_cont(deps),
        },
        mapper: PaddingExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_padding_extension_cont(deps: SpecUint0Ffff) -> SpecPaddingExtensionPaddingCombinator {
    let l = deps;
    spec_padding_extension_padding(l)
}

                
pub fn padding_extension<'a>() -> (o: PaddingExtensionCombinator<'a>)
    ensures o@ == spec_padding_extension(),
{
    PaddingExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: PaddingExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_padding_extension_cont(deps)),
        },
        mapper: PaddingExtensionMapper::new(),
    }
)
}


pub struct PaddingExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> PaddingExtensionCont<'a> {
    pub fn new() -> Self {
        PaddingExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for PaddingExtensionCont<'a> {
    type Output = PaddingExtensionPaddingCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_padding_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        padding_extension_padding(l)
    }
}

                
pub type SpecSessionTicket = SpecOpaque0Ffff;
pub type SessionTicket<'a> = Opaque0Ffff<'a>;


pub struct SpecSessionTicketCombinator(SpecSessionTicketCombinatorAlias);

impl SpecCombinator for SpecSessionTicketCombinator {
    type SpecResult = SpecSessionTicket;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSessionTicketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSessionTicketCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct SessionTicketCombinator<'a>(SessionTicketCombinatorAlias<'a>);

impl<'a> View for SessionTicketCombinator<'a> {
    type V = SpecSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecSessionTicketCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for SessionTicketCombinator<'a> {
    type Result = SessionTicket<'a>;
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
pub type SessionTicketCombinatorAlias<'a> = Opaque0FfffCombinator<'a>;


pub closed spec fn spec_session_ticket() -> SpecSessionTicketCombinator {
    SpecSessionTicketCombinator(spec_opaque_0_ffff())
}


                
pub fn session_ticket<'a>() -> (o: SessionTicketCombinator<'a>)
    ensures o@ == spec_session_ticket(),
{
    SessionTicketCombinator(opaque_0_ffff())
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
        SpecPskIdentity {
            identity,
            obfuscated_ticket_age,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskIdentity<'a> {
    pub identity: Opaque1Ffff<'a>,
    pub obfuscated_ticket_age: u32,
}
pub type PskIdentityInner<'a> = (Opaque1Ffff<'a>, u32);
impl View for PskIdentity<'_> {
    type V = SpecPskIdentity;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentity {
            identity: self.identity@,
            obfuscated_ticket_age: self.obfuscated_ticket_age@,
        }
    }
}
impl<'a> From<PskIdentity<'a>> for PskIdentityInner<'a> {
    fn ex_from(m: PskIdentity<'a>) -> PskIdentityInner<'a> {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl<'a> From<PskIdentityInner<'a>> for PskIdentity<'a> {
    fn ex_from(m: PskIdentityInner<'a>) -> PskIdentity<'a> {
        let (identity, obfuscated_ticket_age) = m;
        PskIdentity {
            identity,
            obfuscated_ticket_age,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecPskIdentityCombinator(Mapped { inner: (spec_opaque_1_ffff(), U32Be), mapper: PskIdentityMapper::spec_new() })
}


                
pub fn psk_identity<'a>() -> (o: PskIdentityCombinator<'a>)
    ensures o@ == spec_psk_identity(),
{
    PskIdentityCombinator(Mapped { inner: (opaque_1_ffff(), U32Be), mapper: PskIdentityMapper::new() })
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
        SpecPskIdentities {
            l,
            identities,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskIdentities<'a> {
    pub l: u16,
    pub identities: PskIdentitiesIdentities<'a>,
}
pub type PskIdentitiesInner<'a> = (u16, PskIdentitiesIdentities<'a>);
impl View for PskIdentities<'_> {
    type V = SpecPskIdentities;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentities {
            l: self.l@,
            identities: self.identities@,
        }
    }
}
impl<'a> From<PskIdentities<'a>> for PskIdentitiesInner<'a> {
    fn ex_from(m: PskIdentities<'a>) -> PskIdentitiesInner<'a> {
        (m.l, m.identities)
    }
}
impl<'a> From<PskIdentitiesInner<'a>> for PskIdentities<'a> {
    fn ex_from(m: PskIdentitiesInner<'a>) -> PskIdentities<'a> {
        let (l, identities) = m;
        PskIdentities {
            l,
            identities,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for PskIdentitiesMapper<'a> {
    type Src = PskIdentitiesInner<'a>;
    type Dst = PskIdentities<'a>;
}
    
impl SpecPred for Predicate17762240283561303569 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 7 && i <= 65535) {
            true
        } else {
            false
        }
    }
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
pub type SpecPskIdentitiesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate17762240283561303569>, SpecPskIdentitiesIdentitiesCombinator>, PskIdentitiesMapper<'static>>;
pub struct Predicate17762240283561303569;
impl View for Predicate17762240283561303569 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17762240283561303569 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 7 && i <= 65535) {
            true
        } else {
            false
        }
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
pub type PskIdentitiesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate17762240283561303569>, PskIdentitiesIdentitiesCombinator<'a>, PskIdentitiesCont<'a>>, PskIdentitiesMapper<'a>>;


pub closed spec fn spec_psk_identities() -> SpecPskIdentitiesCombinator {
    SpecPskIdentitiesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate17762240283561303569 },
            snd: |deps| spec_psk_identities_cont(deps),
        },
        mapper: PskIdentitiesMapper::spec_new(),
    }
)
}


pub open spec fn spec_psk_identities_cont(deps: u16) -> SpecPskIdentitiesIdentitiesCombinator {
    let l = deps;
    spec_psk_identities_identities(l)
}

                
pub fn psk_identities<'a>() -> (o: PskIdentitiesCombinator<'a>)
    ensures o@ == spec_psk_identities(),
{
    PskIdentitiesCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate17762240283561303569 },
            snd: PskIdentitiesCont::new(),
            spec_snd: Ghost(|deps| spec_psk_identities_cont(deps)),
        },
        mapper: PskIdentitiesMapper::new(),
    }
)
}


pub struct PskIdentitiesCont<'a>(PhantomData<&'a ()>);
impl<'a> PskIdentitiesCont<'a> {
    pub fn new() -> Self {
        PskIdentitiesCont(PhantomData)
    }
}
impl<'a> Continuation<u16> for PskIdentitiesCont<'a> {
    type Output = PskIdentitiesIdentitiesCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_psk_identities_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        psk_identities_identities(l)
    }
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
        SpecPskBinderEntry {
            l,
            entries,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskBinderEntry<'a> {
    pub l: u8,
    pub entries: &'a [u8],
}
pub type PskBinderEntryInner<'a> = (u8, &'a [u8]);
impl View for PskBinderEntry<'_> {
    type V = SpecPskBinderEntry;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntry {
            l: self.l@,
            entries: self.entries@,
        }
    }
}
impl<'a> From<PskBinderEntry<'a>> for PskBinderEntryInner<'a> {
    fn ex_from(m: PskBinderEntry<'a>) -> PskBinderEntryInner<'a> {
        (m.l, m.entries)
    }
}
impl<'a> From<PskBinderEntryInner<'a>> for PskBinderEntry<'a> {
    fn ex_from(m: PskBinderEntryInner<'a>) -> PskBinderEntry<'a> {
        let (l, entries) = m;
        PskBinderEntry {
            l,
            entries,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for PskBinderEntryMapper<'a> {
    type Src = PskBinderEntryInner<'a>;
    type Dst = PskBinderEntry<'a>;
}
    
impl SpecPred for Predicate14956021864372697443 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 32 && i <= 255) {
            true
        } else {
            false
        }
    }
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
pub type SpecPskBinderEntryCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate14956021864372697443>, Bytes>, PskBinderEntryMapper<'static>>;
pub struct Predicate14956021864372697443;
impl View for Predicate14956021864372697443 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14956021864372697443 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 32 && i <= 255) {
            true
        } else {
            false
        }
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
pub type PskBinderEntryCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate14956021864372697443>, Bytes, PskBinderEntryCont<'a>>, PskBinderEntryMapper<'a>>;


pub closed spec fn spec_psk_binder_entry() -> SpecPskBinderEntryCombinator {
    SpecPskBinderEntryCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate14956021864372697443 },
            snd: |deps| spec_psk_binder_entry_cont(deps),
        },
        mapper: PskBinderEntryMapper::spec_new(),
    }
)
}


pub open spec fn spec_psk_binder_entry_cont(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn psk_binder_entry<'a>() -> (o: PskBinderEntryCombinator<'a>)
    ensures o@ == spec_psk_binder_entry(),
{
    PskBinderEntryCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate14956021864372697443 },
            snd: PskBinderEntryCont::new(),
            spec_snd: Ghost(|deps| spec_psk_binder_entry_cont(deps)),
        },
        mapper: PskBinderEntryMapper::new(),
    }
)
}


pub struct PskBinderEntryCont<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntryCont<'a> {
    pub fn new() -> Self {
        PskBinderEntryCont(PhantomData)
    }
}
impl<'a> Continuation<u8> for PskBinderEntryCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entry_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
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
        SpecPskBinderEntries {
            l,
            binders,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskBinderEntries<'a> {
    pub l: u16,
    pub binders: PskBinderEntriesBinders<'a>,
}
pub type PskBinderEntriesInner<'a> = (u16, PskBinderEntriesBinders<'a>);
impl View for PskBinderEntries<'_> {
    type V = SpecPskBinderEntries;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntries {
            l: self.l@,
            binders: self.binders@,
        }
    }
}
impl<'a> From<PskBinderEntries<'a>> for PskBinderEntriesInner<'a> {
    fn ex_from(m: PskBinderEntries<'a>) -> PskBinderEntriesInner<'a> {
        (m.l, m.binders)
    }
}
impl<'a> From<PskBinderEntriesInner<'a>> for PskBinderEntries<'a> {
    fn ex_from(m: PskBinderEntriesInner<'a>) -> PskBinderEntries<'a> {
        let (l, binders) = m;
        PskBinderEntries {
            l,
            binders,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for PskBinderEntriesMapper<'a> {
    type Src = PskBinderEntriesInner<'a>;
    type Dst = PskBinderEntries<'a>;
}
    
impl SpecPred for Predicate14504484746533333987 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 33 && i <= 65535) {
            true
        } else {
            false
        }
    }
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
pub type SpecPskBinderEntriesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate14504484746533333987>, SpecPskBinderEntriesBindersCombinator>, PskBinderEntriesMapper<'static>>;
pub struct Predicate14504484746533333987;
impl View for Predicate14504484746533333987 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14504484746533333987 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 33 && i <= 65535) {
            true
        } else {
            false
        }
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
pub type PskBinderEntriesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate14504484746533333987>, PskBinderEntriesBindersCombinator<'a>, PskBinderEntriesCont<'a>>, PskBinderEntriesMapper<'a>>;


pub closed spec fn spec_psk_binder_entries() -> SpecPskBinderEntriesCombinator {
    SpecPskBinderEntriesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate14504484746533333987 },
            snd: |deps| spec_psk_binder_entries_cont(deps),
        },
        mapper: PskBinderEntriesMapper::spec_new(),
    }
)
}


pub open spec fn spec_psk_binder_entries_cont(deps: u16) -> SpecPskBinderEntriesBindersCombinator {
    let l = deps;
    spec_psk_binder_entries_binders(l)
}

                
pub fn psk_binder_entries<'a>() -> (o: PskBinderEntriesCombinator<'a>)
    ensures o@ == spec_psk_binder_entries(),
{
    PskBinderEntriesCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate14504484746533333987 },
            snd: PskBinderEntriesCont::new(),
            spec_snd: Ghost(|deps| spec_psk_binder_entries_cont(deps)),
        },
        mapper: PskBinderEntriesMapper::new(),
    }
)
}


pub struct PskBinderEntriesCont<'a>(PhantomData<&'a ()>);
impl<'a> PskBinderEntriesCont<'a> {
    pub fn new() -> Self {
        PskBinderEntriesCont(PhantomData)
    }
}
impl<'a> Continuation<u16> for PskBinderEntriesCont<'a> {
    type Output = PskBinderEntriesBindersCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entries_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
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
        SpecOfferedPsks {
            identities,
            binders,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OfferedPsks<'a> {
    pub identities: PskIdentities<'a>,
    pub binders: PskBinderEntries<'a>,
}
pub type OfferedPsksInner<'a> = (PskIdentities<'a>, PskBinderEntries<'a>);
impl View for OfferedPsks<'_> {
    type V = SpecOfferedPsks;
    open spec fn view(&self) -> Self::V {
        SpecOfferedPsks {
            identities: self.identities@,
            binders: self.binders@,
        }
    }
}
impl<'a> From<OfferedPsks<'a>> for OfferedPsksInner<'a> {
    fn ex_from(m: OfferedPsks<'a>) -> OfferedPsksInner<'a> {
        (m.identities, m.binders)
    }
}
impl<'a> From<OfferedPsksInner<'a>> for OfferedPsks<'a> {
    fn ex_from(m: OfferedPsksInner<'a>) -> OfferedPsks<'a> {
        let (identities, binders) = m;
        OfferedPsks {
            identities,
            binders,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecOfferedPsksCombinator(Mapped { inner: (spec_psk_identities(), spec_psk_binder_entries()), mapper: OfferedPsksMapper::spec_new() })
}


                
pub fn offered_psks<'a>() -> (o: OfferedPsksCombinator<'a>)
    ensures o@ == spec_offered_psks(),
{
    OfferedPsksCombinator(Mapped { inner: (psk_identities(), psk_binder_entries()), mapper: OfferedPsksMapper::new() })
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
        SpecPreSharedKeyClientExtension {
            offers,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreSharedKeyClientExtension<'a> {
    pub offers: OfferedPsks<'a>,
}
pub type PreSharedKeyClientExtensionInner<'a> = OfferedPsks<'a>;
impl View for PreSharedKeyClientExtension<'_> {
    type V = SpecPreSharedKeyClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyClientExtension {
            offers: self.offers@,
        }
    }
}
impl<'a> From<PreSharedKeyClientExtension<'a>> for PreSharedKeyClientExtensionInner<'a> {
    fn ex_from(m: PreSharedKeyClientExtension<'a>) -> PreSharedKeyClientExtensionInner<'a> {
        m.offers
    }
}
impl<'a> From<PreSharedKeyClientExtensionInner<'a>> for PreSharedKeyClientExtension<'a> {
    fn ex_from(m: PreSharedKeyClientExtensionInner<'a>) -> PreSharedKeyClientExtension<'a> {
        let offers = m;
        PreSharedKeyClientExtension {
            offers,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecPreSharedKeyClientExtensionCombinator(Mapped { inner: spec_offered_psks(), mapper: PreSharedKeyClientExtensionMapper::spec_new() })
}


                
pub fn pre_shared_key_client_extension<'a>() -> (o: PreSharedKeyClientExtensionCombinator<'a>)
    ensures o@ == spec_pre_shared_key_client_extension(),
{
    PreSharedKeyClientExtensionCombinator(Mapped { inner: offered_psks(), mapper: PreSharedKeyClientExtensionMapper::new() })
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


                
pub fn supported_versions_client_versions(l: u8) -> (o: SupportedVersionsClientVersionsCombinator)
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
        SpecSupportedVersionsClient {
            l,
            versions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupportedVersionsClient {
    pub l: u8,
    pub versions: SupportedVersionsClientVersions,
}
pub type SupportedVersionsClientInner = (u8, SupportedVersionsClientVersions);
impl View for SupportedVersionsClient {
    type V = SpecSupportedVersionsClient;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsClient {
            l: self.l@,
            versions: self.versions@,
        }
    }
}
impl From<SupportedVersionsClient> for SupportedVersionsClientInner {
    fn ex_from(m: SupportedVersionsClient) -> SupportedVersionsClientInner {
        (m.l, m.versions)
    }
}
impl From<SupportedVersionsClientInner> for SupportedVersionsClient {
    fn ex_from(m: SupportedVersionsClientInner) -> SupportedVersionsClient {
        let (l, versions) = m;
        SupportedVersionsClient {
            l,
            versions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SupportedVersionsClientMapper {
    type Src = SupportedVersionsClientInner;
    type Dst = SupportedVersionsClient;
}
    
impl SpecPred for Predicate12026843412570934212 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 254) {
            true
        } else {
            false
        }
    }
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
pub type SpecSupportedVersionsClientCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate12026843412570934212>, SpecSupportedVersionsClientVersionsCombinator>, SupportedVersionsClientMapper>;
pub struct Predicate12026843412570934212;
impl View for Predicate12026843412570934212 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate12026843412570934212 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 254) {
            true
        } else {
            false
        }
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
pub type SupportedVersionsClientCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate12026843412570934212>, SupportedVersionsClientVersionsCombinator, SupportedVersionsClientCont<'a>>, SupportedVersionsClientMapper>;


pub closed spec fn spec_supported_versions_client() -> SpecSupportedVersionsClientCombinator {
    SpecSupportedVersionsClientCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate12026843412570934212 },
            snd: |deps| spec_supported_versions_client_cont(deps),
        },
        mapper: SupportedVersionsClientMapper::spec_new(),
    }
)
}


pub open spec fn spec_supported_versions_client_cont(deps: u8) -> SpecSupportedVersionsClientVersionsCombinator {
    let l = deps;
    spec_supported_versions_client_versions(l)
}

                
pub fn supported_versions_client<'a>() -> (o: SupportedVersionsClientCombinator<'a>)
    ensures o@ == spec_supported_versions_client(),
{
    SupportedVersionsClientCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate12026843412570934212 },
            snd: SupportedVersionsClientCont::new(),
            spec_snd: Ghost(|deps| spec_supported_versions_client_cont(deps)),
        },
        mapper: SupportedVersionsClientMapper::new(),
    }
)
}


pub struct SupportedVersionsClientCont<'a>(PhantomData<&'a ()>);
impl<'a> SupportedVersionsClientCont<'a> {
    pub fn new() -> Self {
        SupportedVersionsClientCont(PhantomData)
    }
}
impl<'a> Continuation<u8> for SupportedVersionsClientCont<'a> {
    type Output = SupportedVersionsClientVersionsCombinator;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_supported_versions_client_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
        supported_versions_client_versions(l)
    }
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


                
pub fn psk_key_exchange_modes_modes(l: Uint1Ff) -> (o: PskKeyExchangeModesModesCombinator)
    ensures o@ == spec_psk_key_exchange_modes_modes(l@),
{
    PskKeyExchangeModesModesCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_key_exchange_mode())))
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
        SpecPskKeyExchangeModes {
            l,
            modes,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskKeyExchangeModes {
    pub l: Uint1Ff,
    pub modes: PskKeyExchangeModesModes,
}
pub type PskKeyExchangeModesInner = (Uint1Ff, PskKeyExchangeModesModes);
impl View for PskKeyExchangeModes {
    type V = SpecPskKeyExchangeModes;
    open spec fn view(&self) -> Self::V {
        SpecPskKeyExchangeModes {
            l: self.l@,
            modes: self.modes@,
        }
    }
}
impl From<PskKeyExchangeModes> for PskKeyExchangeModesInner {
    fn ex_from(m: PskKeyExchangeModes) -> PskKeyExchangeModesInner {
        (m.l, m.modes)
    }
}
impl From<PskKeyExchangeModesInner> for PskKeyExchangeModes {
    fn ex_from(m: PskKeyExchangeModesInner) -> PskKeyExchangeModes {
        let (l, modes) = m;
        PskKeyExchangeModes {
            l,
            modes,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type PskKeyExchangeModesCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfCombinator, PskKeyExchangeModesModesCombinator, PskKeyExchangeModesCont<'a>>, PskKeyExchangeModesMapper>;


pub closed spec fn spec_psk_key_exchange_modes() -> SpecPskKeyExchangeModesCombinator {
    SpecPskKeyExchangeModesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_psk_key_exchange_modes_cont(deps),
        },
        mapper: PskKeyExchangeModesMapper::spec_new(),
    }
)
}


pub open spec fn spec_psk_key_exchange_modes_cont(deps: SpecUint1Ff) -> SpecPskKeyExchangeModesModesCombinator {
    let l = deps;
    spec_psk_key_exchange_modes_modes(l)
}

                
pub fn psk_key_exchange_modes<'a>() -> (o: PskKeyExchangeModesCombinator<'a>)
    ensures o@ == spec_psk_key_exchange_modes(),
{
    PskKeyExchangeModesCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: PskKeyExchangeModesCont::new(),
            spec_snd: Ghost(|deps| spec_psk_key_exchange_modes_cont(deps)),
        },
        mapper: PskKeyExchangeModesMapper::new(),
    }
)
}


pub struct PskKeyExchangeModesCont<'a>(PhantomData<&'a ()>);
impl<'a> PskKeyExchangeModesCont<'a> {
    pub fn new() -> Self {
        PskKeyExchangeModesCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ff> for PskKeyExchangeModesCont<'a> {
    type Output = PskKeyExchangeModesModesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_psk_key_exchange_modes_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        psk_key_exchange_modes_modes(l)
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
        SpecCertificateAuthoritiesExtension {
            l,
            authorities,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateAuthoritiesExtension<'a> {
    pub l: u16,
    pub authorities: CertificateAuthoritiesExtensionAuthorities<'a>,
}
pub type CertificateAuthoritiesExtensionInner<'a> = (u16, CertificateAuthoritiesExtensionAuthorities<'a>);
impl View for CertificateAuthoritiesExtension<'_> {
    type V = SpecCertificateAuthoritiesExtension;
    open spec fn view(&self) -> Self::V {
        SpecCertificateAuthoritiesExtension {
            l: self.l@,
            authorities: self.authorities@,
        }
    }
}
impl<'a> From<CertificateAuthoritiesExtension<'a>> for CertificateAuthoritiesExtensionInner<'a> {
    fn ex_from(m: CertificateAuthoritiesExtension<'a>) -> CertificateAuthoritiesExtensionInner<'a> {
        (m.l, m.authorities)
    }
}
impl<'a> From<CertificateAuthoritiesExtensionInner<'a>> for CertificateAuthoritiesExtension<'a> {
    fn ex_from(m: CertificateAuthoritiesExtensionInner<'a>) -> CertificateAuthoritiesExtension<'a> {
        let (l, authorities) = m;
        CertificateAuthoritiesExtension {
            l,
            authorities,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for CertificateAuthoritiesExtensionMapper<'a> {
    type Src = CertificateAuthoritiesExtensionInner<'a>;
    type Dst = CertificateAuthoritiesExtension<'a>;
}
    
impl SpecPred for Predicate17709910934222271310 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 3 && i <= 65535) {
            true
        } else {
            false
        }
    }
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
pub type SpecCertificateAuthoritiesExtensionCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate17709910934222271310>, SpecCertificateAuthoritiesExtensionAuthoritiesCombinator>, CertificateAuthoritiesExtensionMapper<'static>>;
pub struct Predicate17709910934222271310;
impl View for Predicate17709910934222271310 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17709910934222271310 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 3 && i <= 65535) {
            true
        } else {
            false
        }
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
pub type CertificateAuthoritiesExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate17709910934222271310>, CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>, CertificateAuthoritiesExtensionCont<'a>>, CertificateAuthoritiesExtensionMapper<'a>>;


pub closed spec fn spec_certificate_authorities_extension() -> SpecCertificateAuthoritiesExtensionCombinator {
    SpecCertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate17709910934222271310 },
            snd: |deps| spec_certificate_authorities_extension_cont(deps),
        },
        mapper: CertificateAuthoritiesExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_certificate_authorities_extension_cont(deps: u16) -> SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    let l = deps;
    spec_certificate_authorities_extension_authorities(l)
}

                
pub fn certificate_authorities_extension<'a>() -> (o: CertificateAuthoritiesExtensionCombinator<'a>)
    ensures o@ == spec_certificate_authorities_extension(),
{
    CertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate17709910934222271310 },
            snd: CertificateAuthoritiesExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_certificate_authorities_extension_cont(deps)),
        },
        mapper: CertificateAuthoritiesExtensionMapper::new(),
    }
)
}


pub struct CertificateAuthoritiesExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> CertificateAuthoritiesExtensionCont<'a> {
    pub fn new() -> Self {
        CertificateAuthoritiesExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<u16> for CertificateAuthoritiesExtensionCont<'a> {
    type Output = CertificateAuthoritiesExtensionAuthoritiesCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_certificate_authorities_extension_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        certificate_authorities_extension_authorities(l)
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
        SpecOidFilter {
            certificate_extension_oid,
            certificate_extension_values,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OidFilter<'a> {
    pub certificate_extension_oid: Opaque1Ff<'a>,
    pub certificate_extension_values: Opaque0Ffff<'a>,
}
pub type OidFilterInner<'a> = (Opaque1Ff<'a>, Opaque0Ffff<'a>);
impl View for OidFilter<'_> {
    type V = SpecOidFilter;
    open spec fn view(&self) -> Self::V {
        SpecOidFilter {
            certificate_extension_oid: self.certificate_extension_oid@,
            certificate_extension_values: self.certificate_extension_values@,
        }
    }
}
impl<'a> From<OidFilter<'a>> for OidFilterInner<'a> {
    fn ex_from(m: OidFilter<'a>) -> OidFilterInner<'a> {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl<'a> From<OidFilterInner<'a>> for OidFilter<'a> {
    fn ex_from(m: OidFilterInner<'a>) -> OidFilter<'a> {
        let (certificate_extension_oid, certificate_extension_values) = m;
        OidFilter {
            certificate_extension_oid,
            certificate_extension_values,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecOidFilterCombinator(Mapped { inner: (spec_opaque_1_ff(), spec_opaque_0_ffff()), mapper: OidFilterMapper::spec_new() })
}


                
pub fn oid_filter<'a>() -> (o: OidFilterCombinator<'a>)
    ensures o@ == spec_oid_filter(),
{
    OidFilterCombinator(Mapped { inner: (opaque_1_ff(), opaque_0_ffff()), mapper: OidFilterMapper::new() })
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
        SpecOidFilterExtension {
            l,
            filters,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OidFilterExtension<'a> {
    pub l: Uint0Ffff,
    pub filters: OidFilterExtensionFilters<'a>,
}
pub type OidFilterExtensionInner<'a> = (Uint0Ffff, OidFilterExtensionFilters<'a>);
impl View for OidFilterExtension<'_> {
    type V = SpecOidFilterExtension;
    open spec fn view(&self) -> Self::V {
        SpecOidFilterExtension {
            l: self.l@,
            filters: self.filters@,
        }
    }
}
impl<'a> From<OidFilterExtension<'a>> for OidFilterExtensionInner<'a> {
    fn ex_from(m: OidFilterExtension<'a>) -> OidFilterExtensionInner<'a> {
        (m.l, m.filters)
    }
}
impl<'a> From<OidFilterExtensionInner<'a>> for OidFilterExtension<'a> {
    fn ex_from(m: OidFilterExtensionInner<'a>) -> OidFilterExtension<'a> {
        let (l, filters) = m;
        OidFilterExtension {
            l,
            filters,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type OidFilterExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, OidFilterExtensionFiltersCombinator<'a>, OidFilterExtensionCont<'a>>, OidFilterExtensionMapper<'a>>;


pub closed spec fn spec_oid_filter_extension() -> SpecOidFilterExtensionCombinator {
    SpecOidFilterExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_oid_filter_extension_cont(deps),
        },
        mapper: OidFilterExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_oid_filter_extension_cont(deps: SpecUint0Ffff) -> SpecOidFilterExtensionFiltersCombinator {
    let l = deps;
    spec_oid_filter_extension_filters(l)
}

                
pub fn oid_filter_extension<'a>() -> (o: OidFilterExtensionCombinator<'a>)
    ensures o@ == spec_oid_filter_extension(),
{
    OidFilterExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: OidFilterExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_oid_filter_extension_cont(deps)),
        },
        mapper: OidFilterExtensionMapper::new(),
    }
)
}


pub struct OidFilterExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> OidFilterExtensionCont<'a> {
    pub fn new() -> Self {
        OidFilterExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for OidFilterExtensionCont<'a> {
    type Output = OidFilterExtensionFiltersCombinator<'a>;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_oid_filter_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        oid_filter_extension_filters(l)
    }
}

                
pub type SpecUint2Fffe = u16;
pub type Uint2Fffe = u16;

impl SpecPred for Predicate13238841935489611399 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

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
pub type SpecUint2FffeCombinatorAlias = Refined<U16Be, Predicate13238841935489611399>;
pub struct Predicate13238841935489611399;
impl View for Predicate13238841935489611399 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate13238841935489611399 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65534) {
            true
        } else {
            false
        }
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
pub type Uint2FffeCombinatorAlias = Refined<U16Be, Predicate13238841935489611399>;


pub closed spec fn spec_uint_2_fffe() -> SpecUint2FffeCombinator {
    SpecUint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate13238841935489611399 })
}


                
pub fn uint_2_fffe() -> (o: Uint2FffeCombinator)
    ensures o@ == spec_uint_2_fffe(),
{
    Uint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate13238841935489611399 })
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


                
pub fn signature_scheme_list_list(l: Uint2Fffe) -> (o: SignatureSchemeListListCombinator)
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
        SpecSignatureSchemeList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureSchemeList {
    pub l: Uint2Fffe,
    pub list: SignatureSchemeListList,
}
pub type SignatureSchemeListInner = (Uint2Fffe, SignatureSchemeListList);
impl View for SignatureSchemeList {
    type V = SpecSignatureSchemeList;
    open spec fn view(&self) -> Self::V {
        SpecSignatureSchemeList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<SignatureSchemeList> for SignatureSchemeListInner {
    fn ex_from(m: SignatureSchemeList) -> SignatureSchemeListInner {
        (m.l, m.list)
    }
}
impl From<SignatureSchemeListInner> for SignatureSchemeList {
    fn ex_from(m: SignatureSchemeListInner) -> SignatureSchemeList {
        let (l, list) = m;
        SignatureSchemeList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SignatureSchemeListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FffeCombinator, SignatureSchemeListListCombinator, SignatureSchemeListCont<'a>>, SignatureSchemeListMapper>;


pub closed spec fn spec_signature_scheme_list() -> SpecSignatureSchemeListCombinator {
    SpecSignatureSchemeListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_fffe(),
            snd: |deps| spec_signature_scheme_list_cont(deps),
        },
        mapper: SignatureSchemeListMapper::spec_new(),
    }
)
}


pub open spec fn spec_signature_scheme_list_cont(deps: SpecUint2Fffe) -> SpecSignatureSchemeListListCombinator {
    let l = deps;
    spec_signature_scheme_list_list(l)
}

                
pub fn signature_scheme_list<'a>() -> (o: SignatureSchemeListCombinator<'a>)
    ensures o@ == spec_signature_scheme_list(),
{
    SignatureSchemeListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_fffe(),
            snd: SignatureSchemeListCont::new(),
            spec_snd: Ghost(|deps| spec_signature_scheme_list_cont(deps)),
        },
        mapper: SignatureSchemeListMapper::new(),
    }
)
}


pub struct SignatureSchemeListCont<'a>(PhantomData<&'a ()>);
impl<'a> SignatureSchemeListCont<'a> {
    pub fn new() -> Self {
        SignatureSchemeListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Fffe> for SignatureSchemeListCont<'a> {
    type Output = SignatureSchemeListListCombinator;

    open spec fn requires(&self, deps: Uint2Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_signature_scheme_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Fffe) -> Self::Output {
        let l = deps;
        signature_scheme_list_list(l)
    }
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
        SpecUncompressedPointRepresentation32 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation32<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation32Inner<'a> = (u8, (&'a [u8], &'a [u8]));
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
impl<'a> From<UncompressedPointRepresentation32<'a>> for UncompressedPointRepresentation32Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation32<'a>) -> UncompressedPointRepresentation32Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation32Inner<'a>> for UncompressedPointRepresentation32<'a> {
    fn ex_from(m: UncompressedPointRepresentation32Inner<'a>) -> UncompressedPointRepresentation32<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation32 {
            legacy_form,
            x,
            y,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecUncompressedPointRepresentation32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)), mapper: UncompressedPointRepresentation32Mapper::spec_new() })
}


                
pub fn uncompressed_point_representation32<'a>() -> (o: UncompressedPointRepresentation32Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation32(),
{
    UncompressedPointRepresentation32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)), mapper: UncompressedPointRepresentation32Mapper::new() })
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
        SpecUncompressedPointRepresentation48 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation48<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation48Inner<'a> = (u8, (&'a [u8], &'a [u8]));
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
impl<'a> From<UncompressedPointRepresentation48<'a>> for UncompressedPointRepresentation48Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation48<'a>) -> UncompressedPointRepresentation48Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation48Inner<'a>> for UncompressedPointRepresentation48<'a> {
    fn ex_from(m: UncompressedPointRepresentation48Inner<'a>) -> UncompressedPointRepresentation48<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation48 {
            legacy_form,
            x,
            y,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecUncompressedPointRepresentation48Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)), mapper: UncompressedPointRepresentation48Mapper::spec_new() })
}


                
pub fn uncompressed_point_representation48<'a>() -> (o: UncompressedPointRepresentation48Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation48(),
{
    UncompressedPointRepresentation48Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)), mapper: UncompressedPointRepresentation48Mapper::new() })
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
        SpecUncompressedPointRepresentation66 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation66<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation66Inner<'a> = (u8, (&'a [u8], &'a [u8]));
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
impl<'a> From<UncompressedPointRepresentation66<'a>> for UncompressedPointRepresentation66Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation66<'a>) -> UncompressedPointRepresentation66Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation66Inner<'a>> for UncompressedPointRepresentation66<'a> {
    fn ex_from(m: UncompressedPointRepresentation66Inner<'a>) -> UncompressedPointRepresentation66<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation66 {
            legacy_form,
            x,
            y,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecUncompressedPointRepresentation66Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)), mapper: UncompressedPointRepresentation66Mapper::spec_new() })
}


                
pub fn uncompressed_point_representation66<'a>() -> (o: UncompressedPointRepresentation66Combinator<'a>)
    ensures o@ == spec_uncompressed_point_representation66(),
{
    UncompressedPointRepresentation66Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)), mapper: UncompressedPointRepresentation66Mapper::new() })
}


                
pub struct SpecMontgomeryPoint32 {
    pub legacy_form: u8,
    pub point: Seq<u8>,
}
pub type SpecMontgomeryPoint32Inner = (u8, Seq<u8>);
impl SpecFrom<SpecMontgomeryPoint32> for SpecMontgomeryPoint32Inner {
    open spec fn spec_from(m: SpecMontgomeryPoint32) -> SpecMontgomeryPoint32Inner {
        (m.legacy_form, m.point)
    }
}
impl SpecFrom<SpecMontgomeryPoint32Inner> for SpecMontgomeryPoint32 {
    open spec fn spec_from(m: SpecMontgomeryPoint32Inner) -> SpecMontgomeryPoint32 {
        let (legacy_form, point) = m;
        SpecMontgomeryPoint32 {
            legacy_form,
            point,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MontgomeryPoint32<'a> {
    pub legacy_form: u8,
    pub point: &'a [u8],
}
pub type MontgomeryPoint32Inner<'a> = (u8, &'a [u8]);
impl View for MontgomeryPoint32<'_> {
    type V = SpecMontgomeryPoint32;
    open spec fn view(&self) -> Self::V {
        SpecMontgomeryPoint32 {
            legacy_form: self.legacy_form@,
            point: self.point@,
        }
    }
}
impl<'a> From<MontgomeryPoint32<'a>> for MontgomeryPoint32Inner<'a> {
    fn ex_from(m: MontgomeryPoint32<'a>) -> MontgomeryPoint32Inner<'a> {
        (m.legacy_form, m.point)
    }
}
impl<'a> From<MontgomeryPoint32Inner<'a>> for MontgomeryPoint32<'a> {
    fn ex_from(m: MontgomeryPoint32Inner<'a>) -> MontgomeryPoint32<'a> {
        let (legacy_form, point) = m;
        MontgomeryPoint32 {
            legacy_form,
            point,
        }
    }
}

pub struct MontgomeryPoint32Mapper<'a>(PhantomData<&'a ()>);
impl<'a> MontgomeryPoint32Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MontgomeryPoint32Mapper(PhantomData)
    }
    pub fn new() -> Self {
        MontgomeryPoint32Mapper(PhantomData)
    }
}
impl View for MontgomeryPoint32Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MontgomeryPoint32Mapper<'_> {
    type Src = SpecMontgomeryPoint32Inner;
    type Dst = SpecMontgomeryPoint32;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for MontgomeryPoint32Mapper<'a> {
    type Src = MontgomeryPoint32Inner<'a>;
    type Dst = MontgomeryPoint32<'a>;
}
    
pub const MONTGOMERYPOINT32_LEGACY_FORM: u8 = 4;

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
pub type SpecMontgomeryPoint32CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, BytesN<32>), MontgomeryPoint32Mapper<'static>>;

pub struct MontgomeryPoint32Combinator<'a>(MontgomeryPoint32CombinatorAlias<'a>);

impl<'a> View for MontgomeryPoint32Combinator<'a> {
    type V = SpecMontgomeryPoint32Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryPoint32Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MontgomeryPoint32Combinator<'a> {
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
pub type MontgomeryPoint32CombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, BytesN<32>), MontgomeryPoint32Mapper<'a>>;


pub closed spec fn spec_montgomery_point32() -> SpecMontgomeryPoint32Combinator {
    SpecMontgomeryPoint32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(MONTGOMERYPOINT32_LEGACY_FORM) }, BytesN::<32>), mapper: MontgomeryPoint32Mapper::spec_new() })
}


                
pub fn montgomery_point32<'a>() -> (o: MontgomeryPoint32Combinator<'a>)
    ensures o@ == spec_montgomery_point32(),
{
    MontgomeryPoint32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(MONTGOMERYPOINT32_LEGACY_FORM) }, BytesN::<32>), mapper: MontgomeryPoint32Mapper::new() })
}


                
pub struct SpecMontgomeryForm56 {
    pub legacy_form: u8,
    pub point: Seq<u8>,
}
pub type SpecMontgomeryForm56Inner = (u8, Seq<u8>);
impl SpecFrom<SpecMontgomeryForm56> for SpecMontgomeryForm56Inner {
    open spec fn spec_from(m: SpecMontgomeryForm56) -> SpecMontgomeryForm56Inner {
        (m.legacy_form, m.point)
    }
}
impl SpecFrom<SpecMontgomeryForm56Inner> for SpecMontgomeryForm56 {
    open spec fn spec_from(m: SpecMontgomeryForm56Inner) -> SpecMontgomeryForm56 {
        let (legacy_form, point) = m;
        SpecMontgomeryForm56 {
            legacy_form,
            point,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MontgomeryForm56<'a> {
    pub legacy_form: u8,
    pub point: &'a [u8],
}
pub type MontgomeryForm56Inner<'a> = (u8, &'a [u8]);
impl View for MontgomeryForm56<'_> {
    type V = SpecMontgomeryForm56;
    open spec fn view(&self) -> Self::V {
        SpecMontgomeryForm56 {
            legacy_form: self.legacy_form@,
            point: self.point@,
        }
    }
}
impl<'a> From<MontgomeryForm56<'a>> for MontgomeryForm56Inner<'a> {
    fn ex_from(m: MontgomeryForm56<'a>) -> MontgomeryForm56Inner<'a> {
        (m.legacy_form, m.point)
    }
}
impl<'a> From<MontgomeryForm56Inner<'a>> for MontgomeryForm56<'a> {
    fn ex_from(m: MontgomeryForm56Inner<'a>) -> MontgomeryForm56<'a> {
        let (legacy_form, point) = m;
        MontgomeryForm56 {
            legacy_form,
            point,
        }
    }
}

pub struct MontgomeryForm56Mapper<'a>(PhantomData<&'a ()>);
impl<'a> MontgomeryForm56Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MontgomeryForm56Mapper(PhantomData)
    }
    pub fn new() -> Self {
        MontgomeryForm56Mapper(PhantomData)
    }
}
impl View for MontgomeryForm56Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MontgomeryForm56Mapper<'_> {
    type Src = SpecMontgomeryForm56Inner;
    type Dst = SpecMontgomeryForm56;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for MontgomeryForm56Mapper<'a> {
    type Src = MontgomeryForm56Inner<'a>;
    type Dst = MontgomeryForm56<'a>;
}
    
pub const MONTGOMERYFORM56_LEGACY_FORM: u8 = 4;

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
pub type SpecMontgomeryForm56CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, BytesN<56>), MontgomeryForm56Mapper<'static>>;

pub struct MontgomeryForm56Combinator<'a>(MontgomeryForm56CombinatorAlias<'a>);

impl<'a> View for MontgomeryForm56Combinator<'a> {
    type V = SpecMontgomeryForm56Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryForm56Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for MontgomeryForm56Combinator<'a> {
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
pub type MontgomeryForm56CombinatorAlias<'a> = Mapped<(Refined<U8, TagPred<u8>>, BytesN<56>), MontgomeryForm56Mapper<'a>>;


pub closed spec fn spec_montgomery_form56() -> SpecMontgomeryForm56Combinator {
    SpecMontgomeryForm56Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(MONTGOMERYFORM56_LEGACY_FORM) }, BytesN::<56>), mapper: MontgomeryForm56Mapper::spec_new() })
}


                
pub fn montgomery_form56<'a>() -> (o: MontgomeryForm56Combinator<'a>)
    ensures o@ == spec_montgomery_form56(),
{
    MontgomeryForm56Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(MONTGOMERYFORM56_LEGACY_FORM) }, BytesN::<56>), mapper: MontgomeryForm56Mapper::new() })
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
        SpecSeverDhParams {
            dh_p,
            dh_g,
            dh_ys,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeverDhParams<'a> {
    pub dh_p: Opaque1Ffff<'a>,
    pub dh_g: Opaque1Ffff<'a>,
    pub dh_ys: Opaque1Ffff<'a>,
}
pub type SeverDhParamsInner<'a> = (Opaque1Ffff<'a>, (Opaque1Ffff<'a>, Opaque1Ffff<'a>));
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
impl<'a> From<SeverDhParams<'a>> for SeverDhParamsInner<'a> {
    fn ex_from(m: SeverDhParams<'a>) -> SeverDhParamsInner<'a> {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl<'a> From<SeverDhParamsInner<'a>> for SeverDhParams<'a> {
    fn ex_from(m: SeverDhParamsInner<'a>) -> SeverDhParams<'a> {
        let (dh_p, (dh_g, dh_ys)) = m;
        SeverDhParams {
            dh_p,
            dh_g,
            dh_ys,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecSeverDhParamsCombinator(Mapped { inner: (spec_opaque_1_ffff(), (spec_opaque_1_ffff(), spec_opaque_1_ffff())), mapper: SeverDhParamsMapper::spec_new() })
}


                
pub fn sever_dh_params<'a>() -> (o: SeverDhParamsCombinator<'a>)
    ensures o@ == spec_sever_dh_params(),
{
    SeverDhParamsCombinator(Mapped { inner: (opaque_1_ffff(), (opaque_1_ffff(), opaque_1_ffff())), mapper: SeverDhParamsMapper::new() })
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


                
pub enum SpecKeyShareEntryKeyExchange {
    Secp256r1(SpecUncompressedPointRepresentation32),
    Secp384r1(SpecUncompressedPointRepresentation48),
    Secp521r1(SpecUncompressedPointRepresentation66),
    X25519(SpecMontgomeryPoint32),
    X448(SpecMontgomeryForm56),
    Ffdhe2048(SpecSeverDhParams),
    Ffdhe3072(SpecSeverDhParams),
    Ffdhe4096(SpecSeverDhParams),
    Ffdhe6144(SpecSeverDhParams),
    Ffdhe8192(SpecSeverDhParams),
    Unrecognized(SpecKeyExchangeData),
}
pub type SpecKeyShareEntryKeyExchangeInner = Either<SpecUncompressedPointRepresentation32, Either<SpecUncompressedPointRepresentation48, Either<SpecUncompressedPointRepresentation66, Either<SpecMontgomeryPoint32, Either<SpecMontgomeryForm56, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, SpecKeyExchangeData>>>>>>>>>>;
impl SpecFrom<SpecKeyShareEntryKeyExchange> for SpecKeyShareEntryKeyExchangeInner {
    open spec fn spec_from(m: SpecKeyShareEntryKeyExchange) -> SpecKeyShareEntryKeyExchangeInner {
        match m {
            SpecKeyShareEntryKeyExchange::Secp256r1(m) => Either::Left(m),
            SpecKeyShareEntryKeyExchange::Secp384r1(m) => Either::Right(Either::Left(m)),
            SpecKeyShareEntryKeyExchange::Secp521r1(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecKeyShareEntryKeyExchange::X25519(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecKeyShareEntryKeyExchange::X448(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecKeyShareEntryKeyExchange::Ffdhe2048(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecKeyShareEntryKeyExchange::Ffdhe3072(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe4096(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe6144(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe8192(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecKeyShareEntryKeyExchange::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }
}
impl SpecFrom<SpecKeyShareEntryKeyExchangeInner> for SpecKeyShareEntryKeyExchange {
    open spec fn spec_from(m: SpecKeyShareEntryKeyExchangeInner) -> SpecKeyShareEntryKeyExchange {
        match m {
            Either::Left(m) => SpecKeyShareEntryKeyExchange::Secp256r1(m),
            Either::Right(Either::Left(m)) => SpecKeyShareEntryKeyExchange::Secp384r1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecKeyShareEntryKeyExchange::Secp521r1(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecKeyShareEntryKeyExchange::X25519(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecKeyShareEntryKeyExchange::X448(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecKeyShareEntryKeyExchange::Ffdhe2048(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecKeyShareEntryKeyExchange::Ffdhe3072(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecKeyShareEntryKeyExchange::Ffdhe4096(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecKeyShareEntryKeyExchange::Ffdhe6144(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecKeyShareEntryKeyExchange::Ffdhe8192(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecKeyShareEntryKeyExchange::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyShareEntryKeyExchange<'a> {
    Secp256r1(UncompressedPointRepresentation32<'a>),
    Secp384r1(UncompressedPointRepresentation48<'a>),
    Secp521r1(UncompressedPointRepresentation66<'a>),
    X25519(MontgomeryPoint32<'a>),
    X448(MontgomeryForm56<'a>),
    Ffdhe2048(SeverDhParams<'a>),
    Ffdhe3072(SeverDhParams<'a>),
    Ffdhe4096(SeverDhParams<'a>),
    Ffdhe6144(SeverDhParams<'a>),
    Ffdhe8192(SeverDhParams<'a>),
    Unrecognized(KeyExchangeData<'a>),
}
pub type KeyShareEntryKeyExchangeInner<'a> = Either<UncompressedPointRepresentation32<'a>, Either<UncompressedPointRepresentation48<'a>, Either<UncompressedPointRepresentation66<'a>, Either<MontgomeryPoint32<'a>, Either<MontgomeryForm56<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, KeyExchangeData<'a>>>>>>>>>>>;
impl View for KeyShareEntryKeyExchange<'_> {
    type V = SpecKeyShareEntryKeyExchange;
    open spec fn view(&self) -> Self::V {
        match self {
            KeyShareEntryKeyExchange::Secp256r1(m) => SpecKeyShareEntryKeyExchange::Secp256r1(m@),
            KeyShareEntryKeyExchange::Secp384r1(m) => SpecKeyShareEntryKeyExchange::Secp384r1(m@),
            KeyShareEntryKeyExchange::Secp521r1(m) => SpecKeyShareEntryKeyExchange::Secp521r1(m@),
            KeyShareEntryKeyExchange::X25519(m) => SpecKeyShareEntryKeyExchange::X25519(m@),
            KeyShareEntryKeyExchange::X448(m) => SpecKeyShareEntryKeyExchange::X448(m@),
            KeyShareEntryKeyExchange::Ffdhe2048(m) => SpecKeyShareEntryKeyExchange::Ffdhe2048(m@),
            KeyShareEntryKeyExchange::Ffdhe3072(m) => SpecKeyShareEntryKeyExchange::Ffdhe3072(m@),
            KeyShareEntryKeyExchange::Ffdhe4096(m) => SpecKeyShareEntryKeyExchange::Ffdhe4096(m@),
            KeyShareEntryKeyExchange::Ffdhe6144(m) => SpecKeyShareEntryKeyExchange::Ffdhe6144(m@),
            KeyShareEntryKeyExchange::Ffdhe8192(m) => SpecKeyShareEntryKeyExchange::Ffdhe8192(m@),
            KeyShareEntryKeyExchange::Unrecognized(m) => SpecKeyShareEntryKeyExchange::Unrecognized(m@),
        }
    }
}
impl<'a> From<KeyShareEntryKeyExchange<'a>> for KeyShareEntryKeyExchangeInner<'a> {
    fn ex_from(m: KeyShareEntryKeyExchange<'a>) -> KeyShareEntryKeyExchangeInner<'a> {
        match m {
            KeyShareEntryKeyExchange::Secp256r1(m) => Either::Left(m),
            KeyShareEntryKeyExchange::Secp384r1(m) => Either::Right(Either::Left(m)),
            KeyShareEntryKeyExchange::Secp521r1(m) => Either::Right(Either::Right(Either::Left(m))),
            KeyShareEntryKeyExchange::X25519(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            KeyShareEntryKeyExchange::X448(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            KeyShareEntryKeyExchange::Ffdhe2048(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            KeyShareEntryKeyExchange::Ffdhe3072(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            KeyShareEntryKeyExchange::Ffdhe4096(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            KeyShareEntryKeyExchange::Ffdhe6144(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            KeyShareEntryKeyExchange::Ffdhe8192(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            KeyShareEntryKeyExchange::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }
}
impl<'a> From<KeyShareEntryKeyExchangeInner<'a>> for KeyShareEntryKeyExchange<'a> {
    fn ex_from(m: KeyShareEntryKeyExchangeInner<'a>) -> KeyShareEntryKeyExchange<'a> {
        match m {
            Either::Left(m) => KeyShareEntryKeyExchange::Secp256r1(m),
            Either::Right(Either::Left(m)) => KeyShareEntryKeyExchange::Secp384r1(m),
            Either::Right(Either::Right(Either::Left(m))) => KeyShareEntryKeyExchange::Secp521r1(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => KeyShareEntryKeyExchange::X25519(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => KeyShareEntryKeyExchange::X448(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => KeyShareEntryKeyExchange::Ffdhe2048(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => KeyShareEntryKeyExchange::Ffdhe3072(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => KeyShareEntryKeyExchange::Ffdhe4096(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => KeyShareEntryKeyExchange::Ffdhe6144(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => KeyShareEntryKeyExchange::Ffdhe8192(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => KeyShareEntryKeyExchange::Unrecognized(m),
        }
    }
}

pub struct KeyShareEntryKeyExchangeMapper<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareEntryKeyExchangeMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        KeyShareEntryKeyExchangeMapper(PhantomData)
    }
    pub fn new() -> Self {
        KeyShareEntryKeyExchangeMapper(PhantomData)
    }
}
impl View for KeyShareEntryKeyExchangeMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareEntryKeyExchangeMapper<'_> {
    type Src = SpecKeyShareEntryKeyExchangeInner;
    type Dst = SpecKeyShareEntryKeyExchange;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for KeyShareEntryKeyExchangeMapper<'a> {
    type Src = KeyShareEntryKeyExchangeInner<'a>;
    type Dst = KeyShareEntryKeyExchange<'a>;
}
    

pub struct SpecKeyShareEntryKeyExchangeCombinator(SpecKeyShareEntryKeyExchangeCombinatorAlias);

impl SpecCombinator for SpecKeyShareEntryKeyExchangeCombinator {
    type SpecResult = SpecKeyShareEntryKeyExchange;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareEntryKeyExchangeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareEntryKeyExchangeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareEntryKeyExchangeCombinatorAlias = Mapped<OrdChoice<Cond<SpecUncompressedPointRepresentation32Combinator>, OrdChoice<Cond<SpecUncompressedPointRepresentation48Combinator>, OrdChoice<Cond<SpecUncompressedPointRepresentation66Combinator>, OrdChoice<Cond<SpecMontgomeryPoint32Combinator>, OrdChoice<Cond<SpecMontgomeryForm56Combinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, Cond<SpecKeyExchangeDataCombinator>>>>>>>>>>>, KeyShareEntryKeyExchangeMapper<'static>>;

pub struct KeyShareEntryKeyExchangeCombinator<'a>(KeyShareEntryKeyExchangeCombinatorAlias<'a>);

impl<'a> View for KeyShareEntryKeyExchangeCombinator<'a> {
    type V = SpecKeyShareEntryKeyExchangeCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareEntryKeyExchangeCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for KeyShareEntryKeyExchangeCombinator<'a> {
    type Result = KeyShareEntryKeyExchange<'a>;
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
pub type KeyShareEntryKeyExchangeCombinatorAlias<'a> = Mapped<OrdChoice<Cond<UncompressedPointRepresentation32Combinator<'a>>, OrdChoice<Cond<UncompressedPointRepresentation48Combinator<'a>>, OrdChoice<Cond<UncompressedPointRepresentation66Combinator<'a>>, OrdChoice<Cond<MontgomeryPoint32Combinator<'a>>, OrdChoice<Cond<MontgomeryForm56Combinator<'a>>, OrdChoice<Cond<SeverDhParamsCombinator<'a>>, OrdChoice<Cond<SeverDhParamsCombinator<'a>>, OrdChoice<Cond<SeverDhParamsCombinator<'a>>, OrdChoice<Cond<SeverDhParamsCombinator<'a>>, OrdChoice<Cond<SeverDhParamsCombinator<'a>>, Cond<KeyExchangeDataCombinator<'a>>>>>>>>>>>>, KeyShareEntryKeyExchangeMapper<'a>>;


pub closed spec fn spec_key_share_entry_key_exchange(group: SpecNamedGroup) -> SpecKeyShareEntryKeyExchangeCombinator {
    SpecKeyShareEntryKeyExchangeCombinator(Mapped { inner: OrdChoice(Cond { cond: group == 23, inner: spec_uncompressed_point_representation32() }, OrdChoice(Cond { cond: group == 24, inner: spec_uncompressed_point_representation48() }, OrdChoice(Cond { cond: group == 25, inner: spec_uncompressed_point_representation66() }, OrdChoice(Cond { cond: group == 29, inner: spec_montgomery_point32() }, OrdChoice(Cond { cond: group == 30, inner: spec_montgomery_form56() }, OrdChoice(Cond { cond: group == 256, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 257, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 258, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 259, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 260, inner: spec_sever_dh_params() }, Cond { cond: !(group == 1 || group == 2 || group == 3 || group == 4 || group == 5 || group == 6 || group == 7 || group == 8 || group == 9 || group == 10 || group == 11 || group == 12 || group == 13 || group == 14 || group == 15 || group == 16 || group == 17 || group == 18 || group == 19 || group == 20 || group == 21 || group == 22 || group == 23 || group == 24 || group == 25 || group == 29 || group == 30 || group == 256 || group == 257 || group == 258 || group == 259 || group == 260), inner: spec_key_exchange_data() })))))))))), mapper: KeyShareEntryKeyExchangeMapper::spec_new() })
}


                
pub fn key_share_entry_key_exchange<'a>(group: NamedGroup) -> (o: KeyShareEntryKeyExchangeCombinator<'a>)
    ensures o@ == spec_key_share_entry_key_exchange(group@),
{
    KeyShareEntryKeyExchangeCombinator(Mapped { inner: OrdChoice(Cond { cond: group == 23, inner: uncompressed_point_representation32() }, OrdChoice(Cond { cond: group == 24, inner: uncompressed_point_representation48() }, OrdChoice(Cond { cond: group == 25, inner: uncompressed_point_representation66() }, OrdChoice(Cond { cond: group == 29, inner: montgomery_point32() }, OrdChoice(Cond { cond: group == 30, inner: montgomery_form56() }, OrdChoice(Cond { cond: group == 256, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 257, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 258, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 259, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 260, inner: sever_dh_params() }, Cond { cond: !(group == 1 || group == 2 || group == 3 || group == 4 || group == 5 || group == 6 || group == 7 || group == 8 || group == 9 || group == 10 || group == 11 || group == 12 || group == 13 || group == 14 || group == 15 || group == 16 || group == 17 || group == 18 || group == 19 || group == 20 || group == 21 || group == 22 || group == 23 || group == 24 || group == 25 || group == 29 || group == 30 || group == 256 || group == 257 || group == 258 || group == 259 || group == 260), inner: key_exchange_data() })))))))))), mapper: KeyShareEntryKeyExchangeMapper::new() })
}


                
pub struct SpecKeyShareEntry {
    pub group: SpecNamedGroup,
    pub key_exchange: SpecKeyShareEntryKeyExchange,
}
pub type SpecKeyShareEntryInner = (SpecNamedGroup, SpecKeyShareEntryKeyExchange);
impl SpecFrom<SpecKeyShareEntry> for SpecKeyShareEntryInner {
    open spec fn spec_from(m: SpecKeyShareEntry) -> SpecKeyShareEntryInner {
        (m.group, m.key_exchange)
    }
}
impl SpecFrom<SpecKeyShareEntryInner> for SpecKeyShareEntry {
    open spec fn spec_from(m: SpecKeyShareEntryInner) -> SpecKeyShareEntry {
        let (group, key_exchange) = m;
        SpecKeyShareEntry {
            group,
            key_exchange,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyShareEntry<'a> {
    pub group: NamedGroup,
    pub key_exchange: KeyShareEntryKeyExchange<'a>,
}
pub type KeyShareEntryInner<'a> = (NamedGroup, KeyShareEntryKeyExchange<'a>);
impl View for KeyShareEntry<'_> {
    type V = SpecKeyShareEntry;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareEntry {
            group: self.group@,
            key_exchange: self.key_exchange@,
        }
    }
}
impl<'a> From<KeyShareEntry<'a>> for KeyShareEntryInner<'a> {
    fn ex_from(m: KeyShareEntry<'a>) -> KeyShareEntryInner<'a> {
        (m.group, m.key_exchange)
    }
}
impl<'a> From<KeyShareEntryInner<'a>> for KeyShareEntry<'a> {
    fn ex_from(m: KeyShareEntryInner<'a>) -> KeyShareEntry<'a> {
        let (group, key_exchange) = m;
        KeyShareEntry {
            group,
            key_exchange,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecKeyShareEntryCombinatorAlias = Mapped<SpecDepend<SpecNamedGroupCombinator, SpecKeyShareEntryKeyExchangeCombinator>, KeyShareEntryMapper<'static>>;

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
pub type KeyShareEntryCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, NamedGroupCombinator, KeyShareEntryKeyExchangeCombinator<'a>, KeyShareEntryCont<'a>>, KeyShareEntryMapper<'a>>;


pub closed spec fn spec_key_share_entry() -> SpecKeyShareEntryCombinator {
    SpecKeyShareEntryCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_named_group(),
            snd: |deps| spec_key_share_entry_cont(deps),
        },
        mapper: KeyShareEntryMapper::spec_new(),
    }
)
}


pub open spec fn spec_key_share_entry_cont(deps: SpecNamedGroup) -> SpecKeyShareEntryKeyExchangeCombinator {
    let group = deps;
    spec_key_share_entry_key_exchange(group)
}

                
pub fn key_share_entry<'a>() -> (o: KeyShareEntryCombinator<'a>)
    ensures o@ == spec_key_share_entry(),
{
    KeyShareEntryCombinator(
    Mapped {
        inner: Depend {
            fst: named_group(),
            snd: KeyShareEntryCont::new(),
            spec_snd: Ghost(|deps| spec_key_share_entry_cont(deps)),
        },
        mapper: KeyShareEntryMapper::new(),
    }
)
}


pub struct KeyShareEntryCont<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareEntryCont<'a> {
    pub fn new() -> Self {
        KeyShareEntryCont(PhantomData)
    }
}
impl<'a> Continuation<NamedGroup> for KeyShareEntryCont<'a> {
    type Output = KeyShareEntryKeyExchangeCombinator<'a>;

    open spec fn requires(&self, deps: NamedGroup) -> bool {
        true
    }

    open spec fn ensures(&self, deps: NamedGroup, o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont(deps@)
    }

    fn apply(&self, deps: NamedGroup) -> Self::Output {
        let group = deps;
        key_share_entry_key_exchange(group)
    }
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
        SpecKeyShareClientHello {
            l,
            client_shares,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyShareClientHello<'a> {
    pub l: Uint0Ffff,
    pub client_shares: KeyShareClientHelloClientShares<'a>,
}
pub type KeyShareClientHelloInner<'a> = (Uint0Ffff, KeyShareClientHelloClientShares<'a>);
impl View for KeyShareClientHello<'_> {
    type V = SpecKeyShareClientHello;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareClientHello {
            l: self.l@,
            client_shares: self.client_shares@,
        }
    }
}
impl<'a> From<KeyShareClientHello<'a>> for KeyShareClientHelloInner<'a> {
    fn ex_from(m: KeyShareClientHello<'a>) -> KeyShareClientHelloInner<'a> {
        (m.l, m.client_shares)
    }
}
impl<'a> From<KeyShareClientHelloInner<'a>> for KeyShareClientHello<'a> {
    fn ex_from(m: KeyShareClientHelloInner<'a>) -> KeyShareClientHello<'a> {
        let (l, client_shares) = m;
        KeyShareClientHello {
            l,
            client_shares,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type KeyShareClientHelloCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, KeyShareClientHelloClientSharesCombinator<'a>, KeyShareClientHelloCont<'a>>, KeyShareClientHelloMapper<'a>>;


pub closed spec fn spec_key_share_client_hello() -> SpecKeyShareClientHelloCombinator {
    SpecKeyShareClientHelloCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_key_share_client_hello_cont(deps),
        },
        mapper: KeyShareClientHelloMapper::spec_new(),
    }
)
}


pub open spec fn spec_key_share_client_hello_cont(deps: SpecUint0Ffff) -> SpecKeyShareClientHelloClientSharesCombinator {
    let l = deps;
    spec_key_share_client_hello_client_shares(l)
}

                
pub fn key_share_client_hello<'a>() -> (o: KeyShareClientHelloCombinator<'a>)
    ensures o@ == spec_key_share_client_hello(),
{
    KeyShareClientHelloCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: KeyShareClientHelloCont::new(),
            spec_snd: Ghost(|deps| spec_key_share_client_hello_cont(deps)),
        },
        mapper: KeyShareClientHelloMapper::new(),
    }
)
}


pub struct KeyShareClientHelloCont<'a>(PhantomData<&'a ()>);
impl<'a> KeyShareClientHelloCont<'a> {
    pub fn new() -> Self {
        KeyShareClientHelloCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for KeyShareClientHelloCont<'a> {
    type Output = KeyShareClientHelloClientSharesCombinator<'a>;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_key_share_client_hello_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        key_share_client_hello_client_shares(l)
    }
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


                
pub enum SpecClientHelloExtensionExtensionData {
    ServerName(SpecEmpty),
    MaxFragmentLength(SpecMaxFragmentLength),
    StatusRequest(SpecEmpty),
    ECPointFormats(SpecEcPointFormatList),
    UseSRTP(SpecUseSrtpData),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SigedCertificateTimestamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(SpecPaddingExtension),
    EncryptThenMac(SpecEmpty),
    ExtendedMasterSecret(SpecEmpty),
    SessionTicket(SpecSessionTicket),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    EarlyData(SpecEmpty),
    SupportedVersions(SpecSupportedVersionsClient),
    Cookie(SpecCookie),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    PostHandshakeAuth(SpecEmpty),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    KeyShare(SpecKeyShareClientHello),
    Unrecognized(SpecUnknownExtension),
}
pub type SpecClientHelloExtensionExtensionDataInner = Either<SpecEmpty, Either<SpecMaxFragmentLength, Either<SpecEmpty, Either<SpecEcPointFormatList, Either<SpecUseSrtpData, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecPaddingExtension, Either<SpecEmpty, Either<SpecEmpty, Either<SpecSessionTicket, Either<SpecPreSharedKeyClientExtension, Either<SpecEmpty, Either<SpecSupportedVersionsClient, Either<SpecCookie, Either<SpecPskKeyExchangeModes, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecEmpty, Either<SpecSignatureSchemeList, Either<SpecKeyShareClientHello, SpecUnknownExtension>>>>>>>>>>>>>>>>>>>>>>>>;
impl SpecFrom<SpecClientHelloExtensionExtensionData> for SpecClientHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionData) -> SpecClientHelloExtensionExtensionDataInner {
        match m {
            SpecClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecClientHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecClientHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))),
        }
    }
}
impl SpecFrom<SpecClientHelloExtensionExtensionDataInner> for SpecClientHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionDataInner) -> SpecClientHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecClientHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClientHelloExtensionExtensionData<'a> {
    ServerName(Empty<'a>),
    MaxFragmentLength(MaxFragmentLength),
    StatusRequest(Empty<'a>),
    ECPointFormats(EcPointFormatList),
    UseSRTP(UseSrtpData<'a>),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SigedCertificateTimestamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(PaddingExtension),
    EncryptThenMac(Empty<'a>),
    ExtendedMasterSecret(Empty<'a>),
    SessionTicket(SessionTicket<'a>),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    EarlyData(Empty<'a>),
    SupportedVersions(SupportedVersionsClient),
    Cookie(Cookie<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    PostHandshakeAuth(Empty<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    KeyShare(KeyShareClientHello<'a>),
    Unrecognized(UnknownExtension<'a>),
}
pub type ClientHelloExtensionExtensionDataInner<'a> = Either<Empty<'a>, Either<MaxFragmentLength, Either<Empty<'a>, Either<EcPointFormatList, Either<UseSrtpData<'a>, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<PaddingExtension, Either<Empty<'a>, Either<Empty<'a>, Either<SessionTicket<'a>, Either<PreSharedKeyClientExtension<'a>, Either<Empty<'a>, Either<SupportedVersionsClient, Either<Cookie<'a>, Either<PskKeyExchangeModes, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<Empty<'a>, Either<SignatureSchemeList, Either<KeyShareClientHello<'a>, UnknownExtension<'a>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for ClientHelloExtensionExtensionData<'_> {
    type V = SpecClientHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionExtensionData::ServerName(m) => SpecClientHelloExtensionExtensionData::ServerName(m@),
            ClientHelloExtensionExtensionData::MaxFragmentLength(m) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m@),
            ClientHelloExtensionExtensionData::StatusRequest(m) => SpecClientHelloExtensionExtensionData::StatusRequest(m@),
            ClientHelloExtensionExtensionData::ECPointFormats(m) => SpecClientHelloExtensionExtensionData::ECPointFormats(m@),
            ClientHelloExtensionExtensionData::UseSRTP(m) => SpecClientHelloExtensionExtensionData::UseSRTP(m@),
            ClientHelloExtensionExtensionData::Heartbeat(m) => SpecClientHelloExtensionExtensionData::Heartbeat(m@),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m@),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m@),
            ClientHelloExtensionExtensionData::Padding(m) => SpecClientHelloExtensionExtensionData::Padding(m@),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m@),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            ClientHelloExtensionExtensionData::SessionTicket(m) => SpecClientHelloExtensionExtensionData::SessionTicket(m@),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => SpecClientHelloExtensionExtensionData::PreSharedKey(m@),
            ClientHelloExtensionExtensionData::EarlyData(m) => SpecClientHelloExtensionExtensionData::EarlyData(m@),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => SpecClientHelloExtensionExtensionData::SupportedVersions(m@),
            ClientHelloExtensionExtensionData::Cookie(m) => SpecClientHelloExtensionExtensionData::Cookie(m@),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m@),
            ClientHelloExtensionExtensionData::OidFilters(m) => SpecClientHelloExtensionExtensionData::OidFilters(m@),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            ClientHelloExtensionExtensionData::KeyShare(m) => SpecClientHelloExtensionExtensionData::KeyShare(m@),
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
            ClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))),
        }
    }
}
impl<'a> From<ClientHelloExtensionExtensionDataInner<'a>> for ClientHelloExtensionExtensionData<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionDataInner<'a>) -> ClientHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => ClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))) => ClientHelloExtensionExtensionData::Unrecognized(m),
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecClientHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEcPointFormatListCombinator>, OrdChoice<Cond<SpecUseSrtpDataCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecPaddingExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSessionTicketCombinator>, OrdChoice<Cond<SpecPreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSupportedVersionsClientCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecPskKeyExchangeModesCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecKeyShareClientHelloCombinator>, Cond<SpecUnknownExtensionCombinator>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper<'static>>>;

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
pub type ClientHelloExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EcPointFormatListCombinator<'a>>, OrdChoice<Cond<UseSrtpDataCombinator<'a>>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator<'a>>, OrdChoice<Cond<SignedCertificateTimestampListCombinator<'a>>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<PaddingExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SessionTicketCombinator<'a>>, OrdChoice<Cond<PreSharedKeyClientExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SupportedVersionsClientCombinator<'a>>, OrdChoice<Cond<CookieCombinator<'a>>, OrdChoice<Cond<PskKeyExchangeModesCombinator<'a>>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator<'a>>, OrdChoice<Cond<OidFilterExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<KeyShareClientHelloCombinator<'a>>, Cond<UnknownExtensionCombinator<'a>>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_client_hello_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecClientHelloExtensionExtensionDataCombinator {
    SpecClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 11, inner: spec_ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: spec_use_srtp_data() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: spec_padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: spec_session_ticket() }, OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51), inner: spec_unknown_extension() })))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper::spec_new() }))
}


                
pub fn client_hello_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: ClientHelloExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_client_hello_extension_extension_data(ext_len@, extension_type@),
{
    ClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: empty() }, OrdChoice(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: empty() }, OrdChoice(Cond { cond: extension_type == 11, inner: ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: use_srtp_data() }, OrdChoice(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: session_ticket() }, OrdChoice(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51), inner: unknown_extension() })))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper::new() }))
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
        SpecClientHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: ClientHelloExtensionExtensionData<'a>,
}
pub type ClientHelloExtensionInner<'a> = ((ExtensionType, u16), ClientHelloExtensionExtensionData<'a>);
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
impl<'a> From<ClientHelloExtension<'a>> for ClientHelloExtensionInner<'a> {
    fn ex_from(m: ClientHelloExtension<'a>) -> ClientHelloExtensionInner<'a> {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<ClientHelloExtensionInner<'a>> for ClientHelloExtension<'a> {
    fn ex_from(m: ClientHelloExtensionInner<'a>) -> ClientHelloExtension<'a> {
        let ((extension_type, ext_len), extension_data) = m;
        ClientHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecClientHelloExtensionCombinatorAlias = Mapped<SpecDepend<(SpecExtensionTypeCombinator, U16Be), SpecClientHelloExtensionExtensionDataCombinator>, ClientHelloExtensionMapper<'static>>;

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
pub type ClientHelloExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (ExtensionTypeCombinator, U16Be), ClientHelloExtensionExtensionDataCombinator<'a>, ClientHelloExtensionCont<'a>>, ClientHelloExtensionMapper<'a>>;


pub closed spec fn spec_client_hello_extension() -> SpecClientHelloExtensionCombinator {
    SpecClientHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_extension_type(), U16Be),
            snd: |deps| spec_client_hello_extension_cont(deps),
        },
        mapper: ClientHelloExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_client_hello_extension_cont(deps: (SpecExtensionType, u16)) -> SpecClientHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_client_hello_extension_extension_data(ext_len, extension_type)
}

                
pub fn client_hello_extension<'a>() -> (o: ClientHelloExtensionCombinator<'a>)
    ensures o@ == spec_client_hello_extension(),
{
    ClientHelloExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: (extension_type(), U16Be),
            snd: ClientHelloExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_client_hello_extension_cont(deps)),
        },
        mapper: ClientHelloExtensionMapper::new(),
    }
)
}


pub struct ClientHelloExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> ClientHelloExtensionCont<'a> {
    pub fn new() -> Self {
        ClientHelloExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<(ExtensionType, u16)> for ClientHelloExtensionCont<'a> {
    type Output = ClientHelloExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: (ExtensionType, u16)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont(deps@)
    }

    fn apply(&self, deps: (ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = deps;
        client_hello_extension_extension_data(ext_len, extension_type)
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


                
pub type SpecCertificateRequestExtensionsExtensions = Seq<SpecExtension>;
pub type CertificateRequestExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;


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
pub type SpecCertificateRequestExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

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
pub type CertificateRequestExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<ExtensionCombinator<'a>>>;


pub closed spec fn spec_certificate_request_extensions_extensions(l: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    SpecCertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}


                
pub fn certificate_request_extensions_extensions<'a>(l: Uint2Ffff) -> (o: CertificateRequestExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_request_extensions_extensions(l@),
{
    CertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
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
        SpecOpaque0Ffffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}
pub type Opaque0FfffffInner<'a> = (u24, &'a [u8]);
impl View for Opaque0Ffffff<'_> {
    type V = SpecOpaque0Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ffffff<'a>> for Opaque0FfffffInner<'a> {
    fn ex_from(m: Opaque0Ffffff<'a>) -> Opaque0FfffffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffffInner<'a>> for Opaque0Ffffff<'a> {
    fn ex_from(m: Opaque0FfffffInner<'a>) -> Opaque0Ffffff<'a> {
        let (l, data) = m;
        Opaque0Ffffff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque0FfffffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U24Be, Bytes, Opaque0FfffffCont<'a>>, Opaque0FfffffMapper<'a>>;


pub closed spec fn spec_opaque_0_ffffff() -> SpecOpaque0FfffffCombinator {
    SpecOpaque0FfffffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: U24Be,
            snd: |deps| spec_opaque0_ffffff_cont(deps),
        },
        mapper: Opaque0FfffffMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque0_ffffff_cont(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_0_ffffff<'a>() -> (o: Opaque0FfffffCombinator<'a>)
    ensures o@ == spec_opaque_0_ffffff(),
{
    Opaque0FfffffCombinator(
    Mapped {
        inner: Depend {
            fst: U24Be,
            snd: Opaque0FfffffCont::new(),
            spec_snd: Ghost(|deps| spec_opaque0_ffffff_cont(deps)),
        },
        mapper: Opaque0FfffffMapper::new(),
    }
)
}


pub struct Opaque0FfffffCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque0FfffffCont<'a> {
    pub fn new() -> Self {
        Opaque0FfffffCont(PhantomData)
    }
}
impl<'a> Continuation<u24> for Opaque0FfffffCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffffff_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
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
        SpecKeyUpdate {
            request_update,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyUpdate {
    pub request_update: KeyUpdateRequest,
}
pub type KeyUpdateInner = KeyUpdateRequest;
impl View for KeyUpdate {
    type V = SpecKeyUpdate;
    open spec fn view(&self) -> Self::V {
        SpecKeyUpdate {
            request_update: self.request_update@,
        }
    }
}
impl From<KeyUpdate> for KeyUpdateInner {
    fn ex_from(m: KeyUpdate) -> KeyUpdateInner {
        m.request_update
    }
}
impl From<KeyUpdateInner> for KeyUpdate {
    fn ex_from(m: KeyUpdateInner) -> KeyUpdate {
        let request_update = m;
        KeyUpdate {
            request_update,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecKeyUpdateCombinator(Mapped { inner: spec_key_update_request(), mapper: KeyUpdateMapper::spec_new() })
}


                
pub fn key_update() -> (o: KeyUpdateCombinator)
    ensures o@ == spec_key_update(),
{
    KeyUpdateCombinator(Mapped { inner: key_update_request(), mapper: KeyUpdateMapper::new() })
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
        SpecCertificateStatus {
            status_type,
            response,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateStatus<'a> {
    pub status_type: u8,
    pub response: OcspResponse<'a>,
}
pub type CertificateStatusInner<'a> = (u8, OcspResponse<'a>);
impl View for CertificateStatus<'_> {
    type V = SpecCertificateStatus;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatus {
            status_type: self.status_type@,
            response: self.response@,
        }
    }
}
impl<'a> From<CertificateStatus<'a>> for CertificateStatusInner<'a> {
    fn ex_from(m: CertificateStatus<'a>) -> CertificateStatusInner<'a> {
        (m.status_type, m.response)
    }
}
impl<'a> From<CertificateStatusInner<'a>> for CertificateStatus<'a> {
    fn ex_from(m: CertificateStatusInner<'a>) -> CertificateStatus<'a> {
        let (status_type, response) = m;
        CertificateStatus {
            status_type,
            response,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateStatusCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, spec_ocsp_response()), mapper: CertificateStatusMapper::spec_new() })
}


                
pub fn certificate_status<'a>() -> (o: CertificateStatusCombinator<'a>)
    ensures o@ == spec_certificate_status(),
{
    CertificateStatusCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, ocsp_response()), mapper: CertificateStatusMapper::new() })
}


                
pub type SpecNewSessionTicketExtensionsExtensions = Seq<SpecExtension>;
pub type NewSessionTicketExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;


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
pub type SpecNewSessionTicketExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

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
pub type NewSessionTicketExtensionsExtensionsCombinatorAlias<'a> = AndThen<Bytes, Repeat<ExtensionCombinator<'a>>>;


pub closed spec fn spec_new_session_ticket_extensions_extensions(l: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    SpecNewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}


                
pub fn new_session_ticket_extensions_extensions<'a>(l: Uint0Fffe) -> (o: NewSessionTicketExtensionsExtensionsCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extensions_extensions(l@),
{
    NewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
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
        SpecClientCertTypeServerExtension {
            client_certificate_type,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientCertTypeServerExtension {
    pub client_certificate_type: CertificateType,
}
pub type ClientCertTypeServerExtensionInner = CertificateType;
impl View for ClientCertTypeServerExtension {
    type V = SpecClientCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeServerExtension {
            client_certificate_type: self.client_certificate_type@,
        }
    }
}
impl From<ClientCertTypeServerExtension> for ClientCertTypeServerExtensionInner {
    fn ex_from(m: ClientCertTypeServerExtension) -> ClientCertTypeServerExtensionInner {
        m.client_certificate_type
    }
}
impl From<ClientCertTypeServerExtensionInner> for ClientCertTypeServerExtension {
    fn ex_from(m: ClientCertTypeServerExtensionInner) -> ClientCertTypeServerExtension {
        let client_certificate_type = m;
        ClientCertTypeServerExtension {
            client_certificate_type,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecClientCertTypeServerExtensionCombinator(Mapped { inner: spec_certificate_type(), mapper: ClientCertTypeServerExtensionMapper::spec_new() })
}


                
pub fn client_cert_type_server_extension() -> (o: ClientCertTypeServerExtensionCombinator)
    ensures o@ == spec_client_cert_type_server_extension(),
{
    ClientCertTypeServerExtensionCombinator(Mapped { inner: certificate_type(), mapper: ClientCertTypeServerExtensionMapper::new() })
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
impl View for ServerNameName<'_> {
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    ServerNameNameCombinator(Mapped { inner: OrdChoice(Cond { cond: name_type == 0, inner: host_name() }, Cond { cond: !(name_type == 0), inner: unknown_name() }), mapper: ServerNameNameMapper::new() })
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
        SpecServerName {
            name_type,
            name,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerName<'a> {
    pub name_type: NameType,
    pub name: ServerNameName<'a>,
}
pub type ServerNameInner<'a> = (NameType, ServerNameName<'a>);
impl View for ServerName<'_> {
    type V = SpecServerName;
    open spec fn view(&self) -> Self::V {
        SpecServerName {
            name_type: self.name_type@,
            name: self.name@,
        }
    }
}
impl<'a> From<ServerName<'a>> for ServerNameInner<'a> {
    fn ex_from(m: ServerName<'a>) -> ServerNameInner<'a> {
        (m.name_type, m.name)
    }
}
impl<'a> From<ServerNameInner<'a>> for ServerName<'a> {
    fn ex_from(m: ServerNameInner<'a>) -> ServerName<'a> {
        let (name_type, name) = m;
        ServerName {
            name_type,
            name,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type ServerNameCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, NameTypeCombinator, ServerNameNameCombinator<'a>, ServerNameCont<'a>>, ServerNameMapper<'a>>;


pub closed spec fn spec_server_name() -> SpecServerNameCombinator {
    SpecServerNameCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_name_type(),
            snd: |deps| spec_server_name_cont(deps),
        },
        mapper: ServerNameMapper::spec_new(),
    }
)
}


pub open spec fn spec_server_name_cont(deps: SpecNameType) -> SpecServerNameNameCombinator {
    let name_type = deps;
    spec_server_name_name(name_type)
}

                
pub fn server_name<'a>() -> (o: ServerNameCombinator<'a>)
    ensures o@ == spec_server_name(),
{
    ServerNameCombinator(
    Mapped {
        inner: Depend {
            fst: name_type(),
            snd: ServerNameCont::new(),
            spec_snd: Ghost(|deps| spec_server_name_cont(deps)),
        },
        mapper: ServerNameMapper::new(),
    }
)
}


pub struct ServerNameCont<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameCont<'a> {
    pub fn new() -> Self {
        ServerNameCont(PhantomData)
    }
}
impl<'a> Continuation<NameType> for ServerNameCont<'a> {
    type Output = ServerNameNameCombinator<'a>;

    open spec fn requires(&self, deps: NameType) -> bool {
        true
    }

    open spec fn ensures(&self, deps: NameType, o: Self::Output) -> bool {
        o@ == spec_server_name_cont(deps@)
    }

    fn apply(&self, deps: NameType) -> Self::Output {
        let name_type = deps;
        server_name_name(name_type)
    }
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
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EarlyDataIndicationNewSessionTicket {
    pub max_early_data_size: u32,
}
pub type EarlyDataIndicationNewSessionTicketInner = u32;
impl View for EarlyDataIndicationNewSessionTicket {
    type V = SpecEarlyDataIndicationNewSessionTicket;
    open spec fn view(&self) -> Self::V {
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size: self.max_early_data_size@,
        }
    }
}
impl From<EarlyDataIndicationNewSessionTicket> for EarlyDataIndicationNewSessionTicketInner {
    fn ex_from(m: EarlyDataIndicationNewSessionTicket) -> EarlyDataIndicationNewSessionTicketInner {
        m.max_early_data_size
    }
}
impl From<EarlyDataIndicationNewSessionTicketInner> for EarlyDataIndicationNewSessionTicket {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketInner) -> EarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        EarlyDataIndicationNewSessionTicket {
            max_early_data_size,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecEarlyDataIndicationNewSessionTicketCombinator(Mapped { inner: U32Be, mapper: EarlyDataIndicationNewSessionTicketMapper::spec_new() })
}


                
pub fn early_data_indication_new_session_ticket() -> (o: EarlyDataIndicationNewSessionTicketCombinator)
    ensures o@ == spec_early_data_indication_new_session_ticket(),
{
    EarlyDataIndicationNewSessionTicketCombinator(Mapped { inner: U32Be, mapper: EarlyDataIndicationNewSessionTicketMapper::new() })
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
        SpecCertificate {
            certificate_request_context,
            certificate_list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Certificate<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub certificate_list: CertificateList<'a>,
}
pub type CertificateInner<'a> = (Opaque0Ff<'a>, CertificateList<'a>);
impl View for Certificate<'_> {
    type V = SpecCertificate;
    open spec fn view(&self) -> Self::V {
        SpecCertificate {
            certificate_request_context: self.certificate_request_context@,
            certificate_list: self.certificate_list@,
        }
    }
}
impl<'a> From<Certificate<'a>> for CertificateInner<'a> {
    fn ex_from(m: Certificate<'a>) -> CertificateInner<'a> {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl<'a> From<CertificateInner<'a>> for Certificate<'a> {
    fn ex_from(m: CertificateInner<'a>) -> Certificate<'a> {
        let (certificate_request_context, certificate_list) = m;
        Certificate {
            certificate_request_context,
            certificate_list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateCombinator(Mapped { inner: (spec_opaque_0_ff(), spec_certificate_list()), mapper: CertificateMapper::spec_new() })
}


                
pub fn certificate<'a>() -> (o: CertificateCombinator<'a>)
    ensures o@ == spec_certificate(),
{
    CertificateCombinator(Mapped { inner: (opaque_0_ff(), certificate_list()), mapper: CertificateMapper::new() })
}


                
pub struct SpecCertificateVerify {
    pub signature_scheme: SpecSignatureScheme,
    pub signature: SpecOpaque0Ffff,
}
pub type SpecCertificateVerifyInner = (SpecSignatureScheme, SpecOpaque0Ffff);
impl SpecFrom<SpecCertificateVerify> for SpecCertificateVerifyInner {
    open spec fn spec_from(m: SpecCertificateVerify) -> SpecCertificateVerifyInner {
        (m.signature_scheme, m.signature)
    }
}
impl SpecFrom<SpecCertificateVerifyInner> for SpecCertificateVerify {
    open spec fn spec_from(m: SpecCertificateVerifyInner) -> SpecCertificateVerify {
        let (signature_scheme, signature) = m;
        SpecCertificateVerify {
            signature_scheme,
            signature,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateVerify<'a> {
    pub signature_scheme: SignatureScheme,
    pub signature: Opaque0Ffff<'a>,
}
pub type CertificateVerifyInner<'a> = (SignatureScheme, Opaque0Ffff<'a>);
impl View for CertificateVerify<'_> {
    type V = SpecCertificateVerify;
    open spec fn view(&self) -> Self::V {
        SpecCertificateVerify {
            signature_scheme: self.signature_scheme@,
            signature: self.signature@,
        }
    }
}
impl<'a> From<CertificateVerify<'a>> for CertificateVerifyInner<'a> {
    fn ex_from(m: CertificateVerify<'a>) -> CertificateVerifyInner<'a> {
        (m.signature_scheme, m.signature)
    }
}
impl<'a> From<CertificateVerifyInner<'a>> for CertificateVerify<'a> {
    fn ex_from(m: CertificateVerifyInner<'a>) -> CertificateVerify<'a> {
        let (signature_scheme, signature) = m;
        CertificateVerify {
            signature_scheme,
            signature,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateVerifyCombinator(Mapped { inner: (spec_signature_scheme(), spec_opaque_0_ffff()), mapper: CertificateVerifyMapper::spec_new() })
}


                
pub fn certificate_verify<'a>() -> (o: CertificateVerifyCombinator<'a>)
    ensures o@ == spec_certificate_verify(),
{
    CertificateVerifyCombinator(Mapped { inner: (signature_scheme(), opaque_0_ffff()), mapper: CertificateVerifyMapper::new() })
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
        SpecServerNameList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerNameList<'a> {
    pub l: Uint1Ffff,
    pub list: ServerNameListList<'a>,
}
pub type ServerNameListInner<'a> = (Uint1Ffff, ServerNameListList<'a>);
impl View for ServerNameList<'_> {
    type V = SpecServerNameList;
    open spec fn view(&self) -> Self::V {
        SpecServerNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<ServerNameList<'a>> for ServerNameListInner<'a> {
    fn ex_from(m: ServerNameList<'a>) -> ServerNameListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<ServerNameListInner<'a>> for ServerNameList<'a> {
    fn ex_from(m: ServerNameListInner<'a>) -> ServerNameList<'a> {
        let (l, list) = m;
        ServerNameList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type ServerNameListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint1FfffCombinator, ServerNameListListCombinator<'a>, ServerNameListCont<'a>>, ServerNameListMapper<'a>>;


pub closed spec fn spec_server_name_list() -> SpecServerNameListCombinator {
    SpecServerNameListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_server_name_list_cont(deps),
        },
        mapper: ServerNameListMapper::spec_new(),
    }
)
}


pub open spec fn spec_server_name_list_cont(deps: SpecUint1Ffff) -> SpecServerNameListListCombinator {
    let l = deps;
    spec_server_name_list_list(l)
}

                
pub fn server_name_list<'a>() -> (o: ServerNameListCombinator<'a>)
    ensures o@ == spec_server_name_list(),
{
    ServerNameListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: ServerNameListCont::new(),
            spec_snd: Ghost(|deps| spec_server_name_list_cont(deps)),
        },
        mapper: ServerNameListMapper::new(),
    }
)
}


pub struct ServerNameListCont<'a>(PhantomData<&'a ()>);
impl<'a> ServerNameListCont<'a> {
    pub fn new() -> Self {
        ServerNameListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint1Ffff> for ServerNameListCont<'a> {
    type Output = ServerNameListListCombinator<'a>;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_server_name_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        server_name_list_list(l)
    }
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
        SpecResponderIdList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResponderIdList<'a> {
    pub l: Uint0Ffff,
    pub list: ResponderIdListList<'a>,
}
pub type ResponderIdListInner<'a> = (Uint0Ffff, ResponderIdListList<'a>);
impl View for ResponderIdList<'_> {
    type V = SpecResponderIdList;
    open spec fn view(&self) -> Self::V {
        SpecResponderIdList {
            l: self.l@,
            list: self.list@,
        }
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
        ResponderIdList {
            l,
            list,
        }
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
pub type ResponderIdListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FfffCombinator, ResponderIdListListCombinator<'a>, ResponderIdListCont<'a>>, ResponderIdListMapper<'a>>;


pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_responder_id_list_cont(deps),
        },
        mapper: ResponderIdListMapper::spec_new(),
    }
)
}


pub open spec fn spec_responder_id_list_cont(deps: SpecUint0Ffff) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}

                
pub fn responder_id_list<'a>() -> (o: ResponderIdListCombinator<'a>)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: ResponderIdListCont::new(),
            spec_snd: Ghost(|deps| spec_responder_id_list_cont(deps)),
        },
        mapper: ResponderIdListMapper::new(),
    }
)
}


pub struct ResponderIdListCont<'a>(PhantomData<&'a ()>);
impl<'a> ResponderIdListCont<'a> {
    pub fn new() -> Self {
        ResponderIdListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Ffff> for ResponderIdListCont<'a> {
    type Output = ResponderIdListListCombinator<'a>;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
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
        SpecOscpStatusRequest {
            responder_id_list,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OscpStatusRequest<'a> {
    pub responder_id_list: ResponderIdList<'a>,
    pub extensions: OcspExtensions<'a>,
}
pub type OscpStatusRequestInner<'a> = (ResponderIdList<'a>, OcspExtensions<'a>);
impl View for OscpStatusRequest<'_> {
    type V = SpecOscpStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecOscpStatusRequest {
            responder_id_list: self.responder_id_list@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<OscpStatusRequest<'a>> for OscpStatusRequestInner<'a> {
    fn ex_from(m: OscpStatusRequest<'a>) -> OscpStatusRequestInner<'a> {
        (m.responder_id_list, m.extensions)
    }
}
impl<'a> From<OscpStatusRequestInner<'a>> for OscpStatusRequest<'a> {
    fn ex_from(m: OscpStatusRequestInner<'a>) -> OscpStatusRequest<'a> {
        let (responder_id_list, extensions) = m;
        OscpStatusRequest {
            responder_id_list,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecOscpStatusRequestCombinator(Mapped { inner: (spec_responder_id_list(), spec_ocsp_extensions()), mapper: OscpStatusRequestMapper::spec_new() })
}


                
pub fn oscp_status_request<'a>() -> (o: OscpStatusRequestCombinator<'a>)
    ensures o@ == spec_oscp_status_request(),
{
    OscpStatusRequestCombinator(Mapped { inner: (responder_id_list(), ocsp_extensions()), mapper: OscpStatusRequestMapper::new() })
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
        SpecCertificateStatusRequest {
            status_type,
            request,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateStatusRequest<'a> {
    pub status_type: u8,
    pub request: OscpStatusRequest<'a>,
}
pub type CertificateStatusRequestInner<'a> = (u8, OscpStatusRequest<'a>);
impl View for CertificateStatusRequest<'_> {
    type V = SpecCertificateStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatusRequest {
            status_type: self.status_type@,
            request: self.request@,
        }
    }
}
impl<'a> From<CertificateStatusRequest<'a>> for CertificateStatusRequestInner<'a> {
    fn ex_from(m: CertificateStatusRequest<'a>) -> CertificateStatusRequestInner<'a> {
        (m.status_type, m.request)
    }
}
impl<'a> From<CertificateStatusRequestInner<'a>> for CertificateStatusRequest<'a> {
    fn ex_from(m: CertificateStatusRequestInner<'a>) -> CertificateStatusRequest<'a> {
        let (status_type, request) = m;
        CertificateStatusRequest {
            status_type,
            request,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateStatusRequestCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, spec_oscp_status_request()), mapper: CertificateStatusRequestMapper::spec_new() })
}


                
pub fn certificate_status_request<'a>() -> (o: CertificateStatusRequestCombinator<'a>)
    ensures o@ == spec_certificate_status_request(),
{
    CertificateStatusRequestCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, oscp_status_request()), mapper: CertificateStatusRequestMapper::new() })
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


                
pub fn named_group_list_list(l: Uint2Ffff) -> (o: NamedGroupListListCombinator)
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
        SpecNamedGroupList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedGroupList {
    pub l: Uint2Ffff,
    pub list: NamedGroupListList,
}
pub type NamedGroupListInner = (Uint2Ffff, NamedGroupListList);
impl View for NamedGroupList {
    type V = SpecNamedGroupList;
    open spec fn view(&self) -> Self::V {
        SpecNamedGroupList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<NamedGroupList> for NamedGroupListInner {
    fn ex_from(m: NamedGroupList) -> NamedGroupListInner {
        (m.l, m.list)
    }
}
impl From<NamedGroupListInner> for NamedGroupList {
    fn ex_from(m: NamedGroupListInner) -> NamedGroupList {
        let (l, list) = m;
        NamedGroupList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type NamedGroupListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, NamedGroupListListCombinator, NamedGroupListCont<'a>>, NamedGroupListMapper>;


pub closed spec fn spec_named_group_list() -> SpecNamedGroupListCombinator {
    SpecNamedGroupListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_named_group_list_cont(deps),
        },
        mapper: NamedGroupListMapper::spec_new(),
    }
)
}


pub open spec fn spec_named_group_list_cont(deps: SpecUint2Ffff) -> SpecNamedGroupListListCombinator {
    let l = deps;
    spec_named_group_list_list(l)
}

                
pub fn named_group_list<'a>() -> (o: NamedGroupListCombinator<'a>)
    ensures o@ == spec_named_group_list(),
{
    NamedGroupListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: NamedGroupListCont::new(),
            spec_snd: Ghost(|deps| spec_named_group_list_cont(deps)),
        },
        mapper: NamedGroupListMapper::new(),
    }
)
}


pub struct NamedGroupListCont<'a>(PhantomData<&'a ()>);
impl<'a> NamedGroupListCont<'a> {
    pub fn new() -> Self {
        NamedGroupListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Ffff> for NamedGroupListCont<'a> {
    type Output = NamedGroupListListCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_named_group_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        named_group_list_list(l)
    }
}

                
pub enum SpecSeverHelloExtensionExtensionData {
    ServerName(SpecServerNameList),
    MaxFragmentLength(SpecMaxFragmentLength),
    StatusRequest(SpecCertificateStatusRequest),
    SupportedGroups(SpecNamedGroupList),
    ECPointFormats(SpecEcPointFormatList),
    SignatureAlgorithms(SpecSignatureSchemeList),
    UseSRTP(SpecSrtpProtectionProfiles),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SigedCertificateTimestamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(SpecPaddingExtension),
    EncryptThenMac(SpecEmpty),
    ExtendedMasterSecret(SpecEmpty),
    SessionTicket(SpecSessionTicket),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    EarlyData(SpecEmpty),
    SupportedVersions(SpecSupportedVersionsClient),
    Cookie(SpecCookie),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    PostHandshakeAuth(SpecEmpty),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    KeyShare(SpecKeyShareClientHello),
    Unrecognized(SpecUnknownExtension),
}
pub type SpecSeverHelloExtensionExtensionDataInner = Either<SpecServerNameList, Either<SpecMaxFragmentLength, Either<SpecCertificateStatusRequest, Either<SpecNamedGroupList, Either<SpecEcPointFormatList, Either<SpecSignatureSchemeList, Either<SpecSrtpProtectionProfiles, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecPaddingExtension, Either<SpecEmpty, Either<SpecEmpty, Either<SpecSessionTicket, Either<SpecPreSharedKeyClientExtension, Either<SpecEmpty, Either<SpecSupportedVersionsClient, Either<SpecCookie, Either<SpecPskKeyExchangeModes, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecEmpty, Either<SpecSignatureSchemeList, Either<SpecKeyShareClientHello, SpecUnknownExtension>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl SpecFrom<SpecSeverHelloExtensionExtensionData> for SpecSeverHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionData) -> SpecSeverHelloExtensionExtensionDataInner {
        match m {
            SpecSeverHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecSeverHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecSeverHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecSeverHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecSeverHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecSeverHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecSeverHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecSeverHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecSeverHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecSeverHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl SpecFrom<SpecSeverHelloExtensionExtensionDataInner> for SpecSeverHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionDataInner) -> SpecSeverHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecSeverHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecSeverHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecSeverHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecSeverHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecSeverHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecSeverHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecSeverHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecSeverHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecSeverHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecSeverHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecSeverHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecSeverHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeverHelloExtensionExtensionData<'a> {
    ServerName(ServerNameList<'a>),
    MaxFragmentLength(MaxFragmentLength),
    StatusRequest(CertificateStatusRequest<'a>),
    SupportedGroups(NamedGroupList),
    ECPointFormats(EcPointFormatList),
    SignatureAlgorithms(SignatureSchemeList),
    UseSRTP(SrtpProtectionProfiles<'a>),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SigedCertificateTimestamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(PaddingExtension),
    EncryptThenMac(Empty<'a>),
    ExtendedMasterSecret(Empty<'a>),
    SessionTicket(SessionTicket<'a>),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    EarlyData(Empty<'a>),
    SupportedVersions(SupportedVersionsClient),
    Cookie(Cookie<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    PostHandshakeAuth(Empty<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    KeyShare(KeyShareClientHello<'a>),
    Unrecognized(UnknownExtension<'a>),
}
pub type SeverHelloExtensionExtensionDataInner<'a> = Either<ServerNameList<'a>, Either<MaxFragmentLength, Either<CertificateStatusRequest<'a>, Either<NamedGroupList, Either<EcPointFormatList, Either<SignatureSchemeList, Either<SrtpProtectionProfiles<'a>, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<PaddingExtension, Either<Empty<'a>, Either<Empty<'a>, Either<SessionTicket<'a>, Either<PreSharedKeyClientExtension<'a>, Either<Empty<'a>, Either<SupportedVersionsClient, Either<Cookie<'a>, Either<PskKeyExchangeModes, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<Empty<'a>, Either<SignatureSchemeList, Either<KeyShareClientHello<'a>, UnknownExtension<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for SeverHelloExtensionExtensionData<'_> {
    type V = SpecSeverHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            SeverHelloExtensionExtensionData::ServerName(m) => SpecSeverHelloExtensionExtensionData::ServerName(m@),
            SeverHelloExtensionExtensionData::MaxFragmentLength(m) => SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m@),
            SeverHelloExtensionExtensionData::StatusRequest(m) => SpecSeverHelloExtensionExtensionData::StatusRequest(m@),
            SeverHelloExtensionExtensionData::SupportedGroups(m) => SpecSeverHelloExtensionExtensionData::SupportedGroups(m@),
            SeverHelloExtensionExtensionData::ECPointFormats(m) => SpecSeverHelloExtensionExtensionData::ECPointFormats(m@),
            SeverHelloExtensionExtensionData::SignatureAlgorithms(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m@),
            SeverHelloExtensionExtensionData::UseSRTP(m) => SpecSeverHelloExtensionExtensionData::UseSRTP(m@),
            SeverHelloExtensionExtensionData::Heartbeat(m) => SpecSeverHelloExtensionExtensionData::Heartbeat(m@),
            SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            SeverHelloExtensionExtensionData::ClientCertificateType(m) => SpecSeverHelloExtensionExtensionData::ClientCertificateType(m@),
            SeverHelloExtensionExtensionData::ServerCertificateType(m) => SpecSeverHelloExtensionExtensionData::ServerCertificateType(m@),
            SeverHelloExtensionExtensionData::Padding(m) => SpecSeverHelloExtensionExtensionData::Padding(m@),
            SeverHelloExtensionExtensionData::EncryptThenMac(m) => SpecSeverHelloExtensionExtensionData::EncryptThenMac(m@),
            SeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            SeverHelloExtensionExtensionData::SessionTicket(m) => SpecSeverHelloExtensionExtensionData::SessionTicket(m@),
            SeverHelloExtensionExtensionData::PreSharedKey(m) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m@),
            SeverHelloExtensionExtensionData::EarlyData(m) => SpecSeverHelloExtensionExtensionData::EarlyData(m@),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m@),
            SeverHelloExtensionExtensionData::Cookie(m) => SpecSeverHelloExtensionExtensionData::Cookie(m@),
            SeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            SeverHelloExtensionExtensionData::CertificateAuthorities(m) => SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m@),
            SeverHelloExtensionExtensionData::OidFilters(m) => SpecSeverHelloExtensionExtensionData::OidFilters(m@),
            SeverHelloExtensionExtensionData::PostHandshakeAuth(m) => SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m@),
            SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            SeverHelloExtensionExtensionData::KeyShare(m) => SpecSeverHelloExtensionExtensionData::KeyShare(m@),
            SeverHelloExtensionExtensionData::Unrecognized(m) => SpecSeverHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}
impl<'a> From<SeverHelloExtensionExtensionData<'a>> for SeverHelloExtensionExtensionDataInner<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionData<'a>) -> SeverHelloExtensionExtensionDataInner<'a> {
        match m {
            SeverHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SeverHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SeverHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SeverHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SeverHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SeverHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SeverHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SeverHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SeverHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SeverHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SeverHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SeverHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SeverHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SeverHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SeverHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SeverHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SeverHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl<'a> From<SeverHelloExtensionExtensionDataInner<'a>> for SeverHelloExtensionExtensionData<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionDataInner<'a>) -> SeverHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => SeverHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SeverHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SeverHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SeverHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SeverHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SeverHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SeverHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SeverHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SeverHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SeverHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SeverHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SeverHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SeverHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SeverHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SeverHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SeverHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SeverHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SeverHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SeverHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SeverHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::Unrecognized(m),
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecSeverHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecServerNameListCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecCertificateStatusRequestCombinator>, OrdChoice<Cond<SpecNamedGroupListCombinator>, OrdChoice<Cond<SpecEcPointFormatListCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecSrtpProtectionProfilesCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecPaddingExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSessionTicketCombinator>, OrdChoice<Cond<SpecPreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSupportedVersionsClientCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecPskKeyExchangeModesCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecKeyShareClientHelloCombinator>, Cond<SpecUnknownExtensionCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>, SeverHelloExtensionExtensionDataMapper<'static>>>;

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
pub type SeverHelloExtensionExtensionDataCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<ServerNameListCombinator<'a>>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<CertificateStatusRequestCombinator<'a>>, OrdChoice<Cond<NamedGroupListCombinator<'a>>, OrdChoice<Cond<EcPointFormatListCombinator<'a>>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<SrtpProtectionProfilesCombinator<'a>>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator<'a>>, OrdChoice<Cond<SignedCertificateTimestampListCombinator<'a>>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator<'a>>, OrdChoice<Cond<PaddingExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SessionTicketCombinator<'a>>, OrdChoice<Cond<PreSharedKeyClientExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SupportedVersionsClientCombinator<'a>>, OrdChoice<Cond<CookieCombinator<'a>>, OrdChoice<Cond<PskKeyExchangeModesCombinator<'a>>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator<'a>>, OrdChoice<Cond<OidFilterExtensionCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator<'a>>, OrdChoice<Cond<KeyShareClientHelloCombinator<'a>>, Cond<UnknownExtensionCombinator<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>, SeverHelloExtensionExtensionDataMapper<'a>>>;


pub closed spec fn spec_sever_hello_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecSeverHelloExtensionExtensionDataCombinator {
    SpecSeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: spec_ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: spec_srtp_protection_profiles() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: spec_padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: spec_session_ticket() }, OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51), inner: spec_unknown_extension() })))))))))))))))))))))))))), mapper: SeverHelloExtensionExtensionDataMapper::spec_new() }))
}


                
pub fn sever_hello_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: SeverHelloExtensionExtensionDataCombinator<'a>)
    ensures o@ == spec_sever_hello_extension_extension_data(ext_len@, extension_type@),
{
    SeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: srtp_protection_profiles() }, OrdChoice(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: session_ticket() }, OrdChoice(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51), inner: unknown_extension() })))))))))))))))))))))))))), mapper: SeverHelloExtensionExtensionDataMapper::new() }))
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

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
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
        SpecTlsPlaintext {
            content_type,
            legacy_record_version,
            fragment,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsPlaintext<'a> {
    pub content_type: ContentType,
    pub legacy_record_version: ProtocolVersion,
    pub fragment: Opaque0Ffff<'a>,
}
pub type TlsPlaintextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
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
impl<'a> From<TlsPlaintext<'a>> for TlsPlaintextInner<'a> {
    fn ex_from(m: TlsPlaintext<'a>) -> TlsPlaintextInner<'a> {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl<'a> From<TlsPlaintextInner<'a>> for TlsPlaintext<'a> {
    fn ex_from(m: TlsPlaintextInner<'a>) -> TlsPlaintext<'a> {
        let (content_type, (legacy_record_version, fragment)) = m;
        TlsPlaintext {
            content_type,
            legacy_record_version,
            fragment,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecTlsPlaintextCombinator(Mapped { inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())), mapper: TlsPlaintextMapper::spec_new() })
}


                
pub fn tls_plaintext<'a>() -> (o: TlsPlaintextCombinator<'a>)
    ensures o@ == spec_tls_plaintext(),
{
    TlsPlaintextCombinator(Mapped { inner: (content_type(), (protocol_version(), opaque_0_ffff())), mapper: TlsPlaintextMapper::new() })
}


                
pub type SpecUint0Fffe = u16;
pub type Uint0Fffe = u16;

impl SpecPred for Predicate184937773087435626 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

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
pub type SpecUint0FffeCombinatorAlias = Refined<U16Be, Predicate184937773087435626>;
pub struct Predicate184937773087435626;
impl View for Predicate184937773087435626 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate184937773087435626 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65534) {
            true
        } else {
            false
        }
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
pub type Uint0FffeCombinatorAlias = Refined<U16Be, Predicate184937773087435626>;


pub closed spec fn spec_uint_0_fffe() -> SpecUint0FffeCombinator {
    SpecUint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate184937773087435626 })
}


                
pub fn uint_0_fffe() -> (o: Uint0FffeCombinator)
    ensures o@ == spec_uint_0_fffe(),
{
    Uint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate184937773087435626 })
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
        SpecNewSessionTicketExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewSessionTicketExtensions<'a> {
    pub l: Uint0Fffe,
    pub extensions: NewSessionTicketExtensionsExtensions<'a>,
}
pub type NewSessionTicketExtensionsInner<'a> = (Uint0Fffe, NewSessionTicketExtensionsExtensions<'a>);
impl View for NewSessionTicketExtensions<'_> {
    type V = SpecNewSessionTicketExtensions;
    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<NewSessionTicketExtensions<'a>> for NewSessionTicketExtensionsInner<'a> {
    fn ex_from(m: NewSessionTicketExtensions<'a>) -> NewSessionTicketExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<NewSessionTicketExtensionsInner<'a>> for NewSessionTicketExtensions<'a> {
    fn ex_from(m: NewSessionTicketExtensionsInner<'a>) -> NewSessionTicketExtensions<'a> {
        let (l, extensions) = m;
        NewSessionTicketExtensions {
            l,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type NewSessionTicketExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint0FffeCombinator, NewSessionTicketExtensionsExtensionsCombinator<'a>, NewSessionTicketExtensionsCont<'a>>, NewSessionTicketExtensionsMapper<'a>>;


pub closed spec fn spec_new_session_ticket_extensions() -> SpecNewSessionTicketExtensionsCombinator {
    SpecNewSessionTicketExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_fffe(),
            snd: |deps| spec_new_session_ticket_extensions_cont(deps),
        },
        mapper: NewSessionTicketExtensionsMapper::spec_new(),
    }
)
}


pub open spec fn spec_new_session_ticket_extensions_cont(deps: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    let l = deps;
    spec_new_session_ticket_extensions_extensions(l)
}

                
pub fn new_session_ticket_extensions<'a>() -> (o: NewSessionTicketExtensionsCombinator<'a>)
    ensures o@ == spec_new_session_ticket_extensions(),
{
    NewSessionTicketExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_fffe(),
            snd: NewSessionTicketExtensionsCont::new(),
            spec_snd: Ghost(|deps| spec_new_session_ticket_extensions_cont(deps)),
        },
        mapper: NewSessionTicketExtensionsMapper::new(),
    }
)
}


pub struct NewSessionTicketExtensionsCont<'a>(PhantomData<&'a ()>);
impl<'a> NewSessionTicketExtensionsCont<'a> {
    pub fn new() -> Self {
        NewSessionTicketExtensionsCont(PhantomData)
    }
}
impl<'a> Continuation<Uint0Fffe> for NewSessionTicketExtensionsCont<'a> {
    type Output = NewSessionTicketExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: Uint0Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Fffe, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint0Fffe) -> Self::Output {
        let l = deps;
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
        SpecNewSessionTicket {
            ticket_lifetime,
            ticket_age_add,
            ticket_nonce,
            ticket,
            extensions,
        }
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
pub type NewSessionTicketInner<'a> = (u32, (u32, (Opaque0Ff<'a>, (Opaque1Ffff<'a>, NewSessionTicketExtensions<'a>))));
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
impl<'a> From<NewSessionTicket<'a>> for NewSessionTicketInner<'a> {
    fn ex_from(m: NewSessionTicket<'a>) -> NewSessionTicketInner<'a> {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl<'a> From<NewSessionTicketInner<'a>> for NewSessionTicket<'a> {
    fn ex_from(m: NewSessionTicketInner<'a>) -> NewSessionTicket<'a> {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        NewSessionTicket {
            ticket_lifetime,
            ticket_age_add,
            ticket_nonce,
            ticket,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecNewSessionTicketCombinator(Mapped { inner: (U32Be, (U32Be, (spec_opaque_0_ff(), (spec_opaque_1_ffff(), spec_new_session_ticket_extensions())))), mapper: NewSessionTicketMapper::spec_new() })
}


                
pub fn new_session_ticket<'a>() -> (o: NewSessionTicketCombinator<'a>)
    ensures o@ == spec_new_session_ticket(),
{
    NewSessionTicketCombinator(Mapped { inner: (U32Be, (U32Be, (opaque_0_ff(), (opaque_1_ffff(), new_session_ticket_extensions())))), mapper: NewSessionTicketMapper::new() })
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

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
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

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
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
        SpecAlert {
            level,
            description,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Alert {
    pub level: AlertLevel,
    pub description: AlertDescription,
}
pub type AlertInner = (AlertLevel, AlertDescription);
impl View for Alert {
    type V = SpecAlert;
    open spec fn view(&self) -> Self::V {
        SpecAlert {
            level: self.level@,
            description: self.description@,
        }
    }
}
impl From<Alert> for AlertInner {
    fn ex_from(m: Alert) -> AlertInner {
        (m.level, m.description)
    }
}
impl From<AlertInner> for Alert {
    fn ex_from(m: AlertInner) -> Alert {
        let (level, description) = m;
        Alert {
            level,
            description,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecAlertCombinator(Mapped { inner: (spec_alert_level(), spec_alert_description()), mapper: AlertMapper::spec_new() })
}


                
pub fn alert() -> (o: AlertCombinator)
    ensures o@ == spec_alert(),
{
    AlertCombinator(Mapped { inner: (alert_level(), alert_description()), mapper: AlertMapper::new() })
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
        SpecCertificateRequestExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateRequestExtensions<'a> {
    pub l: Uint2Ffff,
    pub extensions: CertificateRequestExtensionsExtensions<'a>,
}
pub type CertificateRequestExtensionsInner<'a> = (Uint2Ffff, CertificateRequestExtensionsExtensions<'a>);
impl View for CertificateRequestExtensions<'_> {
    type V = SpecCertificateRequestExtensions;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateRequestExtensions<'a>> for CertificateRequestExtensionsInner<'a> {
    fn ex_from(m: CertificateRequestExtensions<'a>) -> CertificateRequestExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<CertificateRequestExtensionsInner<'a>> for CertificateRequestExtensions<'a> {
    fn ex_from(m: CertificateRequestExtensionsInner<'a>) -> CertificateRequestExtensions<'a> {
        let (l, extensions) = m;
        CertificateRequestExtensions {
            l,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type CertificateRequestExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, CertificateRequestExtensionsExtensionsCombinator<'a>, CertificateRequestExtensionsCont<'a>>, CertificateRequestExtensionsMapper<'a>>;


pub closed spec fn spec_certificate_request_extensions() -> SpecCertificateRequestExtensionsCombinator {
    SpecCertificateRequestExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_certificate_request_extensions_cont(deps),
        },
        mapper: CertificateRequestExtensionsMapper::spec_new(),
    }
)
}


pub open spec fn spec_certificate_request_extensions_cont(deps: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    let l = deps;
    spec_certificate_request_extensions_extensions(l)
}

                
pub fn certificate_request_extensions<'a>() -> (o: CertificateRequestExtensionsCombinator<'a>)
    ensures o@ == spec_certificate_request_extensions(),
{
    CertificateRequestExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: CertificateRequestExtensionsCont::new(),
            spec_snd: Ghost(|deps| spec_certificate_request_extensions_cont(deps)),
        },
        mapper: CertificateRequestExtensionsMapper::new(),
    }
)
}


pub struct CertificateRequestExtensionsCont<'a>(PhantomData<&'a ()>);
impl<'a> CertificateRequestExtensionsCont<'a> {
    pub fn new() -> Self {
        CertificateRequestExtensionsCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Ffff> for CertificateRequestExtensionsCont<'a> {
    type Output = CertificateRequestExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
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
        SpecCertificateRequest {
            certificate_request_context,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateRequest<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub extensions: CertificateRequestExtensions<'a>,
}
pub type CertificateRequestInner<'a> = (Opaque0Ff<'a>, CertificateRequestExtensions<'a>);
impl View for CertificateRequest<'_> {
    type V = SpecCertificateRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequest {
            certificate_request_context: self.certificate_request_context@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateRequest<'a>> for CertificateRequestInner<'a> {
    fn ex_from(m: CertificateRequest<'a>) -> CertificateRequestInner<'a> {
        (m.certificate_request_context, m.extensions)
    }
}
impl<'a> From<CertificateRequestInner<'a>> for CertificateRequest<'a> {
    fn ex_from(m: CertificateRequestInner<'a>) -> CertificateRequest<'a> {
        let (certificate_request_context, extensions) = m;
        CertificateRequest {
            certificate_request_context,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecCertificateRequestCombinator(Mapped { inner: (spec_opaque_0_ff(), spec_certificate_request_extensions()), mapper: CertificateRequestMapper::spec_new() })
}


                
pub fn certificate_request<'a>() -> (o: CertificateRequestCombinator<'a>)
    ensures o@ == spec_certificate_request(),
{
    CertificateRequestCombinator(Mapped { inner: (opaque_0_ff(), certificate_request_extensions()), mapper: CertificateRequestMapper::new() })
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
        SpecSeverHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeverHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: SeverHelloExtensionExtensionData<'a>,
}
pub type SeverHelloExtensionInner<'a> = ((ExtensionType, u16), SeverHelloExtensionExtensionData<'a>);
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
impl<'a> From<SeverHelloExtension<'a>> for SeverHelloExtensionInner<'a> {
    fn ex_from(m: SeverHelloExtension<'a>) -> SeverHelloExtensionInner<'a> {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<SeverHelloExtensionInner<'a>> for SeverHelloExtension<'a> {
    fn ex_from(m: SeverHelloExtensionInner<'a>) -> SeverHelloExtension<'a> {
        let ((extension_type, ext_len), extension_data) = m;
        SeverHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecSeverHelloExtensionCombinatorAlias = Mapped<SpecDepend<(SpecExtensionTypeCombinator, U16Be), SpecSeverHelloExtensionExtensionDataCombinator>, SeverHelloExtensionMapper<'static>>;

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
pub type SeverHelloExtensionCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (ExtensionTypeCombinator, U16Be), SeverHelloExtensionExtensionDataCombinator<'a>, SeverHelloExtensionCont<'a>>, SeverHelloExtensionMapper<'a>>;


pub closed spec fn spec_sever_hello_extension() -> SpecSeverHelloExtensionCombinator {
    SpecSeverHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_extension_type(), U16Be),
            snd: |deps| spec_sever_hello_extension_cont(deps),
        },
        mapper: SeverHelloExtensionMapper::spec_new(),
    }
)
}


pub open spec fn spec_sever_hello_extension_cont(deps: (SpecExtensionType, u16)) -> SpecSeverHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_sever_hello_extension_extension_data(ext_len, extension_type)
}

                
pub fn sever_hello_extension<'a>() -> (o: SeverHelloExtensionCombinator<'a>)
    ensures o@ == spec_sever_hello_extension(),
{
    SeverHelloExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: (extension_type(), U16Be),
            snd: SeverHelloExtensionCont::new(),
            spec_snd: Ghost(|deps| spec_sever_hello_extension_cont(deps)),
        },
        mapper: SeverHelloExtensionMapper::new(),
    }
)
}


pub struct SeverHelloExtensionCont<'a>(PhantomData<&'a ()>);
impl<'a> SeverHelloExtensionCont<'a> {
    pub fn new() -> Self {
        SeverHelloExtensionCont(PhantomData)
    }
}
impl<'a> Continuation<(ExtensionType, u16)> for SeverHelloExtensionCont<'a> {
    type Output = SeverHelloExtensionExtensionDataCombinator<'a>;

    open spec fn requires(&self, deps: (ExtensionType, u16)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont(deps@)
    }

    fn apply(&self, deps: (ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = deps;
        sever_hello_extension_extension_data(ext_len, extension_type)
    }
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
        SpecSessionId {
            l,
            id,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionId<'a> {
    pub l: u8,
    pub id: &'a [u8],
}
pub type SessionIdInner<'a> = (u8, &'a [u8]);
impl View for SessionId<'_> {
    type V = SpecSessionId;
    open spec fn view(&self) -> Self::V {
        SpecSessionId {
            l: self.l@,
            id: self.id@,
        }
    }
}
impl<'a> From<SessionId<'a>> for SessionIdInner<'a> {
    fn ex_from(m: SessionId<'a>) -> SessionIdInner<'a> {
        (m.l, m.id)
    }
}
impl<'a> From<SessionIdInner<'a>> for SessionId<'a> {
    fn ex_from(m: SessionIdInner<'a>) -> SessionId<'a> {
        let (l, id) = m;
        SessionId {
            l,
            id,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for SessionIdMapper<'a> {
    type Src = SessionIdInner<'a>;
    type Dst = SessionId<'a>;
}
    
impl SpecPred for Predicate10693986609604791304 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 32) {
            true
        } else {
            false
        }
    }
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
pub type SpecSessionIdCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate10693986609604791304>, Bytes>, SessionIdMapper<'static>>;
pub struct Predicate10693986609604791304;
impl View for Predicate10693986609604791304 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate10693986609604791304 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 32) {
            true
        } else {
            false
        }
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
pub type SessionIdCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U8, Predicate10693986609604791304>, Bytes, SessionIdCont<'a>>, SessionIdMapper<'a>>;


pub closed spec fn spec_session_id() -> SpecSessionIdCombinator {
    SpecSessionIdCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate10693986609604791304 },
            snd: |deps| spec_session_id_cont(deps),
        },
        mapper: SessionIdMapper::spec_new(),
    }
)
}


pub open spec fn spec_session_id_cont(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn session_id<'a>() -> (o: SessionIdCombinator<'a>)
    ensures o@ == spec_session_id(),
{
    SessionIdCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate10693986609604791304 },
            snd: SessionIdCont::new(),
            spec_snd: Ghost(|deps| spec_session_id_cont(deps)),
        },
        mapper: SessionIdMapper::new(),
    }
)
}


pub struct SessionIdCont<'a>(PhantomData<&'a ()>);
impl<'a> SessionIdCont<'a> {
    pub fn new() -> Self {
        SessionIdCont(PhantomData)
    }
}
impl<'a> Continuation<u8> for SessionIdCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_session_id_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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
        SpecHeartbeatExtension {
            mode,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeartbeatExtension {
    pub mode: HeartbeatMode,
}
pub type HeartbeatExtensionInner = HeartbeatMode;
impl View for HeartbeatExtension {
    type V = SpecHeartbeatExtension;
    open spec fn view(&self) -> Self::V {
        SpecHeartbeatExtension {
            mode: self.mode@,
        }
    }
}
impl From<HeartbeatExtension> for HeartbeatExtensionInner {
    fn ex_from(m: HeartbeatExtension) -> HeartbeatExtensionInner {
        m.mode
    }
}
impl From<HeartbeatExtensionInner> for HeartbeatExtension {
    fn ex_from(m: HeartbeatExtensionInner) -> HeartbeatExtension {
        let mode = m;
        HeartbeatExtension {
            mode,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecHeartbeatExtensionCombinator(Mapped { inner: spec_heartbeat_mode(), mapper: HeartbeatExtensionMapper::spec_new() })
}


                
pub fn heartbeat_extension() -> (o: HeartbeatExtensionCombinator)
    ensures o@ == spec_heartbeat_extension(),
{
    HeartbeatExtensionCombinator(Mapped { inner: heartbeat_mode(), mapper: HeartbeatExtensionMapper::new() })
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
        SpecOpaque2Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque2Ffff<'a> {
    pub l: Uint2Ffff,
    pub data: &'a [u8],
}
pub type Opaque2FfffInner<'a> = (Uint2Ffff, &'a [u8]);
impl View for Opaque2Ffff<'_> {
    type V = SpecOpaque2Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque2Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque2Ffff<'a>> for Opaque2FfffInner<'a> {
    fn ex_from(m: Opaque2Ffff<'a>) -> Opaque2FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque2FfffInner<'a>> for Opaque2Ffff<'a> {
    fn ex_from(m: Opaque2FfffInner<'a>) -> Opaque2Ffff<'a> {
        let (l, data) = m;
        Opaque2Ffff {
            l,
            data,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type Opaque2FfffCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FfffCombinator, Bytes, Opaque2FfffCont<'a>>, Opaque2FfffMapper<'a>>;


pub closed spec fn spec_opaque_2_ffff() -> SpecOpaque2FfffCombinator {
    SpecOpaque2FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_opaque2_ffff_cont(deps),
        },
        mapper: Opaque2FfffMapper::spec_new(),
    }
)
}


pub open spec fn spec_opaque2_ffff_cont(deps: SpecUint2Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}

                
pub fn opaque_2_ffff<'a>() -> (o: Opaque2FfffCombinator<'a>)
    ensures o@ == spec_opaque_2_ffff(),
{
    Opaque2FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: Opaque2FfffCont::new(),
            spec_snd: Ghost(|deps| spec_opaque2_ffff_cont(deps)),
        },
        mapper: Opaque2FfffMapper::new(),
    }
)
}


pub struct Opaque2FfffCont<'a>(PhantomData<&'a ()>);
impl<'a> Opaque2FfffCont<'a> {
    pub fn new() -> Self {
        Opaque2FfffCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Ffff> for Opaque2FfffCont<'a> {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque2_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
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
        SpecPreSharedKeyServerExtension {
            selected_identity,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreSharedKeyServerExtension {
    pub selected_identity: u16,
}
pub type PreSharedKeyServerExtensionInner = u16;
impl View for PreSharedKeyServerExtension {
    type V = SpecPreSharedKeyServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyServerExtension {
            selected_identity: self.selected_identity@,
        }
    }
}
impl From<PreSharedKeyServerExtension> for PreSharedKeyServerExtensionInner {
    fn ex_from(m: PreSharedKeyServerExtension) -> PreSharedKeyServerExtensionInner {
        m.selected_identity
    }
}
impl From<PreSharedKeyServerExtensionInner> for PreSharedKeyServerExtension {
    fn ex_from(m: PreSharedKeyServerExtensionInner) -> PreSharedKeyServerExtension {
        let selected_identity = m;
        PreSharedKeyServerExtension {
            selected_identity,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecPreSharedKeyServerExtensionCombinator(Mapped { inner: U16Be, mapper: PreSharedKeyServerExtensionMapper::spec_new() })
}


                
pub fn pre_shared_key_server_extension() -> (o: PreSharedKeyServerExtensionCombinator)
    ensures o@ == spec_pre_shared_key_server_extension(),
{
    PreSharedKeyServerExtensionCombinator(Mapped { inner: U16Be, mapper: PreSharedKeyServerExtensionMapper::new() })
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

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
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


                
pub type SpecRandom = Seq<u8>;
pub type Random<'a> = &'a [u8];


pub struct SpecRandomCombinator(SpecRandomCombinatorAlias);

impl SpecCombinator for SpecRandomCombinator {
    type SpecResult = SpecRandom;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecRandomCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecRandomCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecRandomCombinatorAlias = BytesN<32>;

pub struct RandomCombinator(RandomCombinatorAlias);

impl View for RandomCombinator {
    type V = SpecRandomCombinator;
    closed spec fn view(&self) -> Self::V { SpecRandomCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for RandomCombinator {
    type Result = Random<'a>;
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
pub type RandomCombinatorAlias = BytesN<32>;


pub closed spec fn spec_random() -> SpecRandomCombinator {
    SpecRandomCombinator(BytesN::<32>)
}


                
pub fn random() -> (o: RandomCombinator)
    ensures o@ == spec_random(),
{
    RandomCombinator(BytesN::<32>)
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


                
pub fn cipher_suite_list_list(l: Uint2Fffe) -> (o: CipherSuiteListListCombinator)
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
        SpecCipherSuiteList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CipherSuiteList {
    pub l: Uint2Fffe,
    pub list: CipherSuiteListList,
}
pub type CipherSuiteListInner = (Uint2Fffe, CipherSuiteListList);
impl View for CipherSuiteList {
    type V = SpecCipherSuiteList;
    open spec fn view(&self) -> Self::V {
        SpecCipherSuiteList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<CipherSuiteList> for CipherSuiteListInner {
    fn ex_from(m: CipherSuiteList) -> CipherSuiteListInner {
        (m.l, m.list)
    }
}
impl From<CipherSuiteListInner> for CipherSuiteList {
    fn ex_from(m: CipherSuiteListInner) -> CipherSuiteList {
        let (l, list) = m;
        CipherSuiteList {
            l,
            list,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type CipherSuiteListCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Uint2FffeCombinator, CipherSuiteListListCombinator, CipherSuiteListCont<'a>>, CipherSuiteListMapper>;


pub closed spec fn spec_cipher_suite_list() -> SpecCipherSuiteListCombinator {
    SpecCipherSuiteListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_fffe(),
            snd: |deps| spec_cipher_suite_list_cont(deps),
        },
        mapper: CipherSuiteListMapper::spec_new(),
    }
)
}


pub open spec fn spec_cipher_suite_list_cont(deps: SpecUint2Fffe) -> SpecCipherSuiteListListCombinator {
    let l = deps;
    spec_cipher_suite_list_list(l)
}

                
pub fn cipher_suite_list<'a>() -> (o: CipherSuiteListCombinator<'a>)
    ensures o@ == spec_cipher_suite_list(),
{
    CipherSuiteListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_fffe(),
            snd: CipherSuiteListCont::new(),
            spec_snd: Ghost(|deps| spec_cipher_suite_list_cont(deps)),
        },
        mapper: CipherSuiteListMapper::new(),
    }
)
}


pub struct CipherSuiteListCont<'a>(PhantomData<&'a ()>);
impl<'a> CipherSuiteListCont<'a> {
    pub fn new() -> Self {
        CipherSuiteListCont(PhantomData)
    }
}
impl<'a> Continuation<Uint2Fffe> for CipherSuiteListCont<'a> {
    type Output = CipherSuiteListListCombinator;

    open spec fn requires(&self, deps: Uint2Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_cipher_suite_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Fffe) -> Self::Output {
        let l = deps;
        cipher_suite_list_list(l)
    }
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
        SpecClientExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientExtensions<'a> {
    pub l: u16,
    pub extensions: ClientExtensionsExtensions<'a>,
}
pub type ClientExtensionsInner<'a> = (u16, ClientExtensionsExtensions<'a>);
impl View for ClientExtensions<'_> {
    type V = SpecClientExtensions;
    open spec fn view(&self) -> Self::V {
        SpecClientExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ClientExtensions<'a>> for ClientExtensionsInner<'a> {
    fn ex_from(m: ClientExtensions<'a>) -> ClientExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<ClientExtensionsInner<'a>> for ClientExtensions<'a> {
    fn ex_from(m: ClientExtensionsInner<'a>) -> ClientExtensions<'a> {
        let (l, extensions) = m;
        ClientExtensions {
            l,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for ClientExtensionsMapper<'a> {
    type Src = ClientExtensionsInner<'a>;
    type Dst = ClientExtensions<'a>;
}
    
impl SpecPred for Predicate15770232246241775772 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 8 && i <= 65535) {
            true
        } else {
            false
        }
    }
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
pub type SpecClientExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate15770232246241775772>, SpecClientExtensionsExtensionsCombinator>, ClientExtensionsMapper<'static>>;
pub struct Predicate15770232246241775772;
impl View for Predicate15770232246241775772 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate15770232246241775772 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 8 && i <= 65535) {
            true
        } else {
            false
        }
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
pub type ClientExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate15770232246241775772>, ClientExtensionsExtensionsCombinator<'a>, ClientExtensionsCont<'a>>, ClientExtensionsMapper<'a>>;


pub closed spec fn spec_client_extensions() -> SpecClientExtensionsCombinator {
    SpecClientExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate15770232246241775772 },
            snd: |deps| spec_client_extensions_cont(deps),
        },
        mapper: ClientExtensionsMapper::spec_new(),
    }
)
}


pub open spec fn spec_client_extensions_cont(deps: u16) -> SpecClientExtensionsExtensionsCombinator {
    let l = deps;
    spec_client_extensions_extensions(l)
}

                
pub fn client_extensions<'a>() -> (o: ClientExtensionsCombinator<'a>)
    ensures o@ == spec_client_extensions(),
{
    ClientExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate15770232246241775772 },
            snd: ClientExtensionsCont::new(),
            spec_snd: Ghost(|deps| spec_client_extensions_cont(deps)),
        },
        mapper: ClientExtensionsMapper::new(),
    }
)
}


pub struct ClientExtensionsCont<'a>(PhantomData<&'a ()>);
impl<'a> ClientExtensionsCont<'a> {
    pub fn new() -> Self {
        ClientExtensionsCont(PhantomData)
    }
}
impl<'a> Continuation<u16> for ClientExtensionsCont<'a> {
    type Output = ClientExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_client_extensions_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        client_extensions_extensions(l)
    }
}

                
pub struct SpecClientHello {
    pub legacy_version: SpecProtocolVersion,
    pub random: SpecRandom,
    pub legacy_session_id: SpecSessionId,
    pub cipher_suites: SpecCipherSuiteList,
    pub legacy_compression_methods: SpecOpaque1Ff,
    pub extensions: SpecClientExtensions,
}
pub type SpecClientHelloInner = (SpecProtocolVersion, (SpecRandom, (SpecSessionId, (SpecCipherSuiteList, (SpecOpaque1Ff, SpecClientExtensions)))));
impl SpecFrom<SpecClientHello> for SpecClientHelloInner {
    open spec fn spec_from(m: SpecClientHello) -> SpecClientHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl SpecFrom<SpecClientHelloInner> for SpecClientHello {
    open spec fn spec_from(m: SpecClientHelloInner) -> SpecClientHello {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        SpecClientHello {
            legacy_version,
            random,
            legacy_session_id,
            cipher_suites,
            legacy_compression_methods,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientHello<'a> {
    pub legacy_version: ProtocolVersion,
    pub random: Random<'a>,
    pub legacy_session_id: SessionId<'a>,
    pub cipher_suites: CipherSuiteList,
    pub legacy_compression_methods: Opaque1Ff<'a>,
    pub extensions: ClientExtensions<'a>,
}
pub type ClientHelloInner<'a> = (ProtocolVersion, (Random<'a>, (SessionId<'a>, (CipherSuiteList, (Opaque1Ff<'a>, ClientExtensions<'a>)))));
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
impl<'a> From<ClientHello<'a>> for ClientHelloInner<'a> {
    fn ex_from(m: ClientHello<'a>) -> ClientHelloInner<'a> {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl<'a> From<ClientHelloInner<'a>> for ClientHello<'a> {
    fn ex_from(m: ClientHelloInner<'a>) -> ClientHello<'a> {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        ClientHello {
            legacy_version,
            random,
            legacy_session_id,
            cipher_suites,
            legacy_compression_methods,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for ClientHelloMapper<'a> {
    type Src = ClientHelloInner<'a>;
    type Dst = ClientHello<'a>;
}
    

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
pub type SpecClientHelloCombinatorAlias = Mapped<(SpecProtocolVersionCombinator, (SpecRandomCombinator, (SpecSessionIdCombinator, (SpecCipherSuiteListCombinator, (SpecOpaque1FfCombinator, SpecClientExtensionsCombinator))))), ClientHelloMapper<'static>>;

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
pub type ClientHelloCombinatorAlias<'a> = Mapped<(ProtocolVersionCombinator, (RandomCombinator, (SessionIdCombinator<'a>, (CipherSuiteListCombinator<'a>, (Opaque1FfCombinator<'a>, ClientExtensionsCombinator<'a>))))), ClientHelloMapper<'a>>;


pub closed spec fn spec_client_hello() -> SpecClientHelloCombinator {
    SpecClientHelloCombinator(Mapped { inner: (spec_protocol_version(), (spec_random(), (spec_session_id(), (spec_cipher_suite_list(), (spec_opaque_1_ff(), spec_client_extensions()))))), mapper: ClientHelloMapper::spec_new() })
}


                
pub fn client_hello<'a>() -> (o: ClientHelloCombinator<'a>)
    ensures o@ == spec_client_hello(),
{
    ClientHelloCombinator(Mapped { inner: (protocol_version(), (random(), (session_id(), (cipher_suite_list(), (opaque_1_ff(), client_extensions()))))), mapper: ClientHelloMapper::new() })
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
        SpecServerExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerExtensions<'a> {
    pub l: u16,
    pub extensions: ServerExtensionsExtensions<'a>,
}
pub type ServerExtensionsInner<'a> = (u16, ServerExtensionsExtensions<'a>);
impl View for ServerExtensions<'_> {
    type V = SpecServerExtensions;
    open spec fn view(&self) -> Self::V {
        SpecServerExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ServerExtensions<'a>> for ServerExtensionsInner<'a> {
    fn ex_from(m: ServerExtensions<'a>) -> ServerExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<ServerExtensionsInner<'a>> for ServerExtensions<'a> {
    fn ex_from(m: ServerExtensionsInner<'a>) -> ServerExtensions<'a> {
        let (l, extensions) = m;
        ServerExtensions {
            l,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl<'a> Iso for ServerExtensionsMapper<'a> {
    type Src = ServerExtensionsInner<'a>;
    type Dst = ServerExtensions<'a>;
}
    
impl SpecPred for Predicate503472032047519273 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 6 && i <= 65535) {
            true
        } else {
            false
        }
    }
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
pub type SpecServerExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate503472032047519273>, SpecServerExtensionsExtensionsCombinator>, ServerExtensionsMapper<'static>>;
pub struct Predicate503472032047519273;
impl View for Predicate503472032047519273 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate503472032047519273 {
    type Input = u16;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 6 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

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
pub type ServerExtensionsCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, Refined<U16Be, Predicate503472032047519273>, ServerExtensionsExtensionsCombinator<'a>, ServerExtensionsCont<'a>>, ServerExtensionsMapper<'a>>;


pub closed spec fn spec_server_extensions() -> SpecServerExtensionsCombinator {
    SpecServerExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate503472032047519273 },
            snd: |deps| spec_server_extensions_cont(deps),
        },
        mapper: ServerExtensionsMapper::spec_new(),
    }
)
}


pub open spec fn spec_server_extensions_cont(deps: u16) -> SpecServerExtensionsExtensionsCombinator {
    let l = deps;
    spec_server_extensions_extensions(l)
}

                
pub fn server_extensions<'a>() -> (o: ServerExtensionsCombinator<'a>)
    ensures o@ == spec_server_extensions(),
{
    ServerExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate503472032047519273 },
            snd: ServerExtensionsCont::new(),
            spec_snd: Ghost(|deps| spec_server_extensions_cont(deps)),
        },
        mapper: ServerExtensionsMapper::new(),
    }
)
}


pub struct ServerExtensionsCont<'a>(PhantomData<&'a ()>);
impl<'a> ServerExtensionsCont<'a> {
    pub fn new() -> Self {
        ServerExtensionsCont(PhantomData)
    }
}
impl<'a> Continuation<u16> for ServerExtensionsCont<'a> {
    type Output = ServerExtensionsExtensionsCombinator<'a>;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_server_extensions_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        server_extensions_extensions(l)
    }
}

                
pub struct SpecServerHello {
    pub legacy_version: SpecProtocolVersion,
    pub random: SpecRandom,
    pub legacy_session_id_echo: SpecSessionId,
    pub cipher_suite: SpecCipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: SpecServerExtensions,
}
pub type SpecServerHelloInner = (SpecProtocolVersion, (SpecRandom, (SpecSessionId, (SpecCipherSuite, (u8, SpecServerExtensions)))));
impl SpecFrom<SpecServerHello> for SpecServerHelloInner {
    open spec fn spec_from(m: SpecServerHello) -> SpecServerHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))))
    }
}
impl SpecFrom<SpecServerHelloInner> for SpecServerHello {
    open spec fn spec_from(m: SpecServerHelloInner) -> SpecServerHello {
        let (legacy_version, (random, (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))))) = m;
        SpecServerHello {
            legacy_version,
            random,
            legacy_session_id_echo,
            cipher_suite,
            legacy_compression_method,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerHello<'a> {
    pub legacy_version: ProtocolVersion,
    pub random: Random<'a>,
    pub legacy_session_id_echo: SessionId<'a>,
    pub cipher_suite: CipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: ServerExtensions<'a>,
}
pub type ServerHelloInner<'a> = (ProtocolVersion, (Random<'a>, (SessionId<'a>, (CipherSuite, (u8, ServerExtensions<'a>)))));
impl View for ServerHello<'_> {
    type V = SpecServerHello;
    open spec fn view(&self) -> Self::V {
        SpecServerHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id_echo: self.legacy_session_id_echo@,
            cipher_suite: self.cipher_suite@,
            legacy_compression_method: self.legacy_compression_method@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ServerHello<'a>> for ServerHelloInner<'a> {
    fn ex_from(m: ServerHello<'a>) -> ServerHelloInner<'a> {
        (m.legacy_version, (m.random, (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))))
    }
}
impl<'a> From<ServerHelloInner<'a>> for ServerHello<'a> {
    fn ex_from(m: ServerHelloInner<'a>) -> ServerHello<'a> {
        let (legacy_version, (random, (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))))) = m;
        ServerHello {
            legacy_version,
            random,
            legacy_session_id_echo,
            cipher_suite,
            legacy_compression_method,
            extensions,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecServerHelloCombinatorAlias = Mapped<(SpecProtocolVersionCombinator, (SpecRandomCombinator, (SpecSessionIdCombinator, (SpecCipherSuiteCombinator, (Refined<U8, TagPred<u8>>, SpecServerExtensionsCombinator))))), ServerHelloMapper<'static>>;

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
pub type ServerHelloCombinatorAlias<'a> = Mapped<(ProtocolVersionCombinator, (RandomCombinator, (SessionIdCombinator<'a>, (CipherSuiteCombinator, (Refined<U8, TagPred<u8>>, ServerExtensionsCombinator<'a>))))), ServerHelloMapper<'a>>;


pub closed spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(Mapped { inner: (spec_protocol_version(), (spec_random(), (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, spec_server_extensions()))))), mapper: ServerHelloMapper::spec_new() })
}


                
pub fn server_hello<'a>() -> (o: ServerHelloCombinator<'a>)
    ensures o@ == spec_server_hello(),
{
    ServerHelloCombinator(Mapped { inner: (protocol_version(), (random(), (session_id(), (cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, server_extensions()))))), mapper: ServerHelloMapper::new() })
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


                
pub fn finished(digest_size: u24) -> (o: FinishedCombinator)
    ensures o@ == spec_finished(digest_size@),
{
    FinishedCombinator(Bytes(digest_size.ex_into()))
}


                
pub enum SpecHandshakeMsg {
    ClientHello(SpecClientHello),
    ServerHello(SpecServerHello),
    NewSessionTicket(SpecNewSessionTicket),
    EndOfEarlyData(SpecEmpty),
    EncryptedExtensions(SpecEncryptedExtensions),
    Certificate(SpecCertificate),
    CertificateRequest(SpecCertificateRequest),
    CertificateVerify(SpecCertificateVerify),
    Finished(SpecFinished),
    KeyUpdate(SpecKeyUpdate),
}
pub type SpecHandshakeMsgInner = Either<SpecClientHello, Either<SpecServerHello, Either<SpecNewSessionTicket, Either<SpecEmpty, Either<SpecEncryptedExtensions, Either<SpecCertificate, Either<SpecCertificateRequest, Either<SpecCertificateVerify, Either<SpecFinished, SpecKeyUpdate>>>>>>>>>;
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
    ServerHello(ServerHello<'a>),
    NewSessionTicket(NewSessionTicket<'a>),
    EndOfEarlyData(Empty<'a>),
    EncryptedExtensions(EncryptedExtensions<'a>),
    Certificate(Certificate<'a>),
    CertificateRequest(CertificateRequest<'a>),
    CertificateVerify(CertificateVerify<'a>),
    Finished(Finished<'a>),
    KeyUpdate(KeyUpdate),
}
pub type HandshakeMsgInner<'a> = Either<ClientHello<'a>, Either<ServerHello<'a>, Either<NewSessionTicket<'a>, Either<Empty<'a>, Either<EncryptedExtensions<'a>, Either<Certificate<'a>, Either<CertificateRequest<'a>, Either<CertificateVerify<'a>, Either<Finished<'a>, KeyUpdate>>>>>>>>>;
impl View for HandshakeMsg<'_> {
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecHandshakeMsgCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecClientHelloCombinator>, OrdChoice<Cond<SpecServerHelloCombinator>, OrdChoice<Cond<SpecNewSessionTicketCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEncryptedExtensionsCombinator>, OrdChoice<Cond<SpecCertificateCombinator>, OrdChoice<Cond<SpecCertificateRequestCombinator>, OrdChoice<Cond<SpecCertificateVerifyCombinator>, OrdChoice<Cond<SpecFinishedCombinator>, Cond<SpecKeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper<'static>>>;

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
pub type HandshakeMsgCombinatorAlias<'a> = AndThen<Bytes, Mapped<OrdChoice<Cond<ClientHelloCombinator<'a>>, OrdChoice<Cond<ServerHelloCombinator<'a>>, OrdChoice<Cond<NewSessionTicketCombinator<'a>>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EncryptedExtensionsCombinator<'a>>, OrdChoice<Cond<CertificateCombinator<'a>>, OrdChoice<Cond<CertificateRequestCombinator<'a>>, OrdChoice<Cond<CertificateVerifyCombinator<'a>>, OrdChoice<Cond<FinishedCombinator>, Cond<KeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper<'a>>>;


pub closed spec fn spec_handshake_msg(length: u24, msg_type: SpecHandshakeType) -> SpecHandshakeMsgCombinator {
    SpecHandshakeMsgCombinator(AndThen(Bytes(length.spec_into()), Mapped { inner: OrdChoice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: spec_client_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: spec_server_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: spec_new_session_ticket() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: spec_empty() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: spec_encrypted_extensions() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Certificate, inner: spec_certificate() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: spec_certificate_request() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: spec_certificate_verify() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Finished, inner: spec_finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: spec_key_update() }))))))))), mapper: HandshakeMsgMapper::spec_new() }))
}


                
pub fn handshake_msg<'a>(length: u24, msg_type: HandshakeType) -> (o: HandshakeMsgCombinator<'a>)
    ensures o@ == spec_handshake_msg(length@, msg_type@),
{
    HandshakeMsgCombinator(AndThen(Bytes(length.ex_into()), Mapped { inner: OrdChoice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: client_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: server_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: new_session_ticket() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: empty() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: encrypted_extensions() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Certificate, inner: certificate() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: certificate_request() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: certificate_verify() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Finished, inner: finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: key_update() }))))))))), mapper: HandshakeMsgMapper::new() }))
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
        SpecHandshake {
            msg_type,
            length,
            msg,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Handshake<'a> {
    pub msg_type: HandshakeType,
    pub length: u24,
    pub msg: HandshakeMsg<'a>,
}
pub type HandshakeInner<'a> = ((HandshakeType, u24), HandshakeMsg<'a>);
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
impl<'a> From<Handshake<'a>> for HandshakeInner<'a> {
    fn ex_from(m: Handshake<'a>) -> HandshakeInner<'a> {
        ((m.msg_type, m.length), m.msg)
    }
}
impl<'a> From<HandshakeInner<'a>> for Handshake<'a> {
    fn ex_from(m: HandshakeInner<'a>) -> Handshake<'a> {
        let ((msg_type, length), msg) = m;
        Handshake {
            msg_type,
            length,
            msg,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
pub type SpecHandshakeCombinatorAlias = Mapped<SpecDepend<(SpecHandshakeTypeCombinator, U24Be), SpecHandshakeMsgCombinator>, HandshakeMapper<'static>>;

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
pub type HandshakeCombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, (HandshakeTypeCombinator, U24Be), HandshakeMsgCombinator<'a>, HandshakeCont<'a>>, HandshakeMapper<'a>>;


pub closed spec fn spec_handshake() -> SpecHandshakeCombinator {
    SpecHandshakeCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_handshake_type(), U24Be),
            snd: |deps| spec_handshake_cont(deps),
        },
        mapper: HandshakeMapper::spec_new(),
    }
)
}


pub open spec fn spec_handshake_cont(deps: (SpecHandshakeType, u24)) -> SpecHandshakeMsgCombinator {
    let (msg_type, length) = deps;
    spec_handshake_msg(length, msg_type)
}

                
pub fn handshake<'a>() -> (o: HandshakeCombinator<'a>)
    ensures o@ == spec_handshake(),
{
    HandshakeCombinator(
    Mapped {
        inner: Depend {
            fst: (handshake_type(), U24Be),
            snd: HandshakeCont::new(),
            spec_snd: Ghost(|deps| spec_handshake_cont(deps)),
        },
        mapper: HandshakeMapper::new(),
    }
)
}


pub struct HandshakeCont<'a>(PhantomData<&'a ()>);
impl<'a> HandshakeCont<'a> {
    pub fn new() -> Self {
        HandshakeCont(PhantomData)
    }
}
impl<'a> Continuation<(HandshakeType, u24)> for HandshakeCont<'a> {
    type Output = HandshakeMsgCombinator<'a>;

    open spec fn requires(&self, deps: (HandshakeType, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (HandshakeType, u24), o: Self::Output) -> bool {
        o@ == spec_handshake_cont(deps@)
    }

    fn apply(&self, deps: (HandshakeType, u24)) -> Self::Output {
        let (msg_type, length) = deps;
        handshake_msg(length, msg_type)
    }
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
        SpecTlsCiphertext {
            opaque_type,
            version,
            encrypted_record,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsCiphertext<'a> {
    pub opaque_type: ContentType,
    pub version: ProtocolVersion,
    pub encrypted_record: Opaque0Ffff<'a>,
}
pub type TlsCiphertextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
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
impl<'a> From<TlsCiphertext<'a>> for TlsCiphertextInner<'a> {
    fn ex_from(m: TlsCiphertext<'a>) -> TlsCiphertextInner<'a> {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl<'a> From<TlsCiphertextInner<'a>> for TlsCiphertext<'a> {
    fn ex_from(m: TlsCiphertextInner<'a>) -> TlsCiphertext<'a> {
        let (opaque_type, (version, encrypted_record)) = m;
        TlsCiphertext {
            opaque_type,
            version,
            encrypted_record,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecTlsCiphertextCombinator(Mapped { inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())), mapper: TlsCiphertextMapper::spec_new() })
}


                
pub fn tls_ciphertext<'a>() -> (o: TlsCiphertextCombinator<'a>)
    ensures o@ == spec_tls_ciphertext(),
{
    TlsCiphertextCombinator(Mapped { inner: (content_type(), (protocol_version(), opaque_0_ffff())), mapper: TlsCiphertextMapper::new() })
}


                
pub struct SpecSupportedVersionsServer {
    pub selected_version: SpecProtocolVersion,
}
pub type SpecSupportedVersionsServerInner = SpecProtocolVersion;
impl SpecFrom<SpecSupportedVersionsServer> for SpecSupportedVersionsServerInner {
    open spec fn spec_from(m: SpecSupportedVersionsServer) -> SpecSupportedVersionsServerInner {
        m.selected_version
    }
}
impl SpecFrom<SpecSupportedVersionsServerInner> for SpecSupportedVersionsServer {
    open spec fn spec_from(m: SpecSupportedVersionsServerInner) -> SpecSupportedVersionsServer {
        let selected_version = m;
        SpecSupportedVersionsServer {
            selected_version,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupportedVersionsServer {
    pub selected_version: ProtocolVersion,
}
pub type SupportedVersionsServerInner = ProtocolVersion;
impl View for SupportedVersionsServer {
    type V = SpecSupportedVersionsServer;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsServer {
            selected_version: self.selected_version@,
        }
    }
}
impl From<SupportedVersionsServer> for SupportedVersionsServerInner {
    fn ex_from(m: SupportedVersionsServer) -> SupportedVersionsServerInner {
        m.selected_version
    }
}
impl From<SupportedVersionsServerInner> for SupportedVersionsServer {
    fn ex_from(m: SupportedVersionsServerInner) -> SupportedVersionsServer {
        let selected_version = m;
        SupportedVersionsServer {
            selected_version,
        }
    }
}

pub struct SupportedVersionsServerMapper;
impl SupportedVersionsServerMapper {
    pub closed spec fn spec_new() -> Self {
        SupportedVersionsServerMapper
    }
    pub fn new() -> Self {
        SupportedVersionsServerMapper
    }
}
impl View for SupportedVersionsServerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SupportedVersionsServerMapper {
    type Src = SpecSupportedVersionsServerInner;
    type Dst = SpecSupportedVersionsServer;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SupportedVersionsServerMapper {
    type Src = SupportedVersionsServerInner;
    type Dst = SupportedVersionsServer;
}
    

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
pub type SpecSupportedVersionsServerCombinatorAlias = Mapped<SpecProtocolVersionCombinator, SupportedVersionsServerMapper>;

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
pub type SupportedVersionsServerCombinatorAlias = Mapped<ProtocolVersionCombinator, SupportedVersionsServerMapper>;


pub closed spec fn spec_supported_versions_server() -> SpecSupportedVersionsServerCombinator {
    SpecSupportedVersionsServerCombinator(Mapped { inner: spec_protocol_version(), mapper: SupportedVersionsServerMapper::spec_new() })
}


                
pub fn supported_versions_server() -> (o: SupportedVersionsServerCombinator)
    ensures o@ == spec_supported_versions_server(),
{
    SupportedVersionsServerCombinator(Mapped { inner: protocol_version(), mapper: SupportedVersionsServerMapper::new() })
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
        SpecServerCertTypeServerExtension {
            server_certificate_type,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerCertTypeServerExtension {
    pub server_certificate_type: CertificateType,
}
pub type ServerCertTypeServerExtensionInner = CertificateType;
impl View for ServerCertTypeServerExtension {
    type V = SpecServerCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeServerExtension {
            server_certificate_type: self.server_certificate_type@,
        }
    }
}
impl From<ServerCertTypeServerExtension> for ServerCertTypeServerExtensionInner {
    fn ex_from(m: ServerCertTypeServerExtension) -> ServerCertTypeServerExtensionInner {
        m.server_certificate_type
    }
}
impl From<ServerCertTypeServerExtensionInner> for ServerCertTypeServerExtension {
    fn ex_from(m: ServerCertTypeServerExtensionInner) -> ServerCertTypeServerExtension {
        let server_certificate_type = m;
        ServerCertTypeServerExtension {
            server_certificate_type,
        }
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
    }
    proof fn spec_iso_rev(s: Self::Dst) {
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
    SpecServerCertTypeServerExtensionCombinator(Mapped { inner: spec_certificate_type(), mapper: ServerCertTypeServerExtensionMapper::spec_new() })
}


                
pub fn server_cert_type_server_extension() -> (o: ServerCertTypeServerExtensionCombinator)
    ensures o@ == spec_server_cert_type_server_extension(),
{
    ServerCertTypeServerExtensionCombinator(Mapped { inner: certificate_type(), mapper: ServerCertTypeServerExtensionMapper::new() })
}


                

}
