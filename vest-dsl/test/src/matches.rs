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
pub type SpecHelloRetryRequest = u16;
pub type HelloRetryRequest = u16;


pub struct SpecHelloRetryRequestCombinator(SpecHelloRetryRequestCombinatorAlias);

impl SpecCombinator for SpecHelloRetryRequestCombinator {
    type Type = SpecHelloRetryRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHelloRetryRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecHelloRetryRequestCombinatorAlias = U16Le;

pub struct HelloRetryRequestCombinator(HelloRetryRequestCombinatorAlias);

impl View for HelloRetryRequestCombinator {
    type V = SpecHelloRetryRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryRequestCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for HelloRetryRequestCombinator {
    type Type = HelloRetryRequest;
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
pub type HelloRetryRequestCombinatorAlias = U16Le;


pub closed spec fn spec_hello_retry_request() -> SpecHelloRetryRequestCombinator {
    SpecHelloRetryRequestCombinator(U16Le)
}

                
pub fn hello_retry_request() -> (o: HelloRetryRequestCombinator)
    ensures o@ == spec_hello_retry_request(),
{
    HelloRetryRequestCombinator(U16Le)
}

                
pub type SpecServerHello = u32;
pub type ServerHello = u32;


pub struct SpecServerHelloCombinator(SpecServerHelloCombinatorAlias);

impl SpecCombinator for SpecServerHelloCombinator {
    type Type = SpecServerHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerHelloCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerHelloCombinatorAlias = U32Le;

pub struct ServerHelloCombinator(ServerHelloCombinatorAlias);

impl View for ServerHelloCombinator {
    type V = SpecServerHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerHelloCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for ServerHelloCombinator {
    type Type = ServerHello;
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
pub type ServerHelloCombinatorAlias = U32Le;


pub closed spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(U32Le)
}

                
pub fn server_hello() -> (o: ServerHelloCombinator)
    ensures o@ == spec_server_hello(),
{
    ServerHelloCombinator(U32Le)
}

                

pub enum SpecMsg1Payload {
    Variant0(SpecHelloRetryRequest),
    Variant1(SpecServerHello),
}

pub type SpecMsg1PayloadInner = Either<SpecHelloRetryRequest, SpecServerHello>;



impl SpecFrom<SpecMsg1Payload> for SpecMsg1PayloadInner {
    open spec fn spec_from(m: SpecMsg1Payload) -> SpecMsg1PayloadInner {
        match m {
            SpecMsg1Payload::Variant0(m) => Either::Left(m),
            SpecMsg1Payload::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecMsg1PayloadInner> for SpecMsg1Payload {
    open spec fn spec_from(m: SpecMsg1PayloadInner) -> SpecMsg1Payload {
        match m {
            Either::Left(m) => SpecMsg1Payload::Variant0(m),
            Either::Right(m) => SpecMsg1Payload::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg1Payload {
    Variant0(HelloRetryRequest),
    Variant1(ServerHello),
}

pub type Msg1PayloadInner = Either<HelloRetryRequest, ServerHello>;


impl View for Msg1Payload {
    type V = SpecMsg1Payload;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg1Payload::Variant0(m) => SpecMsg1Payload::Variant0(m@),
            Msg1Payload::Variant1(m) => SpecMsg1Payload::Variant1(m@),
        }
    }
}


impl From<Msg1Payload> for Msg1PayloadInner {
    fn ex_from(m: Msg1Payload) -> Msg1PayloadInner {
        match m {
            Msg1Payload::Variant0(m) => Either::Left(m),
            Msg1Payload::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<Msg1PayloadInner> for Msg1Payload {
    fn ex_from(m: Msg1PayloadInner) -> Msg1Payload {
        match m {
            Either::Left(m) => Msg1Payload::Variant0(m),
            Either::Right(m) => Msg1Payload::Variant1(m),
        }
    }
    
}


pub struct Msg1PayloadMapper;
impl Msg1PayloadMapper {
    pub closed spec fn spec_new() -> Self {
        Msg1PayloadMapper
    }
    pub fn new() -> Self {
        Msg1PayloadMapper
    }
}
impl View for Msg1PayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1PayloadMapper {
    type Src = SpecMsg1PayloadInner;
    type Dst = SpecMsg1Payload;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for Msg1PayloadMapper {
    type Src = Msg1PayloadInner;
    type Dst = Msg1Payload;
}


pub struct SpecMsg1PayloadCombinator(SpecMsg1PayloadCombinatorAlias);

impl SpecCombinator for SpecMsg1PayloadCombinator {
    type Type = SpecMsg1Payload;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg1PayloadCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg1PayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg1PayloadCombinatorAlias = Mapped<OrdChoice<Cond<SpecHelloRetryRequestCombinator>, Cond<SpecServerHelloCombinator>>, Msg1PayloadMapper>;

pub struct Msg1PayloadCombinator(Msg1PayloadCombinatorAlias);

impl View for Msg1PayloadCombinator {
    type V = SpecMsg1PayloadCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg1PayloadCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg1PayloadCombinator {
    type Type = Msg1Payload;
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
pub type Msg1PayloadCombinatorAlias = Mapped<OrdChoice<Cond<HelloRetryRequestCombinator>, Cond<ServerHelloCombinator>>, Msg1PayloadMapper>;


pub closed spec fn spec_msg1_payload(b: Seq<u8>) -> SpecMsg1PayloadCombinator {
    SpecMsg1PayloadCombinator(Mapped { inner: OrdChoice(Cond { cond: b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8], inner: spec_hello_retry_request() }, Cond { cond: !(b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8]), inner: spec_server_hello() }), mapper: Msg1PayloadMapper::spec_new() })
}

                
pub fn msg1_payload<'a>(b: &'a [u8]) -> (o: Msg1PayloadCombinator)
    ensures o@ == spec_msg1_payload(b@),
{
    Msg1PayloadCombinator(Mapped { inner: OrdChoice::new(Cond { cond: compare_slice(b, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice()), inner: hello_retry_request() }, Cond { cond: !(compare_slice(b, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice())), inner: server_hello() }), mapper: Msg1PayloadMapper::new() })
}

                

pub struct SpecMsg1 {
    pub b: Seq<u8>,
    pub payload: SpecMsg1Payload,
}

pub type SpecMsg1Inner = (Seq<u8>, SpecMsg1Payload);
impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(m: SpecMsg1) -> SpecMsg1Inner {
        (m.b, m.payload)
    }
}
impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(m: SpecMsg1Inner) -> SpecMsg1 {
        let (b, payload) = m;
        SpecMsg1 { b, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg1<'a> {
    pub b: &'a [u8],
    pub payload: Msg1Payload,
}

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 {
            b: self.b@,
            payload: self.payload@,
        }
    }
}
pub type Msg1Inner<'a> = (&'a [u8], Msg1Payload);
impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
    fn ex_from(m: Msg1) -> Msg1Inner {
        (m.b, m.payload)
    }
}
impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (b, payload) = m;
        Msg1 { b, payload }
    }
}

pub struct Msg1Mapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg1Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg1Mapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg1Mapper(PhantomData)
    }
}
impl View for Msg1Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1Mapper<'_> {
    type Src = SpecMsg1Inner;
    type Dst = SpecMsg1;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg1Mapper<'a> {
    type Src = Msg1Inner<'a>;
    type Dst = Msg1<'a>;
}

pub struct SpecMsg1Combinator(SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg1Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg1CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg1CombinatorAlias = Mapped<SpecDepend<BytesN<32>, SpecMsg1PayloadCombinator>, Msg1Mapper<'static>>;

pub struct Msg1Combinator<'a>(Msg1CombinatorAlias<'a>);

impl<'a> View for Msg1Combinator<'a> {
    type V = SpecMsg1Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg1Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg1Combinator<'a> {
    type Type = Msg1<'a>;
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
pub type Msg1CombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BytesN<32>, Msg1PayloadCombinator, Msg1Cont0<'a>>, Msg1Mapper<'a>>;


pub closed spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
    Mapped {
        inner: SpecDepend { fst: BytesN::<32>, snd: |deps| spec_msg1_cont0(deps) },
        mapper: Msg1Mapper::spec_new(),
    })
}

pub open spec fn spec_msg1_cont0(deps: Seq<u8>) -> SpecMsg1PayloadCombinator {
    let b = deps;
    spec_msg1_payload(b)
}
                
pub fn msg1<'a>() -> (o: Msg1Combinator<'a>)
    ensures o@ == spec_msg1(),
{
    Msg1Combinator(
    Mapped {
        inner: Depend { fst: BytesN::<32>, snd: Msg1Cont0::new(), spec_snd: Ghost(|deps| spec_msg1_cont0(deps)) },
        mapper: Msg1Mapper::new(),
    })
}

pub struct Msg1Cont0<'a>(PhantomData<&'a ()>);
impl<'a> Msg1Cont0<'a> {
    pub fn new() -> Self {
        Msg1Cont0(PhantomData)
    }
}
impl<'a> Continuation<&&'a [u8]> for Msg1Cont0<'a> {
    type Output = Msg1PayloadCombinator;

    open spec fn requires(&self, deps: &&'a [u8]) -> bool { true }

    open spec fn ensures(&self, deps: &&'a [u8], o: Self::Output) -> bool {
        o@ == spec_msg1_cont0(deps@)
    }

    fn apply(&self, deps: &&'a [u8]) -> Self::Output {
        let b = *deps;
        msg1_payload(b)
    }
}
                

pub enum SpecMsg5Content {
    Variant0(u16),
    Variant1(Seq<u8>),
}

pub type SpecMsg5ContentInner = Either<u16, Seq<u8>>;



impl SpecFrom<SpecMsg5Content> for SpecMsg5ContentInner {
    open spec fn spec_from(m: SpecMsg5Content) -> SpecMsg5ContentInner {
        match m {
            SpecMsg5Content::Variant0(m) => Either::Left(m),
            SpecMsg5Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecMsg5ContentInner> for SpecMsg5Content {
    open spec fn spec_from(m: SpecMsg5ContentInner) -> SpecMsg5Content {
        match m {
            Either::Left(m) => SpecMsg5Content::Variant0(m),
            Either::Right(m) => SpecMsg5Content::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg5Content<'a> {
    Variant0(u16),
    Variant1(&'a [u8]),
}

pub type Msg5ContentInner<'a> = Either<u16, &'a [u8]>;


impl<'a> View for Msg5Content<'a> {
    type V = SpecMsg5Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg5Content::Variant0(m) => SpecMsg5Content::Variant0(m@),
            Msg5Content::Variant1(m) => SpecMsg5Content::Variant1(m@),
        }
    }
}


impl<'a> From<Msg5Content<'a>> for Msg5ContentInner<'a> {
    fn ex_from(m: Msg5Content<'a>) -> Msg5ContentInner<'a> {
        match m {
            Msg5Content::Variant0(m) => Either::Left(m),
            Msg5Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<Msg5ContentInner<'a>> for Msg5Content<'a> {
    fn ex_from(m: Msg5ContentInner<'a>) -> Msg5Content<'a> {
        match m {
            Either::Left(m) => Msg5Content::Variant0(m),
            Either::Right(m) => Msg5Content::Variant1(m),
        }
    }
    
}


pub struct Msg5ContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg5ContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg5ContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg5ContentMapper(PhantomData)
    }
}
impl View for Msg5ContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5ContentMapper<'_> {
    type Src = SpecMsg5ContentInner;
    type Dst = SpecMsg5Content;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg5ContentMapper<'a> {
    type Src = Msg5ContentInner<'a>;
    type Dst = Msg5Content<'a>;
}


pub struct SpecMsg5ContentCombinator(SpecMsg5ContentCombinatorAlias);

impl SpecCombinator for SpecMsg5ContentCombinator {
    type Type = SpecMsg5Content;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg5ContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg5ContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg5ContentCombinatorAlias = Mapped<OrdChoice<Cond<U16Le>, Cond<Tail>>, Msg5ContentMapper<'static>>;

pub struct Msg5ContentCombinator<'a>(Msg5ContentCombinatorAlias<'a>);

impl<'a> View for Msg5ContentCombinator<'a> {
    type V = SpecMsg5ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg5ContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg5ContentCombinator<'a> {
    type Type = Msg5Content<'a>;
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
pub type Msg5ContentCombinatorAlias<'a> = Mapped<OrdChoice<Cond<U16Le>, Cond<Tail>>, Msg5ContentMapper<'a>>;


pub closed spec fn spec_msg5_content(i: VarInt) -> SpecMsg5ContentCombinator {
    SpecMsg5ContentCombinator(Mapped { inner: OrdChoice(Cond { cond: i.spec_as_usize() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_usize() == 1), inner: Tail }), mapper: Msg5ContentMapper::spec_new() })
}

                
pub fn msg5_content<'a>(i: VarInt) -> (o: Msg5ContentCombinator<'a>)
    ensures o@ == spec_msg5_content(i@),
{
    Msg5ContentCombinator(Mapped { inner: OrdChoice::new(Cond { cond: i.as_usize() == 1, inner: U16Le }, Cond { cond: !(i.as_usize() == 1), inner: Tail }), mapper: Msg5ContentMapper::new() })
}

                

pub struct SpecMsg5 {
    pub i: VarInt,
    pub content: SpecMsg5Content,
}

pub type SpecMsg5Inner = (VarInt, SpecMsg5Content);
impl SpecFrom<SpecMsg5> for SpecMsg5Inner {
    open spec fn spec_from(m: SpecMsg5) -> SpecMsg5Inner {
        (m.i, m.content)
    }
}
impl SpecFrom<SpecMsg5Inner> for SpecMsg5 {
    open spec fn spec_from(m: SpecMsg5Inner) -> SpecMsg5 {
        let (i, content) = m;
        SpecMsg5 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg5<'a> {
    pub i: VarInt,
    pub content: Msg5Content<'a>,
}

impl View for Msg5<'_> {
    type V = SpecMsg5;

    open spec fn view(&self) -> Self::V {
        SpecMsg5 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg5Inner<'a> = (VarInt, Msg5Content<'a>);
impl<'a> From<Msg5<'a>> for Msg5Inner<'a> {
    fn ex_from(m: Msg5) -> Msg5Inner {
        (m.i, m.content)
    }
}
impl<'a> From<Msg5Inner<'a>> for Msg5<'a> {
    fn ex_from(m: Msg5Inner) -> Msg5 {
        let (i, content) = m;
        Msg5 { i, content }
    }
}

pub struct Msg5Mapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg5Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg5Mapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg5Mapper(PhantomData)
    }
}
impl View for Msg5Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5Mapper<'_> {
    type Src = SpecMsg5Inner;
    type Dst = SpecMsg5;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg5Mapper<'a> {
    type Src = Msg5Inner<'a>;
    type Dst = Msg5<'a>;
}

pub struct SpecMsg5Combinator(SpecMsg5CombinatorAlias);

impl SpecCombinator for SpecMsg5Combinator {
    type Type = SpecMsg5;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg5Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg5CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg5CombinatorAlias = Mapped<SpecDepend<BtcVarint, SpecMsg5ContentCombinator>, Msg5Mapper<'static>>;

pub struct Msg5Combinator<'a>(Msg5CombinatorAlias<'a>);

impl<'a> View for Msg5Combinator<'a> {
    type V = SpecMsg5Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg5Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg5Combinator<'a> {
    type Type = Msg5<'a>;
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
pub type Msg5CombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BtcVarint, Msg5ContentCombinator<'a>, Msg5Cont0<'a>>, Msg5Mapper<'a>>;


pub closed spec fn spec_msg5() -> SpecMsg5Combinator {
    SpecMsg5Combinator(
    Mapped {
        inner: SpecDepend { fst: BtcVarint, snd: |deps| spec_msg5_cont0(deps) },
        mapper: Msg5Mapper::spec_new(),
    })
}

pub open spec fn spec_msg5_cont0(deps: VarInt) -> SpecMsg5ContentCombinator {
    let i = deps;
    spec_msg5_content(i)
}
                
pub fn msg5<'a>() -> (o: Msg5Combinator<'a>)
    ensures o@ == spec_msg5(),
{
    Msg5Combinator(
    Mapped {
        inner: Depend { fst: BtcVarint, snd: Msg5Cont0::new(), spec_snd: Ghost(|deps| spec_msg5_cont0(deps)) },
        mapper: Msg5Mapper::new(),
    })
}

pub struct Msg5Cont0<'a>(PhantomData<&'a ()>);
impl<'a> Msg5Cont0<'a> {
    pub fn new() -> Self {
        Msg5Cont0(PhantomData)
    }
}
impl<'a> Continuation<&VarInt> for Msg5Cont0<'a> {
    type Output = Msg5ContentCombinator<'a>;

    open spec fn requires(&self, deps: &VarInt) -> bool { true }

    open spec fn ensures(&self, deps: &VarInt, o: Self::Output) -> bool {
        o@ == spec_msg5_cont0(deps@)
    }

    fn apply(&self, deps: &VarInt) -> Self::Output {
        let i = *deps;
        msg5_content(i)
    }
}
                

pub enum SpecMsg3Content {
    Variant0(u16),
    Variant1(u32),
    Variant2(u32),
    Variant3(Seq<u8>),
}

pub type SpecMsg3ContentInner = Either<u16, Either<u32, Either<u32, Seq<u8>>>>;



impl SpecFrom<SpecMsg3Content> for SpecMsg3ContentInner {
    open spec fn spec_from(m: SpecMsg3Content) -> SpecMsg3ContentInner {
        match m {
            SpecMsg3Content::Variant0(m) => Either::Left(m),
            SpecMsg3Content::Variant1(m) => Either::Right(Either::Left(m)),
            SpecMsg3Content::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMsg3Content::Variant3(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl SpecFrom<SpecMsg3ContentInner> for SpecMsg3Content {
    open spec fn spec_from(m: SpecMsg3ContentInner) -> SpecMsg3Content {
        match m {
            Either::Left(m) => SpecMsg3Content::Variant0(m),
            Either::Right(Either::Left(m)) => SpecMsg3Content::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMsg3Content::Variant2(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecMsg3Content::Variant3(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg3Content<'a> {
    Variant0(u16),
    Variant1(u32),
    Variant2(u32),
    Variant3(&'a [u8]),
}

pub type Msg3ContentInner<'a> = Either<u16, Either<u32, Either<u32, &'a [u8]>>>;


impl<'a> View for Msg3Content<'a> {
    type V = SpecMsg3Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg3Content::Variant0(m) => SpecMsg3Content::Variant0(m@),
            Msg3Content::Variant1(m) => SpecMsg3Content::Variant1(m@),
            Msg3Content::Variant2(m) => SpecMsg3Content::Variant2(m@),
            Msg3Content::Variant3(m) => SpecMsg3Content::Variant3(m@),
        }
    }
}


impl<'a> From<Msg3Content<'a>> for Msg3ContentInner<'a> {
    fn ex_from(m: Msg3Content<'a>) -> Msg3ContentInner<'a> {
        match m {
            Msg3Content::Variant0(m) => Either::Left(m),
            Msg3Content::Variant1(m) => Either::Right(Either::Left(m)),
            Msg3Content::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            Msg3Content::Variant3(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<Msg3ContentInner<'a>> for Msg3Content<'a> {
    fn ex_from(m: Msg3ContentInner<'a>) -> Msg3Content<'a> {
        match m {
            Either::Left(m) => Msg3Content::Variant0(m),
            Either::Right(Either::Left(m)) => Msg3Content::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => Msg3Content::Variant2(m),
            Either::Right(Either::Right(Either::Right(m))) => Msg3Content::Variant3(m),
        }
    }
    
}


pub struct Msg3ContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg3ContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg3ContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg3ContentMapper(PhantomData)
    }
}
impl View for Msg3ContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3ContentMapper<'_> {
    type Src = SpecMsg3ContentInner;
    type Dst = SpecMsg3Content;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg3ContentMapper<'a> {
    type Src = Msg3ContentInner<'a>;
    type Dst = Msg3Content<'a>;
}


pub struct SpecMsg3ContentCombinator(SpecMsg3ContentCombinatorAlias);

impl SpecCombinator for SpecMsg3ContentCombinator {
    type Type = SpecMsg3Content;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg3ContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg3ContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg3ContentCombinatorAlias = Mapped<OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>, Msg3ContentMapper<'static>>;

pub struct Msg3ContentCombinator<'a>(Msg3ContentCombinatorAlias<'a>);

impl<'a> View for Msg3ContentCombinator<'a> {
    type V = SpecMsg3ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg3ContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg3ContentCombinator<'a> {
    type Type = Msg3Content<'a>;
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
pub type Msg3ContentCombinatorAlias<'a> = Mapped<OrdChoice<Cond<U16Le>, OrdChoice<Cond<U32Le>, OrdChoice<Cond<U32Le>, Cond<Tail>>>>, Msg3ContentMapper<'a>>;


pub closed spec fn spec_msg3_content(i: u8) -> SpecMsg3ContentCombinator {
    SpecMsg3ContentCombinator(Mapped { inner: OrdChoice(Cond { cond: i == 1, inner: U16Le }, OrdChoice(Cond { cond: i == 2, inner: U32Le }, OrdChoice(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: Tail }))), mapper: Msg3ContentMapper::spec_new() })
}

                
pub fn msg3_content<'a>(i: u8) -> (o: Msg3ContentCombinator<'a>)
    ensures o@ == spec_msg3_content(i@),
{
    Msg3ContentCombinator(Mapped { inner: OrdChoice::new(Cond { cond: i == 1, inner: U16Le }, OrdChoice::new(Cond { cond: i == 2, inner: U32Le }, OrdChoice::new(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: Tail }))), mapper: Msg3ContentMapper::new() })
}

                

pub enum SpecMsg2Content {
    Variant0(u16),
    Variant1(u32),
}

pub type SpecMsg2ContentInner = Either<u16, u32>;



impl SpecFrom<SpecMsg2Content> for SpecMsg2ContentInner {
    open spec fn spec_from(m: SpecMsg2Content) -> SpecMsg2ContentInner {
        match m {
            SpecMsg2Content::Variant0(m) => Either::Left(m),
            SpecMsg2Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecMsg2ContentInner> for SpecMsg2Content {
    open spec fn spec_from(m: SpecMsg2ContentInner) -> SpecMsg2Content {
        match m {
            Either::Left(m) => SpecMsg2Content::Variant0(m),
            Either::Right(m) => SpecMsg2Content::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg2Content {
    Variant0(u16),
    Variant1(u32),
}

pub type Msg2ContentInner = Either<u16, u32>;


impl View for Msg2Content {
    type V = SpecMsg2Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg2Content::Variant0(m) => SpecMsg2Content::Variant0(m@),
            Msg2Content::Variant1(m) => SpecMsg2Content::Variant1(m@),
        }
    }
}


impl From<Msg2Content> for Msg2ContentInner {
    fn ex_from(m: Msg2Content) -> Msg2ContentInner {
        match m {
            Msg2Content::Variant0(m) => Either::Left(m),
            Msg2Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<Msg2ContentInner> for Msg2Content {
    fn ex_from(m: Msg2ContentInner) -> Msg2Content {
        match m {
            Either::Left(m) => Msg2Content::Variant0(m),
            Either::Right(m) => Msg2Content::Variant1(m),
        }
    }
    
}


pub struct Msg2ContentMapper;
impl Msg2ContentMapper {
    pub closed spec fn spec_new() -> Self {
        Msg2ContentMapper
    }
    pub fn new() -> Self {
        Msg2ContentMapper
    }
}
impl View for Msg2ContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2ContentMapper {
    type Src = SpecMsg2ContentInner;
    type Dst = SpecMsg2Content;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl Iso for Msg2ContentMapper {
    type Src = Msg2ContentInner;
    type Dst = Msg2Content;
}


pub struct SpecMsg2ContentCombinator(SpecMsg2ContentCombinatorAlias);

impl SpecCombinator for SpecMsg2ContentCombinator {
    type Type = SpecMsg2Content;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg2ContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg2ContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg2ContentCombinatorAlias = Mapped<OrdChoice<Cond<U16Le>, Cond<U32Le>>, Msg2ContentMapper>;

pub struct Msg2ContentCombinator(Msg2ContentCombinatorAlias);

impl View for Msg2ContentCombinator {
    type V = SpecMsg2ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg2ContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg2ContentCombinator {
    type Type = Msg2Content;
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
pub type Msg2ContentCombinatorAlias = Mapped<OrdChoice<Cond<U16Le>, Cond<U32Le>>, Msg2ContentMapper>;


pub closed spec fn spec_msg2_content(b: Seq<u8>) -> SpecMsg2ContentCombinator {
    SpecMsg2ContentCombinator(Mapped { inner: OrdChoice(Cond { cond: b == seq![22u8, 3u8, 1u8], inner: U16Le }, Cond { cond: !(b == seq![22u8, 3u8, 1u8]), inner: U32Le }), mapper: Msg2ContentMapper::spec_new() })
}

                
pub fn msg2_content<'a>(b: &'a [u8]) -> (o: Msg2ContentCombinator)
    ensures o@ == spec_msg2_content(b@),
{
    Msg2ContentCombinator(Mapped { inner: OrdChoice::new(Cond { cond: compare_slice(b, [22, 3, 1].as_slice()), inner: U16Le }, Cond { cond: !(compare_slice(b, [22, 3, 1].as_slice())), inner: U32Le }), mapper: Msg2ContentMapper::new() })
}

                

pub enum SpecMsg4Content {
    Variant0(u16),
    Variant1(Seq<u8>),
}

pub type SpecMsg4ContentInner = Either<u16, Seq<u8>>;



impl SpecFrom<SpecMsg4Content> for SpecMsg4ContentInner {
    open spec fn spec_from(m: SpecMsg4Content) -> SpecMsg4ContentInner {
        match m {
            SpecMsg4Content::Variant0(m) => Either::Left(m),
            SpecMsg4Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl SpecFrom<SpecMsg4ContentInner> for SpecMsg4Content {
    open spec fn spec_from(m: SpecMsg4ContentInner) -> SpecMsg4Content {
        match m {
            Either::Left(m) => SpecMsg4Content::Variant0(m),
            Either::Right(m) => SpecMsg4Content::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg4Content<'a> {
    Variant0(u16),
    Variant1(&'a [u8]),
}

pub type Msg4ContentInner<'a> = Either<u16, &'a [u8]>;


impl<'a> View for Msg4Content<'a> {
    type V = SpecMsg4Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg4Content::Variant0(m) => SpecMsg4Content::Variant0(m@),
            Msg4Content::Variant1(m) => SpecMsg4Content::Variant1(m@),
        }
    }
}


impl<'a> From<Msg4Content<'a>> for Msg4ContentInner<'a> {
    fn ex_from(m: Msg4Content<'a>) -> Msg4ContentInner<'a> {
        match m {
            Msg4Content::Variant0(m) => Either::Left(m),
            Msg4Content::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<Msg4ContentInner<'a>> for Msg4Content<'a> {
    fn ex_from(m: Msg4ContentInner<'a>) -> Msg4Content<'a> {
        match m {
            Either::Left(m) => Msg4Content::Variant0(m),
            Either::Right(m) => Msg4Content::Variant1(m),
        }
    }
    
}


pub struct Msg4ContentMapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg4ContentMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg4ContentMapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg4ContentMapper(PhantomData)
    }
}
impl View for Msg4ContentMapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4ContentMapper<'_> {
    type Src = SpecMsg4ContentInner;
    type Dst = SpecMsg4Content;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg4ContentMapper<'a> {
    type Src = Msg4ContentInner<'a>;
    type Dst = Msg4Content<'a>;
}


pub struct SpecMsg4ContentCombinator(SpecMsg4ContentCombinatorAlias);

impl SpecCombinator for SpecMsg4ContentCombinator {
    type Type = SpecMsg4Content;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg4ContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg4ContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg4ContentCombinatorAlias = Mapped<OrdChoice<Cond<U16Le>, Cond<Tail>>, Msg4ContentMapper<'static>>;

pub struct Msg4ContentCombinator<'a>(Msg4ContentCombinatorAlias<'a>);

impl<'a> View for Msg4ContentCombinator<'a> {
    type V = SpecMsg4ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4ContentCombinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg4ContentCombinator<'a> {
    type Type = Msg4Content<'a>;
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
pub type Msg4ContentCombinatorAlias<'a> = Mapped<OrdChoice<Cond<U16Le>, Cond<Tail>>, Msg4ContentMapper<'a>>;


pub closed spec fn spec_msg4_content(i: u24) -> SpecMsg4ContentCombinator {
    SpecMsg4ContentCombinator(Mapped { inner: OrdChoice(Cond { cond: i.spec_as_u32() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_u32() == 1), inner: Tail }), mapper: Msg4ContentMapper::spec_new() })
}

                
pub fn msg4_content<'a>(i: u24) -> (o: Msg4ContentCombinator<'a>)
    ensures o@ == spec_msg4_content(i@),
{
    Msg4ContentCombinator(Mapped { inner: OrdChoice::new(Cond { cond: i.as_u32() == 1, inner: U16Le }, Cond { cond: !(i.as_u32() == 1), inner: Tail }), mapper: Msg4ContentMapper::new() })
}

                

pub struct SpecMsg4 {
    pub i: u24,
    pub content: SpecMsg4Content,
}

pub type SpecMsg4Inner = (u24, SpecMsg4Content);
impl SpecFrom<SpecMsg4> for SpecMsg4Inner {
    open spec fn spec_from(m: SpecMsg4) -> SpecMsg4Inner {
        (m.i, m.content)
    }
}
impl SpecFrom<SpecMsg4Inner> for SpecMsg4 {
    open spec fn spec_from(m: SpecMsg4Inner) -> SpecMsg4 {
        let (i, content) = m;
        SpecMsg4 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg4<'a> {
    pub i: u24,
    pub content: Msg4Content<'a>,
}

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg4Inner<'a> = (u24, Msg4Content<'a>);
impl<'a> From<Msg4<'a>> for Msg4Inner<'a> {
    fn ex_from(m: Msg4) -> Msg4Inner {
        (m.i, m.content)
    }
}
impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner) -> Msg4 {
        let (i, content) = m;
        Msg4 { i, content }
    }
}

pub struct Msg4Mapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg4Mapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg4Mapper(PhantomData)
    }
}
impl View for Msg4Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4Mapper<'_> {
    type Src = SpecMsg4Inner;
    type Dst = SpecMsg4;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg4Mapper<'a> {
    type Src = Msg4Inner<'a>;
    type Dst = Msg4<'a>;
}

pub struct SpecMsg4Combinator(SpecMsg4CombinatorAlias);

impl SpecCombinator for SpecMsg4Combinator {
    type Type = SpecMsg4;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg4Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg4CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg4CombinatorAlias = Mapped<SpecDepend<U24Le, SpecMsg4ContentCombinator>, Msg4Mapper<'static>>;

pub struct Msg4Combinator<'a>(Msg4CombinatorAlias<'a>);

impl<'a> View for Msg4Combinator<'a> {
    type V = SpecMsg4Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg4Combinator<'a> {
    type Type = Msg4<'a>;
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
pub type Msg4CombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U24Le, Msg4ContentCombinator<'a>, Msg4Cont0<'a>>, Msg4Mapper<'a>>;


pub closed spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
    Mapped {
        inner: SpecDepend { fst: U24Le, snd: |deps| spec_msg4_cont0(deps) },
        mapper: Msg4Mapper::spec_new(),
    })
}

pub open spec fn spec_msg4_cont0(deps: u24) -> SpecMsg4ContentCombinator {
    let i = deps;
    spec_msg4_content(i)
}
                
pub fn msg4<'a>() -> (o: Msg4Combinator<'a>)
    ensures o@ == spec_msg4(),
{
    Msg4Combinator(
    Mapped {
        inner: Depend { fst: U24Le, snd: Msg4Cont0::new(), spec_snd: Ghost(|deps| spec_msg4_cont0(deps)) },
        mapper: Msg4Mapper::new(),
    })
}

pub struct Msg4Cont0<'a>(PhantomData<&'a ()>);
impl<'a> Msg4Cont0<'a> {
    pub fn new() -> Self {
        Msg4Cont0(PhantomData)
    }
}
impl<'a> Continuation<&u24> for Msg4Cont0<'a> {
    type Output = Msg4ContentCombinator<'a>;

    open spec fn requires(&self, deps: &u24) -> bool { true }

    open spec fn ensures(&self, deps: &u24, o: Self::Output) -> bool {
        o@ == spec_msg4_cont0(deps@)
    }

    fn apply(&self, deps: &u24) -> Self::Output {
        let i = *deps;
        msg4_content(i)
    }
}
                

pub struct SpecMsg3 {
    pub i: u8,
    pub content: SpecMsg3Content,
}

pub type SpecMsg3Inner = (u8, SpecMsg3Content);
impl SpecFrom<SpecMsg3> for SpecMsg3Inner {
    open spec fn spec_from(m: SpecMsg3) -> SpecMsg3Inner {
        (m.i, m.content)
    }
}
impl SpecFrom<SpecMsg3Inner> for SpecMsg3 {
    open spec fn spec_from(m: SpecMsg3Inner) -> SpecMsg3 {
        let (i, content) = m;
        SpecMsg3 { i, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg3<'a> {
    pub i: u8,
    pub content: Msg3Content<'a>,
}

impl View for Msg3<'_> {
    type V = SpecMsg3;

    open spec fn view(&self) -> Self::V {
        SpecMsg3 {
            i: self.i@,
            content: self.content@,
        }
    }
}
pub type Msg3Inner<'a> = (u8, Msg3Content<'a>);
impl<'a> From<Msg3<'a>> for Msg3Inner<'a> {
    fn ex_from(m: Msg3) -> Msg3Inner {
        (m.i, m.content)
    }
}
impl<'a> From<Msg3Inner<'a>> for Msg3<'a> {
    fn ex_from(m: Msg3Inner) -> Msg3 {
        let (i, content) = m;
        Msg3 { i, content }
    }
}

pub struct Msg3Mapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg3Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg3Mapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg3Mapper(PhantomData)
    }
}
impl View for Msg3Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3Mapper<'_> {
    type Src = SpecMsg3Inner;
    type Dst = SpecMsg3;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg3Mapper<'a> {
    type Src = Msg3Inner<'a>;
    type Dst = Msg3<'a>;
}

pub struct SpecMsg3Combinator(SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg3Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg3CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg3CombinatorAlias = Mapped<SpecDepend<U8, SpecMsg3ContentCombinator>, Msg3Mapper<'static>>;

pub struct Msg3Combinator<'a>(Msg3CombinatorAlias<'a>);

impl<'a> View for Msg3Combinator<'a> {
    type V = SpecMsg3Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg3Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg3Combinator<'a> {
    type Type = Msg3<'a>;
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
pub type Msg3CombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, U8, Msg3ContentCombinator<'a>, Msg3Cont0<'a>>, Msg3Mapper<'a>>;


pub closed spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(
    Mapped {
        inner: SpecDepend { fst: U8, snd: |deps| spec_msg3_cont0(deps) },
        mapper: Msg3Mapper::spec_new(),
    })
}

pub open spec fn spec_msg3_cont0(deps: u8) -> SpecMsg3ContentCombinator {
    let i = deps;
    spec_msg3_content(i)
}
                
pub fn msg3<'a>() -> (o: Msg3Combinator<'a>)
    ensures o@ == spec_msg3(),
{
    Msg3Combinator(
    Mapped {
        inner: Depend { fst: U8, snd: Msg3Cont0::new(), spec_snd: Ghost(|deps| spec_msg3_cont0(deps)) },
        mapper: Msg3Mapper::new(),
    })
}

pub struct Msg3Cont0<'a>(PhantomData<&'a ()>);
impl<'a> Msg3Cont0<'a> {
    pub fn new() -> Self {
        Msg3Cont0(PhantomData)
    }
}
impl<'a> Continuation<&u8> for Msg3Cont0<'a> {
    type Output = Msg3ContentCombinator<'a>;

    open spec fn requires(&self, deps: &u8) -> bool { true }

    open spec fn ensures(&self, deps: &u8, o: Self::Output) -> bool {
        o@ == spec_msg3_cont0(deps@)
    }

    fn apply(&self, deps: &u8) -> Self::Output {
        let i = *deps;
        msg3_content(i)
    }
}
                

pub struct SpecMsg2 {
    pub b: Seq<u8>,
    pub content: SpecMsg2Content,
}

pub type SpecMsg2Inner = (Seq<u8>, SpecMsg2Content);
impl SpecFrom<SpecMsg2> for SpecMsg2Inner {
    open spec fn spec_from(m: SpecMsg2) -> SpecMsg2Inner {
        (m.b, m.content)
    }
}
impl SpecFrom<SpecMsg2Inner> for SpecMsg2 {
    open spec fn spec_from(m: SpecMsg2Inner) -> SpecMsg2 {
        let (b, content) = m;
        SpecMsg2 { b, content }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Msg2<'a> {
    pub b: &'a [u8],
    pub content: Msg2Content,
}

impl View for Msg2<'_> {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 {
            b: self.b@,
            content: self.content@,
        }
    }
}
pub type Msg2Inner<'a> = (&'a [u8], Msg2Content);
impl<'a> From<Msg2<'a>> for Msg2Inner<'a> {
    fn ex_from(m: Msg2) -> Msg2Inner {
        (m.b, m.content)
    }
}
impl<'a> From<Msg2Inner<'a>> for Msg2<'a> {
    fn ex_from(m: Msg2Inner) -> Msg2 {
        let (b, content) = m;
        Msg2 { b, content }
    }
}

pub struct Msg2Mapper<'a>(PhantomData<&'a ()>);
impl<'a> Msg2Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg2Mapper(PhantomData)
    }
    pub fn new() -> Self {
        Msg2Mapper(PhantomData)
    }
}
impl View for Msg2Mapper<'_> {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2Mapper<'_> {
    type Src = SpecMsg2Inner;
    type Dst = SpecMsg2;
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso for Msg2Mapper<'a> {
    type Src = Msg2Inner<'a>;
    type Dst = Msg2<'a>;
}

pub struct SpecMsg2Combinator(SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMsg2Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMsg2CombinatorAlias::is_prefix_secure() }
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
pub type SpecMsg2CombinatorAlias = Mapped<SpecDepend<BytesN<3>, SpecMsg2ContentCombinator>, Msg2Mapper<'static>>;

pub struct Msg2Combinator<'a>(Msg2CombinatorAlias<'a>);

impl<'a> View for Msg2Combinator<'a> {
    type V = SpecMsg2Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg2Combinator(self.0@) }
}
impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg2Combinator<'a> {
    type Type = Msg2<'a>;
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
pub type Msg2CombinatorAlias<'a> = Mapped<Depend<&'a [u8], Vec<u8>, BytesN<3>, Msg2ContentCombinator, Msg2Cont0<'a>>, Msg2Mapper<'a>>;


pub closed spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(
    Mapped {
        inner: SpecDepend { fst: BytesN::<3>, snd: |deps| spec_msg2_cont0(deps) },
        mapper: Msg2Mapper::spec_new(),
    })
}

pub open spec fn spec_msg2_cont0(deps: Seq<u8>) -> SpecMsg2ContentCombinator {
    let b = deps;
    spec_msg2_content(b)
}
                
pub fn msg2<'a>() -> (o: Msg2Combinator<'a>)
    ensures o@ == spec_msg2(),
{
    Msg2Combinator(
    Mapped {
        inner: Depend { fst: BytesN::<3>, snd: Msg2Cont0::new(), spec_snd: Ghost(|deps| spec_msg2_cont0(deps)) },
        mapper: Msg2Mapper::new(),
    })
}

pub struct Msg2Cont0<'a>(PhantomData<&'a ()>);
impl<'a> Msg2Cont0<'a> {
    pub fn new() -> Self {
        Msg2Cont0(PhantomData)
    }
}
impl<'a> Continuation<&&'a [u8]> for Msg2Cont0<'a> {
    type Output = Msg2ContentCombinator;

    open spec fn requires(&self, deps: &&'a [u8]) -> bool { true }

    open spec fn ensures(&self, deps: &&'a [u8], o: Self::Output) -> bool {
        o@ == spec_msg2_cont0(deps@)
    }

    fn apply(&self, deps: &&'a [u8]) -> Self::Output {
        let b = *deps;
        msg2_content(b)
    }
}
                

}
