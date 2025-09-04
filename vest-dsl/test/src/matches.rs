
#![allow(warnings)]
#![allow(unused)]
use vstd::prelude::*;
use vest::regular::modifier::*;
use vest::regular::bytes;
use vest::regular::variant::*;
use vest::regular::sequence::*;
use vest::regular::repetition::*;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::utils::*;
use vest::properties::*;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::regular::leb128::*;

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
pub type SpecHelloRetryRequest = u16;
pub type HelloRetryRequest = u16;
pub type HelloRetryRequestRef<'a> = &'a u16;


pub struct SpecHelloRetryRequestCombinator(SpecHelloRetryRequestCombinatorAlias);

impl SpecCombinator for SpecHelloRetryRequestCombinator {
    type Type = SpecHelloRetryRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryRequestCombinator {
    type Type = HelloRetryRequest;
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
pub type ServerHelloRef<'a> = &'a u32;


pub struct SpecServerHelloCombinator(SpecServerHelloCombinatorAlias);

impl SpecCombinator for SpecServerHelloCombinator {
    type Type = SpecServerHello;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerHelloCombinator {
    type Type = ServerHello;
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

pub type Msg1PayloadInnerRef<'a> = Either<&'a HelloRetryRequest, &'a ServerHello>;


impl View for Msg1Payload {
    type V = SpecMsg1Payload;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg1Payload::Variant0(m) => SpecMsg1Payload::Variant0(m@),
            Msg1Payload::Variant1(m) => SpecMsg1Payload::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg1Payload> for Msg1PayloadInnerRef<'a> {
    fn ex_from(m: &'a Msg1Payload) -> Msg1PayloadInnerRef<'a> {
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
impl View for Msg1PayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1PayloadMapper {
    type Src = SpecMsg1PayloadInner;
    type Dst = SpecMsg1Payload;
}
impl SpecIsoProof for Msg1PayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg1PayloadMapper {
    type Src = Msg1PayloadInner;
    type Dst = Msg1Payload;
    type RefSrc = Msg1PayloadInnerRef<'a>;
}

type SpecMsg1PayloadCombinatorAlias1 = Choice<Cond<SpecHelloRetryRequestCombinator>, Cond<SpecServerHelloCombinator>>;
pub struct SpecMsg1PayloadCombinator(SpecMsg1PayloadCombinatorAlias);

impl SpecCombinator for SpecMsg1PayloadCombinator {
    type Type = SpecMsg1Payload;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg1PayloadCombinatorAlias = Mapped<SpecMsg1PayloadCombinatorAlias1, Msg1PayloadMapper>;
type Msg1PayloadCombinatorAlias1 = Choice<Cond<HelloRetryRequestCombinator>, Cond<ServerHelloCombinator>>;
struct Msg1PayloadCombinator1(Msg1PayloadCombinatorAlias1);
impl View for Msg1PayloadCombinator1 {
    type V = SpecMsg1PayloadCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg1PayloadCombinator1, Msg1PayloadCombinatorAlias1);

pub struct Msg1PayloadCombinator(Msg1PayloadCombinatorAlias);

impl View for Msg1PayloadCombinator {
    type V = SpecMsg1PayloadCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg1PayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1PayloadCombinator {
    type Type = Msg1Payload;
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
pub type Msg1PayloadCombinatorAlias = Mapped<Msg1PayloadCombinator1, Msg1PayloadMapper>;


pub closed spec fn spec_msg1_payload(b: Seq<u8>) -> SpecMsg1PayloadCombinator {
    SpecMsg1PayloadCombinator(Mapped { inner: Choice(Cond { cond: b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8], inner: spec_hello_retry_request() }, Cond { cond: !(b == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8]), inner: spec_server_hello() }), mapper: Msg1PayloadMapper })
}

pub fn msg1_payload<'a>(b: &'a [u8]) -> (o: Msg1PayloadCombinator)
    ensures o@ == spec_msg1_payload(b@),
{
    Msg1PayloadCombinator(Mapped { inner: Msg1PayloadCombinator1(Choice::new(Cond { cond: compare_slice(b, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice()), inner: hello_retry_request() }, Cond { cond: !(compare_slice(b, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice())), inner: server_hello() })), mapper: Msg1PayloadMapper })
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

pub type Msg2ContentInnerRef<'a> = Either<&'a u16, &'a u32>;


impl View for Msg2Content {
    type V = SpecMsg2Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg2Content::Variant0(m) => SpecMsg2Content::Variant0(m@),
            Msg2Content::Variant1(m) => SpecMsg2Content::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg2Content> for Msg2ContentInnerRef<'a> {
    fn ex_from(m: &'a Msg2Content) -> Msg2ContentInnerRef<'a> {
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
impl View for Msg2ContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2ContentMapper {
    type Src = SpecMsg2ContentInner;
    type Dst = SpecMsg2Content;
}
impl SpecIsoProof for Msg2ContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg2ContentMapper {
    type Src = Msg2ContentInner;
    type Dst = Msg2Content;
    type RefSrc = Msg2ContentInnerRef<'a>;
}

type SpecMsg2ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
pub struct SpecMsg2ContentCombinator(SpecMsg2ContentCombinatorAlias);

impl SpecCombinator for SpecMsg2ContentCombinator {
    type Type = SpecMsg2Content;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg2ContentCombinatorAlias = Mapped<SpecMsg2ContentCombinatorAlias1, Msg2ContentMapper>;
type Msg2ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
struct Msg2ContentCombinator1(Msg2ContentCombinatorAlias1);
impl View for Msg2ContentCombinator1 {
    type V = SpecMsg2ContentCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg2ContentCombinator1, Msg2ContentCombinatorAlias1);

pub struct Msg2ContentCombinator(Msg2ContentCombinatorAlias);

impl View for Msg2ContentCombinator {
    type V = SpecMsg2ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg2ContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2ContentCombinator {
    type Type = Msg2Content;
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
pub type Msg2ContentCombinatorAlias = Mapped<Msg2ContentCombinator1, Msg2ContentMapper>;


pub closed spec fn spec_msg2_content(b: Seq<u8>) -> SpecMsg2ContentCombinator {
    SpecMsg2ContentCombinator(Mapped { inner: Choice(Cond { cond: b == seq![22u8, 3u8, 1u8], inner: U16Le }, Cond { cond: !(b == seq![22u8, 3u8, 1u8]), inner: U32Le }), mapper: Msg2ContentMapper })
}

pub fn msg2_content<'a>(b: &'a [u8]) -> (o: Msg2ContentCombinator)
    ensures o@ == spec_msg2_content(b@),
{
    Msg2ContentCombinator(Mapped { inner: Msg2ContentCombinator1(Choice::new(Cond { cond: compare_slice(b, [22, 3, 1].as_slice()), inner: U16Le }, Cond { cond: !(compare_slice(b, [22, 3, 1].as_slice())), inner: U32Le })), mapper: Msg2ContentMapper })
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

pub type Msg1InnerRef<'a> = (&'a &'a [u8], &'a Msg1Payload);
impl<'a> From<&'a Msg1<'a>> for Msg1InnerRef<'a> {
    fn ex_from(m: &'a Msg1) -> Msg1InnerRef<'a> {
        (&m.b, &m.payload)
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (b, payload) = m;
        Msg1 { b, payload }
    }
}

pub struct Msg1Mapper;
impl View for Msg1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg1Mapper {
    type Src = SpecMsg1Inner;
    type Dst = SpecMsg1;
}
impl SpecIsoProof for Msg1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg1Mapper {
    type Src = Msg1Inner<'a>;
    type Dst = Msg1<'a>;
    type RefSrc = Msg1InnerRef<'a>;
}

pub struct SpecMsg1Combinator(SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg1CombinatorAlias = Mapped<SpecPair<bytes::Fixed<32>, SpecMsg1PayloadCombinator>, Msg1Mapper>;

pub struct Msg1Combinator(Msg1CombinatorAlias);

impl View for Msg1Combinator {
    type V = SpecMsg1Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg1Combinator {
    type Type = Msg1<'a>;
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
pub type Msg1CombinatorAlias = Mapped<Pair<bytes::Fixed<32>, Msg1PayloadCombinator, Msg1Cont0>, Msg1Mapper>;


pub closed spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
    Mapped {
        inner: Pair::spec_new(bytes::Fixed::<32>, |deps| spec_msg1_cont0(deps)),
        mapper: Msg1Mapper,
    })
}

pub open spec fn spec_msg1_cont0(deps: Seq<u8>) -> SpecMsg1PayloadCombinator {
    let b = deps;
    spec_msg1_payload(b)
}

impl View for Msg1Cont0 {
    type V = spec_fn(Seq<u8>) -> SpecMsg1PayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: Seq<u8>| {
            spec_msg1_cont0(deps)
        }
    }
}

                
pub fn msg1() -> (o: Msg1Combinator)
    ensures o@ == spec_msg1(),
{
    Msg1Combinator(
    Mapped {
        inner: Pair::new(bytes::Fixed::<32>, Msg1Cont0),
        mapper: Msg1Mapper,
    })
}

pub struct Msg1Cont0;
type Msg1Cont0Type<'a, 'b> = &'b &'a [u8];
type Msg1Cont0SType<'a, 'x> = &'x &'a [u8];
type Msg1Cont0Input<'a, 'b, 'x> = POrSType<Msg1Cont0Type<'a, 'b>, Msg1Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg1Cont0Input<'a, 'b, 'x>> for Msg1Cont0 {
    type Output = Msg1PayloadCombinator;

    open spec fn requires(&self, deps: Msg1Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg1Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg1_cont0(deps@)
    }

    fn apply(&self, deps: Msg1Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let b = *deps;
                msg1_payload(b)
            }
            POrSType::S(deps) => {
                let b = deps;
                let b = *b;
                msg1_payload(b)
            }
        }
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

pub type Msg5ContentInnerRef<'a> = Either<&'a u16, &'a &'a [u8]>;


impl<'a> View for Msg5Content<'a> {
    type V = SpecMsg5Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg5Content::Variant0(m) => SpecMsg5Content::Variant0(m@),
            Msg5Content::Variant1(m) => SpecMsg5Content::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg5Content<'a>> for Msg5ContentInnerRef<'a> {
    fn ex_from(m: &'a Msg5Content<'a>) -> Msg5ContentInnerRef<'a> {
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


pub struct Msg5ContentMapper;
impl View for Msg5ContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5ContentMapper {
    type Src = SpecMsg5ContentInner;
    type Dst = SpecMsg5Content;
}
impl SpecIsoProof for Msg5ContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg5ContentMapper {
    type Src = Msg5ContentInner<'a>;
    type Dst = Msg5Content<'a>;
    type RefSrc = Msg5ContentInnerRef<'a>;
}

type SpecMsg5ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct SpecMsg5ContentCombinator(SpecMsg5ContentCombinatorAlias);

impl SpecCombinator for SpecMsg5ContentCombinator {
    type Type = SpecMsg5Content;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg5ContentCombinatorAlias = Mapped<SpecMsg5ContentCombinatorAlias1, Msg5ContentMapper>;
type Msg5ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
struct Msg5ContentCombinator1(Msg5ContentCombinatorAlias1);
impl View for Msg5ContentCombinator1 {
    type V = SpecMsg5ContentCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg5ContentCombinator1, Msg5ContentCombinatorAlias1);

pub struct Msg5ContentCombinator(Msg5ContentCombinatorAlias);

impl View for Msg5ContentCombinator {
    type V = SpecMsg5ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg5ContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg5ContentCombinator {
    type Type = Msg5Content<'a>;
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
pub type Msg5ContentCombinatorAlias = Mapped<Msg5ContentCombinator1, Msg5ContentMapper>;


pub closed spec fn spec_msg5_content(i: VarInt) -> SpecMsg5ContentCombinator {
    SpecMsg5ContentCombinator(Mapped { inner: Choice(Cond { cond: i.spec_as_usize() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_usize() == 1), inner: bytes::Tail }), mapper: Msg5ContentMapper })
}

pub fn msg5_content<'a>(i: VarInt) -> (o: Msg5ContentCombinator)
    ensures o@ == spec_msg5_content(i@),
{
    Msg5ContentCombinator(Mapped { inner: Msg5ContentCombinator1(Choice::new(Cond { cond: i.as_usize() == 1, inner: U16Le }, Cond { cond: !(i.as_usize() == 1), inner: bytes::Tail })), mapper: Msg5ContentMapper })
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

pub type Msg5InnerRef<'a> = (&'a VarInt, &'a Msg5Content<'a>);
impl<'a> From<&'a Msg5<'a>> for Msg5InnerRef<'a> {
    fn ex_from(m: &'a Msg5) -> Msg5InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg5Inner<'a>> for Msg5<'a> {
    fn ex_from(m: Msg5Inner) -> Msg5 {
        let (i, content) = m;
        Msg5 { i, content }
    }
}

pub struct Msg5Mapper;
impl View for Msg5Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg5Mapper {
    type Src = SpecMsg5Inner;
    type Dst = SpecMsg5;
}
impl SpecIsoProof for Msg5Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg5Mapper {
    type Src = Msg5Inner<'a>;
    type Dst = Msg5<'a>;
    type RefSrc = Msg5InnerRef<'a>;
}

pub struct SpecMsg5Combinator(SpecMsg5CombinatorAlias);

impl SpecCombinator for SpecMsg5Combinator {
    type Type = SpecMsg5;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg5CombinatorAlias = Mapped<SpecPair<BtcVarint, SpecMsg5ContentCombinator>, Msg5Mapper>;

pub struct Msg5Combinator(Msg5CombinatorAlias);

impl View for Msg5Combinator {
    type V = SpecMsg5Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg5Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg5Combinator {
    type Type = Msg5<'a>;
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
pub type Msg5CombinatorAlias = Mapped<Pair<BtcVarint, Msg5ContentCombinator, Msg5Cont0>, Msg5Mapper>;


pub closed spec fn spec_msg5() -> SpecMsg5Combinator {
    SpecMsg5Combinator(
    Mapped {
        inner: Pair::spec_new(BtcVarint, |deps| spec_msg5_cont0(deps)),
        mapper: Msg5Mapper,
    })
}

pub open spec fn spec_msg5_cont0(deps: VarInt) -> SpecMsg5ContentCombinator {
    let i = deps;
    spec_msg5_content(i)
}

impl View for Msg5Cont0 {
    type V = spec_fn(VarInt) -> SpecMsg5ContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: VarInt| {
            spec_msg5_cont0(deps)
        }
    }
}

                
pub fn msg5() -> (o: Msg5Combinator)
    ensures o@ == spec_msg5(),
{
    Msg5Combinator(
    Mapped {
        inner: Pair::new(BtcVarint, Msg5Cont0),
        mapper: Msg5Mapper,
    })
}

pub struct Msg5Cont0;
type Msg5Cont0Type<'a, 'b> = &'b VarInt;
type Msg5Cont0SType<'a, 'x> = &'x VarInt;
type Msg5Cont0Input<'a, 'b, 'x> = POrSType<Msg5Cont0Type<'a, 'b>, Msg5Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg5Cont0Input<'a, 'b, 'x>> for Msg5Cont0 {
    type Output = Msg5ContentCombinator;

    open spec fn requires(&self, deps: Msg5Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg5Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg5_cont0(deps@)
    }

    fn apply(&self, deps: Msg5Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = *deps;
                msg5_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg5_content(i)
            }
        }
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

pub type Msg3ContentInnerRef<'a> = Either<&'a u16, Either<&'a u32, Either<&'a u32, &'a &'a [u8]>>>;


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


impl<'a> From<&'a Msg3Content<'a>> for Msg3ContentInnerRef<'a> {
    fn ex_from(m: &'a Msg3Content<'a>) -> Msg3ContentInnerRef<'a> {
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


pub struct Msg3ContentMapper;
impl View for Msg3ContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3ContentMapper {
    type Src = SpecMsg3ContentInner;
    type Dst = SpecMsg3Content;
}
impl SpecIsoProof for Msg3ContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg3ContentMapper {
    type Src = Msg3ContentInner<'a>;
    type Dst = Msg3Content<'a>;
    type RefSrc = Msg3ContentInnerRef<'a>;
}

type SpecMsg3ContentCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type SpecMsg3ContentCombinatorAlias2 = Choice<Cond<U32Le>, SpecMsg3ContentCombinatorAlias1>;
type SpecMsg3ContentCombinatorAlias3 = Choice<Cond<U16Le>, SpecMsg3ContentCombinatorAlias2>;
pub struct SpecMsg3ContentCombinator(SpecMsg3ContentCombinatorAlias);

impl SpecCombinator for SpecMsg3ContentCombinator {
    type Type = SpecMsg3Content;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg3ContentCombinatorAlias = Mapped<SpecMsg3ContentCombinatorAlias3, Msg3ContentMapper>;
type Msg3ContentCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type Msg3ContentCombinatorAlias2 = Choice<Cond<U32Le>, Msg3ContentCombinator1>;
type Msg3ContentCombinatorAlias3 = Choice<Cond<U16Le>, Msg3ContentCombinator2>;
struct Msg3ContentCombinator1(Msg3ContentCombinatorAlias1);
impl View for Msg3ContentCombinator1 {
    type V = SpecMsg3ContentCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3ContentCombinator1, Msg3ContentCombinatorAlias1);

struct Msg3ContentCombinator2(Msg3ContentCombinatorAlias2);
impl View for Msg3ContentCombinator2 {
    type V = SpecMsg3ContentCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3ContentCombinator2, Msg3ContentCombinatorAlias2);

struct Msg3ContentCombinator3(Msg3ContentCombinatorAlias3);
impl View for Msg3ContentCombinator3 {
    type V = SpecMsg3ContentCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg3ContentCombinator3, Msg3ContentCombinatorAlias3);

pub struct Msg3ContentCombinator(Msg3ContentCombinatorAlias);

impl View for Msg3ContentCombinator {
    type V = SpecMsg3ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg3ContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3ContentCombinator {
    type Type = Msg3Content<'a>;
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
pub type Msg3ContentCombinatorAlias = Mapped<Msg3ContentCombinator3, Msg3ContentMapper>;


pub closed spec fn spec_msg3_content(i: u8) -> SpecMsg3ContentCombinator {
    SpecMsg3ContentCombinator(Mapped { inner: Choice(Cond { cond: i == 1, inner: U16Le }, Choice(Cond { cond: i == 2, inner: U32Le }, Choice(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: bytes::Tail }))), mapper: Msg3ContentMapper })
}

pub fn msg3_content<'a>(i: u8) -> (o: Msg3ContentCombinator)
    ensures o@ == spec_msg3_content(i@),
{
    Msg3ContentCombinator(Mapped { inner: Msg3ContentCombinator3(Choice::new(Cond { cond: i == 1, inner: U16Le }, Msg3ContentCombinator2(Choice::new(Cond { cond: i == 2, inner: U32Le }, Msg3ContentCombinator1(Choice::new(Cond { cond: i == 3, inner: U32Le }, Cond { cond: !(i == 1 || i == 2 || i == 3), inner: bytes::Tail })))))), mapper: Msg3ContentMapper })
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

pub type Msg2InnerRef<'a> = (&'a &'a [u8], &'a Msg2Content);
impl<'a> From<&'a Msg2<'a>> for Msg2InnerRef<'a> {
    fn ex_from(m: &'a Msg2) -> Msg2InnerRef<'a> {
        (&m.b, &m.content)
    }
}

impl<'a> From<Msg2Inner<'a>> for Msg2<'a> {
    fn ex_from(m: Msg2Inner) -> Msg2 {
        let (b, content) = m;
        Msg2 { b, content }
    }
}

pub struct Msg2Mapper;
impl View for Msg2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg2Mapper {
    type Src = SpecMsg2Inner;
    type Dst = SpecMsg2;
}
impl SpecIsoProof for Msg2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg2Mapper {
    type Src = Msg2Inner<'a>;
    type Dst = Msg2<'a>;
    type RefSrc = Msg2InnerRef<'a>;
}

pub struct SpecMsg2Combinator(SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg2CombinatorAlias = Mapped<SpecPair<bytes::Fixed<3>, SpecMsg2ContentCombinator>, Msg2Mapper>;

pub struct Msg2Combinator(Msg2CombinatorAlias);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg2Combinator {
    type Type = Msg2<'a>;
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
pub type Msg2CombinatorAlias = Mapped<Pair<bytes::Fixed<3>, Msg2ContentCombinator, Msg2Cont0>, Msg2Mapper>;


pub closed spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(
    Mapped {
        inner: Pair::spec_new(bytes::Fixed::<3>, |deps| spec_msg2_cont0(deps)),
        mapper: Msg2Mapper,
    })
}

pub open spec fn spec_msg2_cont0(deps: Seq<u8>) -> SpecMsg2ContentCombinator {
    let b = deps;
    spec_msg2_content(b)
}

impl View for Msg2Cont0 {
    type V = spec_fn(Seq<u8>) -> SpecMsg2ContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: Seq<u8>| {
            spec_msg2_cont0(deps)
        }
    }
}

                
pub fn msg2() -> (o: Msg2Combinator)
    ensures o@ == spec_msg2(),
{
    Msg2Combinator(
    Mapped {
        inner: Pair::new(bytes::Fixed::<3>, Msg2Cont0),
        mapper: Msg2Mapper,
    })
}

pub struct Msg2Cont0;
type Msg2Cont0Type<'a, 'b> = &'b &'a [u8];
type Msg2Cont0SType<'a, 'x> = &'x &'a [u8];
type Msg2Cont0Input<'a, 'b, 'x> = POrSType<Msg2Cont0Type<'a, 'b>, Msg2Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg2Cont0Input<'a, 'b, 'x>> for Msg2Cont0 {
    type Output = Msg2ContentCombinator;

    open spec fn requires(&self, deps: Msg2Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg2Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg2_cont0(deps@)
    }

    fn apply(&self, deps: Msg2Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let b = *deps;
                msg2_content(b)
            }
            POrSType::S(deps) => {
                let b = deps;
                let b = *b;
                msg2_content(b)
            }
        }
    }
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

pub type Msg4ContentInnerRef<'a> = Either<&'a u16, &'a &'a [u8]>;


impl<'a> View for Msg4Content<'a> {
    type V = SpecMsg4Content;
    open spec fn view(&self) -> Self::V {
        match self {
            Msg4Content::Variant0(m) => SpecMsg4Content::Variant0(m@),
            Msg4Content::Variant1(m) => SpecMsg4Content::Variant1(m@),
        }
    }
}


impl<'a> From<&'a Msg4Content<'a>> for Msg4ContentInnerRef<'a> {
    fn ex_from(m: &'a Msg4Content<'a>) -> Msg4ContentInnerRef<'a> {
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


pub struct Msg4ContentMapper;
impl View for Msg4ContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4ContentMapper {
    type Src = SpecMsg4ContentInner;
    type Dst = SpecMsg4Content;
}
impl SpecIsoProof for Msg4ContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg4ContentMapper {
    type Src = Msg4ContentInner<'a>;
    type Dst = Msg4Content<'a>;
    type RefSrc = Msg4ContentInnerRef<'a>;
}

type SpecMsg4ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
pub struct SpecMsg4ContentCombinator(SpecMsg4ContentCombinatorAlias);

impl SpecCombinator for SpecMsg4ContentCombinator {
    type Type = SpecMsg4Content;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg4ContentCombinatorAlias = Mapped<SpecMsg4ContentCombinatorAlias1, Msg4ContentMapper>;
type Msg4ContentCombinatorAlias1 = Choice<Cond<U16Le>, Cond<bytes::Tail>>;
struct Msg4ContentCombinator1(Msg4ContentCombinatorAlias1);
impl View for Msg4ContentCombinator1 {
    type V = SpecMsg4ContentCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Msg4ContentCombinator1, Msg4ContentCombinatorAlias1);

pub struct Msg4ContentCombinator(Msg4ContentCombinatorAlias);

impl View for Msg4ContentCombinator {
    type V = SpecMsg4ContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4ContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4ContentCombinator {
    type Type = Msg4Content<'a>;
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
pub type Msg4ContentCombinatorAlias = Mapped<Msg4ContentCombinator1, Msg4ContentMapper>;


pub closed spec fn spec_msg4_content(i: u24) -> SpecMsg4ContentCombinator {
    SpecMsg4ContentCombinator(Mapped { inner: Choice(Cond { cond: i.spec_as_u32() == 1, inner: U16Le }, Cond { cond: !(i.spec_as_u32() == 1), inner: bytes::Tail }), mapper: Msg4ContentMapper })
}

pub fn msg4_content<'a>(i: u24) -> (o: Msg4ContentCombinator)
    ensures o@ == spec_msg4_content(i@),
{
    Msg4ContentCombinator(Mapped { inner: Msg4ContentCombinator1(Choice::new(Cond { cond: i.as_u32() == 1, inner: U16Le }, Cond { cond: !(i.as_u32() == 1), inner: bytes::Tail })), mapper: Msg4ContentMapper })
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

pub type Msg4InnerRef<'a> = (&'a u24, &'a Msg4Content<'a>);
impl<'a> From<&'a Msg4<'a>> for Msg4InnerRef<'a> {
    fn ex_from(m: &'a Msg4) -> Msg4InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner) -> Msg4 {
        let (i, content) = m;
        Msg4 { i, content }
    }
}

pub struct Msg4Mapper;
impl View for Msg4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg4Mapper {
    type Src = SpecMsg4Inner;
    type Dst = SpecMsg4;
}
impl SpecIsoProof for Msg4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg4Mapper {
    type Src = Msg4Inner<'a>;
    type Dst = Msg4<'a>;
    type RefSrc = Msg4InnerRef<'a>;
}

pub struct SpecMsg4Combinator(SpecMsg4CombinatorAlias);

impl SpecCombinator for SpecMsg4Combinator {
    type Type = SpecMsg4;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg4CombinatorAlias = Mapped<SpecPair<U24Le, SpecMsg4ContentCombinator>, Msg4Mapper>;

pub struct Msg4Combinator(Msg4CombinatorAlias);

impl View for Msg4Combinator {
    type V = SpecMsg4Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg4Combinator {
    type Type = Msg4<'a>;
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
pub type Msg4CombinatorAlias = Mapped<Pair<U24Le, Msg4ContentCombinator, Msg4Cont0>, Msg4Mapper>;


pub closed spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
    Mapped {
        inner: Pair::spec_new(U24Le, |deps| spec_msg4_cont0(deps)),
        mapper: Msg4Mapper,
    })
}

pub open spec fn spec_msg4_cont0(deps: u24) -> SpecMsg4ContentCombinator {
    let i = deps;
    spec_msg4_content(i)
}

impl View for Msg4Cont0 {
    type V = spec_fn(u24) -> SpecMsg4ContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u24| {
            spec_msg4_cont0(deps)
        }
    }
}

                
pub fn msg4() -> (o: Msg4Combinator)
    ensures o@ == spec_msg4(),
{
    Msg4Combinator(
    Mapped {
        inner: Pair::new(U24Le, Msg4Cont0),
        mapper: Msg4Mapper,
    })
}

pub struct Msg4Cont0;
type Msg4Cont0Type<'a, 'b> = &'b u24;
type Msg4Cont0SType<'a, 'x> = &'x u24;
type Msg4Cont0Input<'a, 'b, 'x> = POrSType<Msg4Cont0Type<'a, 'b>, Msg4Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg4Cont0Input<'a, 'b, 'x>> for Msg4Cont0 {
    type Output = Msg4ContentCombinator;

    open spec fn requires(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg4Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg4_cont0(deps@)
    }

    fn apply(&self, deps: Msg4Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = *deps;
                msg4_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg4_content(i)
            }
        }
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

pub type Msg3InnerRef<'a> = (&'a u8, &'a Msg3Content<'a>);
impl<'a> From<&'a Msg3<'a>> for Msg3InnerRef<'a> {
    fn ex_from(m: &'a Msg3) -> Msg3InnerRef<'a> {
        (&m.i, &m.content)
    }
}

impl<'a> From<Msg3Inner<'a>> for Msg3<'a> {
    fn ex_from(m: Msg3Inner) -> Msg3 {
        let (i, content) = m;
        Msg3 { i, content }
    }
}

pub struct Msg3Mapper;
impl View for Msg3Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Msg3Mapper {
    type Src = SpecMsg3Inner;
    type Dst = SpecMsg3;
}
impl SpecIsoProof for Msg3Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Msg3Mapper {
    type Src = Msg3Inner<'a>;
    type Dst = Msg3<'a>;
    type RefSrc = Msg3InnerRef<'a>;
}

pub struct SpecMsg3Combinator(SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
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
pub type SpecMsg3CombinatorAlias = Mapped<SpecPair<U8, SpecMsg3ContentCombinator>, Msg3Mapper>;

pub struct Msg3Combinator(Msg3CombinatorAlias);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;
    closed spec fn view(&self) -> Self::V { SpecMsg3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Msg3Combinator {
    type Type = Msg3<'a>;
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
pub type Msg3CombinatorAlias = Mapped<Pair<U8, Msg3ContentCombinator, Msg3Cont0>, Msg3Mapper>;


pub closed spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_msg3_cont0(deps)),
        mapper: Msg3Mapper,
    })
}

pub open spec fn spec_msg3_cont0(deps: u8) -> SpecMsg3ContentCombinator {
    let i = deps;
    spec_msg3_content(i)
}

impl View for Msg3Cont0 {
    type V = spec_fn(u8) -> SpecMsg3ContentCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_msg3_cont0(deps)
        }
    }
}

                
pub fn msg3() -> (o: Msg3Combinator)
    ensures o@ == spec_msg3(),
{
    Msg3Combinator(
    Mapped {
        inner: Pair::new(U8, Msg3Cont0),
        mapper: Msg3Mapper,
    })
}

pub struct Msg3Cont0;
type Msg3Cont0Type<'a, 'b> = &'b u8;
type Msg3Cont0SType<'a, 'x> = &'x u8;
type Msg3Cont0Input<'a, 'b, 'x> = POrSType<Msg3Cont0Type<'a, 'b>, Msg3Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Msg3Cont0Input<'a, 'b, 'x>> for Msg3Cont0 {
    type Output = Msg3ContentCombinator;

    open spec fn requires(&self, deps: Msg3Cont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Msg3Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_msg3_cont0(deps@)
    }

    fn apply(&self, deps: Msg3Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let i = *deps;
                msg3_content(i)
            }
            POrSType::S(deps) => {
                let i = deps;
                let i = *i;
                msg3_content(i)
            }
        }
    }
}
                

}
