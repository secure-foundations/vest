
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
use vest_lib::infallible::*;
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

            impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for $combinator {
                fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
                { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
            }
        } // verus!
    };
}
verus!{

pub struct SpecGenericHeader {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u16,
}

pub type SpecGenericHeaderInner = (u8, (u8, u16));


impl SpecFrom<SpecGenericHeader> for SpecGenericHeaderInner {
    open spec fn spec_from(m: SpecGenericHeader) -> SpecGenericHeaderInner {
        (m.next_type, (m.reserved, m.payload_length))
    }
}

impl SpecFrom<SpecGenericHeaderInner> for SpecGenericHeader {
    open spec fn spec_from(m: SpecGenericHeaderInner) -> SpecGenericHeader {
        let (next_type, (reserved, payload_length)) = m;
        SpecGenericHeader { next_type, reserved, payload_length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct GenericHeader {
    pub next_type: u8,
    pub reserved: u8,
    pub payload_length: u16,
}

impl View for GenericHeader {
    type V = SpecGenericHeader;

    open spec fn view(&self) -> Self::V {
        SpecGenericHeader {
            next_type: self.next_type@,
            reserved: self.reserved@,
            payload_length: self.payload_length@,
        }
    }
}
pub type GenericHeaderInner = (u8, (u8, u16));

pub type GenericHeaderInnerRef<'a> = (&'a u8, (&'a u8, &'a u16));
impl<'a> From<&'a GenericHeader> for GenericHeaderInnerRef<'a> {
    fn ex_from(m: &'a GenericHeader) -> GenericHeaderInnerRef<'a> {
        (&m.next_type, (&m.reserved, &m.payload_length))
    }
}

impl From<GenericHeaderInner> for GenericHeader {
    fn ex_from(m: GenericHeaderInner) -> GenericHeader {
        let (next_type, (reserved, payload_length)) = m;
        GenericHeader { next_type, reserved, payload_length }
    }
}

pub struct GenericHeaderMapper;
impl View for GenericHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GenericHeaderMapper {
    type Src = SpecGenericHeaderInner;
    type Dst = SpecGenericHeader;
}
impl SpecIsoProof for GenericHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GenericHeaderMapper {
    type Src = GenericHeaderInner;
    type Dst = GenericHeader;
    type RefSrc = GenericHeaderInnerRef<'a>;
}
type SpecGenericHeaderCombinatorAlias1 = (U8, Refined<U16Le, Predicate18193225726552524852>);
type SpecGenericHeaderCombinatorAlias2 = (U8, SpecGenericHeaderCombinatorAlias1);
pub struct SpecGenericHeaderCombinator(pub SpecGenericHeaderCombinatorAlias);

impl SpecCombinator for SpecGenericHeaderCombinator {
    type Type = SpecGenericHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGenericHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecGenericHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecGenericHeaderCombinatorAlias = Mapped<SpecGenericHeaderCombinatorAlias2, GenericHeaderMapper>;
pub struct Predicate18193225726552524852;
impl View for Predicate18193225726552524852 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate18193225726552524852 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate18193225726552524852 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}
type GenericHeaderCombinatorAlias1 = (U8, Refined<U16Le, Predicate18193225726552524852>);
type GenericHeaderCombinatorAlias2 = (U8, GenericHeaderCombinator1);
pub struct GenericHeaderCombinator1(pub GenericHeaderCombinatorAlias1);
impl View for GenericHeaderCombinator1 {
    type V = SpecGenericHeaderCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(GenericHeaderCombinator1, GenericHeaderCombinatorAlias1);

pub struct GenericHeaderCombinator2(pub GenericHeaderCombinatorAlias2);
impl View for GenericHeaderCombinator2 {
    type V = SpecGenericHeaderCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(GenericHeaderCombinator2, GenericHeaderCombinatorAlias2);

pub struct GenericHeaderCombinator(pub GenericHeaderCombinatorAlias);

impl View for GenericHeaderCombinator {
    type V = SpecGenericHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecGenericHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GenericHeaderCombinator {
    type Type = GenericHeader;
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
impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for GenericHeaderCombinator {
    fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
}
pub type GenericHeaderCombinatorAlias = Mapped<GenericHeaderCombinator2, GenericHeaderMapper>;


pub open spec fn spec_generic_header() -> SpecGenericHeaderCombinator {
    SpecGenericHeaderCombinator(
    Mapped {
        inner: (U8, (U8, Refined { inner: U16Le, predicate: Predicate18193225726552524852 })),
        mapper: GenericHeaderMapper,
    })
}

                
pub fn generic_header<'a>() -> (o: GenericHeaderCombinator)
    ensures o@ == spec_generic_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = GenericHeaderCombinator(
    Mapped {
        inner: GenericHeaderCombinator2((U8, GenericHeaderCombinator1((U8, Refined { inner: U16Le, predicate: Predicate18193225726552524852 })))),
        mapper: GenericHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_generic_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_generic_header<'a>(input: &'a [u8]) -> (res: PResult<<GenericHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_generic_header().spec_parse(input@) == Some((n as int, v@)),
        spec_generic_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_generic_header().spec_parse(input@) is None,
        spec_generic_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = generic_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_generic_header<'a>(v: <GenericHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_generic_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_generic_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_generic_header().spec_serialize(v@))
        },
{
    let combinator = generic_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_generic_header_infallible<'a>(v: <GenericHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_generic_header().wf(v@),
        spec_generic_header().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_generic_header().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_generic_header().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_generic_header().spec_serialize(v@)),
{
    let combinator = generic_header();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn generic_header_len<'a>(v: <GenericHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_generic_header().wf(v@),
        spec_generic_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_generic_header().spec_serialize(v@).len(),
{
    let combinator = generic_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecOuterHeader {
    pub magic: u32,
    pub inner: SpecGenericHeader,
}

pub type SpecOuterHeaderInner = (u32, SpecGenericHeader);


impl SpecFrom<SpecOuterHeader> for SpecOuterHeaderInner {
    open spec fn spec_from(m: SpecOuterHeader) -> SpecOuterHeaderInner {
        (m.magic, m.inner)
    }
}

impl SpecFrom<SpecOuterHeaderInner> for SpecOuterHeader {
    open spec fn spec_from(m: SpecOuterHeaderInner) -> SpecOuterHeader {
        let (magic, inner) = m;
        SpecOuterHeader { magic, inner }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OuterHeader {
    pub magic: u32,
    pub inner: GenericHeader,
}

impl View for OuterHeader {
    type V = SpecOuterHeader;

    open spec fn view(&self) -> Self::V {
        SpecOuterHeader {
            magic: self.magic@,
            inner: self.inner@,
        }
    }
}
pub type OuterHeaderInner = (u32, GenericHeader);

pub type OuterHeaderInnerRef<'a> = (&'a u32, &'a GenericHeader);
impl<'a> From<&'a OuterHeader> for OuterHeaderInnerRef<'a> {
    fn ex_from(m: &'a OuterHeader) -> OuterHeaderInnerRef<'a> {
        (&m.magic, &m.inner)
    }
}

impl From<OuterHeaderInner> for OuterHeader {
    fn ex_from(m: OuterHeaderInner) -> OuterHeader {
        let (magic, inner) = m;
        OuterHeader { magic, inner }
    }
}

pub struct OuterHeaderMapper;
impl View for OuterHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OuterHeaderMapper {
    type Src = SpecOuterHeaderInner;
    type Dst = SpecOuterHeader;
}
impl SpecIsoProof for OuterHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OuterHeaderMapper {
    type Src = OuterHeaderInner;
    type Dst = OuterHeader;
    type RefSrc = OuterHeaderInnerRef<'a>;
}
type SpecOuterHeaderCombinatorAlias1 = (U32Le, SpecGenericHeaderCombinator);
pub struct SpecOuterHeaderCombinator(pub SpecOuterHeaderCombinatorAlias);

impl SpecCombinator for SpecOuterHeaderCombinator {
    type Type = SpecOuterHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOuterHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecOuterHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecOuterHeaderCombinatorAlias = Mapped<SpecOuterHeaderCombinatorAlias1, OuterHeaderMapper>;
type OuterHeaderCombinatorAlias1 = (U32Le, GenericHeaderCombinator);
pub struct OuterHeaderCombinator1(pub OuterHeaderCombinatorAlias1);
impl View for OuterHeaderCombinator1 {
    type V = SpecOuterHeaderCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(OuterHeaderCombinator1, OuterHeaderCombinatorAlias1);

pub struct OuterHeaderCombinator(pub OuterHeaderCombinatorAlias);

impl View for OuterHeaderCombinator {
    type V = SpecOuterHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecOuterHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OuterHeaderCombinator {
    type Type = OuterHeader;
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
impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for OuterHeaderCombinator {
    fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
}
pub type OuterHeaderCombinatorAlias = Mapped<OuterHeaderCombinator1, OuterHeaderMapper>;


pub open spec fn spec_outer_header() -> SpecOuterHeaderCombinator {
    SpecOuterHeaderCombinator(
    Mapped {
        inner: (U32Le, spec_generic_header()),
        mapper: OuterHeaderMapper,
    })
}

                
pub fn outer_header<'a>() -> (o: OuterHeaderCombinator)
    ensures o@ == spec_outer_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = OuterHeaderCombinator(
    Mapped {
        inner: OuterHeaderCombinator1((U32Le, generic_header())),
        mapper: OuterHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_outer_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_outer_header<'a>(input: &'a [u8]) -> (res: PResult<<OuterHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_outer_header().spec_parse(input@) == Some((n as int, v@)),
        spec_outer_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_outer_header().spec_parse(input@) is None,
        spec_outer_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = outer_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_outer_header<'a>(v: <OuterHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_outer_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_outer_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_outer_header().spec_serialize(v@))
        },
{
    let combinator = outer_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_outer_header_infallible<'a>(v: <OuterHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_outer_header().wf(v@),
        spec_outer_header().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_outer_header().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_outer_header().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_outer_header().spec_serialize(v@)),
{
    let combinator = outer_header();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn outer_header_len<'a>(v: <OuterHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_outer_header().wf(v@),
        spec_outer_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_outer_header().spec_serialize(v@).len(),
{
    let combinator = outer_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecPayloadWithHeader {
    pub hdr: SpecGenericHeader,
    pub body: Seq<u8>,
}

pub type SpecPayloadWithHeaderInner = (SpecGenericHeader, Seq<u8>);


impl SpecFrom<SpecPayloadWithHeader> for SpecPayloadWithHeaderInner {
    open spec fn spec_from(m: SpecPayloadWithHeader) -> SpecPayloadWithHeaderInner {
        (m.hdr, m.body)
    }
}

impl SpecFrom<SpecPayloadWithHeaderInner> for SpecPayloadWithHeader {
    open spec fn spec_from(m: SpecPayloadWithHeaderInner) -> SpecPayloadWithHeader {
        let (hdr, body) = m;
        SpecPayloadWithHeader { hdr, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PayloadWithHeader<'a> {
    pub hdr: GenericHeader,
    pub body: &'a [u8],
}

impl View for PayloadWithHeader<'_> {
    type V = SpecPayloadWithHeader;

    open spec fn view(&self) -> Self::V {
        SpecPayloadWithHeader {
            hdr: self.hdr@,
            body: self.body@,
        }
    }
}
pub type PayloadWithHeaderInner<'a> = (GenericHeader, &'a [u8]);

pub type PayloadWithHeaderInnerRef<'a> = (&'a GenericHeader, &'a &'a [u8]);
impl<'a> From<&'a PayloadWithHeader<'a>> for PayloadWithHeaderInnerRef<'a> {
    fn ex_from(m: &'a PayloadWithHeader) -> PayloadWithHeaderInnerRef<'a> {
        (&m.hdr, &m.body)
    }
}

impl<'a> From<PayloadWithHeaderInner<'a>> for PayloadWithHeader<'a> {
    fn ex_from(m: PayloadWithHeaderInner) -> PayloadWithHeader {
        let (hdr, body) = m;
        PayloadWithHeader { hdr, body }
    }
}

pub struct PayloadWithHeaderMapper;
impl View for PayloadWithHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PayloadWithHeaderMapper {
    type Src = SpecPayloadWithHeaderInner;
    type Dst = SpecPayloadWithHeader;
}
impl SpecIsoProof for PayloadWithHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PayloadWithHeaderMapper {
    type Src = PayloadWithHeaderInner<'a>;
    type Dst = PayloadWithHeader<'a>;
    type RefSrc = PayloadWithHeaderInnerRef<'a>;
}

pub struct SpecPayloadWithHeaderCombinator(pub SpecPayloadWithHeaderCombinatorAlias);

impl SpecCombinator for SpecPayloadWithHeaderCombinator {
    type Type = SpecPayloadWithHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPayloadWithHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPayloadWithHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecPayloadWithHeaderCombinatorAlias = Mapped<SpecPair<SpecGenericHeaderCombinator, bytes::Variable>, PayloadWithHeaderMapper>;

pub struct PayloadWithHeaderCombinator(pub PayloadWithHeaderCombinatorAlias);

impl View for PayloadWithHeaderCombinator {
    type V = SpecPayloadWithHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecPayloadWithHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PayloadWithHeaderCombinator {
    type Type = PayloadWithHeader<'a>;
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
impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for PayloadWithHeaderCombinator {
    fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
}
pub type PayloadWithHeaderCombinatorAlias = Mapped<Pair<GenericHeaderCombinator, bytes::Variable, PayloadWithHeaderCont0>, PayloadWithHeaderMapper>;


pub open spec fn spec_payload_with_header() -> SpecPayloadWithHeaderCombinator {
    SpecPayloadWithHeaderCombinator(
    Mapped {
        inner: Pair::spec_new(spec_generic_header(), |deps| spec_payload_with_header_cont0(deps)),
        mapper: PayloadWithHeaderMapper,
    })
}

pub open spec fn spec_payload_with_header_cont0(deps: SpecGenericHeader) -> bytes::Variable {
    let hdr = deps;
    bytes::Variable(((usize::spec_from(hdr.payload_length) - 4)) as usize)
}

impl View for PayloadWithHeaderCont0 {
    type V = spec_fn(SpecGenericHeader) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: SpecGenericHeader| {
            spec_payload_with_header_cont0(deps)
        }
    }
}

                
pub fn payload_with_header<'a>() -> (o: PayloadWithHeaderCombinator)
    ensures o@ == spec_payload_with_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PayloadWithHeaderCombinator(
    Mapped {
        inner: Pair::new(generic_header(), PayloadWithHeaderCont0),
        mapper: PayloadWithHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_payload_with_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_payload_with_header<'a>(input: &'a [u8]) -> (res: PResult<<PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_payload_with_header().spec_parse(input@) == Some((n as int, v@)),
        spec_payload_with_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_payload_with_header().spec_parse(input@) is None,
        spec_payload_with_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = payload_with_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_payload_with_header<'a>(v: <PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_payload_with_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_payload_with_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_payload_with_header().spec_serialize(v@))
        },
{
    let combinator = payload_with_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_payload_with_header_infallible<'a>(v: <PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_payload_with_header().wf(v@),
        spec_payload_with_header().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_payload_with_header().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_payload_with_header().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_payload_with_header().spec_serialize(v@)),
{
    let combinator = payload_with_header();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn payload_with_header_len<'a>(v: <PayloadWithHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_payload_with_header().wf(v@),
        spec_payload_with_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_payload_with_header().spec_serialize(v@).len(),
{
    let combinator = payload_with_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct PayloadWithHeaderCont0;
type PayloadWithHeaderCont0Type<'a, 'b> = &'b GenericHeader;
type PayloadWithHeaderCont0SType<'a, 'x> = &'x GenericHeader;
type PayloadWithHeaderCont0Input<'a, 'b, 'x> = POrSType<PayloadWithHeaderCont0Type<'a, 'b>, PayloadWithHeaderCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PayloadWithHeaderCont0Input<'a, 'b, 'x>> for PayloadWithHeaderCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: PayloadWithHeaderCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_generic_header()).wf(deps@)
        }

    open spec fn ensures(&self, deps: PayloadWithHeaderCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_payload_with_header_cont0(deps@)
    }

    fn apply(&self, deps: PayloadWithHeaderCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let hdr = deps;
                bytes::Variable(((usize::ex_from(hdr.payload_length) - 4)) as usize)
            }
            POrSType::S(deps) => {
                let hdr = deps;
                bytes::Variable(((usize::ex_from(hdr.payload_length) - 4)) as usize)
            }
        }
    }
}
                

pub struct SpecDeepNested {
    pub outer: SpecOuterHeader,
    pub data: Seq<u8>,
}

pub type SpecDeepNestedInner = (SpecOuterHeader, Seq<u8>);


impl SpecFrom<SpecDeepNested> for SpecDeepNestedInner {
    open spec fn spec_from(m: SpecDeepNested) -> SpecDeepNestedInner {
        (m.outer, m.data)
    }
}

impl SpecFrom<SpecDeepNestedInner> for SpecDeepNested {
    open spec fn spec_from(m: SpecDeepNestedInner) -> SpecDeepNested {
        let (outer, data) = m;
        SpecDeepNested { outer, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct DeepNested<'a> {
    pub outer: OuterHeader,
    pub data: &'a [u8],
}

impl View for DeepNested<'_> {
    type V = SpecDeepNested;

    open spec fn view(&self) -> Self::V {
        SpecDeepNested {
            outer: self.outer@,
            data: self.data@,
        }
    }
}
pub type DeepNestedInner<'a> = (OuterHeader, &'a [u8]);

pub type DeepNestedInnerRef<'a> = (&'a OuterHeader, &'a &'a [u8]);
impl<'a> From<&'a DeepNested<'a>> for DeepNestedInnerRef<'a> {
    fn ex_from(m: &'a DeepNested) -> DeepNestedInnerRef<'a> {
        (&m.outer, &m.data)
    }
}

impl<'a> From<DeepNestedInner<'a>> for DeepNested<'a> {
    fn ex_from(m: DeepNestedInner) -> DeepNested {
        let (outer, data) = m;
        DeepNested { outer, data }
    }
}

pub struct DeepNestedMapper;
impl View for DeepNestedMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DeepNestedMapper {
    type Src = SpecDeepNestedInner;
    type Dst = SpecDeepNested;
}
impl SpecIsoProof for DeepNestedMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DeepNestedMapper {
    type Src = DeepNestedInner<'a>;
    type Dst = DeepNested<'a>;
    type RefSrc = DeepNestedInnerRef<'a>;
}

pub struct SpecDeepNestedCombinator(pub SpecDeepNestedCombinatorAlias);

impl SpecCombinator for SpecDeepNestedCombinator {
    type Type = SpecDeepNested;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDeepNestedCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDeepNestedCombinatorAlias::is_prefix_secure() }
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
pub type SpecDeepNestedCombinatorAlias = Mapped<SpecPair<SpecOuterHeaderCombinator, bytes::Variable>, DeepNestedMapper>;

pub struct DeepNestedCombinator(pub DeepNestedCombinatorAlias);

impl View for DeepNestedCombinator {
    type V = SpecDeepNestedCombinator;
    open spec fn view(&self) -> Self::V { SpecDeepNestedCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DeepNestedCombinator {
    type Type = DeepNested<'a>;
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
impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for DeepNestedCombinator {
    fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
}
pub type DeepNestedCombinatorAlias = Mapped<Pair<OuterHeaderCombinator, bytes::Variable, DeepNestedCont0>, DeepNestedMapper>;


pub open spec fn spec_deep_nested() -> SpecDeepNestedCombinator {
    SpecDeepNestedCombinator(
    Mapped {
        inner: Pair::spec_new(spec_outer_header(), |deps| spec_deep_nested_cont0(deps)),
        mapper: DeepNestedMapper,
    })
}

pub open spec fn spec_deep_nested_cont0(deps: SpecOuterHeader) -> bytes::Variable {
    let outer = deps;
    bytes::Variable(((usize::spec_from(outer.inner.payload_length) - 8)) as usize)
}

impl View for DeepNestedCont0 {
    type V = spec_fn(SpecOuterHeader) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: SpecOuterHeader| {
            spec_deep_nested_cont0(deps)
        }
    }
}

                
pub fn deep_nested<'a>() -> (o: DeepNestedCombinator)
    ensures o@ == spec_deep_nested(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DeepNestedCombinator(
    Mapped {
        inner: Pair::new(outer_header(), DeepNestedCont0),
        mapper: DeepNestedMapper,
    });
    // assert({
    //     &&& combinator@ == spec_deep_nested()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_deep_nested<'a>(input: &'a [u8]) -> (res: PResult<<DeepNestedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_deep_nested().spec_parse(input@) == Some((n as int, v@)),
        spec_deep_nested().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_deep_nested().spec_parse(input@) is None,
        spec_deep_nested().spec_parse(input@) is None ==> res is Err,
{
    let combinator = deep_nested();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_deep_nested<'a>(v: <DeepNestedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_deep_nested().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_deep_nested().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_deep_nested().spec_serialize(v@))
        },
{
    let combinator = deep_nested();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_deep_nested_infallible<'a>(v: <DeepNestedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_deep_nested().wf(v@),
        spec_deep_nested().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_deep_nested().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_deep_nested().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_deep_nested().spec_serialize(v@)),
{
    let combinator = deep_nested();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn deep_nested_len<'a>(v: <DeepNestedCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_deep_nested().wf(v@),
        spec_deep_nested().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_deep_nested().spec_serialize(v@).len(),
{
    let combinator = deep_nested();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct DeepNestedCont0;
type DeepNestedCont0Type<'a, 'b> = &'b OuterHeader;
type DeepNestedCont0SType<'a, 'x> = &'x OuterHeader;
type DeepNestedCont0Input<'a, 'b, 'x> = POrSType<DeepNestedCont0Type<'a, 'b>, DeepNestedCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DeepNestedCont0Input<'a, 'b, 'x>> for DeepNestedCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: DeepNestedCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_outer_header()).wf(deps@)
        }

    open spec fn ensures(&self, deps: DeepNestedCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_deep_nested_cont0(deps@)
    }

    fn apply(&self, deps: DeepNestedCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let outer = deps;
                bytes::Variable(((usize::ex_from(outer.inner.payload_length) - 8)) as usize)
            }
            POrSType::S(deps) => {
                let outer = deps;
                bytes::Variable(((usize::ex_from(outer.inner.payload_length) - 8)) as usize)
            }
        }
    }
}
                

pub struct SpecCombinedExample {
    pub header: SpecGenericHeader,
    pub body: Seq<u8>,
}

pub type SpecCombinedExampleInner = (SpecGenericHeader, Seq<u8>);


impl SpecFrom<SpecCombinedExample> for SpecCombinedExampleInner {
    open spec fn spec_from(m: SpecCombinedExample) -> SpecCombinedExampleInner {
        (m.header, m.body)
    }
}

impl SpecFrom<SpecCombinedExampleInner> for SpecCombinedExample {
    open spec fn spec_from(m: SpecCombinedExampleInner) -> SpecCombinedExample {
        let (header, body) = m;
        SpecCombinedExample { header, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CombinedExample<'a> {
    pub header: GenericHeader,
    pub body: &'a [u8],
}

impl View for CombinedExample<'_> {
    type V = SpecCombinedExample;

    open spec fn view(&self) -> Self::V {
        SpecCombinedExample {
            header: self.header@,
            body: self.body@,
        }
    }
}
pub type CombinedExampleInner<'a> = (GenericHeader, &'a [u8]);

pub type CombinedExampleInnerRef<'a> = (&'a GenericHeader, &'a &'a [u8]);
impl<'a> From<&'a CombinedExample<'a>> for CombinedExampleInnerRef<'a> {
    fn ex_from(m: &'a CombinedExample) -> CombinedExampleInnerRef<'a> {
        (&m.header, &m.body)
    }
}

impl<'a> From<CombinedExampleInner<'a>> for CombinedExample<'a> {
    fn ex_from(m: CombinedExampleInner) -> CombinedExample {
        let (header, body) = m;
        CombinedExample { header, body }
    }
}

pub struct CombinedExampleMapper;
impl View for CombinedExampleMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CombinedExampleMapper {
    type Src = SpecCombinedExampleInner;
    type Dst = SpecCombinedExample;
}
impl SpecIsoProof for CombinedExampleMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CombinedExampleMapper {
    type Src = CombinedExampleInner<'a>;
    type Dst = CombinedExample<'a>;
    type RefSrc = CombinedExampleInnerRef<'a>;
}

pub struct SpecCombinedExampleCombinator(pub SpecCombinedExampleCombinatorAlias);

impl SpecCombinator for SpecCombinedExampleCombinator {
    type Type = SpecCombinedExample;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCombinedExampleCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCombinedExampleCombinatorAlias::is_prefix_secure() }
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
pub type SpecCombinedExampleCombinatorAlias = Mapped<SpecPair<SpecGenericHeaderCombinator, bytes::Variable>, CombinedExampleMapper>;

pub struct CombinedExampleCombinator(pub CombinedExampleCombinatorAlias);

impl View for CombinedExampleCombinator {
    type V = SpecCombinedExampleCombinator;
    open spec fn view(&self) -> Self::V { SpecCombinedExampleCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CombinedExampleCombinator {
    type Type = CombinedExample<'a>;
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
impl<'a> SecureSerialize<'a, &'a [u8], Vec<u8>> for CombinedExampleCombinator {
    fn secure_serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    { <_ as SecureSerialize<'a, &'a [u8], Vec<u8>>>::secure_serialize(&self.0, v, data, pos) }
}
pub type CombinedExampleCombinatorAlias = Mapped<Pair<GenericHeaderCombinator, bytes::Variable, CombinedExampleCont0>, CombinedExampleMapper>;


pub open spec fn spec_combined_example(total_len: u32) -> SpecCombinedExampleCombinator {
    SpecCombinedExampleCombinator(
    Mapped {
        inner: Pair::spec_new(spec_generic_header(), |deps| spec_combined_example_cont0(total_len, deps)),
        mapper: CombinedExampleMapper,
    })
}

pub open spec fn spec_combined_example_cont0(total_len: u32, deps: SpecGenericHeader) -> bytes::Variable {
    let header = deps;
    bytes::Variable(((usize::spec_from(total_len) - usize::spec_from(header.payload_length))) as usize)
}

impl View for CombinedExampleCont0 {
    type V = spec_fn(SpecGenericHeader) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: SpecGenericHeader| {
            spec_combined_example_cont0(self.total_len@, deps)
        }
    }
}

pub fn combined_example<'a>(total_len: u32) -> (o: CombinedExampleCombinator)
    requires
        ((total_len) >= 65535 && (total_len) <= 4294967295),

    ensures o@ == spec_combined_example(total_len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CombinedExampleCombinator(
    Mapped {
        inner: Pair::new(generic_header(), CombinedExampleCont0 { total_len }),
        mapper: CombinedExampleMapper,
    });
    // assert({
    //     &&& combinator@ == spec_combined_example(total_len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_combined_example<'a>(input: &'a [u8], total_len: u32) -> (res: PResult<<CombinedExampleCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((total_len) >= 65535 && (total_len) <= 4294967295),

    ensures
        res matches Ok((n, v)) ==> spec_combined_example(total_len@).spec_parse(input@) == Some((n as int, v@)),
        spec_combined_example(total_len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_combined_example(total_len@).spec_parse(input@) is None,
        spec_combined_example(total_len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = combined_example( total_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_combined_example<'a>(v: <CombinedExampleCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, total_len: u32) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_combined_example(total_len@).wf(v@),
        ((total_len) >= 65535 && (total_len) <= 4294967295),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_combined_example(total_len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_combined_example(total_len@).spec_serialize(v@))
        },
{
    let combinator = combined_example( total_len );
    combinator.serialize(v, data, pos)
}

pub fn serialize_combined_example_infallible<'a>(v: <CombinedExampleCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, total_len: u32) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_combined_example(total_len@).wf(v@),
        ((total_len) >= 65535 && (total_len) <= 4294967295),
        spec_combined_example(total_len@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_combined_example(total_len@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_combined_example(total_len@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_combined_example(total_len@).spec_serialize(v@)),
{
    let combinator = combined_example( total_len );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn combined_example_len<'a>(v: <CombinedExampleCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, total_len: u32) -> (serialize_len: usize)
    requires
        spec_combined_example(total_len@).wf(v@),
        spec_combined_example(total_len@).spec_serialize(v@).len() <= usize::MAX,
        ((total_len) >= 65535 && (total_len) <= 4294967295),

    ensures
        serialize_len == spec_combined_example(total_len@).spec_serialize(v@).len(),
{
    let combinator = combined_example( total_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CombinedExampleCont0 {
    pub total_len: u32,
}
type CombinedExampleCont0Type<'a, 'b> = &'b GenericHeader;
type CombinedExampleCont0SType<'a, 'x> = &'x GenericHeader;
type CombinedExampleCont0Input<'a, 'b, 'x> = POrSType<CombinedExampleCont0Type<'a, 'b>, CombinedExampleCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CombinedExampleCont0Input<'a, 'b, 'x>> for CombinedExampleCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CombinedExampleCont0Input<'a, 'b, 'x>) -> bool {        let total_len = self.total_len@;

        &&& ((self.total_len@) >= 65535 && (self.total_len@) <= 4294967295)
        &&& (spec_generic_header()).wf(deps@)
        }

    open spec fn ensures(&self, deps: CombinedExampleCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_combined_example_cont0(self.total_len@, deps@)
    }

    fn apply(&self, deps: CombinedExampleCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let header = deps;
                let total_len = self.total_len;
                bytes::Variable(((usize::ex_from(total_len) - usize::ex_from(header.payload_length))) as usize)
            }
            POrSType::S(deps) => {
                let header = deps;
                let total_len = self.total_len;
                bytes::Variable(((usize::ex_from(total_len) - usize::ex_from(header.payload_length))) as usize)
            }
        }
    }
}

}
