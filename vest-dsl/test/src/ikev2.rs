
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
pub mod IkeProtocolId {
    use super::*;
    pub spec const SPEC_IKE: u8 = 1;
    pub spec const SPEC_AH: u8 = 2;
    pub spec const SPEC_ESP: u8 = 3;
    pub exec const IKE: u8 ensures IKE == SPEC_IKE { 1 }
    pub exec const AH: u8 ensures AH == SPEC_AH { 2 }
    pub exec const ESP: u8 ensures ESP == SPEC_ESP { 3 }
}


pub struct SpecIkeProtocolIdCombinator(pub SpecIkeProtocolIdCombinatorAlias);

impl SpecCombinator for SpecIkeProtocolIdCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkeProtocolIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkeProtocolIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkeProtocolIdCombinatorAlias = U8;

pub struct IkeProtocolIdCombinator(pub IkeProtocolIdCombinatorAlias);

impl View for IkeProtocolIdCombinator {
    type V = SpecIkeProtocolIdCombinator;
    open spec fn view(&self) -> Self::V { SpecIkeProtocolIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IkeProtocolIdCombinator {
    type Type = u8;
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
pub type IkeProtocolIdCombinatorAlias = U8;


pub open spec fn spec_ike_protocol_id() -> SpecIkeProtocolIdCombinator {
    SpecIkeProtocolIdCombinator(U8)
}

                
pub fn ike_protocol_id<'a>() -> (o: IkeProtocolIdCombinator)
    ensures o@ == spec_ike_protocol_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IkeProtocolIdCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_ike_protocol_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ike_protocol_id<'a>(input: &'a [u8]) -> (res: PResult<<IkeProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ike_protocol_id().spec_parse(input@) == Some((n as int, v@)),
        spec_ike_protocol_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ike_protocol_id().spec_parse(input@) is None,
        spec_ike_protocol_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ike_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ike_protocol_id<'a>(v: <IkeProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ike_protocol_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ike_protocol_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ike_protocol_id().spec_serialize(v@))
        },
{
    let combinator = ike_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ike_protocol_id_len<'a>(v: <IkeProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ike_protocol_id().wf(v@),
        spec_ike_protocol_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ike_protocol_id().spec_serialize(v@).len(),
{
    let combinator = ike_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecProposalSpiSizeByte = u8;
pub type ProposalSpiSizeByte = u8;
pub type ProposalSpiSizeByteRef<'a> = &'a u8;


pub struct SpecProposalSpiSizeByteCombinator(pub SpecProposalSpiSizeByteCombinatorAlias);

impl SpecCombinator for SpecProposalSpiSizeByteCombinator {
    type Type = SpecProposalSpiSizeByte;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalSpiSizeByteCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalSpiSizeByteCombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalSpiSizeByteCombinatorAlias = Refined<U8, Predicate7607843399309189603>;
pub struct Predicate7607843399309189603;
impl View for Predicate7607843399309189603 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7607843399309189603 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 4) || (i == 8)
    }
}
impl SpecPred<u8> for Predicate7607843399309189603 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 4) || (i == 8)
    }
}

pub struct ProposalSpiSizeByteCombinator(pub ProposalSpiSizeByteCombinatorAlias);

impl View for ProposalSpiSizeByteCombinator {
    type V = SpecProposalSpiSizeByteCombinator;
    open spec fn view(&self) -> Self::V { SpecProposalSpiSizeByteCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalSpiSizeByteCombinator {
    type Type = ProposalSpiSizeByte;
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
pub type ProposalSpiSizeByteCombinatorAlias = Refined<U8, Predicate7607843399309189603>;


pub open spec fn spec_proposal_spi_size_byte() -> SpecProposalSpiSizeByteCombinator {
    SpecProposalSpiSizeByteCombinator(Refined { inner: U8, predicate: Predicate7607843399309189603 })
}

                
pub fn proposal_spi_size_byte<'a>() -> (o: ProposalSpiSizeByteCombinator)
    ensures o@ == spec_proposal_spi_size_byte(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalSpiSizeByteCombinator(Refined { inner: U8, predicate: Predicate7607843399309189603 });
    // assert({
    //     &&& combinator@ == spec_proposal_spi_size_byte()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal_spi_size_byte<'a>(input: &'a [u8]) -> (res: PResult<<ProposalSpiSizeByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_proposal_spi_size_byte().spec_parse(input@) == Some((n as int, v@)),
        spec_proposal_spi_size_byte().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal_spi_size_byte().spec_parse(input@) is None,
        spec_proposal_spi_size_byte().spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal_spi_size_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal_spi_size_byte<'a>(v: <ProposalSpiSizeByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal_spi_size_byte().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal_spi_size_byte().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal_spi_size_byte().spec_serialize(v@))
        },
{
    let combinator = proposal_spi_size_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn proposal_spi_size_byte_len<'a>(v: <ProposalSpiSizeByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_proposal_spi_size_byte().wf(v@),
        spec_proposal_spi_size_byte().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_proposal_spi_size_byte().spec_serialize(v@).len(),
{
    let combinator = proposal_spi_size_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod TransformType {
    use super::*;
    pub spec const SPEC_ENCR: u8 = 1;
    pub spec const SPEC_PRF: u8 = 2;
    pub spec const SPEC_INTEG: u8 = 3;
    pub spec const SPEC_DH: u8 = 4;
    pub spec const SPEC_ESN: u8 = 5;
    pub exec const ENCR: u8 ensures ENCR == SPEC_ENCR { 1 }
    pub exec const PRF: u8 ensures PRF == SPEC_PRF { 2 }
    pub exec const INTEG: u8 ensures INTEG == SPEC_INTEG { 3 }
    pub exec const DH: u8 ensures DH == SPEC_DH { 4 }
    pub exec const ESN: u8 ensures ESN == SPEC_ESN { 5 }
}


pub struct SpecTransformTypeCombinator(pub SpecTransformTypeCombinatorAlias);

impl SpecCombinator for SpecTransformTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformTypeCombinatorAlias = U8;

pub struct TransformTypeCombinator(pub TransformTypeCombinatorAlias);

impl View for TransformTypeCombinator {
    type V = SpecTransformTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformTypeCombinator {
    type Type = u8;
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
pub type TransformTypeCombinatorAlias = U8;


pub open spec fn spec_transform_type() -> SpecTransformTypeCombinator {
    SpecTransformTypeCombinator(U8)
}

                
pub fn transform_type<'a>() -> (o: TransformTypeCombinator)
    ensures o@ == spec_transform_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_transform_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_type<'a>(input: &'a [u8]) -> (res: PResult<<TransformTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform_type().spec_parse(input@) == Some((n as int, v@)),
        spec_transform_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_type().spec_parse(input@) is None,
        spec_transform_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_type<'a>(v: <TransformTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_type().spec_serialize(v@))
        },
{
    let combinator = transform_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_type_len<'a>(v: <TransformTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform_type().wf(v@),
        spec_transform_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform_type().spec_serialize(v@).len(),
{
    let combinator = transform_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod EncrId {
    use super::*;
    pub spec const SPEC_ENCR_DES_IV64: u16 = 1;
    pub spec const SPEC_ENCR_DES: u16 = 2;
    pub spec const SPEC_ENCR_3DES: u16 = 3;
    pub spec const SPEC_ENCR_RC5: u16 = 4;
    pub spec const SPEC_ENCR_IDEA: u16 = 5;
    pub spec const SPEC_ENCR_CAST: u16 = 6;
    pub spec const SPEC_ENCR_BLOWFISH: u16 = 7;
    pub spec const SPEC_ENCR_3IDEA: u16 = 8;
    pub spec const SPEC_ENCR_DES_IV32: u16 = 9;
    pub spec const SPEC_ENCR_NULL: u16 = 11;
    pub spec const SPEC_ENCR_AES_CBC: u16 = 12;
    pub spec const SPEC_ENCR_AES_CTR: u16 = 13;
    pub exec const ENCR_DES_IV64: u16 ensures ENCR_DES_IV64 == SPEC_ENCR_DES_IV64 { 1 }
    pub exec const ENCR_DES: u16 ensures ENCR_DES == SPEC_ENCR_DES { 2 }
    pub exec const ENCR_3DES: u16 ensures ENCR_3DES == SPEC_ENCR_3DES { 3 }
    pub exec const ENCR_RC5: u16 ensures ENCR_RC5 == SPEC_ENCR_RC5 { 4 }
    pub exec const ENCR_IDEA: u16 ensures ENCR_IDEA == SPEC_ENCR_IDEA { 5 }
    pub exec const ENCR_CAST: u16 ensures ENCR_CAST == SPEC_ENCR_CAST { 6 }
    pub exec const ENCR_BLOWFISH: u16 ensures ENCR_BLOWFISH == SPEC_ENCR_BLOWFISH { 7 }
    pub exec const ENCR_3IDEA: u16 ensures ENCR_3IDEA == SPEC_ENCR_3IDEA { 8 }
    pub exec const ENCR_DES_IV32: u16 ensures ENCR_DES_IV32 == SPEC_ENCR_DES_IV32 { 9 }
    pub exec const ENCR_NULL: u16 ensures ENCR_NULL == SPEC_ENCR_NULL { 11 }
    pub exec const ENCR_AES_CBC: u16 ensures ENCR_AES_CBC == SPEC_ENCR_AES_CBC { 12 }
    pub exec const ENCR_AES_CTR: u16 ensures ENCR_AES_CTR == SPEC_ENCR_AES_CTR { 13 }
}


pub struct SpecEncrIdCombinator(pub SpecEncrIdCombinatorAlias);

impl SpecCombinator for SpecEncrIdCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEncrIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEncrIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecEncrIdCombinatorAlias = U16Be;

pub struct EncrIdCombinator(pub EncrIdCombinatorAlias);

impl View for EncrIdCombinator {
    type V = SpecEncrIdCombinator;
    open spec fn view(&self) -> Self::V { SpecEncrIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EncrIdCombinator {
    type Type = u16;
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
pub type EncrIdCombinatorAlias = U16Be;


pub open spec fn spec_encr_id() -> SpecEncrIdCombinator {
    SpecEncrIdCombinator(U16Be)
}

                
pub fn encr_id<'a>() -> (o: EncrIdCombinator)
    ensures o@ == spec_encr_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EncrIdCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_encr_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_encr_id<'a>(input: &'a [u8]) -> (res: PResult<<EncrIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_encr_id().spec_parse(input@) == Some((n as int, v@)),
        spec_encr_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_encr_id().spec_parse(input@) is None,
        spec_encr_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = encr_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_encr_id<'a>(v: <EncrIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_encr_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_encr_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_encr_id().spec_serialize(v@))
        },
{
    let combinator = encr_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn encr_id_len<'a>(v: <EncrIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_encr_id().wf(v@),
        spec_encr_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_encr_id().spec_serialize(v@).len(),
{
    let combinator = encr_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod PrfId {
    use super::*;
    pub spec const SPEC_PRF_HMAC_MD5: u16 = 1;
    pub spec const SPEC_PRF_HMAC_SHA1: u16 = 2;
    pub spec const SPEC_PRF_HMAC_TIGER: u16 = 3;
    pub exec const PRF_HMAC_MD5: u16 ensures PRF_HMAC_MD5 == SPEC_PRF_HMAC_MD5 { 1 }
    pub exec const PRF_HMAC_SHA1: u16 ensures PRF_HMAC_SHA1 == SPEC_PRF_HMAC_SHA1 { 2 }
    pub exec const PRF_HMAC_TIGER: u16 ensures PRF_HMAC_TIGER == SPEC_PRF_HMAC_TIGER { 3 }
}


pub struct SpecPrfIdCombinator(pub SpecPrfIdCombinatorAlias);

impl SpecCombinator for SpecPrfIdCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPrfIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPrfIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecPrfIdCombinatorAlias = U16Be;

pub struct PrfIdCombinator(pub PrfIdCombinatorAlias);

impl View for PrfIdCombinator {
    type V = SpecPrfIdCombinator;
    open spec fn view(&self) -> Self::V { SpecPrfIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PrfIdCombinator {
    type Type = u16;
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
pub type PrfIdCombinatorAlias = U16Be;


pub open spec fn spec_prf_id() -> SpecPrfIdCombinator {
    SpecPrfIdCombinator(U16Be)
}

                
pub fn prf_id<'a>() -> (o: PrfIdCombinator)
    ensures o@ == spec_prf_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PrfIdCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_prf_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_prf_id<'a>(input: &'a [u8]) -> (res: PResult<<PrfIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_prf_id().spec_parse(input@) == Some((n as int, v@)),
        spec_prf_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_prf_id().spec_parse(input@) is None,
        spec_prf_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = prf_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_prf_id<'a>(v: <PrfIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_prf_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_prf_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_prf_id().spec_serialize(v@))
        },
{
    let combinator = prf_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn prf_id_len<'a>(v: <PrfIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_prf_id().wf(v@),
        spec_prf_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_prf_id().spec_serialize(v@).len(),
{
    let combinator = prf_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod IntegId {
    use super::*;
    pub spec const SPEC_INTEG_NONE: u16 = 0;
    pub spec const SPEC_AUTH_HMAC_MD5_96: u16 = 1;
    pub spec const SPEC_AUTH_HMAC_SHA1_96: u16 = 2;
    pub spec const SPEC_AUTH_DES_MAC: u16 = 3;
    pub spec const SPEC_AUTH_KPDK_MD5: u16 = 4;
    pub spec const SPEC_AUTH_AES_XCBC_96: u16 = 5;
    pub exec const INTEG_NONE: u16 ensures INTEG_NONE == SPEC_INTEG_NONE { 0 }
    pub exec const AUTH_HMAC_MD5_96: u16 ensures AUTH_HMAC_MD5_96 == SPEC_AUTH_HMAC_MD5_96 { 1 }
    pub exec const AUTH_HMAC_SHA1_96: u16 ensures AUTH_HMAC_SHA1_96 == SPEC_AUTH_HMAC_SHA1_96 { 2 }
    pub exec const AUTH_DES_MAC: u16 ensures AUTH_DES_MAC == SPEC_AUTH_DES_MAC { 3 }
    pub exec const AUTH_KPDK_MD5: u16 ensures AUTH_KPDK_MD5 == SPEC_AUTH_KPDK_MD5 { 4 }
    pub exec const AUTH_AES_XCBC_96: u16 ensures AUTH_AES_XCBC_96 == SPEC_AUTH_AES_XCBC_96 { 5 }
}


pub struct SpecIntegIdCombinator(pub SpecIntegIdCombinatorAlias);

impl SpecCombinator for SpecIntegIdCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIntegIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIntegIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecIntegIdCombinatorAlias = U16Be;

pub struct IntegIdCombinator(pub IntegIdCombinatorAlias);

impl View for IntegIdCombinator {
    type V = SpecIntegIdCombinator;
    open spec fn view(&self) -> Self::V { SpecIntegIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IntegIdCombinator {
    type Type = u16;
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
pub type IntegIdCombinatorAlias = U16Be;


pub open spec fn spec_integ_id() -> SpecIntegIdCombinator {
    SpecIntegIdCombinator(U16Be)
}

                
pub fn integ_id<'a>() -> (o: IntegIdCombinator)
    ensures o@ == spec_integ_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IntegIdCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_integ_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_integ_id<'a>(input: &'a [u8]) -> (res: PResult<<IntegIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_integ_id().spec_parse(input@) == Some((n as int, v@)),
        spec_integ_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_integ_id().spec_parse(input@) is None,
        spec_integ_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = integ_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_integ_id<'a>(v: <IntegIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_integ_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_integ_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_integ_id().spec_serialize(v@))
        },
{
    let combinator = integ_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn integ_id_len<'a>(v: <IntegIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_integ_id().wf(v@),
        spec_integ_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_integ_id().spec_serialize(v@).len(),
{
    let combinator = integ_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod DhId {
    use super::*;
    pub spec const SPEC_DH_NONE: u16 = 0;
    pub spec const SPEC_MODP_768: u16 = 1;
    pub spec const SPEC_MODP_1024: u16 = 2;
    pub spec const SPEC_MODP_1536: u16 = 5;
    pub spec const SPEC_MODP_2048: u16 = 14;
    pub spec const SPEC_MODP_3072: u16 = 15;
    pub spec const SPEC_MODP_4096: u16 = 16;
    pub spec const SPEC_MODP_6144: u16 = 17;
    pub spec const SPEC_MODP_8192: u16 = 18;
    pub exec const DH_NONE: u16 ensures DH_NONE == SPEC_DH_NONE { 0 }
    pub exec const MODP_768: u16 ensures MODP_768 == SPEC_MODP_768 { 1 }
    pub exec const MODP_1024: u16 ensures MODP_1024 == SPEC_MODP_1024 { 2 }
    pub exec const MODP_1536: u16 ensures MODP_1536 == SPEC_MODP_1536 { 5 }
    pub exec const MODP_2048: u16 ensures MODP_2048 == SPEC_MODP_2048 { 14 }
    pub exec const MODP_3072: u16 ensures MODP_3072 == SPEC_MODP_3072 { 15 }
    pub exec const MODP_4096: u16 ensures MODP_4096 == SPEC_MODP_4096 { 16 }
    pub exec const MODP_6144: u16 ensures MODP_6144 == SPEC_MODP_6144 { 17 }
    pub exec const MODP_8192: u16 ensures MODP_8192 == SPEC_MODP_8192 { 18 }
}


pub struct SpecDhIdCombinator(pub SpecDhIdCombinatorAlias);

impl SpecCombinator for SpecDhIdCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDhIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDhIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecDhIdCombinatorAlias = U16Be;

pub struct DhIdCombinator(pub DhIdCombinatorAlias);

impl View for DhIdCombinator {
    type V = SpecDhIdCombinator;
    open spec fn view(&self) -> Self::V { SpecDhIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DhIdCombinator {
    type Type = u16;
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
pub type DhIdCombinatorAlias = U16Be;


pub open spec fn spec_dh_id() -> SpecDhIdCombinator {
    SpecDhIdCombinator(U16Be)
}

                
pub fn dh_id<'a>() -> (o: DhIdCombinator)
    ensures o@ == spec_dh_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DhIdCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_dh_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_dh_id<'a>(input: &'a [u8]) -> (res: PResult<<DhIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_dh_id().spec_parse(input@) == Some((n as int, v@)),
        spec_dh_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_dh_id().spec_parse(input@) is None,
        spec_dh_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = dh_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_dh_id<'a>(v: <DhIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_dh_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_dh_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_dh_id().spec_serialize(v@))
        },
{
    let combinator = dh_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn dh_id_len<'a>(v: <DhIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_dh_id().wf(v@),
        spec_dh_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_dh_id().spec_serialize(v@).len(),
{
    let combinator = dh_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod EsnId {
    use super::*;
    pub spec const SPEC_NoESN: u16 = 0;
    pub spec const SPEC_ESN: u16 = 1;
    pub exec const NoESN: u16 ensures NoESN == SPEC_NoESN { 0 }
    pub exec const ESN: u16 ensures ESN == SPEC_ESN { 1 }
}


pub struct SpecEsnIdCombinator(pub SpecEsnIdCombinatorAlias);

impl SpecCombinator for SpecEsnIdCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEsnIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEsnIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecEsnIdCombinatorAlias = U16Be;

pub struct EsnIdCombinator(pub EsnIdCombinatorAlias);

impl View for EsnIdCombinator {
    type V = SpecEsnIdCombinator;
    open spec fn view(&self) -> Self::V { SpecEsnIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EsnIdCombinator {
    type Type = u16;
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
pub type EsnIdCombinatorAlias = U16Be;


pub open spec fn spec_esn_id() -> SpecEsnIdCombinator {
    SpecEsnIdCombinator(U16Be)
}

                
pub fn esn_id<'a>() -> (o: EsnIdCombinator)
    ensures o@ == spec_esn_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EsnIdCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_esn_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_esn_id<'a>(input: &'a [u8]) -> (res: PResult<<EsnIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_esn_id().spec_parse(input@) == Some((n as int, v@)),
        spec_esn_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_esn_id().spec_parse(input@) is None,
        spec_esn_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = esn_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_esn_id<'a>(v: <EsnIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_esn_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_esn_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_esn_id().spec_serialize(v@))
        },
{
    let combinator = esn_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn esn_id_len<'a>(v: <EsnIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_esn_id().wf(v@),
        spec_esn_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_esn_id().spec_serialize(v@).len(),
{
    let combinator = esn_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecTransformIdValue {
    ENCR(u16),
    PRF(u16),
    INTEG(u16),
    DH(u16),
    ESN(u16),
    Unrecognized(u16),
}

pub type SpecTransformIdValueInner = Either<u16, Either<u16, Either<u16, Either<u16, Either<u16, u16>>>>>;

impl SpecFrom<SpecTransformIdValue> for SpecTransformIdValueInner {
    open spec fn spec_from(m: SpecTransformIdValue) -> SpecTransformIdValueInner {
        match m {
            SpecTransformIdValue::ENCR(m) => Either::Left(m),
            SpecTransformIdValue::PRF(m) => Either::Right(Either::Left(m)),
            SpecTransformIdValue::INTEG(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecTransformIdValue::DH(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecTransformIdValue::ESN(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecTransformIdValue::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

                
impl SpecFrom<SpecTransformIdValueInner> for SpecTransformIdValue {
    open spec fn spec_from(m: SpecTransformIdValueInner) -> SpecTransformIdValue {
        match m {
            Either::Left(m) => SpecTransformIdValue::ENCR(m),
            Either::Right(Either::Left(m)) => SpecTransformIdValue::PRF(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecTransformIdValue::INTEG(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecTransformIdValue::DH(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecTransformIdValue::ESN(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => SpecTransformIdValue::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransformIdValue {
    ENCR(u16),
    PRF(u16),
    INTEG(u16),
    DH(u16),
    ESN(u16),
    Unrecognized(u16),
}

pub type TransformIdValueInner = Either<u16, Either<u16, Either<u16, Either<u16, Either<u16, u16>>>>>;

pub type TransformIdValueInnerRef<'a> = Either<&'a u16, Either<&'a u16, Either<&'a u16, Either<&'a u16, Either<&'a u16, &'a u16>>>>>;


impl View for TransformIdValue {
    type V = SpecTransformIdValue;
    open spec fn view(&self) -> Self::V {
        match self {
            TransformIdValue::ENCR(m) => SpecTransformIdValue::ENCR(m@),
            TransformIdValue::PRF(m) => SpecTransformIdValue::PRF(m@),
            TransformIdValue::INTEG(m) => SpecTransformIdValue::INTEG(m@),
            TransformIdValue::DH(m) => SpecTransformIdValue::DH(m@),
            TransformIdValue::ESN(m) => SpecTransformIdValue::ESN(m@),
            TransformIdValue::Unrecognized(m) => SpecTransformIdValue::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a TransformIdValue> for TransformIdValueInnerRef<'a> {
    fn ex_from(m: &'a TransformIdValue) -> TransformIdValueInnerRef<'a> {
        match m {
            TransformIdValue::ENCR(m) => Either::Left(m),
            TransformIdValue::PRF(m) => Either::Right(Either::Left(m)),
            TransformIdValue::INTEG(m) => Either::Right(Either::Right(Either::Left(m))),
            TransformIdValue::DH(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            TransformIdValue::ESN(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            TransformIdValue::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

impl From<TransformIdValueInner> for TransformIdValue {
    fn ex_from(m: TransformIdValueInner) -> TransformIdValue {
        match m {
            Either::Left(m) => TransformIdValue::ENCR(m),
            Either::Right(Either::Left(m)) => TransformIdValue::PRF(m),
            Either::Right(Either::Right(Either::Left(m))) => TransformIdValue::INTEG(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => TransformIdValue::DH(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => TransformIdValue::ESN(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => TransformIdValue::Unrecognized(m),
        }
    }
    
}


pub struct TransformIdValueMapper;
impl View for TransformIdValueMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformIdValueMapper {
    type Src = SpecTransformIdValueInner;
    type Dst = SpecTransformIdValue;
}
impl SpecIsoProof for TransformIdValueMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformIdValueMapper {
    type Src = TransformIdValueInner;
    type Dst = TransformIdValue;
    type RefSrc = TransformIdValueInnerRef<'a>;
}

type SpecTransformIdValueCombinatorAlias1 = Choice<Cond<SpecEsnIdCombinator>, Cond<U16Be>>;
type SpecTransformIdValueCombinatorAlias2 = Choice<Cond<SpecDhIdCombinator>, SpecTransformIdValueCombinatorAlias1>;
type SpecTransformIdValueCombinatorAlias3 = Choice<Cond<SpecIntegIdCombinator>, SpecTransformIdValueCombinatorAlias2>;
type SpecTransformIdValueCombinatorAlias4 = Choice<Cond<SpecPrfIdCombinator>, SpecTransformIdValueCombinatorAlias3>;
type SpecTransformIdValueCombinatorAlias5 = Choice<Cond<SpecEncrIdCombinator>, SpecTransformIdValueCombinatorAlias4>;
pub struct SpecTransformIdValueCombinator(pub SpecTransformIdValueCombinatorAlias);

impl SpecCombinator for SpecTransformIdValueCombinator {
    type Type = SpecTransformIdValue;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformIdValueCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformIdValueCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformIdValueCombinatorAlias = Mapped<SpecTransformIdValueCombinatorAlias5, TransformIdValueMapper>;
type TransformIdValueCombinatorAlias1 = Choice<Cond<EsnIdCombinator>, Cond<U16Be>>;
type TransformIdValueCombinatorAlias2 = Choice<Cond<DhIdCombinator>, TransformIdValueCombinator1>;
type TransformIdValueCombinatorAlias3 = Choice<Cond<IntegIdCombinator>, TransformIdValueCombinator2>;
type TransformIdValueCombinatorAlias4 = Choice<Cond<PrfIdCombinator>, TransformIdValueCombinator3>;
type TransformIdValueCombinatorAlias5 = Choice<Cond<EncrIdCombinator>, TransformIdValueCombinator4>;
pub struct TransformIdValueCombinator1(pub TransformIdValueCombinatorAlias1);
impl View for TransformIdValueCombinator1 {
    type V = SpecTransformIdValueCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformIdValueCombinator1, TransformIdValueCombinatorAlias1);

pub struct TransformIdValueCombinator2(pub TransformIdValueCombinatorAlias2);
impl View for TransformIdValueCombinator2 {
    type V = SpecTransformIdValueCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformIdValueCombinator2, TransformIdValueCombinatorAlias2);

pub struct TransformIdValueCombinator3(pub TransformIdValueCombinatorAlias3);
impl View for TransformIdValueCombinator3 {
    type V = SpecTransformIdValueCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformIdValueCombinator3, TransformIdValueCombinatorAlias3);

pub struct TransformIdValueCombinator4(pub TransformIdValueCombinatorAlias4);
impl View for TransformIdValueCombinator4 {
    type V = SpecTransformIdValueCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformIdValueCombinator4, TransformIdValueCombinatorAlias4);

pub struct TransformIdValueCombinator5(pub TransformIdValueCombinatorAlias5);
impl View for TransformIdValueCombinator5 {
    type V = SpecTransformIdValueCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformIdValueCombinator5, TransformIdValueCombinatorAlias5);

pub struct TransformIdValueCombinator(pub TransformIdValueCombinatorAlias);

impl View for TransformIdValueCombinator {
    type V = SpecTransformIdValueCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformIdValueCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformIdValueCombinator {
    type Type = TransformIdValue;
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
pub type TransformIdValueCombinatorAlias = Mapped<TransformIdValueCombinator5, TransformIdValueMapper>;


pub open spec fn spec_transform_id_value(kind: u8) -> SpecTransformIdValueCombinator {
    SpecTransformIdValueCombinator(Mapped { inner: Choice(Cond { cond: kind == TransformType::SPEC_ENCR, inner: spec_encr_id() }, Choice(Cond { cond: kind == TransformType::SPEC_PRF, inner: spec_prf_id() }, Choice(Cond { cond: kind == TransformType::SPEC_INTEG, inner: spec_integ_id() }, Choice(Cond { cond: kind == TransformType::SPEC_DH, inner: spec_dh_id() }, Choice(Cond { cond: kind == TransformType::SPEC_ESN, inner: spec_esn_id() }, Cond { cond: !(kind == TransformType::SPEC_ENCR || kind == TransformType::SPEC_PRF || kind == TransformType::SPEC_INTEG || kind == TransformType::SPEC_DH || kind == TransformType::SPEC_ESN), inner: U16Be }))))), mapper: TransformIdValueMapper })
}

pub fn transform_id_value<'a>(kind: u8) -> (o: TransformIdValueCombinator)
    requires
        spec_transform_type().wf(kind@),

    ensures o@ == spec_transform_id_value(kind@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformIdValueCombinator(Mapped { inner: TransformIdValueCombinator5(Choice::new(Cond { cond: kind == TransformType::ENCR, inner: encr_id() }, TransformIdValueCombinator4(Choice::new(Cond { cond: kind == TransformType::PRF, inner: prf_id() }, TransformIdValueCombinator3(Choice::new(Cond { cond: kind == TransformType::INTEG, inner: integ_id() }, TransformIdValueCombinator2(Choice::new(Cond { cond: kind == TransformType::DH, inner: dh_id() }, TransformIdValueCombinator1(Choice::new(Cond { cond: kind == TransformType::ESN, inner: esn_id() }, Cond { cond: !(kind == TransformType::ENCR || kind == TransformType::PRF || kind == TransformType::INTEG || kind == TransformType::DH || kind == TransformType::ESN), inner: U16Be })))))))))), mapper: TransformIdValueMapper });
    // assert({
    //     &&& combinator@ == spec_transform_id_value(kind@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_id_value<'a>(input: &'a [u8], kind: u8) -> (res: PResult<<TransformIdValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_transform_type().wf(kind@),

    ensures
        res matches Ok((n, v)) ==> spec_transform_id_value(kind@).spec_parse(input@) == Some((n as int, v@)),
        spec_transform_id_value(kind@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_id_value(kind@).spec_parse(input@) is None,
        spec_transform_id_value(kind@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_id_value( kind );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_id_value<'a>(v: <TransformIdValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, kind: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_id_value(kind@).wf(v@),
        spec_transform_type().wf(kind@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_id_value(kind@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_id_value(kind@).spec_serialize(v@))
        },
{
    let combinator = transform_id_value( kind );
    combinator.serialize(v, data, pos)
}

pub fn transform_id_value_len<'a>(v: <TransformIdValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, kind: u8) -> (serialize_len: usize)
    requires
        spec_transform_id_value(kind@).wf(v@),
        spec_transform_id_value(kind@).spec_serialize(v@).len() <= usize::MAX,
        spec_transform_type().wf(kind@),

    ensures
        serialize_len == spec_transform_id_value(kind@).spec_serialize(v@).len(),
{
    let combinator = transform_id_value( kind );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecTransformAttrKeyLength {
    pub attr_type_and_af: u16,
    pub key_length_bits: u16,
}

pub type SpecTransformAttrKeyLengthInner = (u16, u16);


impl SpecFrom<SpecTransformAttrKeyLength> for SpecTransformAttrKeyLengthInner {
    open spec fn spec_from(m: SpecTransformAttrKeyLength) -> SpecTransformAttrKeyLengthInner {
        (m.attr_type_and_af, m.key_length_bits)
    }
}

impl SpecFrom<SpecTransformAttrKeyLengthInner> for SpecTransformAttrKeyLength {
    open spec fn spec_from(m: SpecTransformAttrKeyLengthInner) -> SpecTransformAttrKeyLength {
        let (attr_type_and_af, key_length_bits) = m;
        SpecTransformAttrKeyLength { attr_type_and_af, key_length_bits }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TransformAttrKeyLength {
    pub attr_type_and_af: u16,
    pub key_length_bits: u16,
}

impl View for TransformAttrKeyLength {
    type V = SpecTransformAttrKeyLength;

    open spec fn view(&self) -> Self::V {
        SpecTransformAttrKeyLength {
            attr_type_and_af: self.attr_type_and_af@,
            key_length_bits: self.key_length_bits@,
        }
    }
}
pub type TransformAttrKeyLengthInner = (u16, u16);

pub type TransformAttrKeyLengthInnerRef<'a> = (&'a u16, &'a u16);
impl<'a> From<&'a TransformAttrKeyLength> for TransformAttrKeyLengthInnerRef<'a> {
    fn ex_from(m: &'a TransformAttrKeyLength) -> TransformAttrKeyLengthInnerRef<'a> {
        (&m.attr_type_and_af, &m.key_length_bits)
    }
}

impl From<TransformAttrKeyLengthInner> for TransformAttrKeyLength {
    fn ex_from(m: TransformAttrKeyLengthInner) -> TransformAttrKeyLength {
        let (attr_type_and_af, key_length_bits) = m;
        TransformAttrKeyLength { attr_type_and_af, key_length_bits }
    }
}

pub struct TransformAttrKeyLengthMapper;
impl View for TransformAttrKeyLengthMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformAttrKeyLengthMapper {
    type Src = SpecTransformAttrKeyLengthInner;
    type Dst = SpecTransformAttrKeyLength;
}
impl SpecIsoProof for TransformAttrKeyLengthMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformAttrKeyLengthMapper {
    type Src = TransformAttrKeyLengthInner;
    type Dst = TransformAttrKeyLength;
    type RefSrc = TransformAttrKeyLengthInnerRef<'a>;
}
pub const TRANSFORMATTRKEYLENGTHATTR_TYPE_AND_AF_CONST: u16 = 32782;
type SpecTransformAttrKeyLengthCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, U16Be);
pub struct SpecTransformAttrKeyLengthCombinator(pub SpecTransformAttrKeyLengthCombinatorAlias);

impl SpecCombinator for SpecTransformAttrKeyLengthCombinator {
    type Type = SpecTransformAttrKeyLength;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformAttrKeyLengthCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformAttrKeyLengthCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformAttrKeyLengthCombinatorAlias = Mapped<SpecTransformAttrKeyLengthCombinatorAlias1, TransformAttrKeyLengthMapper>;
type TransformAttrKeyLengthCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, U16Be);
pub struct TransformAttrKeyLengthCombinator1(pub TransformAttrKeyLengthCombinatorAlias1);
impl View for TransformAttrKeyLengthCombinator1 {
    type V = SpecTransformAttrKeyLengthCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformAttrKeyLengthCombinator1, TransformAttrKeyLengthCombinatorAlias1);

pub struct TransformAttrKeyLengthCombinator(pub TransformAttrKeyLengthCombinatorAlias);

impl View for TransformAttrKeyLengthCombinator {
    type V = SpecTransformAttrKeyLengthCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformAttrKeyLengthCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformAttrKeyLengthCombinator {
    type Type = TransformAttrKeyLength;
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
pub type TransformAttrKeyLengthCombinatorAlias = Mapped<TransformAttrKeyLengthCombinator1, TransformAttrKeyLengthMapper>;


pub open spec fn spec_transform_attr_key_length() -> SpecTransformAttrKeyLengthCombinator {
    SpecTransformAttrKeyLengthCombinator(
    Mapped {
        inner: (Refined { inner: U16Be, predicate: TagPred(TRANSFORMATTRKEYLENGTHATTR_TYPE_AND_AF_CONST) }, U16Be),
        mapper: TransformAttrKeyLengthMapper,
    })
}

                
pub fn transform_attr_key_length<'a>() -> (o: TransformAttrKeyLengthCombinator)
    ensures o@ == spec_transform_attr_key_length(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformAttrKeyLengthCombinator(
    Mapped {
        inner: TransformAttrKeyLengthCombinator1((Refined { inner: U16Be, predicate: TagPred(TRANSFORMATTRKEYLENGTHATTR_TYPE_AND_AF_CONST) }, U16Be)),
        mapper: TransformAttrKeyLengthMapper,
    });
    // assert({
    //     &&& combinator@ == spec_transform_attr_key_length()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_attr_key_length<'a>(input: &'a [u8]) -> (res: PResult<<TransformAttrKeyLengthCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform_attr_key_length().spec_parse(input@) == Some((n as int, v@)),
        spec_transform_attr_key_length().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_attr_key_length().spec_parse(input@) is None,
        spec_transform_attr_key_length().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_attr_key_length();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_attr_key_length<'a>(v: <TransformAttrKeyLengthCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_attr_key_length().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_attr_key_length().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_attr_key_length().spec_serialize(v@))
        },
{
    let combinator = transform_attr_key_length();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_attr_key_length_len<'a>(v: <TransformAttrKeyLengthCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform_attr_key_length().wf(v@),
        spec_transform_attr_key_length().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform_attr_key_length().spec_serialize(v@).len(),
{
    let combinator = transform_attr_key_length();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTransformAttrTv {
    pub type_and_af: u16,
    pub value: u16,
}

pub type SpecTransformAttrTvInner = (u16, u16);


impl SpecFrom<SpecTransformAttrTv> for SpecTransformAttrTvInner {
    open spec fn spec_from(m: SpecTransformAttrTv) -> SpecTransformAttrTvInner {
        (m.type_and_af, m.value)
    }
}

impl SpecFrom<SpecTransformAttrTvInner> for SpecTransformAttrTv {
    open spec fn spec_from(m: SpecTransformAttrTvInner) -> SpecTransformAttrTv {
        let (type_and_af, value) = m;
        SpecTransformAttrTv { type_and_af, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TransformAttrTv {
    pub type_and_af: u16,
    pub value: u16,
}

impl View for TransformAttrTv {
    type V = SpecTransformAttrTv;

    open spec fn view(&self) -> Self::V {
        SpecTransformAttrTv {
            type_and_af: self.type_and_af@,
            value: self.value@,
        }
    }
}
pub type TransformAttrTvInner = (u16, u16);

pub type TransformAttrTvInnerRef<'a> = (&'a u16, &'a u16);
impl<'a> From<&'a TransformAttrTv> for TransformAttrTvInnerRef<'a> {
    fn ex_from(m: &'a TransformAttrTv) -> TransformAttrTvInnerRef<'a> {
        (&m.type_and_af, &m.value)
    }
}

impl From<TransformAttrTvInner> for TransformAttrTv {
    fn ex_from(m: TransformAttrTvInner) -> TransformAttrTv {
        let (type_and_af, value) = m;
        TransformAttrTv { type_and_af, value }
    }
}

pub struct TransformAttrTvMapper;
impl View for TransformAttrTvMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformAttrTvMapper {
    type Src = SpecTransformAttrTvInner;
    type Dst = SpecTransformAttrTv;
}
impl SpecIsoProof for TransformAttrTvMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformAttrTvMapper {
    type Src = TransformAttrTvInner;
    type Dst = TransformAttrTv;
    type RefSrc = TransformAttrTvInnerRef<'a>;
}

pub struct SpecTransformAttrTvCombinator(pub SpecTransformAttrTvCombinatorAlias);

impl SpecCombinator for SpecTransformAttrTvCombinator {
    type Type = SpecTransformAttrTv;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformAttrTvCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformAttrTvCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformAttrTvCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate11909926070075194211>, U16Be>, TransformAttrTvMapper>;
pub struct Predicate11909926070075194211;
impl View for Predicate11909926070075194211 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate11909926070075194211 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 32768 && i <= 32781) || (i >= 32783 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate11909926070075194211 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 32768 && i <= 32781) || (i >= 32783 && i <= 65535)
    }
}

pub struct TransformAttrTvCombinator(pub TransformAttrTvCombinatorAlias);

impl View for TransformAttrTvCombinator {
    type V = SpecTransformAttrTvCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformAttrTvCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformAttrTvCombinator {
    type Type = TransformAttrTv;
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
pub type TransformAttrTvCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate11909926070075194211>, U16Be, TransformAttrTvCont0>, TransformAttrTvMapper>;


pub open spec fn spec_transform_attr_tv() -> SpecTransformAttrTvCombinator {
    SpecTransformAttrTvCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate11909926070075194211 }, |deps| spec_transform_attr_tv_cont0(deps)),
        mapper: TransformAttrTvMapper,
    })
}

pub open spec fn spec_transform_attr_tv_cont0(deps: u16) -> U16Be {
    let type_and_af = deps;
    U16Be
}

impl View for TransformAttrTvCont0 {
    type V = spec_fn(u16) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_transform_attr_tv_cont0(deps)
        }
    }
}

                
pub fn transform_attr_tv<'a>() -> (o: TransformAttrTvCombinator)
    ensures o@ == spec_transform_attr_tv(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformAttrTvCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate11909926070075194211 }, TransformAttrTvCont0),
        mapper: TransformAttrTvMapper,
    });
    // assert({
    //     &&& combinator@ == spec_transform_attr_tv()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_attr_tv<'a>(input: &'a [u8]) -> (res: PResult<<TransformAttrTvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform_attr_tv().spec_parse(input@) == Some((n as int, v@)),
        spec_transform_attr_tv().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_attr_tv().spec_parse(input@) is None,
        spec_transform_attr_tv().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_attr_tv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_attr_tv<'a>(v: <TransformAttrTvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_attr_tv().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_attr_tv().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_attr_tv().spec_serialize(v@))
        },
{
    let combinator = transform_attr_tv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_attr_tv_len<'a>(v: <TransformAttrTvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform_attr_tv().wf(v@),
        spec_transform_attr_tv().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform_attr_tv().spec_serialize(v@).len(),
{
    let combinator = transform_attr_tv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TransformAttrTvCont0;
type TransformAttrTvCont0Type<'a, 'b> = &'b u16;
type TransformAttrTvCont0SType<'a, 'x> = &'x u16;
type TransformAttrTvCont0Input<'a, 'b, 'x> = POrSType<TransformAttrTvCont0Type<'a, 'b>, TransformAttrTvCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TransformAttrTvCont0Input<'a, 'b, 'x>> for TransformAttrTvCont0 {
    type Output = U16Be;

    open spec fn requires(&self, deps: TransformAttrTvCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Refined { inner: U16Be, predicate: Predicate11909926070075194211 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: TransformAttrTvCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_transform_attr_tv_cont0(deps@)
    }

    fn apply(&self, deps: TransformAttrTvCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let type_and_af = deps;
                let type_and_af = *type_and_af;
                U16Be
            }
            POrSType::S(deps) => {
                let type_and_af = deps;
                let type_and_af = *type_and_af;
                U16Be
            }
        }
    }
}
                

pub struct SpecTransformAttrTlv {
    pub type_and_af: u16,
    pub length: u16,
    pub value: Seq<u8>,
}

pub type SpecTransformAttrTlvInner = ((u16, u16), Seq<u8>);


impl SpecFrom<SpecTransformAttrTlv> for SpecTransformAttrTlvInner {
    open spec fn spec_from(m: SpecTransformAttrTlv) -> SpecTransformAttrTlvInner {
        ((m.type_and_af, m.length), m.value)
    }
}

impl SpecFrom<SpecTransformAttrTlvInner> for SpecTransformAttrTlv {
    open spec fn spec_from(m: SpecTransformAttrTlvInner) -> SpecTransformAttrTlv {
        let ((type_and_af, length), value) = m;
        SpecTransformAttrTlv { type_and_af, length, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TransformAttrTlv<'a> {
    pub type_and_af: u16,
    pub length: u16,
    pub value: &'a [u8],
}

impl View for TransformAttrTlv<'_> {
    type V = SpecTransformAttrTlv;

    open spec fn view(&self) -> Self::V {
        SpecTransformAttrTlv {
            type_and_af: self.type_and_af@,
            length: self.length@,
            value: self.value@,
        }
    }
}
pub type TransformAttrTlvInner<'a> = ((u16, u16), &'a [u8]);

pub type TransformAttrTlvInnerRef<'a> = ((&'a u16, &'a u16), &'a &'a [u8]);
impl<'a> From<&'a TransformAttrTlv<'a>> for TransformAttrTlvInnerRef<'a> {
    fn ex_from(m: &'a TransformAttrTlv) -> TransformAttrTlvInnerRef<'a> {
        ((&m.type_and_af, &m.length), &m.value)
    }
}

impl<'a> From<TransformAttrTlvInner<'a>> for TransformAttrTlv<'a> {
    fn ex_from(m: TransformAttrTlvInner) -> TransformAttrTlv {
        let ((type_and_af, length), value) = m;
        TransformAttrTlv { type_and_af, length, value }
    }
}

pub struct TransformAttrTlvMapper;
impl View for TransformAttrTlvMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformAttrTlvMapper {
    type Src = SpecTransformAttrTlvInner;
    type Dst = SpecTransformAttrTlv;
}
impl SpecIsoProof for TransformAttrTlvMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformAttrTlvMapper {
    type Src = TransformAttrTlvInner<'a>;
    type Dst = TransformAttrTlv<'a>;
    type RefSrc = TransformAttrTlvInnerRef<'a>;
}

pub struct SpecTransformAttrTlvCombinator(pub SpecTransformAttrTlvCombinatorAlias);

impl SpecCombinator for SpecTransformAttrTlvCombinator {
    type Type = SpecTransformAttrTlv;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformAttrTlvCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformAttrTlvCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformAttrTlvCombinatorAlias = Mapped<SpecPair<SpecPair<Refined<U16Be, Predicate5630542192344936318>, U16Be>, bytes::Variable>, TransformAttrTlvMapper>;
pub struct Predicate5630542192344936318;
impl View for Predicate5630542192344936318 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate5630542192344936318 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32767)
    }
}
impl SpecPred<u16> for Predicate5630542192344936318 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32767)
    }
}

pub struct TransformAttrTlvCombinator(pub TransformAttrTlvCombinatorAlias);

impl View for TransformAttrTlvCombinator {
    type V = SpecTransformAttrTlvCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformAttrTlvCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformAttrTlvCombinator {
    type Type = TransformAttrTlv<'a>;
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
pub type TransformAttrTlvCombinatorAlias = Mapped<Pair<Pair<Refined<U16Be, Predicate5630542192344936318>, U16Be, TransformAttrTlvCont1>, bytes::Variable, TransformAttrTlvCont0>, TransformAttrTlvMapper>;


pub open spec fn spec_transform_attr_tlv() -> SpecTransformAttrTlvCombinator {
    SpecTransformAttrTlvCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(Refined { inner: U16Be, predicate: Predicate5630542192344936318 }, |deps| spec_transform_attr_tlv_cont1(deps)), |deps| spec_transform_attr_tlv_cont0(deps)),
        mapper: TransformAttrTlvMapper,
    })
}

pub open spec fn spec_transform_attr_tlv_cont1(deps: u16) -> U16Be {
    let type_and_af = deps;
    U16Be
}

impl View for TransformAttrTlvCont1 {
    type V = spec_fn(u16) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_transform_attr_tlv_cont1(deps)
        }
    }
}

pub open spec fn spec_transform_attr_tlv_cont0(deps: (u16, u16)) -> bytes::Variable {
    let (type_and_af, length) = deps;
    bytes::Variable((usize::spec_from(length)) as usize)
}

impl View for TransformAttrTlvCont0 {
    type V = spec_fn((u16, u16)) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: (u16, u16)| {
            spec_transform_attr_tlv_cont0(deps)
        }
    }
}

                
pub fn transform_attr_tlv<'a>() -> (o: TransformAttrTlvCombinator)
    ensures o@ == spec_transform_attr_tlv(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformAttrTlvCombinator(
    Mapped {
        inner: Pair::new(Pair::new(Refined { inner: U16Be, predicate: Predicate5630542192344936318 }, TransformAttrTlvCont1), TransformAttrTlvCont0),
        mapper: TransformAttrTlvMapper,
    });
    // assert({
    //     &&& combinator@ == spec_transform_attr_tlv()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_attr_tlv<'a>(input: &'a [u8]) -> (res: PResult<<TransformAttrTlvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform_attr_tlv().spec_parse(input@) == Some((n as int, v@)),
        spec_transform_attr_tlv().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_attr_tlv().spec_parse(input@) is None,
        spec_transform_attr_tlv().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_attr_tlv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_attr_tlv<'a>(v: <TransformAttrTlvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_attr_tlv().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_attr_tlv().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_attr_tlv().spec_serialize(v@))
        },
{
    let combinator = transform_attr_tlv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_attr_tlv_len<'a>(v: <TransformAttrTlvCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform_attr_tlv().wf(v@),
        spec_transform_attr_tlv().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform_attr_tlv().spec_serialize(v@).len(),
{
    let combinator = transform_attr_tlv();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TransformAttrTlvCont1;
type TransformAttrTlvCont1Type<'a, 'b> = &'b u16;
type TransformAttrTlvCont1SType<'a, 'x> = &'x u16;
type TransformAttrTlvCont1Input<'a, 'b, 'x> = POrSType<TransformAttrTlvCont1Type<'a, 'b>, TransformAttrTlvCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TransformAttrTlvCont1Input<'a, 'b, 'x>> for TransformAttrTlvCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: TransformAttrTlvCont1Input<'a, 'b, 'x>) -> bool {
        &&& (Refined { inner: U16Be, predicate: Predicate5630542192344936318 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: TransformAttrTlvCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_transform_attr_tlv_cont1(deps@)
    }

    fn apply(&self, deps: TransformAttrTlvCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let type_and_af = deps;
                let type_and_af = *type_and_af;
                U16Be
            }
            POrSType::S(deps) => {
                let type_and_af = deps;
                let type_and_af = *type_and_af;
                U16Be
            }
        }
    }
}
pub struct TransformAttrTlvCont0;
type TransformAttrTlvCont0Type<'a, 'b> = &'b (u16, u16);
type TransformAttrTlvCont0SType<'a, 'x> = (&'x u16, &'x u16);
type TransformAttrTlvCont0Input<'a, 'b, 'x> = POrSType<TransformAttrTlvCont0Type<'a, 'b>, TransformAttrTlvCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TransformAttrTlvCont0Input<'a, 'b, 'x>> for TransformAttrTlvCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: TransformAttrTlvCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(Refined { inner: U16Be, predicate: Predicate5630542192344936318 }, |deps| spec_transform_attr_tlv_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: TransformAttrTlvCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_transform_attr_tlv_cont0(deps@)
    }

    fn apply(&self, deps: TransformAttrTlvCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (type_and_af, length) = deps;
                let type_and_af = *type_and_af;
                let length = *length;
                bytes::Variable((usize::ex_from(length)) as usize)
            }
            POrSType::S(deps) => {
                let (type_and_af, length) = deps;
                let type_and_af = *type_and_af;
                let length = *length;
                bytes::Variable((usize::ex_from(length)) as usize)
            }
        }
    }
}
                

pub enum SpecTransformAttr {
    KeyLength(SpecTransformAttrKeyLength),
    TV(SpecTransformAttrTv),
    TLV(SpecTransformAttrTlv),
}

pub type SpecTransformAttrInner = Either<SpecTransformAttrKeyLength, Either<SpecTransformAttrTv, SpecTransformAttrTlv>>;

impl SpecFrom<SpecTransformAttr> for SpecTransformAttrInner {
    open spec fn spec_from(m: SpecTransformAttr) -> SpecTransformAttrInner {
        match m {
            SpecTransformAttr::KeyLength(m) => Either::Left(m),
            SpecTransformAttr::TV(m) => Either::Right(Either::Left(m)),
            SpecTransformAttr::TLV(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecTransformAttrInner> for SpecTransformAttr {
    open spec fn spec_from(m: SpecTransformAttrInner) -> SpecTransformAttr {
        match m {
            Either::Left(m) => SpecTransformAttr::KeyLength(m),
            Either::Right(Either::Left(m)) => SpecTransformAttr::TV(m),
            Either::Right(Either::Right(m)) => SpecTransformAttr::TLV(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TransformAttr<'a> {
    KeyLength(TransformAttrKeyLength),
    TV(TransformAttrTv),
    TLV(TransformAttrTlv<'a>),
}

pub type TransformAttrInner<'a> = Either<TransformAttrKeyLength, Either<TransformAttrTv, TransformAttrTlv<'a>>>;

pub type TransformAttrInnerRef<'a> = Either<&'a TransformAttrKeyLength, Either<&'a TransformAttrTv, &'a TransformAttrTlv<'a>>>;


impl<'a> View for TransformAttr<'a> {
    type V = SpecTransformAttr;
    open spec fn view(&self) -> Self::V {
        match self {
            TransformAttr::KeyLength(m) => SpecTransformAttr::KeyLength(m@),
            TransformAttr::TV(m) => SpecTransformAttr::TV(m@),
            TransformAttr::TLV(m) => SpecTransformAttr::TLV(m@),
        }
    }
}


impl<'a> From<&'a TransformAttr<'a>> for TransformAttrInnerRef<'a> {
    fn ex_from(m: &'a TransformAttr<'a>) -> TransformAttrInnerRef<'a> {
        match m {
            TransformAttr::KeyLength(m) => Either::Left(m),
            TransformAttr::TV(m) => Either::Right(Either::Left(m)),
            TransformAttr::TLV(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<TransformAttrInner<'a>> for TransformAttr<'a> {
    fn ex_from(m: TransformAttrInner<'a>) -> TransformAttr<'a> {
        match m {
            Either::Left(m) => TransformAttr::KeyLength(m),
            Either::Right(Either::Left(m)) => TransformAttr::TV(m),
            Either::Right(Either::Right(m)) => TransformAttr::TLV(m),
        }
    }
    
}


pub struct TransformAttrMapper;
impl View for TransformAttrMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformAttrMapper {
    type Src = SpecTransformAttrInner;
    type Dst = SpecTransformAttr;
}
impl SpecIsoProof for TransformAttrMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformAttrMapper {
    type Src = TransformAttrInner<'a>;
    type Dst = TransformAttr<'a>;
    type RefSrc = TransformAttrInnerRef<'a>;
}

type SpecTransformAttrCombinatorAlias1 = Choice<SpecTransformAttrTvCombinator, SpecTransformAttrTlvCombinator>;
type SpecTransformAttrCombinatorAlias2 = Choice<SpecTransformAttrKeyLengthCombinator, SpecTransformAttrCombinatorAlias1>;
impl DisjointFrom<SpecTransformAttrKeyLengthCombinator> for SpecTransformAttrTvCombinator {
    open spec fn disjoint_from(&self, other: &SpecTransformAttrKeyLengthCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecTransformAttrKeyLengthCombinator, buf: Seq<u8>)
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecTransformAttrKeyLengthCombinator> for SpecTransformAttrTlvCombinator {
    open spec fn disjoint_from(&self, other: &SpecTransformAttrKeyLengthCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecTransformAttrKeyLengthCombinator, buf: Seq<u8>)
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecTransformAttrTvCombinator> for SpecTransformAttrTlvCombinator {
    open spec fn disjoint_from(&self, other: &SpecTransformAttrTvCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecTransformAttrTvCombinator, buf: Seq<u8>)
    { self.0.parse_disjoint_on(&other.0, buf); }
}
pub struct SpecTransformAttrCombinator(pub SpecTransformAttrCombinatorAlias);

impl SpecCombinator for SpecTransformAttrCombinator {
    type Type = SpecTransformAttr;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformAttrCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformAttrCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformAttrCombinatorAlias = Mapped<SpecTransformAttrCombinatorAlias2, TransformAttrMapper>;
type TransformAttrCombinatorAlias1 = Choice<TransformAttrTvCombinator, TransformAttrTlvCombinator>;
type TransformAttrCombinatorAlias2 = Choice<TransformAttrKeyLengthCombinator, TransformAttrCombinator1>;
pub struct TransformAttrCombinator1(pub TransformAttrCombinatorAlias1);
impl View for TransformAttrCombinator1 {
    type V = SpecTransformAttrCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformAttrCombinator1, TransformAttrCombinatorAlias1);

pub struct TransformAttrCombinator2(pub TransformAttrCombinatorAlias2);
impl View for TransformAttrCombinator2 {
    type V = SpecTransformAttrCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TransformAttrCombinator2, TransformAttrCombinatorAlias2);

pub struct TransformAttrCombinator(pub TransformAttrCombinatorAlias);

impl View for TransformAttrCombinator {
    type V = SpecTransformAttrCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformAttrCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformAttrCombinator {
    type Type = TransformAttr<'a>;
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
pub type TransformAttrCombinatorAlias = Mapped<TransformAttrCombinator2, TransformAttrMapper>;


pub open spec fn spec_transform_attr() -> SpecTransformAttrCombinator {
    SpecTransformAttrCombinator(Mapped { inner: Choice(spec_transform_attr_key_length(), Choice(spec_transform_attr_tv(), spec_transform_attr_tlv())), mapper: TransformAttrMapper })
}

                
pub fn transform_attr<'a>() -> (o: TransformAttrCombinator)
    ensures o@ == spec_transform_attr(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformAttrCombinator(Mapped { inner: TransformAttrCombinator2(Choice::new(transform_attr_key_length(), TransformAttrCombinator1(Choice::new(transform_attr_tv(), transform_attr_tlv())))), mapper: TransformAttrMapper });
    // assert({
    //     &&& combinator@ == spec_transform_attr()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform_attr<'a>(input: &'a [u8]) -> (res: PResult<<TransformAttrCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform_attr().spec_parse(input@) == Some((n as int, v@)),
        spec_transform_attr().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform_attr().spec_parse(input@) is None,
        spec_transform_attr().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform_attr();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform_attr<'a>(v: <TransformAttrCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform_attr().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform_attr().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform_attr().spec_serialize(v@))
        },
{
    let combinator = transform_attr();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_attr_len<'a>(v: <TransformAttrCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform_attr().wf(v@),
        spec_transform_attr().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform_attr().spec_serialize(v@).len(),
{
    let combinator = transform_attr();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTransform {
    pub last_or_more: u8,
    pub reserved: u8,
    pub transform_length: u16,
    pub transform_type: u8,
    pub reserved2: u8,
    pub transform_id: SpecTransformIdValue,
    pub attrs: Seq<SpecTransformAttr>,
}

pub type SpecTransformInner = (((u8, (u8, u16)), u8), (u8, (SpecTransformIdValue, Seq<SpecTransformAttr>)));


impl SpecFrom<SpecTransform> for SpecTransformInner {
    open spec fn spec_from(m: SpecTransform) -> SpecTransformInner {
        (((m.last_or_more, (m.reserved, m.transform_length)), m.transform_type), (m.reserved2, (m.transform_id, m.attrs)))
    }
}

impl SpecFrom<SpecTransformInner> for SpecTransform {
    open spec fn spec_from(m: SpecTransformInner) -> SpecTransform {
        let (((last_or_more, (reserved, transform_length)), transform_type), (reserved2, (transform_id, attrs))) = m;
        SpecTransform { last_or_more, reserved, transform_length, transform_type, reserved2, transform_id, attrs }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Transform<'a> {
    pub last_or_more: u8,
    pub reserved: u8,
    pub transform_length: u16,
    pub transform_type: u8,
    pub reserved2: u8,
    pub transform_id: TransformIdValue,
    pub attrs: RepeatResult<TransformAttr<'a>>,
}

impl View for Transform<'_> {
    type V = SpecTransform;

    open spec fn view(&self) -> Self::V {
        SpecTransform {
            last_or_more: self.last_or_more@,
            reserved: self.reserved@,
            transform_length: self.transform_length@,
            transform_type: self.transform_type@,
            reserved2: self.reserved2@,
            transform_id: self.transform_id@,
            attrs: self.attrs@,
        }
    }
}
pub type TransformInner<'a> = (((u8, (u8, u16)), u8), (u8, (TransformIdValue, RepeatResult<TransformAttr<'a>>)));

pub type TransformInnerRef<'a> = (((&'a u8, (&'a u8, &'a u16)), &'a u8), (&'a u8, (&'a TransformIdValue, &'a RepeatResult<TransformAttr<'a>>)));
impl<'a> From<&'a Transform<'a>> for TransformInnerRef<'a> {
    fn ex_from(m: &'a Transform) -> TransformInnerRef<'a> {
        (((&m.last_or_more, (&m.reserved, &m.transform_length)), &m.transform_type), (&m.reserved2, (&m.transform_id, &m.attrs)))
    }
}

impl<'a> From<TransformInner<'a>> for Transform<'a> {
    fn ex_from(m: TransformInner) -> Transform {
        let (((last_or_more, (reserved, transform_length)), transform_type), (reserved2, (transform_id, attrs))) = m;
        Transform { last_or_more, reserved, transform_length, transform_type, reserved2, transform_id, attrs }
    }
}

pub struct TransformMapper;
impl View for TransformMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TransformMapper {
    type Src = SpecTransformInner;
    type Dst = SpecTransform;
}
impl SpecIsoProof for TransformMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TransformMapper {
    type Src = TransformInner<'a>;
    type Dst = Transform<'a>;
    type RefSrc = TransformInnerRef<'a>;
}
pub const TRANSFORMRESERVED_CONST: u8 = 0;
pub const TRANSFORMRESERVED2_CONST: u8 = 0;

pub struct SpecTransformCombinator(pub SpecTransformCombinatorAlias);

impl SpecCombinator for SpecTransformCombinator {
    type Type = SpecTransform;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTransformCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTransformCombinatorAlias::is_prefix_secure() }
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
pub type SpecTransformCombinatorAlias = Mapped<SpecPair<SpecPair<(Refined<U8, Predicate11363499016643468509>, (Refined<U8, TagPred<u8>>, Refined<U16Be, Predicate18193225726552524852>)), SpecTransformTypeCombinator>, (Refined<U8, TagPred<u8>>, (SpecTransformIdValueCombinator, AndThen<bytes::Variable, Repeat<SpecTransformAttrCombinator>>))>, TransformMapper>;
pub struct Predicate11363499016643468509;
impl View for Predicate11363499016643468509 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate11363499016643468509 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 3)
    }
}
impl SpecPred<u8> for Predicate11363499016643468509 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 3)
    }
}
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

pub struct TransformCombinator(pub TransformCombinatorAlias);

impl View for TransformCombinator {
    type V = SpecTransformCombinator;
    open spec fn view(&self) -> Self::V { SpecTransformCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TransformCombinator {
    type Type = Transform<'a>;
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
pub type TransformCombinatorAlias = Mapped<Pair<Pair<(Refined<U8, Predicate11363499016643468509>, (Refined<U8, TagPred<u8>>, Refined<U16Be, Predicate18193225726552524852>)), TransformTypeCombinator, TransformCont1>, (Refined<U8, TagPred<u8>>, (TransformIdValueCombinator, AndThen<bytes::Variable, Repeat<TransformAttrCombinator>>)), TransformCont0>, TransformMapper>;


pub open spec fn spec_transform() -> SpecTransformCombinator {
    SpecTransformCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new((Refined { inner: U8, predicate: Predicate11363499016643468509 }, (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_transform_cont1(deps)), |deps| spec_transform_cont0(deps)),
        mapper: TransformMapper,
    })
}

pub open spec fn spec_transform_cont1(deps: (u8, (u8, u16))) -> SpecTransformTypeCombinator {
    let (_, (_, transform_length)) = deps;
    spec_transform_type()
}

impl View for TransformCont1 {
    type V = spec_fn((u8, (u8, u16))) -> SpecTransformTypeCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, (u8, u16))| {
            spec_transform_cont1(deps)
        }
    }
}

pub open spec fn spec_transform_cont0(deps: ((u8, (u8, u16)), u8)) -> (Refined<U8, TagPred<u8>>, (SpecTransformIdValueCombinator, AndThen<bytes::Variable, Repeat<SpecTransformAttrCombinator>>)) {
    let ((_, (_, transform_length)), transform_type) = deps;
    (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED2_CONST) }, (spec_transform_id_value(transform_type), AndThen(bytes::Variable(((usize::spec_from(transform_length) - 8)) as usize), Repeat(spec_transform_attr()))))
}

impl View for TransformCont0 {
    type V = spec_fn(((u8, (u8, u16)), u8)) -> (Refined<U8, TagPred<u8>>, (SpecTransformIdValueCombinator, AndThen<bytes::Variable, Repeat<SpecTransformAttrCombinator>>));

    open spec fn view(&self) -> Self::V {
        |deps: ((u8, (u8, u16)), u8)| {
            spec_transform_cont0(deps)
        }
    }
}

                
pub fn transform<'a>() -> (o: TransformCombinator)
    ensures o@ == spec_transform(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TransformCombinator(
    Mapped {
        inner: Pair::new(Pair::new((Refined { inner: U8, predicate: Predicate11363499016643468509 }, (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), TransformCont1), TransformCont0),
        mapper: TransformMapper,
    });
    // assert({
    //     &&& combinator@ == spec_transform()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_transform<'a>(input: &'a [u8]) -> (res: PResult<<TransformCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_transform().spec_parse(input@) == Some((n as int, v@)),
        spec_transform().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_transform().spec_parse(input@) is None,
        spec_transform().spec_parse(input@) is None ==> res is Err,
{
    let combinator = transform();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_transform<'a>(v: <TransformCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_transform().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_transform().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_transform().spec_serialize(v@))
        },
{
    let combinator = transform();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn transform_len<'a>(v: <TransformCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_transform().wf(v@),
        spec_transform().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_transform().spec_serialize(v@).len(),
{
    let combinator = transform();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TransformCont1;
type TransformCont1Type<'a, 'b> = &'b (u8, (u8, u16));
type TransformCont1SType<'a, 'x> = (&'x u8, (&'x u8, &'x u16));
type TransformCont1Input<'a, 'b, 'x> = POrSType<TransformCont1Type<'a, 'b>, TransformCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TransformCont1Input<'a, 'b, 'x>> for TransformCont1 {
    type Output = TransformTypeCombinator;

    open spec fn requires(&self, deps: TransformCont1Input<'a, 'b, 'x>) -> bool {
        &&& ((Refined { inner: U8, predicate: Predicate11363499016643468509 }, (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 }))).wf(deps@)
        }

    open spec fn ensures(&self, deps: TransformCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_transform_cont1(deps@)
    }

    fn apply(&self, deps: TransformCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, (_, transform_length)) = deps;
                let transform_length = *transform_length;
                transform_type()
            }
            POrSType::S(deps) => {
                let (_, (_, transform_length)) = deps;
                let transform_length = *transform_length;
                transform_type()
            }
        }
    }
}
pub struct TransformCont0;
type TransformCont0Type<'a, 'b> = &'b ((u8, (u8, u16)), u8);
type TransformCont0SType<'a, 'x> = ((&'x u8, (&'x u8, &'x u16)), &'x u8);
type TransformCont0Input<'a, 'b, 'x> = POrSType<TransformCont0Type<'a, 'b>, TransformCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TransformCont0Input<'a, 'b, 'x>> for TransformCont0 {
    type Output = (Refined<U8, TagPred<u8>>, (TransformIdValueCombinator, AndThen<bytes::Variable, Repeat<TransformAttrCombinator>>));

    open spec fn requires(&self, deps: TransformCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new((Refined { inner: U8, predicate: Predicate11363499016643468509 }, (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_transform_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: TransformCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_transform_cont0(deps@)
    }

    fn apply(&self, deps: TransformCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((_, (_, transform_length)), transform_type) = deps;
                let transform_length = *transform_length;
                let transform_type = *transform_type;
                (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED2_CONST) }, (transform_id_value(transform_type), AndThen(bytes::Variable(((usize::ex_from(transform_length) - 8)) as usize), Repeat::new(transform_attr()))))
            }
            POrSType::S(deps) => {
                let ((_, (_, transform_length)), transform_type) = deps;
                let transform_length = *transform_length;
                let transform_type = *transform_type;
                (Refined { inner: U8, predicate: TagPred(TRANSFORMRESERVED2_CONST) }, (transform_id_value(transform_type), AndThen(bytes::Variable(((usize::ex_from(transform_length) - 8)) as usize), Repeat::new(transform_attr()))))
            }
        }
    }
}
                

pub struct SpecProposalBodySpi0 {
    pub spi: Seq<u8>,
    pub transforms: Seq<SpecTransform>,
}

pub type SpecProposalBodySpi0Inner = (Seq<u8>, Seq<SpecTransform>);


impl SpecFrom<SpecProposalBodySpi0> for SpecProposalBodySpi0Inner {
    open spec fn spec_from(m: SpecProposalBodySpi0) -> SpecProposalBodySpi0Inner {
        (m.spi, m.transforms)
    }
}

impl SpecFrom<SpecProposalBodySpi0Inner> for SpecProposalBodySpi0 {
    open spec fn spec_from(m: SpecProposalBodySpi0Inner) -> SpecProposalBodySpi0 {
        let (spi, transforms) = m;
        SpecProposalBodySpi0 { spi, transforms }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ProposalBodySpi0<'a> {
    pub spi: &'a [u8],
    pub transforms: RepeatResult<Transform<'a>>,
}

impl View for ProposalBodySpi0<'_> {
    type V = SpecProposalBodySpi0;

    open spec fn view(&self) -> Self::V {
        SpecProposalBodySpi0 {
            spi: self.spi@,
            transforms: self.transforms@,
        }
    }
}
pub type ProposalBodySpi0Inner<'a> = (&'a [u8], RepeatResult<Transform<'a>>);

pub type ProposalBodySpi0InnerRef<'a> = (&'a &'a [u8], &'a RepeatResult<Transform<'a>>);
impl<'a> From<&'a ProposalBodySpi0<'a>> for ProposalBodySpi0InnerRef<'a> {
    fn ex_from(m: &'a ProposalBodySpi0) -> ProposalBodySpi0InnerRef<'a> {
        (&m.spi, &m.transforms)
    }
}

impl<'a> From<ProposalBodySpi0Inner<'a>> for ProposalBodySpi0<'a> {
    fn ex_from(m: ProposalBodySpi0Inner) -> ProposalBodySpi0 {
        let (spi, transforms) = m;
        ProposalBodySpi0 { spi, transforms }
    }
}

pub struct ProposalBodySpi0Mapper;
impl View for ProposalBodySpi0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProposalBodySpi0Mapper {
    type Src = SpecProposalBodySpi0Inner;
    type Dst = SpecProposalBodySpi0;
}
impl SpecIsoProof for ProposalBodySpi0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProposalBodySpi0Mapper {
    type Src = ProposalBodySpi0Inner<'a>;
    type Dst = ProposalBodySpi0<'a>;
    type RefSrc = ProposalBodySpi0InnerRef<'a>;
}
type SpecProposalBodySpi0CombinatorAlias1 = (bytes::Fixed<0>, AndThen<bytes::Tail, RepeatN<SpecTransformCombinator>>);
pub struct SpecProposalBodySpi0Combinator(pub SpecProposalBodySpi0CombinatorAlias);

impl SpecCombinator for SpecProposalBodySpi0Combinator {
    type Type = SpecProposalBodySpi0;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalBodySpi0Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalBodySpi0CombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalBodySpi0CombinatorAlias = Mapped<SpecProposalBodySpi0CombinatorAlias1, ProposalBodySpi0Mapper>;
type ProposalBodySpi0CombinatorAlias1 = (bytes::Fixed<0>, AndThen<bytes::Tail, RepeatN<TransformCombinator>>);
pub struct ProposalBodySpi0Combinator1(pub ProposalBodySpi0CombinatorAlias1);
impl View for ProposalBodySpi0Combinator1 {
    type V = SpecProposalBodySpi0CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ProposalBodySpi0Combinator1, ProposalBodySpi0CombinatorAlias1);

pub struct ProposalBodySpi0Combinator(pub ProposalBodySpi0CombinatorAlias);

impl View for ProposalBodySpi0Combinator {
    type V = SpecProposalBodySpi0Combinator;
    open spec fn view(&self) -> Self::V { SpecProposalBodySpi0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalBodySpi0Combinator {
    type Type = ProposalBodySpi0<'a>;
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
pub type ProposalBodySpi0CombinatorAlias = Mapped<ProposalBodySpi0Combinator1, ProposalBodySpi0Mapper>;


pub open spec fn spec_proposal_body_spi0(num_transforms: u8) -> SpecProposalBodySpi0Combinator {
    SpecProposalBodySpi0Combinator(
    Mapped {
        inner: (bytes::Fixed::<0>, AndThen(bytes::Tail, RepeatN(spec_transform(), (usize::spec_from(num_transforms)) as usize))),
        mapper: ProposalBodySpi0Mapper,
    })
}

pub fn proposal_body_spi0<'a>(num_transforms: u8) -> (o: ProposalBodySpi0Combinator)
    requires
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures o@ == spec_proposal_body_spi0(num_transforms@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalBodySpi0Combinator(
    Mapped {
        inner: ProposalBodySpi0Combinator1((bytes::Fixed::<0>, AndThen(bytes::Tail, RepeatN(transform(), (usize::ex_from(num_transforms)) as usize)))),
        mapper: ProposalBodySpi0Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_proposal_body_spi0(num_transforms@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal_body_spi0<'a>(input: &'a [u8], num_transforms: u8) -> (res: PResult<<ProposalBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        res matches Ok((n, v)) ==> spec_proposal_body_spi0(num_transforms@).spec_parse(input@) == Some((n as int, v@)),
        spec_proposal_body_spi0(num_transforms@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal_body_spi0(num_transforms@).spec_parse(input@) is None,
        spec_proposal_body_spi0(num_transforms@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal_body_spi0( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal_body_spi0<'a>(v: <ProposalBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, num_transforms: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal_body_spi0(num_transforms@).wf(v@),
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal_body_spi0(num_transforms@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal_body_spi0(num_transforms@).spec_serialize(v@))
        },
{
    let combinator = proposal_body_spi0( num_transforms );
    combinator.serialize(v, data, pos)
}

pub fn proposal_body_spi0_len<'a>(v: <ProposalBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, num_transforms: u8) -> (serialize_len: usize)
    requires
        spec_proposal_body_spi0(num_transforms@).wf(v@),
        spec_proposal_body_spi0(num_transforms@).spec_serialize(v@).len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        serialize_len == spec_proposal_body_spi0(num_transforms@).spec_serialize(v@).len(),
{
    let combinator = proposal_body_spi0( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecProposalBodySpi4 {
    pub spi: Seq<u8>,
    pub transforms: Seq<SpecTransform>,
}

pub type SpecProposalBodySpi4Inner = (Seq<u8>, Seq<SpecTransform>);


impl SpecFrom<SpecProposalBodySpi4> for SpecProposalBodySpi4Inner {
    open spec fn spec_from(m: SpecProposalBodySpi4) -> SpecProposalBodySpi4Inner {
        (m.spi, m.transforms)
    }
}

impl SpecFrom<SpecProposalBodySpi4Inner> for SpecProposalBodySpi4 {
    open spec fn spec_from(m: SpecProposalBodySpi4Inner) -> SpecProposalBodySpi4 {
        let (spi, transforms) = m;
        SpecProposalBodySpi4 { spi, transforms }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ProposalBodySpi4<'a> {
    pub spi: &'a [u8],
    pub transforms: RepeatResult<Transform<'a>>,
}

impl View for ProposalBodySpi4<'_> {
    type V = SpecProposalBodySpi4;

    open spec fn view(&self) -> Self::V {
        SpecProposalBodySpi4 {
            spi: self.spi@,
            transforms: self.transforms@,
        }
    }
}
pub type ProposalBodySpi4Inner<'a> = (&'a [u8], RepeatResult<Transform<'a>>);

pub type ProposalBodySpi4InnerRef<'a> = (&'a &'a [u8], &'a RepeatResult<Transform<'a>>);
impl<'a> From<&'a ProposalBodySpi4<'a>> for ProposalBodySpi4InnerRef<'a> {
    fn ex_from(m: &'a ProposalBodySpi4) -> ProposalBodySpi4InnerRef<'a> {
        (&m.spi, &m.transforms)
    }
}

impl<'a> From<ProposalBodySpi4Inner<'a>> for ProposalBodySpi4<'a> {
    fn ex_from(m: ProposalBodySpi4Inner) -> ProposalBodySpi4 {
        let (spi, transforms) = m;
        ProposalBodySpi4 { spi, transforms }
    }
}

pub struct ProposalBodySpi4Mapper;
impl View for ProposalBodySpi4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProposalBodySpi4Mapper {
    type Src = SpecProposalBodySpi4Inner;
    type Dst = SpecProposalBodySpi4;
}
impl SpecIsoProof for ProposalBodySpi4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProposalBodySpi4Mapper {
    type Src = ProposalBodySpi4Inner<'a>;
    type Dst = ProposalBodySpi4<'a>;
    type RefSrc = ProposalBodySpi4InnerRef<'a>;
}
type SpecProposalBodySpi4CombinatorAlias1 = (bytes::Fixed<4>, AndThen<bytes::Tail, RepeatN<SpecTransformCombinator>>);
pub struct SpecProposalBodySpi4Combinator(pub SpecProposalBodySpi4CombinatorAlias);

impl SpecCombinator for SpecProposalBodySpi4Combinator {
    type Type = SpecProposalBodySpi4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalBodySpi4Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalBodySpi4CombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalBodySpi4CombinatorAlias = Mapped<SpecProposalBodySpi4CombinatorAlias1, ProposalBodySpi4Mapper>;
type ProposalBodySpi4CombinatorAlias1 = (bytes::Fixed<4>, AndThen<bytes::Tail, RepeatN<TransformCombinator>>);
pub struct ProposalBodySpi4Combinator1(pub ProposalBodySpi4CombinatorAlias1);
impl View for ProposalBodySpi4Combinator1 {
    type V = SpecProposalBodySpi4CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ProposalBodySpi4Combinator1, ProposalBodySpi4CombinatorAlias1);

pub struct ProposalBodySpi4Combinator(pub ProposalBodySpi4CombinatorAlias);

impl View for ProposalBodySpi4Combinator {
    type V = SpecProposalBodySpi4Combinator;
    open spec fn view(&self) -> Self::V { SpecProposalBodySpi4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalBodySpi4Combinator {
    type Type = ProposalBodySpi4<'a>;
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
pub type ProposalBodySpi4CombinatorAlias = Mapped<ProposalBodySpi4Combinator1, ProposalBodySpi4Mapper>;


pub open spec fn spec_proposal_body_spi4(num_transforms: u8) -> SpecProposalBodySpi4Combinator {
    SpecProposalBodySpi4Combinator(
    Mapped {
        inner: (bytes::Fixed::<4>, AndThen(bytes::Tail, RepeatN(spec_transform(), (usize::spec_from(num_transforms)) as usize))),
        mapper: ProposalBodySpi4Mapper,
    })
}

pub fn proposal_body_spi4<'a>(num_transforms: u8) -> (o: ProposalBodySpi4Combinator)
    requires
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures o@ == spec_proposal_body_spi4(num_transforms@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalBodySpi4Combinator(
    Mapped {
        inner: ProposalBodySpi4Combinator1((bytes::Fixed::<4>, AndThen(bytes::Tail, RepeatN(transform(), (usize::ex_from(num_transforms)) as usize)))),
        mapper: ProposalBodySpi4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_proposal_body_spi4(num_transforms@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal_body_spi4<'a>(input: &'a [u8], num_transforms: u8) -> (res: PResult<<ProposalBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        res matches Ok((n, v)) ==> spec_proposal_body_spi4(num_transforms@).spec_parse(input@) == Some((n as int, v@)),
        spec_proposal_body_spi4(num_transforms@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal_body_spi4(num_transforms@).spec_parse(input@) is None,
        spec_proposal_body_spi4(num_transforms@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal_body_spi4( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal_body_spi4<'a>(v: <ProposalBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, num_transforms: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal_body_spi4(num_transforms@).wf(v@),
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal_body_spi4(num_transforms@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal_body_spi4(num_transforms@).spec_serialize(v@))
        },
{
    let combinator = proposal_body_spi4( num_transforms );
    combinator.serialize(v, data, pos)
}

pub fn proposal_body_spi4_len<'a>(v: <ProposalBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, num_transforms: u8) -> (serialize_len: usize)
    requires
        spec_proposal_body_spi4(num_transforms@).wf(v@),
        spec_proposal_body_spi4(num_transforms@).spec_serialize(v@).len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        serialize_len == spec_proposal_body_spi4(num_transforms@).spec_serialize(v@).len(),
{
    let combinator = proposal_body_spi4( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecProposalBodySpi8 {
    pub spi: Seq<u8>,
    pub transforms: Seq<SpecTransform>,
}

pub type SpecProposalBodySpi8Inner = (Seq<u8>, Seq<SpecTransform>);


impl SpecFrom<SpecProposalBodySpi8> for SpecProposalBodySpi8Inner {
    open spec fn spec_from(m: SpecProposalBodySpi8) -> SpecProposalBodySpi8Inner {
        (m.spi, m.transforms)
    }
}

impl SpecFrom<SpecProposalBodySpi8Inner> for SpecProposalBodySpi8 {
    open spec fn spec_from(m: SpecProposalBodySpi8Inner) -> SpecProposalBodySpi8 {
        let (spi, transforms) = m;
        SpecProposalBodySpi8 { spi, transforms }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ProposalBodySpi8<'a> {
    pub spi: &'a [u8],
    pub transforms: RepeatResult<Transform<'a>>,
}

impl View for ProposalBodySpi8<'_> {
    type V = SpecProposalBodySpi8;

    open spec fn view(&self) -> Self::V {
        SpecProposalBodySpi8 {
            spi: self.spi@,
            transforms: self.transforms@,
        }
    }
}
pub type ProposalBodySpi8Inner<'a> = (&'a [u8], RepeatResult<Transform<'a>>);

pub type ProposalBodySpi8InnerRef<'a> = (&'a &'a [u8], &'a RepeatResult<Transform<'a>>);
impl<'a> From<&'a ProposalBodySpi8<'a>> for ProposalBodySpi8InnerRef<'a> {
    fn ex_from(m: &'a ProposalBodySpi8) -> ProposalBodySpi8InnerRef<'a> {
        (&m.spi, &m.transforms)
    }
}

impl<'a> From<ProposalBodySpi8Inner<'a>> for ProposalBodySpi8<'a> {
    fn ex_from(m: ProposalBodySpi8Inner) -> ProposalBodySpi8 {
        let (spi, transforms) = m;
        ProposalBodySpi8 { spi, transforms }
    }
}

pub struct ProposalBodySpi8Mapper;
impl View for ProposalBodySpi8Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProposalBodySpi8Mapper {
    type Src = SpecProposalBodySpi8Inner;
    type Dst = SpecProposalBodySpi8;
}
impl SpecIsoProof for ProposalBodySpi8Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProposalBodySpi8Mapper {
    type Src = ProposalBodySpi8Inner<'a>;
    type Dst = ProposalBodySpi8<'a>;
    type RefSrc = ProposalBodySpi8InnerRef<'a>;
}
type SpecProposalBodySpi8CombinatorAlias1 = (bytes::Fixed<8>, AndThen<bytes::Tail, RepeatN<SpecTransformCombinator>>);
pub struct SpecProposalBodySpi8Combinator(pub SpecProposalBodySpi8CombinatorAlias);

impl SpecCombinator for SpecProposalBodySpi8Combinator {
    type Type = SpecProposalBodySpi8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalBodySpi8Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalBodySpi8CombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalBodySpi8CombinatorAlias = Mapped<SpecProposalBodySpi8CombinatorAlias1, ProposalBodySpi8Mapper>;
type ProposalBodySpi8CombinatorAlias1 = (bytes::Fixed<8>, AndThen<bytes::Tail, RepeatN<TransformCombinator>>);
pub struct ProposalBodySpi8Combinator1(pub ProposalBodySpi8CombinatorAlias1);
impl View for ProposalBodySpi8Combinator1 {
    type V = SpecProposalBodySpi8CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ProposalBodySpi8Combinator1, ProposalBodySpi8CombinatorAlias1);

pub struct ProposalBodySpi8Combinator(pub ProposalBodySpi8CombinatorAlias);

impl View for ProposalBodySpi8Combinator {
    type V = SpecProposalBodySpi8Combinator;
    open spec fn view(&self) -> Self::V { SpecProposalBodySpi8Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalBodySpi8Combinator {
    type Type = ProposalBodySpi8<'a>;
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
pub type ProposalBodySpi8CombinatorAlias = Mapped<ProposalBodySpi8Combinator1, ProposalBodySpi8Mapper>;


pub open spec fn spec_proposal_body_spi8(num_transforms: u8) -> SpecProposalBodySpi8Combinator {
    SpecProposalBodySpi8Combinator(
    Mapped {
        inner: (bytes::Fixed::<8>, AndThen(bytes::Tail, RepeatN(spec_transform(), (usize::spec_from(num_transforms)) as usize))),
        mapper: ProposalBodySpi8Mapper,
    })
}

pub fn proposal_body_spi8<'a>(num_transforms: u8) -> (o: ProposalBodySpi8Combinator)
    requires
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures o@ == spec_proposal_body_spi8(num_transforms@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalBodySpi8Combinator(
    Mapped {
        inner: ProposalBodySpi8Combinator1((bytes::Fixed::<8>, AndThen(bytes::Tail, RepeatN(transform(), (usize::ex_from(num_transforms)) as usize)))),
        mapper: ProposalBodySpi8Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_proposal_body_spi8(num_transforms@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal_body_spi8<'a>(input: &'a [u8], num_transforms: u8) -> (res: PResult<<ProposalBodySpi8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        res matches Ok((n, v)) ==> spec_proposal_body_spi8(num_transforms@).spec_parse(input@) == Some((n as int, v@)),
        spec_proposal_body_spi8(num_transforms@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal_body_spi8(num_transforms@).spec_parse(input@) is None,
        spec_proposal_body_spi8(num_transforms@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal_body_spi8( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal_body_spi8<'a>(v: <ProposalBodySpi8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, num_transforms: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal_body_spi8(num_transforms@).wf(v@),
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal_body_spi8(num_transforms@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal_body_spi8(num_transforms@).spec_serialize(v@))
        },
{
    let combinator = proposal_body_spi8( num_transforms );
    combinator.serialize(v, data, pos)
}

pub fn proposal_body_spi8_len<'a>(v: <ProposalBodySpi8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, num_transforms: u8) -> (serialize_len: usize)
    requires
        spec_proposal_body_spi8(num_transforms@).wf(v@),
        spec_proposal_body_spi8(num_transforms@).spec_serialize(v@).len() <= usize::MAX,
        ((num_transforms) >= 1 && (num_transforms) <= 255),

    ensures
        serialize_len == spec_proposal_body_spi8(num_transforms@).spec_serialize(v@).len(),
{
    let combinator = proposal_body_spi8( num_transforms );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecProposalBody {
    Variant0(SpecProposalBodySpi0),
    Variant1(SpecProposalBodySpi4),
    Variant2(SpecProposalBodySpi8),
}

pub type SpecProposalBodyInner = Either<SpecProposalBodySpi0, Either<SpecProposalBodySpi4, SpecProposalBodySpi8>>;

impl SpecFrom<SpecProposalBody> for SpecProposalBodyInner {
    open spec fn spec_from(m: SpecProposalBody) -> SpecProposalBodyInner {
        match m {
            SpecProposalBody::Variant0(m) => Either::Left(m),
            SpecProposalBody::Variant1(m) => Either::Right(Either::Left(m)),
            SpecProposalBody::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecProposalBodyInner> for SpecProposalBody {
    open spec fn spec_from(m: SpecProposalBodyInner) -> SpecProposalBody {
        match m {
            Either::Left(m) => SpecProposalBody::Variant0(m),
            Either::Right(Either::Left(m)) => SpecProposalBody::Variant1(m),
            Either::Right(Either::Right(m)) => SpecProposalBody::Variant2(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProposalBody<'a> {
    Variant0(ProposalBodySpi0<'a>),
    Variant1(ProposalBodySpi4<'a>),
    Variant2(ProposalBodySpi8<'a>),
}

pub type ProposalBodyInner<'a> = Either<ProposalBodySpi0<'a>, Either<ProposalBodySpi4<'a>, ProposalBodySpi8<'a>>>;

pub type ProposalBodyInnerRef<'a> = Either<&'a ProposalBodySpi0<'a>, Either<&'a ProposalBodySpi4<'a>, &'a ProposalBodySpi8<'a>>>;


impl<'a> View for ProposalBody<'a> {
    type V = SpecProposalBody;
    open spec fn view(&self) -> Self::V {
        match self {
            ProposalBody::Variant0(m) => SpecProposalBody::Variant0(m@),
            ProposalBody::Variant1(m) => SpecProposalBody::Variant1(m@),
            ProposalBody::Variant2(m) => SpecProposalBody::Variant2(m@),
        }
    }
}


impl<'a> From<&'a ProposalBody<'a>> for ProposalBodyInnerRef<'a> {
    fn ex_from(m: &'a ProposalBody<'a>) -> ProposalBodyInnerRef<'a> {
        match m {
            ProposalBody::Variant0(m) => Either::Left(m),
            ProposalBody::Variant1(m) => Either::Right(Either::Left(m)),
            ProposalBody::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<ProposalBodyInner<'a>> for ProposalBody<'a> {
    fn ex_from(m: ProposalBodyInner<'a>) -> ProposalBody<'a> {
        match m {
            Either::Left(m) => ProposalBody::Variant0(m),
            Either::Right(Either::Left(m)) => ProposalBody::Variant1(m),
            Either::Right(Either::Right(m)) => ProposalBody::Variant2(m),
        }
    }
    
}


pub struct ProposalBodyMapper;
impl View for ProposalBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProposalBodyMapper {
    type Src = SpecProposalBodyInner;
    type Dst = SpecProposalBody;
}
impl SpecIsoProof for ProposalBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProposalBodyMapper {
    type Src = ProposalBodyInner<'a>;
    type Dst = ProposalBody<'a>;
    type RefSrc = ProposalBodyInnerRef<'a>;
}

type SpecProposalBodyCombinatorAlias1 = Choice<Cond<SpecProposalBodySpi4Combinator>, Cond<SpecProposalBodySpi8Combinator>>;
type SpecProposalBodyCombinatorAlias2 = Choice<Cond<SpecProposalBodySpi0Combinator>, SpecProposalBodyCombinatorAlias1>;
pub struct SpecProposalBodyCombinator(pub SpecProposalBodyCombinatorAlias);

impl SpecCombinator for SpecProposalBodyCombinator {
    type Type = SpecProposalBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalBodyCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecProposalBodyCombinatorAlias2, ProposalBodyMapper>>;
type ProposalBodyCombinatorAlias1 = Choice<Cond<ProposalBodySpi4Combinator>, Cond<ProposalBodySpi8Combinator>>;
type ProposalBodyCombinatorAlias2 = Choice<Cond<ProposalBodySpi0Combinator>, ProposalBodyCombinator1>;
pub struct ProposalBodyCombinator1(pub ProposalBodyCombinatorAlias1);
impl View for ProposalBodyCombinator1 {
    type V = SpecProposalBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ProposalBodyCombinator1, ProposalBodyCombinatorAlias1);

pub struct ProposalBodyCombinator2(pub ProposalBodyCombinatorAlias2);
impl View for ProposalBodyCombinator2 {
    type V = SpecProposalBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ProposalBodyCombinator2, ProposalBodyCombinatorAlias2);

pub struct ProposalBodyCombinator(pub ProposalBodyCombinatorAlias);

impl View for ProposalBodyCombinator {
    type V = SpecProposalBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecProposalBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalBodyCombinator {
    type Type = ProposalBody<'a>;
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
pub type ProposalBodyCombinatorAlias = AndThen<bytes::Variable, Mapped<ProposalBodyCombinator2, ProposalBodyMapper>>;


pub open spec fn spec_proposal_body(proposal_length: u16, num_transforms: u8, spi_size: SpecProposalSpiSizeByte) -> SpecProposalBodyCombinator {
    SpecProposalBodyCombinator(AndThen(bytes::Variable(((usize::spec_from(proposal_length) - 8)) as usize), Mapped { inner: Choice(Cond { cond: spi_size == 0, inner: spec_proposal_body_spi0(num_transforms) }, Choice(Cond { cond: spi_size == 4, inner: spec_proposal_body_spi4(num_transforms) }, Cond { cond: spi_size == 8, inner: spec_proposal_body_spi8(num_transforms) })), mapper: ProposalBodyMapper }))
}

pub fn proposal_body<'a>(proposal_length: u16, num_transforms: u8, spi_size: ProposalSpiSizeByte) -> (o: ProposalBodyCombinator)
    requires
        ((proposal_length) >= 8 && (proposal_length) <= 65535),
        ((num_transforms) >= 1 && (num_transforms) <= 255),
        spec_proposal_spi_size_byte().wf(spi_size@),

    ensures o@ == spec_proposal_body(proposal_length@, num_transforms@, spi_size@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalBodyCombinator(AndThen(bytes::Variable(((usize::ex_from(proposal_length) - 8)) as usize), Mapped { inner: ProposalBodyCombinator2(Choice::new(Cond { cond: spi_size == 0, inner: proposal_body_spi0(num_transforms) }, ProposalBodyCombinator1(Choice::new(Cond { cond: spi_size == 4, inner: proposal_body_spi4(num_transforms) }, Cond { cond: spi_size == 8, inner: proposal_body_spi8(num_transforms) })))), mapper: ProposalBodyMapper }));
    // assert({
    //     &&& combinator@ == spec_proposal_body(proposal_length@, num_transforms@, spi_size@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal_body<'a>(input: &'a [u8], proposal_length: u16, num_transforms: u8, spi_size: ProposalSpiSizeByte) -> (res: PResult<<ProposalBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((proposal_length) >= 8 && (proposal_length) <= 65535),
        ((num_transforms) >= 1 && (num_transforms) <= 255),
        spec_proposal_spi_size_byte().wf(spi_size@),

    ensures
        res matches Ok((n, v)) ==> spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_parse(input@) == Some((n as int, v@)),
        spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_parse(input@) is None,
        spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal_body( proposal_length, num_transforms, spi_size );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal_body<'a>(v: <ProposalBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, proposal_length: u16, num_transforms: u8, spi_size: ProposalSpiSizeByte) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal_body(proposal_length@, num_transforms@, spi_size@).wf(v@),
        ((proposal_length) >= 8 && (proposal_length) <= 65535),
        ((num_transforms) >= 1 && (num_transforms) <= 255),
        spec_proposal_spi_size_byte().wf(spi_size@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_serialize(v@))
        },
{
    let combinator = proposal_body( proposal_length, num_transforms, spi_size );
    combinator.serialize(v, data, pos)
}

pub fn proposal_body_len<'a>(v: <ProposalBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, proposal_length: u16, num_transforms: u8, spi_size: ProposalSpiSizeByte) -> (serialize_len: usize)
    requires
        spec_proposal_body(proposal_length@, num_transforms@, spi_size@).wf(v@),
        spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_serialize(v@).len() <= usize::MAX,
        ((proposal_length) >= 8 && (proposal_length) <= 65535),
        ((num_transforms) >= 1 && (num_transforms) <= 255),
        spec_proposal_spi_size_byte().wf(spi_size@),

    ensures
        serialize_len == spec_proposal_body(proposal_length@, num_transforms@, spi_size@).spec_serialize(v@).len(),
{
    let combinator = proposal_body( proposal_length, num_transforms, spi_size );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecProposal {
    pub last_or_more: u8,
    pub reserved: u8,
    pub proposal_length: u16,
    pub proposal_num: u8,
    pub protocol_id: u8,
    pub spi_size: SpecProposalSpiSizeByte,
    pub num_transforms: u8,
    pub body: SpecProposalBody,
}

pub type SpecProposalInner = (((((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte), u8), SpecProposalBody);


impl SpecFrom<SpecProposal> for SpecProposalInner {
    open spec fn spec_from(m: SpecProposal) -> SpecProposalInner {
        (((((m.last_or_more, (m.reserved, m.proposal_length)), (m.proposal_num, m.protocol_id)), m.spi_size), m.num_transforms), m.body)
    }
}

impl SpecFrom<SpecProposalInner> for SpecProposal {
    open spec fn spec_from(m: SpecProposalInner) -> SpecProposal {
        let (((((last_or_more, (reserved, proposal_length)), (proposal_num, protocol_id)), spi_size), num_transforms), body) = m;
        SpecProposal { last_or_more, reserved, proposal_length, proposal_num, protocol_id, spi_size, num_transforms, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Proposal<'a> {
    pub last_or_more: u8,
    pub reserved: u8,
    pub proposal_length: u16,
    pub proposal_num: u8,
    pub protocol_id: u8,
    pub spi_size: ProposalSpiSizeByte,
    pub num_transforms: u8,
    pub body: ProposalBody<'a>,
}

impl View for Proposal<'_> {
    type V = SpecProposal;

    open spec fn view(&self) -> Self::V {
        SpecProposal {
            last_or_more: self.last_or_more@,
            reserved: self.reserved@,
            proposal_length: self.proposal_length@,
            proposal_num: self.proposal_num@,
            protocol_id: self.protocol_id@,
            spi_size: self.spi_size@,
            num_transforms: self.num_transforms@,
            body: self.body@,
        }
    }
}
pub type ProposalInner<'a> = (((((u8, (u8, u16)), (u8, u8)), ProposalSpiSizeByte), u8), ProposalBody<'a>);

pub type ProposalInnerRef<'a> = (((((&'a u8, (&'a u8, &'a u16)), (&'a u8, &'a u8)), &'a ProposalSpiSizeByte), &'a u8), &'a ProposalBody<'a>);
impl<'a> From<&'a Proposal<'a>> for ProposalInnerRef<'a> {
    fn ex_from(m: &'a Proposal) -> ProposalInnerRef<'a> {
        (((((&m.last_or_more, (&m.reserved, &m.proposal_length)), (&m.proposal_num, &m.protocol_id)), &m.spi_size), &m.num_transforms), &m.body)
    }
}

impl<'a> From<ProposalInner<'a>> for Proposal<'a> {
    fn ex_from(m: ProposalInner) -> Proposal {
        let (((((last_or_more, (reserved, proposal_length)), (proposal_num, protocol_id)), spi_size), num_transforms), body) = m;
        Proposal { last_or_more, reserved, proposal_length, proposal_num, protocol_id, spi_size, num_transforms, body }
    }
}

pub struct ProposalMapper;
impl View for ProposalMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProposalMapper {
    type Src = SpecProposalInner;
    type Dst = SpecProposal;
}
impl SpecIsoProof for ProposalMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProposalMapper {
    type Src = ProposalInner<'a>;
    type Dst = Proposal<'a>;
    type RefSrc = ProposalInnerRef<'a>;
}
pub const PROPOSALRESERVED_CONST: u8 = 0;

pub struct SpecProposalCombinator(pub SpecProposalCombinatorAlias);

impl SpecCombinator for SpecProposalCombinator {
    type Type = SpecProposal;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProposalCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecProposalCombinatorAlias::is_prefix_secure() }
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
pub type SpecProposalCombinatorAlias = Mapped<SpecPair<SpecPair<SpecPair<SpecPair<(Refined<U8, Predicate7277979220772363767>, (Refined<U8, TagPred<u8>>, Refined<U16Be, Predicate18193225726552524852>)), (Refined<U8, Predicate2172399096230090262>, SpecIkeProtocolIdCombinator)>, SpecProposalSpiSizeByteCombinator>, Refined<U8, Predicate3651688686135228051>>, SpecProposalBodyCombinator>, ProposalMapper>;
pub struct Predicate7277979220772363767;
impl View for Predicate7277979220772363767 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7277979220772363767 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 2)
    }
}
impl SpecPred<u8> for Predicate7277979220772363767 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 2)
    }
}
pub struct Predicate2172399096230090262;
impl View for Predicate2172399096230090262 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2172399096230090262 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}
impl SpecPred<u8> for Predicate2172399096230090262 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1)
    }
}
pub struct Predicate3651688686135228051;
impl View for Predicate3651688686135228051 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3651688686135228051 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}
impl SpecPred<u8> for Predicate3651688686135228051 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}

pub struct ProposalCombinator(pub ProposalCombinatorAlias);

impl View for ProposalCombinator {
    type V = SpecProposalCombinator;
    open spec fn view(&self) -> Self::V { SpecProposalCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProposalCombinator {
    type Type = Proposal<'a>;
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
pub type ProposalCombinatorAlias = Mapped<Pair<Pair<Pair<Pair<(Refined<U8, Predicate7277979220772363767>, (Refined<U8, TagPred<u8>>, Refined<U16Be, Predicate18193225726552524852>)), (Refined<U8, Predicate2172399096230090262>, IkeProtocolIdCombinator), ProposalCont3>, ProposalSpiSizeByteCombinator, ProposalCont2>, Refined<U8, Predicate3651688686135228051>, ProposalCont1>, ProposalBodyCombinator, ProposalCont0>, ProposalMapper>;


pub open spec fn spec_proposal() -> SpecProposalCombinator {
    SpecProposalCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(Pair::spec_new(Pair::spec_new((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_proposal_cont3(deps)), |deps| spec_proposal_cont2(deps)), |deps| spec_proposal_cont1(deps)), |deps| spec_proposal_cont0(deps)),
        mapper: ProposalMapper,
    })
}

pub open spec fn spec_proposal_cont3(deps: (u8, (u8, u16))) -> (Refined<U8, Predicate2172399096230090262>, SpecIkeProtocolIdCombinator) {
    let (_, (_, proposal_length)) = deps;
    (Refined { inner: U8, predicate: Predicate2172399096230090262 }, spec_ike_protocol_id())
}

impl View for ProposalCont3 {
    type V = spec_fn((u8, (u8, u16))) -> (Refined<U8, Predicate2172399096230090262>, SpecIkeProtocolIdCombinator);

    open spec fn view(&self) -> Self::V {
        |deps: (u8, (u8, u16))| {
            spec_proposal_cont3(deps)
        }
    }
}

pub open spec fn spec_proposal_cont2(deps: ((u8, (u8, u16)), (u8, u8))) -> SpecProposalSpiSizeByteCombinator {
    let ((_, (_, proposal_length)), (_, protocol_id)) = deps;
    spec_proposal_spi_size_byte()
}

impl View for ProposalCont2 {
    type V = spec_fn(((u8, (u8, u16)), (u8, u8))) -> SpecProposalSpiSizeByteCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: ((u8, (u8, u16)), (u8, u8))| {
            spec_proposal_cont2(deps)
        }
    }
}

pub open spec fn spec_proposal_cont1(deps: (((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte)) -> Refined<U8, Predicate3651688686135228051> {
    let (((_, (_, proposal_length)), (_, protocol_id)), spi_size) = deps;
    Refined { inner: U8, predicate: Predicate3651688686135228051 }
}

impl View for ProposalCont1 {
    type V = spec_fn((((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte)) -> Refined<U8, Predicate3651688686135228051>;

    open spec fn view(&self) -> Self::V {
        |deps: (((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte)| {
            spec_proposal_cont1(deps)
        }
    }
}

pub open spec fn spec_proposal_cont0(deps: ((((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte), u8)) -> SpecProposalBodyCombinator {
    let ((((_, (_, proposal_length)), (_, protocol_id)), spi_size), num_transforms) = deps;
    spec_proposal_body(proposal_length, num_transforms, spi_size)
}

impl View for ProposalCont0 {
    type V = spec_fn(((((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte), u8)) -> SpecProposalBodyCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: ((((u8, (u8, u16)), (u8, u8)), SpecProposalSpiSizeByte), u8)| {
            spec_proposal_cont0(deps)
        }
    }
}

                
pub fn proposal<'a>() -> (o: ProposalCombinator)
    ensures o@ == spec_proposal(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ProposalCombinator(
    Mapped {
        inner: Pair::new(Pair::new(Pair::new(Pair::new((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), ProposalCont3), ProposalCont2), ProposalCont1), ProposalCont0),
        mapper: ProposalMapper,
    });
    // assert({
    //     &&& combinator@ == spec_proposal()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_proposal<'a>(input: &'a [u8]) -> (res: PResult<<ProposalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_proposal().spec_parse(input@) == Some((n as int, v@)),
        spec_proposal().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_proposal().spec_parse(input@) is None,
        spec_proposal().spec_parse(input@) is None ==> res is Err,
{
    let combinator = proposal();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_proposal<'a>(v: <ProposalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_proposal().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_proposal().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_proposal().spec_serialize(v@))
        },
{
    let combinator = proposal();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn proposal_len<'a>(v: <ProposalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_proposal().wf(v@),
        spec_proposal().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_proposal().spec_serialize(v@).len(),
{
    let combinator = proposal();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct ProposalCont3;
type ProposalCont3Type<'a, 'b> = &'b (u8, (u8, u16));
type ProposalCont3SType<'a, 'x> = (&'x u8, (&'x u8, &'x u16));
type ProposalCont3Input<'a, 'b, 'x> = POrSType<ProposalCont3Type<'a, 'b>, ProposalCont3SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ProposalCont3Input<'a, 'b, 'x>> for ProposalCont3 {
    type Output = (Refined<U8, Predicate2172399096230090262>, IkeProtocolIdCombinator);

    open spec fn requires(&self, deps: ProposalCont3Input<'a, 'b, 'x>) -> bool {
        &&& ((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 }))).wf(deps@)
        }

    open spec fn ensures(&self, deps: ProposalCont3Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_proposal_cont3(deps@)
    }

    fn apply(&self, deps: ProposalCont3Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, (_, proposal_length)) = deps;
                let proposal_length = *proposal_length;
                (Refined { inner: U8, predicate: Predicate2172399096230090262 }, ike_protocol_id())
            }
            POrSType::S(deps) => {
                let (_, (_, proposal_length)) = deps;
                let proposal_length = *proposal_length;
                (Refined { inner: U8, predicate: Predicate2172399096230090262 }, ike_protocol_id())
            }
        }
    }
}
pub struct ProposalCont2;
type ProposalCont2Type<'a, 'b> = &'b ((u8, (u8, u16)), (u8, u8));
type ProposalCont2SType<'a, 'x> = ((&'x u8, (&'x u8, &'x u16)), (&'x u8, &'x u8));
type ProposalCont2Input<'a, 'b, 'x> = POrSType<ProposalCont2Type<'a, 'b>, ProposalCont2SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ProposalCont2Input<'a, 'b, 'x>> for ProposalCont2 {
    type Output = ProposalSpiSizeByteCombinator;

    open spec fn requires(&self, deps: ProposalCont2Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_proposal_cont3(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: ProposalCont2Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_proposal_cont2(deps@)
    }

    fn apply(&self, deps: ProposalCont2Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((_, (_, proposal_length)), (_, protocol_id)) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                proposal_spi_size_byte()
            }
            POrSType::S(deps) => {
                let ((_, (_, proposal_length)), (_, protocol_id)) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                proposal_spi_size_byte()
            }
        }
    }
}
pub struct ProposalCont1;
type ProposalCont1Type<'a, 'b> = &'b (((u8, (u8, u16)), (u8, u8)), ProposalSpiSizeByte);
type ProposalCont1SType<'a, 'x> = (((&'x u8, (&'x u8, &'x u16)), (&'x u8, &'x u8)), &'x ProposalSpiSizeByte);
type ProposalCont1Input<'a, 'b, 'x> = POrSType<ProposalCont1Type<'a, 'b>, ProposalCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ProposalCont1Input<'a, 'b, 'x>> for ProposalCont1 {
    type Output = Refined<U8, Predicate3651688686135228051>;

    open spec fn requires(&self, deps: ProposalCont1Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(Pair::spec_new((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_proposal_cont3(deps)), |deps| spec_proposal_cont2(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: ProposalCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_proposal_cont1(deps@)
    }

    fn apply(&self, deps: ProposalCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (((_, (_, proposal_length)), (_, protocol_id)), spi_size) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                Refined { inner: U8, predicate: Predicate3651688686135228051 }
            }
            POrSType::S(deps) => {
                let (((_, (_, proposal_length)), (_, protocol_id)), spi_size) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                Refined { inner: U8, predicate: Predicate3651688686135228051 }
            }
        }
    }
}
pub struct ProposalCont0;
type ProposalCont0Type<'a, 'b> = &'b ((((u8, (u8, u16)), (u8, u8)), ProposalSpiSizeByte), u8);
type ProposalCont0SType<'a, 'x> = ((((&'x u8, (&'x u8, &'x u16)), (&'x u8, &'x u8)), &'x ProposalSpiSizeByte), &'x u8);
type ProposalCont0Input<'a, 'b, 'x> = POrSType<ProposalCont0Type<'a, 'b>, ProposalCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ProposalCont0Input<'a, 'b, 'x>> for ProposalCont0 {
    type Output = ProposalBodyCombinator;

    open spec fn requires(&self, deps: ProposalCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(Pair::spec_new(Pair::spec_new((Refined { inner: U8, predicate: Predicate7277979220772363767 }, (Refined { inner: U8, predicate: TagPred(PROPOSALRESERVED_CONST) }, Refined { inner: U16Be, predicate: Predicate18193225726552524852 })), |deps| spec_proposal_cont3(deps)), |deps| spec_proposal_cont2(deps)), |deps| spec_proposal_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: ProposalCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_proposal_cont0(deps@)
    }

    fn apply(&self, deps: ProposalCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((((_, (_, proposal_length)), (_, protocol_id)), spi_size), num_transforms) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                let num_transforms = *num_transforms;
                proposal_body(proposal_length, num_transforms, spi_size)
            }
            POrSType::S(deps) => {
                let ((((_, (_, proposal_length)), (_, protocol_id)), spi_size), num_transforms) = deps;
                let proposal_length = *proposal_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                let num_transforms = *num_transforms;
                proposal_body(proposal_length, num_transforms, spi_size)
            }
        }
    }
}
                

pub struct SpecSaPayloadBody {
    pub proposals: Seq<SpecProposal>,
}

pub type SpecSaPayloadBodyInner = Seq<SpecProposal>;


impl SpecFrom<SpecSaPayloadBody> for SpecSaPayloadBodyInner {
    open spec fn spec_from(m: SpecSaPayloadBody) -> SpecSaPayloadBodyInner {
        m.proposals
    }
}

impl SpecFrom<SpecSaPayloadBodyInner> for SpecSaPayloadBody {
    open spec fn spec_from(m: SpecSaPayloadBodyInner) -> SpecSaPayloadBody {
        let proposals = m;
        SpecSaPayloadBody { proposals }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SaPayloadBody<'a> {
    pub proposals: RepeatResult<Proposal<'a>>,
}

impl View for SaPayloadBody<'_> {
    type V = SpecSaPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecSaPayloadBody {
            proposals: self.proposals@,
        }
    }
}
pub type SaPayloadBodyInner<'a> = RepeatResult<Proposal<'a>>;

pub type SaPayloadBodyInnerRef<'a> = &'a RepeatResult<Proposal<'a>>;
impl<'a> From<&'a SaPayloadBody<'a>> for SaPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a SaPayloadBody) -> SaPayloadBodyInnerRef<'a> {
        &m.proposals
    }
}

impl<'a> From<SaPayloadBodyInner<'a>> for SaPayloadBody<'a> {
    fn ex_from(m: SaPayloadBodyInner) -> SaPayloadBody {
        let proposals = m;
        SaPayloadBody { proposals }
    }
}

pub struct SaPayloadBodyMapper;
impl View for SaPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SaPayloadBodyMapper {
    type Src = SpecSaPayloadBodyInner;
    type Dst = SpecSaPayloadBody;
}
impl SpecIsoProof for SaPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SaPayloadBodyMapper {
    type Src = SaPayloadBodyInner<'a>;
    type Dst = SaPayloadBody<'a>;
    type RefSrc = SaPayloadBodyInnerRef<'a>;
}

pub struct SpecSaPayloadBodyCombinator(pub SpecSaPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecSaPayloadBodyCombinator {
    type Type = SpecSaPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSaPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecSaPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecSaPayloadBodyCombinatorAlias = Mapped<AndThen<bytes::Variable, Repeat<SpecProposalCombinator>>, SaPayloadBodyMapper>;

pub struct SaPayloadBodyCombinator(pub SaPayloadBodyCombinatorAlias);

impl View for SaPayloadBodyCombinator {
    type V = SpecSaPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecSaPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SaPayloadBodyCombinator {
    type Type = SaPayloadBody<'a>;
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
pub type SaPayloadBodyCombinatorAlias = Mapped<AndThen<bytes::Variable, Repeat<ProposalCombinator>>, SaPayloadBodyMapper>;


pub open spec fn spec_sa_payload_body(payload_length: u16) -> SpecSaPayloadBodyCombinator {
    SpecSaPayloadBodyCombinator(
    Mapped {
        inner: AndThen(bytes::Variable(((usize::spec_from(payload_length) - 4)) as usize), Repeat(spec_proposal())),
        mapper: SaPayloadBodyMapper,
    })
}

pub fn sa_payload_body<'a>(payload_length: u16) -> (o: SaPayloadBodyCombinator)
    requires
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures o@ == spec_sa_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = SaPayloadBodyCombinator(
    Mapped {
        inner: AndThen(bytes::Variable(((usize::ex_from(payload_length) - 4)) as usize), Repeat::new(proposal())),
        mapper: SaPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_sa_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_sa_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<SaPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_sa_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_sa_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_sa_payload_body(payload_length@).spec_parse(input@) is None,
        spec_sa_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = sa_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_sa_payload_body<'a>(v: <SaPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_sa_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_sa_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_sa_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = sa_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn sa_payload_body_len<'a>(v: <SaPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_sa_payload_body(payload_length@).wf(v@),
        spec_sa_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_sa_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = sa_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecTsIpv6 {
    pub ts_type: u8,
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: Seq<u8>,
    pub end_address: Seq<u8>,
}

pub type SpecTsIpv6Inner = (u8, (u8, (u16, (u16, (u16, (Seq<u8>, Seq<u8>))))));


impl SpecFrom<SpecTsIpv6> for SpecTsIpv6Inner {
    open spec fn spec_from(m: SpecTsIpv6) -> SpecTsIpv6Inner {
        (m.ts_type, (m.ip_protocol_id, (m.selector_length, (m.start_port, (m.end_port, (m.start_address, m.end_address))))))
    }
}

impl SpecFrom<SpecTsIpv6Inner> for SpecTsIpv6 {
    open spec fn spec_from(m: SpecTsIpv6Inner) -> SpecTsIpv6 {
        let (ts_type, (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address)))))) = m;
        SpecTsIpv6 { ts_type, ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsIpv6<'a> {
    pub ts_type: u8,
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: &'a [u8],
    pub end_address: &'a [u8],
}

impl View for TsIpv6<'_> {
    type V = SpecTsIpv6;

    open spec fn view(&self) -> Self::V {
        SpecTsIpv6 {
            ts_type: self.ts_type@,
            ip_protocol_id: self.ip_protocol_id@,
            selector_length: self.selector_length@,
            start_port: self.start_port@,
            end_port: self.end_port@,
            start_address: self.start_address@,
            end_address: self.end_address@,
        }
    }
}
pub type TsIpv6Inner<'a> = (u8, (u8, (u16, (u16, (u16, (&'a [u8], &'a [u8]))))));

pub type TsIpv6InnerRef<'a> = (&'a u8, (&'a u8, (&'a u16, (&'a u16, (&'a u16, (&'a &'a [u8], &'a &'a [u8]))))));
impl<'a> From<&'a TsIpv6<'a>> for TsIpv6InnerRef<'a> {
    fn ex_from(m: &'a TsIpv6) -> TsIpv6InnerRef<'a> {
        (&m.ts_type, (&m.ip_protocol_id, (&m.selector_length, (&m.start_port, (&m.end_port, (&m.start_address, &m.end_address))))))
    }
}

impl<'a> From<TsIpv6Inner<'a>> for TsIpv6<'a> {
    fn ex_from(m: TsIpv6Inner) -> TsIpv6 {
        let (ts_type, (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address)))))) = m;
        TsIpv6 { ts_type, ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}

pub struct TsIpv6Mapper;
impl View for TsIpv6Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsIpv6Mapper {
    type Src = SpecTsIpv6Inner;
    type Dst = SpecTsIpv6;
}
impl SpecIsoProof for TsIpv6Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsIpv6Mapper {
    type Src = TsIpv6Inner<'a>;
    type Dst = TsIpv6<'a>;
    type RefSrc = TsIpv6InnerRef<'a>;
}
pub const TSIPV6TS_TYPE_CONST: u8 = 8;
pub const TSIPV6SELECTOR_LENGTH_CONST: u16 = 40;
type SpecTsIpv6CombinatorAlias1 = (bytes::Fixed<16>, bytes::Fixed<16>);
type SpecTsIpv6CombinatorAlias2 = (U16Be, SpecTsIpv6CombinatorAlias1);
type SpecTsIpv6CombinatorAlias3 = (U16Be, SpecTsIpv6CombinatorAlias2);
type SpecTsIpv6CombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, SpecTsIpv6CombinatorAlias3);
type SpecTsIpv6CombinatorAlias5 = (U8, SpecTsIpv6CombinatorAlias4);
type SpecTsIpv6CombinatorAlias6 = (Refined<U8, TagPred<u8>>, SpecTsIpv6CombinatorAlias5);
pub struct SpecTsIpv6Combinator(pub SpecTsIpv6CombinatorAlias);

impl SpecCombinator for SpecTsIpv6Combinator {
    type Type = SpecTsIpv6;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsIpv6Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsIpv6CombinatorAlias::is_prefix_secure() }
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
pub type SpecTsIpv6CombinatorAlias = Mapped<SpecTsIpv6CombinatorAlias6, TsIpv6Mapper>;
type TsIpv6CombinatorAlias1 = (bytes::Fixed<16>, bytes::Fixed<16>);
type TsIpv6CombinatorAlias2 = (U16Be, TsIpv6Combinator1);
type TsIpv6CombinatorAlias3 = (U16Be, TsIpv6Combinator2);
type TsIpv6CombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, TsIpv6Combinator3);
type TsIpv6CombinatorAlias5 = (U8, TsIpv6Combinator4);
type TsIpv6CombinatorAlias6 = (Refined<U8, TagPred<u8>>, TsIpv6Combinator5);
pub struct TsIpv6Combinator1(pub TsIpv6CombinatorAlias1);
impl View for TsIpv6Combinator1 {
    type V = SpecTsIpv6CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator1, TsIpv6CombinatorAlias1);

pub struct TsIpv6Combinator2(pub TsIpv6CombinatorAlias2);
impl View for TsIpv6Combinator2 {
    type V = SpecTsIpv6CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator2, TsIpv6CombinatorAlias2);

pub struct TsIpv6Combinator3(pub TsIpv6CombinatorAlias3);
impl View for TsIpv6Combinator3 {
    type V = SpecTsIpv6CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator3, TsIpv6CombinatorAlias3);

pub struct TsIpv6Combinator4(pub TsIpv6CombinatorAlias4);
impl View for TsIpv6Combinator4 {
    type V = SpecTsIpv6CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator4, TsIpv6CombinatorAlias4);

pub struct TsIpv6Combinator5(pub TsIpv6CombinatorAlias5);
impl View for TsIpv6Combinator5 {
    type V = SpecTsIpv6CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator5, TsIpv6CombinatorAlias5);

pub struct TsIpv6Combinator6(pub TsIpv6CombinatorAlias6);
impl View for TsIpv6Combinator6 {
    type V = SpecTsIpv6CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6Combinator6, TsIpv6CombinatorAlias6);

pub struct TsIpv6Combinator(pub TsIpv6CombinatorAlias);

impl View for TsIpv6Combinator {
    type V = SpecTsIpv6Combinator;
    open spec fn view(&self) -> Self::V { SpecTsIpv6Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsIpv6Combinator {
    type Type = TsIpv6<'a>;
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
pub type TsIpv6CombinatorAlias = Mapped<TsIpv6Combinator6, TsIpv6Mapper>;


pub open spec fn spec_ts_ipv6() -> SpecTsIpv6Combinator {
    SpecTsIpv6Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(TSIPV6TS_TYPE_CONST) }, (U8, (Refined { inner: U16Be, predicate: TagPred(TSIPV6SELECTOR_LENGTH_CONST) }, (U16Be, (U16Be, (bytes::Fixed::<16>, bytes::Fixed::<16>)))))),
        mapper: TsIpv6Mapper,
    })
}

                
pub fn ts_ipv6<'a>() -> (o: TsIpv6Combinator)
    ensures o@ == spec_ts_ipv6(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsIpv6Combinator(
    Mapped {
        inner: TsIpv6Combinator6((Refined { inner: U8, predicate: TagPred(TSIPV6TS_TYPE_CONST) }, TsIpv6Combinator5((U8, TsIpv6Combinator4((Refined { inner: U16Be, predicate: TagPred(TSIPV6SELECTOR_LENGTH_CONST) }, TsIpv6Combinator3((U16Be, TsIpv6Combinator2((U16Be, TsIpv6Combinator1((bytes::Fixed::<16>, bytes::Fixed::<16>)))))))))))),
        mapper: TsIpv6Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_ipv6()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_ipv6<'a>(input: &'a [u8]) -> (res: PResult<<TsIpv6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_ipv6().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_ipv6().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_ipv6().spec_parse(input@) is None,
        spec_ts_ipv6().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_ipv6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_ipv6<'a>(v: <TsIpv6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_ipv6().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_ipv6().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_ipv6().spec_serialize(v@))
        },
{
    let combinator = ts_ipv6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_ipv6_len<'a>(v: <TsIpv6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_ipv6().wf(v@),
        spec_ts_ipv6().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_ipv6().spec_serialize(v@).len(),
{
    let combinator = ts_ipv6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2SaPayloadInner {
    pub proposals: Seq<SpecProposal>,
}

pub type SpecIkev2SaPayloadInnerInner = Seq<SpecProposal>;


impl SpecFrom<SpecIkev2SaPayloadInner> for SpecIkev2SaPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2SaPayloadInner) -> SpecIkev2SaPayloadInnerInner {
        m.proposals
    }
}

impl SpecFrom<SpecIkev2SaPayloadInnerInner> for SpecIkev2SaPayloadInner {
    open spec fn spec_from(m: SpecIkev2SaPayloadInnerInner) -> SpecIkev2SaPayloadInner {
        let proposals = m;
        SpecIkev2SaPayloadInner { proposals }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2SaPayloadInner<'a> {
    pub proposals: RepeatResult<Proposal<'a>>,
}

impl View for Ikev2SaPayloadInner<'_> {
    type V = SpecIkev2SaPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2SaPayloadInner {
            proposals: self.proposals@,
        }
    }
}
pub type Ikev2SaPayloadInnerInner<'a> = RepeatResult<Proposal<'a>>;

pub type Ikev2SaPayloadInnerInnerRef<'a> = &'a RepeatResult<Proposal<'a>>;
impl<'a> From<&'a Ikev2SaPayloadInner<'a>> for Ikev2SaPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2SaPayloadInner) -> Ikev2SaPayloadInnerInnerRef<'a> {
        &m.proposals
    }
}

impl<'a> From<Ikev2SaPayloadInnerInner<'a>> for Ikev2SaPayloadInner<'a> {
    fn ex_from(m: Ikev2SaPayloadInnerInner) -> Ikev2SaPayloadInner {
        let proposals = m;
        Ikev2SaPayloadInner { proposals }
    }
}

pub struct Ikev2SaPayloadInnerMapper;
impl View for Ikev2SaPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2SaPayloadInnerMapper {
    type Src = SpecIkev2SaPayloadInnerInner;
    type Dst = SpecIkev2SaPayloadInner;
}
impl SpecIsoProof for Ikev2SaPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2SaPayloadInnerMapper {
    type Src = Ikev2SaPayloadInnerInner<'a>;
    type Dst = Ikev2SaPayloadInner<'a>;
    type RefSrc = Ikev2SaPayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2SaPayloadInnerCombinator(pub SpecIkev2SaPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2SaPayloadInnerCombinator {
    type Type = SpecIkev2SaPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2SaPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2SaPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2SaPayloadInnerCombinatorAlias = Mapped<AndThen<bytes::Tail, Repeat<SpecProposalCombinator>>, Ikev2SaPayloadInnerMapper>;

pub struct Ikev2SaPayloadInnerCombinator(pub Ikev2SaPayloadInnerCombinatorAlias);

impl View for Ikev2SaPayloadInnerCombinator {
    type V = SpecIkev2SaPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2SaPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2SaPayloadInnerCombinator {
    type Type = Ikev2SaPayloadInner<'a>;
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
pub type Ikev2SaPayloadInnerCombinatorAlias = Mapped<AndThen<bytes::Tail, Repeat<ProposalCombinator>>, Ikev2SaPayloadInnerMapper>;


pub open spec fn spec_ikev2_sa_payload_inner() -> SpecIkev2SaPayloadInnerCombinator {
    SpecIkev2SaPayloadInnerCombinator(
    Mapped {
        inner: AndThen(bytes::Tail, Repeat(spec_proposal())),
        mapper: Ikev2SaPayloadInnerMapper,
    })
}

                
pub fn ikev2_sa_payload_inner<'a>() -> (o: Ikev2SaPayloadInnerCombinator)
    ensures o@ == spec_ikev2_sa_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2SaPayloadInnerCombinator(
    Mapped {
        inner: AndThen(bytes::Tail, Repeat::new(proposal())),
        mapper: Ikev2SaPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_sa_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_sa_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2SaPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_sa_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_sa_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_sa_payload_inner().spec_parse(input@) is None,
        spec_ikev2_sa_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_sa_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_sa_payload_inner<'a>(v: <Ikev2SaPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_sa_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_sa_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_sa_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_sa_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_sa_payload_inner_len<'a>(v: <Ikev2SaPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_sa_payload_inner().wf(v@),
        spec_ikev2_sa_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_sa_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_sa_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecNoncePayloadBody {
    pub nonce_data: Seq<u8>,
}

pub type SpecNoncePayloadBodyInner = Seq<u8>;


impl SpecFrom<SpecNoncePayloadBody> for SpecNoncePayloadBodyInner {
    open spec fn spec_from(m: SpecNoncePayloadBody) -> SpecNoncePayloadBodyInner {
        m.nonce_data
    }
}

impl SpecFrom<SpecNoncePayloadBodyInner> for SpecNoncePayloadBody {
    open spec fn spec_from(m: SpecNoncePayloadBodyInner) -> SpecNoncePayloadBody {
        let nonce_data = m;
        SpecNoncePayloadBody { nonce_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NoncePayloadBody<'a> {
    pub nonce_data: &'a [u8],
}

impl View for NoncePayloadBody<'_> {
    type V = SpecNoncePayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecNoncePayloadBody {
            nonce_data: self.nonce_data@,
        }
    }
}
pub type NoncePayloadBodyInner<'a> = &'a [u8];

pub type NoncePayloadBodyInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a NoncePayloadBody<'a>> for NoncePayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a NoncePayloadBody) -> NoncePayloadBodyInnerRef<'a> {
        &m.nonce_data
    }
}

impl<'a> From<NoncePayloadBodyInner<'a>> for NoncePayloadBody<'a> {
    fn ex_from(m: NoncePayloadBodyInner) -> NoncePayloadBody {
        let nonce_data = m;
        NoncePayloadBody { nonce_data }
    }
}

pub struct NoncePayloadBodyMapper;
impl View for NoncePayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NoncePayloadBodyMapper {
    type Src = SpecNoncePayloadBodyInner;
    type Dst = SpecNoncePayloadBody;
}
impl SpecIsoProof for NoncePayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NoncePayloadBodyMapper {
    type Src = NoncePayloadBodyInner<'a>;
    type Dst = NoncePayloadBody<'a>;
    type RefSrc = NoncePayloadBodyInnerRef<'a>;
}

pub struct SpecNoncePayloadBodyCombinator(pub SpecNoncePayloadBodyCombinatorAlias);

impl SpecCombinator for SpecNoncePayloadBodyCombinator {
    type Type = SpecNoncePayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNoncePayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNoncePayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecNoncePayloadBodyCombinatorAlias = Mapped<bytes::Variable, NoncePayloadBodyMapper>;

pub struct NoncePayloadBodyCombinator(pub NoncePayloadBodyCombinatorAlias);

impl View for NoncePayloadBodyCombinator {
    type V = SpecNoncePayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecNoncePayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NoncePayloadBodyCombinator {
    type Type = NoncePayloadBody<'a>;
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
pub type NoncePayloadBodyCombinatorAlias = Mapped<bytes::Variable, NoncePayloadBodyMapper>;


pub open spec fn spec_nonce_payload_body(payload_length: u16) -> SpecNoncePayloadBodyCombinator {
    SpecNoncePayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(payload_length) - 4)) as usize),
        mapper: NoncePayloadBodyMapper,
    })
}

pub fn nonce_payload_body<'a>(payload_length: u16) -> (o: NoncePayloadBodyCombinator)
    requires
        ((payload_length) >= 20 && (payload_length) <= 260),

    ensures o@ == spec_nonce_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NoncePayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(payload_length) - 4)) as usize),
        mapper: NoncePayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_nonce_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nonce_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<NoncePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 20 && (payload_length) <= 260),

    ensures
        res matches Ok((n, v)) ==> spec_nonce_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_nonce_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nonce_payload_body(payload_length@).spec_parse(input@) is None,
        spec_nonce_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nonce_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nonce_payload_body<'a>(v: <NoncePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nonce_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 20 && (payload_length) <= 260),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nonce_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nonce_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = nonce_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn nonce_payload_body_len<'a>(v: <NoncePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_nonce_payload_body(payload_length@).wf(v@),
        spec_nonce_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 20 && (payload_length) <= 260),

    ensures
        serialize_len == spec_nonce_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = nonce_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub mod IdType {
    use super::*;
    pub spec const SPEC_ID_IPV4_ADDR: u8 = 1;
    pub spec const SPEC_ID_FQDN: u8 = 2;
    pub spec const SPEC_ID_RFC822_ADDR: u8 = 3;
    pub spec const SPEC_ID_IPV6_ADDR: u8 = 5;
    pub spec const SPEC_ID_DER_ASN1_DN: u8 = 9;
    pub spec const SPEC_ID_DER_ASN1_GN: u8 = 10;
    pub spec const SPEC_ID_KEY_ID: u8 = 11;
    pub exec const ID_IPV4_ADDR: u8 ensures ID_IPV4_ADDR == SPEC_ID_IPV4_ADDR { 1 }
    pub exec const ID_FQDN: u8 ensures ID_FQDN == SPEC_ID_FQDN { 2 }
    pub exec const ID_RFC822_ADDR: u8 ensures ID_RFC822_ADDR == SPEC_ID_RFC822_ADDR { 3 }
    pub exec const ID_IPV6_ADDR: u8 ensures ID_IPV6_ADDR == SPEC_ID_IPV6_ADDR { 5 }
    pub exec const ID_DER_ASN1_DN: u8 ensures ID_DER_ASN1_DN == SPEC_ID_DER_ASN1_DN { 9 }
    pub exec const ID_DER_ASN1_GN: u8 ensures ID_DER_ASN1_GN == SPEC_ID_DER_ASN1_GN { 10 }
    pub exec const ID_KEY_ID: u8 ensures ID_KEY_ID == SPEC_ID_KEY_ID { 11 }
}


pub struct SpecIdTypeCombinator(pub SpecIdTypeCombinatorAlias);

impl SpecCombinator for SpecIdTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIdTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIdTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecIdTypeCombinatorAlias = U8;

pub struct IdTypeCombinator(pub IdTypeCombinatorAlias);

impl View for IdTypeCombinator {
    type V = SpecIdTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecIdTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IdTypeCombinator {
    type Type = u8;
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
pub type IdTypeCombinatorAlias = U8;


pub open spec fn spec_id_type() -> SpecIdTypeCombinator {
    SpecIdTypeCombinator(U8)
}

                
pub fn id_type<'a>() -> (o: IdTypeCombinator)
    ensures o@ == spec_id_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IdTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_id_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_id_type<'a>(input: &'a [u8]) -> (res: PResult<<IdTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_id_type().spec_parse(input@) == Some((n as int, v@)),
        spec_id_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_id_type().spec_parse(input@) is None,
        spec_id_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = id_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_id_type<'a>(v: <IdTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_id_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_id_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_id_type().spec_serialize(v@))
        },
{
    let combinator = id_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn id_type_len<'a>(v: <IdTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_id_type().wf(v@),
        spec_id_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_id_type().spec_serialize(v@).len(),
{
    let combinator = id_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2IdPayloadInner {
    pub id_type: u8,
    pub reserved: Seq<u8>,
    pub id_data: Seq<u8>,
}

pub type SpecIkev2IdPayloadInnerInner = (u8, (Seq<u8>, Seq<u8>));


impl SpecFrom<SpecIkev2IdPayloadInner> for SpecIkev2IdPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2IdPayloadInner) -> SpecIkev2IdPayloadInnerInner {
        (m.id_type, (m.reserved, m.id_data))
    }
}

impl SpecFrom<SpecIkev2IdPayloadInnerInner> for SpecIkev2IdPayloadInner {
    open spec fn spec_from(m: SpecIkev2IdPayloadInnerInner) -> SpecIkev2IdPayloadInner {
        let (id_type, (reserved, id_data)) = m;
        SpecIkev2IdPayloadInner { id_type, reserved, id_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2IdPayloadInner<'a> {
    pub id_type: u8,
    pub reserved: &'a [u8],
    pub id_data: &'a [u8],
}

impl View for Ikev2IdPayloadInner<'_> {
    type V = SpecIkev2IdPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2IdPayloadInner {
            id_type: self.id_type@,
            reserved: self.reserved@,
            id_data: self.id_data@,
        }
    }
}
pub type Ikev2IdPayloadInnerInner<'a> = (u8, (&'a [u8], &'a [u8]));

pub type Ikev2IdPayloadInnerInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a &'a [u8]));
impl<'a> From<&'a Ikev2IdPayloadInner<'a>> for Ikev2IdPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2IdPayloadInner) -> Ikev2IdPayloadInnerInnerRef<'a> {
        (&m.id_type, (&m.reserved, &m.id_data))
    }
}

impl<'a> From<Ikev2IdPayloadInnerInner<'a>> for Ikev2IdPayloadInner<'a> {
    fn ex_from(m: Ikev2IdPayloadInnerInner) -> Ikev2IdPayloadInner {
        let (id_type, (reserved, id_data)) = m;
        Ikev2IdPayloadInner { id_type, reserved, id_data }
    }
}

pub struct Ikev2IdPayloadInnerMapper;
impl View for Ikev2IdPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2IdPayloadInnerMapper {
    type Src = SpecIkev2IdPayloadInnerInner;
    type Dst = SpecIkev2IdPayloadInner;
}
impl SpecIsoProof for Ikev2IdPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2IdPayloadInnerMapper {
    type Src = Ikev2IdPayloadInnerInner<'a>;
    type Dst = Ikev2IdPayloadInner<'a>;
    type RefSrc = Ikev2IdPayloadInnerInnerRef<'a>;
}
pub spec const SPEC_IKEV2IDPAYLOADINNERRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecIkev2IdPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, bytes::Tail);
type SpecIkev2IdPayloadInnerCombinatorAlias2 = (SpecIdTypeCombinator, SpecIkev2IdPayloadInnerCombinatorAlias1);
pub struct SpecIkev2IdPayloadInnerCombinator(pub SpecIkev2IdPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2IdPayloadInnerCombinator {
    type Type = SpecIkev2IdPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2IdPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2IdPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2IdPayloadInnerCombinatorAlias = Mapped<SpecIkev2IdPayloadInnerCombinatorAlias2, Ikev2IdPayloadInnerMapper>;
pub exec static IKEV2IDPAYLOADINNERRESERVED_CONST: [u8; 3]
    ensures IKEV2IDPAYLOADINNERRESERVED_CONST@ == SPEC_IKEV2IDPAYLOADINNERRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_IKEV2IDPAYLOADINNERRESERVED_CONST);
    arr
}
type Ikev2IdPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, bytes::Tail);
type Ikev2IdPayloadInnerCombinatorAlias2 = (IdTypeCombinator, Ikev2IdPayloadInnerCombinator1);
pub struct Ikev2IdPayloadInnerCombinator1(pub Ikev2IdPayloadInnerCombinatorAlias1);
impl View for Ikev2IdPayloadInnerCombinator1 {
    type V = SpecIkev2IdPayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2IdPayloadInnerCombinator1, Ikev2IdPayloadInnerCombinatorAlias1);

pub struct Ikev2IdPayloadInnerCombinator2(pub Ikev2IdPayloadInnerCombinatorAlias2);
impl View for Ikev2IdPayloadInnerCombinator2 {
    type V = SpecIkev2IdPayloadInnerCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2IdPayloadInnerCombinator2, Ikev2IdPayloadInnerCombinatorAlias2);

pub struct Ikev2IdPayloadInnerCombinator(pub Ikev2IdPayloadInnerCombinatorAlias);

impl View for Ikev2IdPayloadInnerCombinator {
    type V = SpecIkev2IdPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2IdPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2IdPayloadInnerCombinator {
    type Type = Ikev2IdPayloadInner<'a>;
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
pub type Ikev2IdPayloadInnerCombinatorAlias = Mapped<Ikev2IdPayloadInnerCombinator2, Ikev2IdPayloadInnerMapper>;


pub open spec fn spec_ikev2_id_payload_inner() -> SpecIkev2IdPayloadInnerCombinator {
    SpecIkev2IdPayloadInnerCombinator(
    Mapped {
        inner: (spec_id_type(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_IKEV2IDPAYLOADINNERRESERVED_CONST) }, bytes::Tail)),
        mapper: Ikev2IdPayloadInnerMapper,
    })
}

                
pub fn ikev2_id_payload_inner<'a>() -> (o: Ikev2IdPayloadInnerCombinator)
    ensures o@ == spec_ikev2_id_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2IdPayloadInnerCombinator(
    Mapped {
        inner: Ikev2IdPayloadInnerCombinator2((id_type(), Ikev2IdPayloadInnerCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IKEV2IDPAYLOADINNERRESERVED_CONST) }, bytes::Tail)))),
        mapper: Ikev2IdPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_id_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_id_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2IdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_id_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_id_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_id_payload_inner().spec_parse(input@) is None,
        spec_ikev2_id_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_id_payload_inner<'a>(v: <Ikev2IdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_id_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_id_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_id_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_id_payload_inner_len<'a>(v: <Ikev2IdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_id_payload_inner().wf(v@),
        spec_ikev2_id_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_id_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecNotifyPayloadBodySpi0 {
    pub spi: Seq<u8>,
    pub notification_data: Seq<u8>,
}

pub type SpecNotifyPayloadBodySpi0Inner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecNotifyPayloadBodySpi0> for SpecNotifyPayloadBodySpi0Inner {
    open spec fn spec_from(m: SpecNotifyPayloadBodySpi0) -> SpecNotifyPayloadBodySpi0Inner {
        (m.spi, m.notification_data)
    }
}

impl SpecFrom<SpecNotifyPayloadBodySpi0Inner> for SpecNotifyPayloadBodySpi0 {
    open spec fn spec_from(m: SpecNotifyPayloadBodySpi0Inner) -> SpecNotifyPayloadBodySpi0 {
        let (spi, notification_data) = m;
        SpecNotifyPayloadBodySpi0 { spi, notification_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NotifyPayloadBodySpi0<'a> {
    pub spi: &'a [u8],
    pub notification_data: &'a [u8],
}

impl View for NotifyPayloadBodySpi0<'_> {
    type V = SpecNotifyPayloadBodySpi0;

    open spec fn view(&self) -> Self::V {
        SpecNotifyPayloadBodySpi0 {
            spi: self.spi@,
            notification_data: self.notification_data@,
        }
    }
}
pub type NotifyPayloadBodySpi0Inner<'a> = (&'a [u8], &'a [u8]);

pub type NotifyPayloadBodySpi0InnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a NotifyPayloadBodySpi0<'a>> for NotifyPayloadBodySpi0InnerRef<'a> {
    fn ex_from(m: &'a NotifyPayloadBodySpi0) -> NotifyPayloadBodySpi0InnerRef<'a> {
        (&m.spi, &m.notification_data)
    }
}

impl<'a> From<NotifyPayloadBodySpi0Inner<'a>> for NotifyPayloadBodySpi0<'a> {
    fn ex_from(m: NotifyPayloadBodySpi0Inner) -> NotifyPayloadBodySpi0 {
        let (spi, notification_data) = m;
        NotifyPayloadBodySpi0 { spi, notification_data }
    }
}

pub struct NotifyPayloadBodySpi0Mapper;
impl View for NotifyPayloadBodySpi0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NotifyPayloadBodySpi0Mapper {
    type Src = SpecNotifyPayloadBodySpi0Inner;
    type Dst = SpecNotifyPayloadBodySpi0;
}
impl SpecIsoProof for NotifyPayloadBodySpi0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NotifyPayloadBodySpi0Mapper {
    type Src = NotifyPayloadBodySpi0Inner<'a>;
    type Dst = NotifyPayloadBodySpi0<'a>;
    type RefSrc = NotifyPayloadBodySpi0InnerRef<'a>;
}
type SpecNotifyPayloadBodySpi0CombinatorAlias1 = (bytes::Fixed<0>, bytes::Tail);
pub struct SpecNotifyPayloadBodySpi0Combinator(pub SpecNotifyPayloadBodySpi0CombinatorAlias);

impl SpecCombinator for SpecNotifyPayloadBodySpi0Combinator {
    type Type = SpecNotifyPayloadBodySpi0;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyPayloadBodySpi0Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyPayloadBodySpi0CombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyPayloadBodySpi0CombinatorAlias = Mapped<SpecNotifyPayloadBodySpi0CombinatorAlias1, NotifyPayloadBodySpi0Mapper>;
type NotifyPayloadBodySpi0CombinatorAlias1 = (bytes::Fixed<0>, bytes::Tail);
pub struct NotifyPayloadBodySpi0Combinator1(pub NotifyPayloadBodySpi0CombinatorAlias1);
impl View for NotifyPayloadBodySpi0Combinator1 {
    type V = SpecNotifyPayloadBodySpi0CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NotifyPayloadBodySpi0Combinator1, NotifyPayloadBodySpi0CombinatorAlias1);

pub struct NotifyPayloadBodySpi0Combinator(pub NotifyPayloadBodySpi0CombinatorAlias);

impl View for NotifyPayloadBodySpi0Combinator {
    type V = SpecNotifyPayloadBodySpi0Combinator;
    open spec fn view(&self) -> Self::V { SpecNotifyPayloadBodySpi0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyPayloadBodySpi0Combinator {
    type Type = NotifyPayloadBodySpi0<'a>;
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
pub type NotifyPayloadBodySpi0CombinatorAlias = Mapped<NotifyPayloadBodySpi0Combinator1, NotifyPayloadBodySpi0Mapper>;


pub open spec fn spec_notify_payload_body_spi0() -> SpecNotifyPayloadBodySpi0Combinator {
    SpecNotifyPayloadBodySpi0Combinator(
    Mapped {
        inner: (bytes::Fixed::<0>, bytes::Tail),
        mapper: NotifyPayloadBodySpi0Mapper,
    })
}

                
pub fn notify_payload_body_spi0<'a>() -> (o: NotifyPayloadBodySpi0Combinator)
    ensures o@ == spec_notify_payload_body_spi0(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyPayloadBodySpi0Combinator(
    Mapped {
        inner: NotifyPayloadBodySpi0Combinator1((bytes::Fixed::<0>, bytes::Tail)),
        mapper: NotifyPayloadBodySpi0Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_notify_payload_body_spi0()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_payload_body_spi0<'a>(input: &'a [u8]) -> (res: PResult<<NotifyPayloadBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_notify_payload_body_spi0().spec_parse(input@) == Some((n as int, v@)),
        spec_notify_payload_body_spi0().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_payload_body_spi0().spec_parse(input@) is None,
        spec_notify_payload_body_spi0().spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_payload_body_spi0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_payload_body_spi0<'a>(v: <NotifyPayloadBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_payload_body_spi0().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_payload_body_spi0().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_payload_body_spi0().spec_serialize(v@))
        },
{
    let combinator = notify_payload_body_spi0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn notify_payload_body_spi0_len<'a>(v: <NotifyPayloadBodySpi0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_notify_payload_body_spi0().wf(v@),
        spec_notify_payload_body_spi0().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_notify_payload_body_spi0().spec_serialize(v@).len(),
{
    let combinator = notify_payload_body_spi0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecCfgAttrTypeWord = u16;
pub type CfgAttrTypeWord = u16;
pub type CfgAttrTypeWordRef<'a> = &'a u16;


pub struct SpecCfgAttrTypeWordCombinator(pub SpecCfgAttrTypeWordCombinatorAlias);

impl SpecCombinator for SpecCfgAttrTypeWordCombinator {
    type Type = SpecCfgAttrTypeWord;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCfgAttrTypeWordCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCfgAttrTypeWordCombinatorAlias::is_prefix_secure() }
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
pub type SpecCfgAttrTypeWordCombinatorAlias = Refined<U16Be, Predicate5630542192344936318>;

pub struct CfgAttrTypeWordCombinator(pub CfgAttrTypeWordCombinatorAlias);

impl View for CfgAttrTypeWordCombinator {
    type V = SpecCfgAttrTypeWordCombinator;
    open spec fn view(&self) -> Self::V { SpecCfgAttrTypeWordCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CfgAttrTypeWordCombinator {
    type Type = CfgAttrTypeWord;
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
pub type CfgAttrTypeWordCombinatorAlias = Refined<U16Be, Predicate5630542192344936318>;


pub open spec fn spec_cfg_attr_type_word() -> SpecCfgAttrTypeWordCombinator {
    SpecCfgAttrTypeWordCombinator(Refined { inner: U16Be, predicate: Predicate5630542192344936318 })
}

                
pub fn cfg_attr_type_word<'a>() -> (o: CfgAttrTypeWordCombinator)
    ensures o@ == spec_cfg_attr_type_word(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CfgAttrTypeWordCombinator(Refined { inner: U16Be, predicate: Predicate5630542192344936318 });
    // assert({
    //     &&& combinator@ == spec_cfg_attr_type_word()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cfg_attr_type_word<'a>(input: &'a [u8]) -> (res: PResult<<CfgAttrTypeWordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_cfg_attr_type_word().spec_parse(input@) == Some((n as int, v@)),
        spec_cfg_attr_type_word().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cfg_attr_type_word().spec_parse(input@) is None,
        spec_cfg_attr_type_word().spec_parse(input@) is None ==> res is Err,
{
    let combinator = cfg_attr_type_word();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cfg_attr_type_word<'a>(v: <CfgAttrTypeWordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cfg_attr_type_word().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cfg_attr_type_word().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cfg_attr_type_word().spec_serialize(v@))
        },
{
    let combinator = cfg_attr_type_word();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn cfg_attr_type_word_len<'a>(v: <CfgAttrTypeWordCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_cfg_attr_type_word().wf(v@),
        spec_cfg_attr_type_word().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_cfg_attr_type_word().spec_serialize(v@).len(),
{
    let combinator = cfg_attr_type_word();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCfgAttribute {
    pub r_and_attr_type: SpecCfgAttrTypeWord,
    pub length: u16,
    pub value: Seq<u8>,
}

pub type SpecCfgAttributeInner = ((SpecCfgAttrTypeWord, u16), Seq<u8>);


impl SpecFrom<SpecCfgAttribute> for SpecCfgAttributeInner {
    open spec fn spec_from(m: SpecCfgAttribute) -> SpecCfgAttributeInner {
        ((m.r_and_attr_type, m.length), m.value)
    }
}

impl SpecFrom<SpecCfgAttributeInner> for SpecCfgAttribute {
    open spec fn spec_from(m: SpecCfgAttributeInner) -> SpecCfgAttribute {
        let ((r_and_attr_type, length), value) = m;
        SpecCfgAttribute { r_and_attr_type, length, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CfgAttribute<'a> {
    pub r_and_attr_type: CfgAttrTypeWord,
    pub length: u16,
    pub value: &'a [u8],
}

impl View for CfgAttribute<'_> {
    type V = SpecCfgAttribute;

    open spec fn view(&self) -> Self::V {
        SpecCfgAttribute {
            r_and_attr_type: self.r_and_attr_type@,
            length: self.length@,
            value: self.value@,
        }
    }
}
pub type CfgAttributeInner<'a> = ((CfgAttrTypeWord, u16), &'a [u8]);

pub type CfgAttributeInnerRef<'a> = ((&'a CfgAttrTypeWord, &'a u16), &'a &'a [u8]);
impl<'a> From<&'a CfgAttribute<'a>> for CfgAttributeInnerRef<'a> {
    fn ex_from(m: &'a CfgAttribute) -> CfgAttributeInnerRef<'a> {
        ((&m.r_and_attr_type, &m.length), &m.value)
    }
}

impl<'a> From<CfgAttributeInner<'a>> for CfgAttribute<'a> {
    fn ex_from(m: CfgAttributeInner) -> CfgAttribute {
        let ((r_and_attr_type, length), value) = m;
        CfgAttribute { r_and_attr_type, length, value }
    }
}

pub struct CfgAttributeMapper;
impl View for CfgAttributeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CfgAttributeMapper {
    type Src = SpecCfgAttributeInner;
    type Dst = SpecCfgAttribute;
}
impl SpecIsoProof for CfgAttributeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CfgAttributeMapper {
    type Src = CfgAttributeInner<'a>;
    type Dst = CfgAttribute<'a>;
    type RefSrc = CfgAttributeInnerRef<'a>;
}

pub struct SpecCfgAttributeCombinator(pub SpecCfgAttributeCombinatorAlias);

impl SpecCombinator for SpecCfgAttributeCombinator {
    type Type = SpecCfgAttribute;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCfgAttributeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCfgAttributeCombinatorAlias::is_prefix_secure() }
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
pub type SpecCfgAttributeCombinatorAlias = Mapped<SpecPair<SpecPair<SpecCfgAttrTypeWordCombinator, U16Be>, bytes::Variable>, CfgAttributeMapper>;

pub struct CfgAttributeCombinator(pub CfgAttributeCombinatorAlias);

impl View for CfgAttributeCombinator {
    type V = SpecCfgAttributeCombinator;
    open spec fn view(&self) -> Self::V { SpecCfgAttributeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CfgAttributeCombinator {
    type Type = CfgAttribute<'a>;
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
pub type CfgAttributeCombinatorAlias = Mapped<Pair<Pair<CfgAttrTypeWordCombinator, U16Be, CfgAttributeCont1>, bytes::Variable, CfgAttributeCont0>, CfgAttributeMapper>;


pub open spec fn spec_cfg_attribute() -> SpecCfgAttributeCombinator {
    SpecCfgAttributeCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_cfg_attr_type_word(), |deps| spec_cfg_attribute_cont1(deps)), |deps| spec_cfg_attribute_cont0(deps)),
        mapper: CfgAttributeMapper,
    })
}

pub open spec fn spec_cfg_attribute_cont1(deps: SpecCfgAttrTypeWord) -> U16Be {
    let r_and_attr_type = deps;
    U16Be
}

impl View for CfgAttributeCont1 {
    type V = spec_fn(SpecCfgAttrTypeWord) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecCfgAttrTypeWord| {
            spec_cfg_attribute_cont1(deps)
        }
    }
}

pub open spec fn spec_cfg_attribute_cont0(deps: (SpecCfgAttrTypeWord, u16)) -> bytes::Variable {
    let (r_and_attr_type, length) = deps;
    bytes::Variable((usize::spec_from(length)) as usize)
}

impl View for CfgAttributeCont0 {
    type V = spec_fn((SpecCfgAttrTypeWord, u16)) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecCfgAttrTypeWord, u16)| {
            spec_cfg_attribute_cont0(deps)
        }
    }
}

                
pub fn cfg_attribute<'a>() -> (o: CfgAttributeCombinator)
    ensures o@ == spec_cfg_attribute(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CfgAttributeCombinator(
    Mapped {
        inner: Pair::new(Pair::new(cfg_attr_type_word(), CfgAttributeCont1), CfgAttributeCont0),
        mapper: CfgAttributeMapper,
    });
    // assert({
    //     &&& combinator@ == spec_cfg_attribute()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cfg_attribute<'a>(input: &'a [u8]) -> (res: PResult<<CfgAttributeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_cfg_attribute().spec_parse(input@) == Some((n as int, v@)),
        spec_cfg_attribute().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cfg_attribute().spec_parse(input@) is None,
        spec_cfg_attribute().spec_parse(input@) is None ==> res is Err,
{
    let combinator = cfg_attribute();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cfg_attribute<'a>(v: <CfgAttributeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cfg_attribute().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cfg_attribute().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cfg_attribute().spec_serialize(v@))
        },
{
    let combinator = cfg_attribute();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn cfg_attribute_len<'a>(v: <CfgAttributeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_cfg_attribute().wf(v@),
        spec_cfg_attribute().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_cfg_attribute().spec_serialize(v@).len(),
{
    let combinator = cfg_attribute();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CfgAttributeCont1;
type CfgAttributeCont1Type<'a, 'b> = &'b CfgAttrTypeWord;
type CfgAttributeCont1SType<'a, 'x> = &'x CfgAttrTypeWord;
type CfgAttributeCont1Input<'a, 'b, 'x> = POrSType<CfgAttributeCont1Type<'a, 'b>, CfgAttributeCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CfgAttributeCont1Input<'a, 'b, 'x>> for CfgAttributeCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: CfgAttributeCont1Input<'a, 'b, 'x>) -> bool {
        &&& (spec_cfg_attr_type_word()).wf(deps@)
        }

    open spec fn ensures(&self, deps: CfgAttributeCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_cfg_attribute_cont1(deps@)
    }

    fn apply(&self, deps: CfgAttributeCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let r_and_attr_type = deps;
                let r_and_attr_type = *r_and_attr_type;
                U16Be
            }
            POrSType::S(deps) => {
                let r_and_attr_type = deps;
                let r_and_attr_type = *r_and_attr_type;
                U16Be
            }
        }
    }
}
pub struct CfgAttributeCont0;
type CfgAttributeCont0Type<'a, 'b> = &'b (CfgAttrTypeWord, u16);
type CfgAttributeCont0SType<'a, 'x> = (&'x CfgAttrTypeWord, &'x u16);
type CfgAttributeCont0Input<'a, 'b, 'x> = POrSType<CfgAttributeCont0Type<'a, 'b>, CfgAttributeCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CfgAttributeCont0Input<'a, 'b, 'x>> for CfgAttributeCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CfgAttributeCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(spec_cfg_attr_type_word(), |deps| spec_cfg_attribute_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: CfgAttributeCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_cfg_attribute_cont0(deps@)
    }

    fn apply(&self, deps: CfgAttributeCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (r_and_attr_type, length) = deps;
                let r_and_attr_type = *r_and_attr_type;
                let length = *length;
                bytes::Variable((usize::ex_from(length)) as usize)
            }
            POrSType::S(deps) => {
                let (r_and_attr_type, length) = deps;
                let r_and_attr_type = *r_and_attr_type;
                let length = *length;
                bytes::Variable((usize::ex_from(length)) as usize)
            }
        }
    }
}
                
pub mod TsType {
    use super::*;
    pub spec const SPEC_TS_IPV4_ADDR_RANGE: u8 = 7;
    pub spec const SPEC_TS_IPV6_ADDR_RANGE: u8 = 8;
    pub exec const TS_IPV4_ADDR_RANGE: u8 ensures TS_IPV4_ADDR_RANGE == SPEC_TS_IPV4_ADDR_RANGE { 7 }
    pub exec const TS_IPV6_ADDR_RANGE: u8 ensures TS_IPV6_ADDR_RANGE == SPEC_TS_IPV6_ADDR_RANGE { 8 }
}


pub struct SpecTsTypeCombinator(pub SpecTsTypeCombinatorAlias);

impl SpecCombinator for SpecTsTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecTsTypeCombinatorAlias = U8;

pub struct TsTypeCombinator(pub TsTypeCombinatorAlias);

impl View for TsTypeCombinator {
    type V = SpecTsTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecTsTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsTypeCombinator {
    type Type = u8;
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
pub type TsTypeCombinatorAlias = U8;


pub open spec fn spec_ts_type() -> SpecTsTypeCombinator {
    SpecTsTypeCombinator(U8)
}

                
pub fn ts_type<'a>() -> (o: TsTypeCombinator)
    ensures o@ == spec_ts_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_ts_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_type<'a>(input: &'a [u8]) -> (res: PResult<<TsTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_type().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_type().spec_parse(input@) is None,
        spec_ts_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_type<'a>(v: <TsTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_type().spec_serialize(v@))
        },
{
    let combinator = ts_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_type_len<'a>(v: <TsTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_type().wf(v@),
        spec_ts_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_type().spec_serialize(v@).len(),
{
    let combinator = ts_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTsIpv4SelectorBody {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: Seq<u8>,
    pub end_address: Seq<u8>,
}

pub type SpecTsIpv4SelectorBodyInner = (u8, (u16, (u16, (u16, (Seq<u8>, Seq<u8>)))));


impl SpecFrom<SpecTsIpv4SelectorBody> for SpecTsIpv4SelectorBodyInner {
    open spec fn spec_from(m: SpecTsIpv4SelectorBody) -> SpecTsIpv4SelectorBodyInner {
        (m.ip_protocol_id, (m.selector_length, (m.start_port, (m.end_port, (m.start_address, m.end_address)))))
    }
}

impl SpecFrom<SpecTsIpv4SelectorBodyInner> for SpecTsIpv4SelectorBody {
    open spec fn spec_from(m: SpecTsIpv4SelectorBodyInner) -> SpecTsIpv4SelectorBody {
        let (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address))))) = m;
        SpecTsIpv4SelectorBody { ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsIpv4SelectorBody<'a> {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: &'a [u8],
    pub end_address: &'a [u8],
}

impl View for TsIpv4SelectorBody<'_> {
    type V = SpecTsIpv4SelectorBody;

    open spec fn view(&self) -> Self::V {
        SpecTsIpv4SelectorBody {
            ip_protocol_id: self.ip_protocol_id@,
            selector_length: self.selector_length@,
            start_port: self.start_port@,
            end_port: self.end_port@,
            start_address: self.start_address@,
            end_address: self.end_address@,
        }
    }
}
pub type TsIpv4SelectorBodyInner<'a> = (u8, (u16, (u16, (u16, (&'a [u8], &'a [u8])))));

pub type TsIpv4SelectorBodyInnerRef<'a> = (&'a u8, (&'a u16, (&'a u16, (&'a u16, (&'a &'a [u8], &'a &'a [u8])))));
impl<'a> From<&'a TsIpv4SelectorBody<'a>> for TsIpv4SelectorBodyInnerRef<'a> {
    fn ex_from(m: &'a TsIpv4SelectorBody) -> TsIpv4SelectorBodyInnerRef<'a> {
        (&m.ip_protocol_id, (&m.selector_length, (&m.start_port, (&m.end_port, (&m.start_address, &m.end_address)))))
    }
}

impl<'a> From<TsIpv4SelectorBodyInner<'a>> for TsIpv4SelectorBody<'a> {
    fn ex_from(m: TsIpv4SelectorBodyInner) -> TsIpv4SelectorBody {
        let (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address))))) = m;
        TsIpv4SelectorBody { ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}

pub struct TsIpv4SelectorBodyMapper;
impl View for TsIpv4SelectorBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsIpv4SelectorBodyMapper {
    type Src = SpecTsIpv4SelectorBodyInner;
    type Dst = SpecTsIpv4SelectorBody;
}
impl SpecIsoProof for TsIpv4SelectorBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsIpv4SelectorBodyMapper {
    type Src = TsIpv4SelectorBodyInner<'a>;
    type Dst = TsIpv4SelectorBody<'a>;
    type RefSrc = TsIpv4SelectorBodyInnerRef<'a>;
}
pub const TSIPV4SELECTORBODYSELECTOR_LENGTH_CONST: u16 = 16;
type SpecTsIpv4SelectorBodyCombinatorAlias1 = (bytes::Fixed<4>, bytes::Fixed<4>);
type SpecTsIpv4SelectorBodyCombinatorAlias2 = (U16Be, SpecTsIpv4SelectorBodyCombinatorAlias1);
type SpecTsIpv4SelectorBodyCombinatorAlias3 = (U16Be, SpecTsIpv4SelectorBodyCombinatorAlias2);
type SpecTsIpv4SelectorBodyCombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, SpecTsIpv4SelectorBodyCombinatorAlias3);
type SpecTsIpv4SelectorBodyCombinatorAlias5 = (U8, SpecTsIpv4SelectorBodyCombinatorAlias4);
pub struct SpecTsIpv4SelectorBodyCombinator(pub SpecTsIpv4SelectorBodyCombinatorAlias);

impl SpecCombinator for SpecTsIpv4SelectorBodyCombinator {
    type Type = SpecTsIpv4SelectorBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsIpv4SelectorBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsIpv4SelectorBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecTsIpv4SelectorBodyCombinatorAlias = Mapped<SpecTsIpv4SelectorBodyCombinatorAlias5, TsIpv4SelectorBodyMapper>;
type TsIpv4SelectorBodyCombinatorAlias1 = (bytes::Fixed<4>, bytes::Fixed<4>);
type TsIpv4SelectorBodyCombinatorAlias2 = (U16Be, TsIpv4SelectorBodyCombinator1);
type TsIpv4SelectorBodyCombinatorAlias3 = (U16Be, TsIpv4SelectorBodyCombinator2);
type TsIpv4SelectorBodyCombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, TsIpv4SelectorBodyCombinator3);
type TsIpv4SelectorBodyCombinatorAlias5 = (U8, TsIpv4SelectorBodyCombinator4);
pub struct TsIpv4SelectorBodyCombinator1(pub TsIpv4SelectorBodyCombinatorAlias1);
impl View for TsIpv4SelectorBodyCombinator1 {
    type V = SpecTsIpv4SelectorBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4SelectorBodyCombinator1, TsIpv4SelectorBodyCombinatorAlias1);

pub struct TsIpv4SelectorBodyCombinator2(pub TsIpv4SelectorBodyCombinatorAlias2);
impl View for TsIpv4SelectorBodyCombinator2 {
    type V = SpecTsIpv4SelectorBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4SelectorBodyCombinator2, TsIpv4SelectorBodyCombinatorAlias2);

pub struct TsIpv4SelectorBodyCombinator3(pub TsIpv4SelectorBodyCombinatorAlias3);
impl View for TsIpv4SelectorBodyCombinator3 {
    type V = SpecTsIpv4SelectorBodyCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4SelectorBodyCombinator3, TsIpv4SelectorBodyCombinatorAlias3);

pub struct TsIpv4SelectorBodyCombinator4(pub TsIpv4SelectorBodyCombinatorAlias4);
impl View for TsIpv4SelectorBodyCombinator4 {
    type V = SpecTsIpv4SelectorBodyCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4SelectorBodyCombinator4, TsIpv4SelectorBodyCombinatorAlias4);

pub struct TsIpv4SelectorBodyCombinator5(pub TsIpv4SelectorBodyCombinatorAlias5);
impl View for TsIpv4SelectorBodyCombinator5 {
    type V = SpecTsIpv4SelectorBodyCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4SelectorBodyCombinator5, TsIpv4SelectorBodyCombinatorAlias5);

pub struct TsIpv4SelectorBodyCombinator(pub TsIpv4SelectorBodyCombinatorAlias);

impl View for TsIpv4SelectorBodyCombinator {
    type V = SpecTsIpv4SelectorBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecTsIpv4SelectorBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsIpv4SelectorBodyCombinator {
    type Type = TsIpv4SelectorBody<'a>;
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
pub type TsIpv4SelectorBodyCombinatorAlias = Mapped<TsIpv4SelectorBodyCombinator5, TsIpv4SelectorBodyMapper>;


pub open spec fn spec_ts_ipv4_selector_body() -> SpecTsIpv4SelectorBodyCombinator {
    SpecTsIpv4SelectorBodyCombinator(
    Mapped {
        inner: (U8, (Refined { inner: U16Be, predicate: TagPred(TSIPV4SELECTORBODYSELECTOR_LENGTH_CONST) }, (U16Be, (U16Be, (bytes::Fixed::<4>, bytes::Fixed::<4>))))),
        mapper: TsIpv4SelectorBodyMapper,
    })
}

                
pub fn ts_ipv4_selector_body<'a>() -> (o: TsIpv4SelectorBodyCombinator)
    ensures o@ == spec_ts_ipv4_selector_body(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsIpv4SelectorBodyCombinator(
    Mapped {
        inner: TsIpv4SelectorBodyCombinator5((U8, TsIpv4SelectorBodyCombinator4((Refined { inner: U16Be, predicate: TagPred(TSIPV4SELECTORBODYSELECTOR_LENGTH_CONST) }, TsIpv4SelectorBodyCombinator3((U16Be, TsIpv4SelectorBodyCombinator2((U16Be, TsIpv4SelectorBodyCombinator1((bytes::Fixed::<4>, bytes::Fixed::<4>)))))))))),
        mapper: TsIpv4SelectorBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_ipv4_selector_body()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_ipv4_selector_body<'a>(input: &'a [u8]) -> (res: PResult<<TsIpv4SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_ipv4_selector_body().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_ipv4_selector_body().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_ipv4_selector_body().spec_parse(input@) is None,
        spec_ts_ipv4_selector_body().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_ipv4_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_ipv4_selector_body<'a>(v: <TsIpv4SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_ipv4_selector_body().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_ipv4_selector_body().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_ipv4_selector_body().spec_serialize(v@))
        },
{
    let combinator = ts_ipv4_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_ipv4_selector_body_len<'a>(v: <TsIpv4SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_ipv4_selector_body().wf(v@),
        spec_ts_ipv4_selector_body().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_ipv4_selector_body().spec_serialize(v@).len(),
{
    let combinator = ts_ipv4_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTsIpv6SelectorBody {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: Seq<u8>,
    pub end_address: Seq<u8>,
}

pub type SpecTsIpv6SelectorBodyInner = (u8, (u16, (u16, (u16, (Seq<u8>, Seq<u8>)))));


impl SpecFrom<SpecTsIpv6SelectorBody> for SpecTsIpv6SelectorBodyInner {
    open spec fn spec_from(m: SpecTsIpv6SelectorBody) -> SpecTsIpv6SelectorBodyInner {
        (m.ip_protocol_id, (m.selector_length, (m.start_port, (m.end_port, (m.start_address, m.end_address)))))
    }
}

impl SpecFrom<SpecTsIpv6SelectorBodyInner> for SpecTsIpv6SelectorBody {
    open spec fn spec_from(m: SpecTsIpv6SelectorBodyInner) -> SpecTsIpv6SelectorBody {
        let (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address))))) = m;
        SpecTsIpv6SelectorBody { ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsIpv6SelectorBody<'a> {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: &'a [u8],
    pub end_address: &'a [u8],
}

impl View for TsIpv6SelectorBody<'_> {
    type V = SpecTsIpv6SelectorBody;

    open spec fn view(&self) -> Self::V {
        SpecTsIpv6SelectorBody {
            ip_protocol_id: self.ip_protocol_id@,
            selector_length: self.selector_length@,
            start_port: self.start_port@,
            end_port: self.end_port@,
            start_address: self.start_address@,
            end_address: self.end_address@,
        }
    }
}
pub type TsIpv6SelectorBodyInner<'a> = (u8, (u16, (u16, (u16, (&'a [u8], &'a [u8])))));

pub type TsIpv6SelectorBodyInnerRef<'a> = (&'a u8, (&'a u16, (&'a u16, (&'a u16, (&'a &'a [u8], &'a &'a [u8])))));
impl<'a> From<&'a TsIpv6SelectorBody<'a>> for TsIpv6SelectorBodyInnerRef<'a> {
    fn ex_from(m: &'a TsIpv6SelectorBody) -> TsIpv6SelectorBodyInnerRef<'a> {
        (&m.ip_protocol_id, (&m.selector_length, (&m.start_port, (&m.end_port, (&m.start_address, &m.end_address)))))
    }
}

impl<'a> From<TsIpv6SelectorBodyInner<'a>> for TsIpv6SelectorBody<'a> {
    fn ex_from(m: TsIpv6SelectorBodyInner) -> TsIpv6SelectorBody {
        let (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address))))) = m;
        TsIpv6SelectorBody { ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}

pub struct TsIpv6SelectorBodyMapper;
impl View for TsIpv6SelectorBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsIpv6SelectorBodyMapper {
    type Src = SpecTsIpv6SelectorBodyInner;
    type Dst = SpecTsIpv6SelectorBody;
}
impl SpecIsoProof for TsIpv6SelectorBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsIpv6SelectorBodyMapper {
    type Src = TsIpv6SelectorBodyInner<'a>;
    type Dst = TsIpv6SelectorBody<'a>;
    type RefSrc = TsIpv6SelectorBodyInnerRef<'a>;
}
pub const TSIPV6SELECTORBODYSELECTOR_LENGTH_CONST: u16 = 40;
type SpecTsIpv6SelectorBodyCombinatorAlias1 = (bytes::Fixed<16>, bytes::Fixed<16>);
type SpecTsIpv6SelectorBodyCombinatorAlias2 = (U16Be, SpecTsIpv6SelectorBodyCombinatorAlias1);
type SpecTsIpv6SelectorBodyCombinatorAlias3 = (U16Be, SpecTsIpv6SelectorBodyCombinatorAlias2);
type SpecTsIpv6SelectorBodyCombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, SpecTsIpv6SelectorBodyCombinatorAlias3);
type SpecTsIpv6SelectorBodyCombinatorAlias5 = (U8, SpecTsIpv6SelectorBodyCombinatorAlias4);
pub struct SpecTsIpv6SelectorBodyCombinator(pub SpecTsIpv6SelectorBodyCombinatorAlias);

impl SpecCombinator for SpecTsIpv6SelectorBodyCombinator {
    type Type = SpecTsIpv6SelectorBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsIpv6SelectorBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsIpv6SelectorBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecTsIpv6SelectorBodyCombinatorAlias = Mapped<SpecTsIpv6SelectorBodyCombinatorAlias5, TsIpv6SelectorBodyMapper>;
type TsIpv6SelectorBodyCombinatorAlias1 = (bytes::Fixed<16>, bytes::Fixed<16>);
type TsIpv6SelectorBodyCombinatorAlias2 = (U16Be, TsIpv6SelectorBodyCombinator1);
type TsIpv6SelectorBodyCombinatorAlias3 = (U16Be, TsIpv6SelectorBodyCombinator2);
type TsIpv6SelectorBodyCombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, TsIpv6SelectorBodyCombinator3);
type TsIpv6SelectorBodyCombinatorAlias5 = (U8, TsIpv6SelectorBodyCombinator4);
pub struct TsIpv6SelectorBodyCombinator1(pub TsIpv6SelectorBodyCombinatorAlias1);
impl View for TsIpv6SelectorBodyCombinator1 {
    type V = SpecTsIpv6SelectorBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6SelectorBodyCombinator1, TsIpv6SelectorBodyCombinatorAlias1);

pub struct TsIpv6SelectorBodyCombinator2(pub TsIpv6SelectorBodyCombinatorAlias2);
impl View for TsIpv6SelectorBodyCombinator2 {
    type V = SpecTsIpv6SelectorBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6SelectorBodyCombinator2, TsIpv6SelectorBodyCombinatorAlias2);

pub struct TsIpv6SelectorBodyCombinator3(pub TsIpv6SelectorBodyCombinatorAlias3);
impl View for TsIpv6SelectorBodyCombinator3 {
    type V = SpecTsIpv6SelectorBodyCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6SelectorBodyCombinator3, TsIpv6SelectorBodyCombinatorAlias3);

pub struct TsIpv6SelectorBodyCombinator4(pub TsIpv6SelectorBodyCombinatorAlias4);
impl View for TsIpv6SelectorBodyCombinator4 {
    type V = SpecTsIpv6SelectorBodyCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6SelectorBodyCombinator4, TsIpv6SelectorBodyCombinatorAlias4);

pub struct TsIpv6SelectorBodyCombinator5(pub TsIpv6SelectorBodyCombinatorAlias5);
impl View for TsIpv6SelectorBodyCombinator5 {
    type V = SpecTsIpv6SelectorBodyCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv6SelectorBodyCombinator5, TsIpv6SelectorBodyCombinatorAlias5);

pub struct TsIpv6SelectorBodyCombinator(pub TsIpv6SelectorBodyCombinatorAlias);

impl View for TsIpv6SelectorBodyCombinator {
    type V = SpecTsIpv6SelectorBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecTsIpv6SelectorBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsIpv6SelectorBodyCombinator {
    type Type = TsIpv6SelectorBody<'a>;
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
pub type TsIpv6SelectorBodyCombinatorAlias = Mapped<TsIpv6SelectorBodyCombinator5, TsIpv6SelectorBodyMapper>;


pub open spec fn spec_ts_ipv6_selector_body() -> SpecTsIpv6SelectorBodyCombinator {
    SpecTsIpv6SelectorBodyCombinator(
    Mapped {
        inner: (U8, (Refined { inner: U16Be, predicate: TagPred(TSIPV6SELECTORBODYSELECTOR_LENGTH_CONST) }, (U16Be, (U16Be, (bytes::Fixed::<16>, bytes::Fixed::<16>))))),
        mapper: TsIpv6SelectorBodyMapper,
    })
}

                
pub fn ts_ipv6_selector_body<'a>() -> (o: TsIpv6SelectorBodyCombinator)
    ensures o@ == spec_ts_ipv6_selector_body(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsIpv6SelectorBodyCombinator(
    Mapped {
        inner: TsIpv6SelectorBodyCombinator5((U8, TsIpv6SelectorBodyCombinator4((Refined { inner: U16Be, predicate: TagPred(TSIPV6SELECTORBODYSELECTOR_LENGTH_CONST) }, TsIpv6SelectorBodyCombinator3((U16Be, TsIpv6SelectorBodyCombinator2((U16Be, TsIpv6SelectorBodyCombinator1((bytes::Fixed::<16>, bytes::Fixed::<16>)))))))))),
        mapper: TsIpv6SelectorBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_ipv6_selector_body()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_ipv6_selector_body<'a>(input: &'a [u8]) -> (res: PResult<<TsIpv6SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_ipv6_selector_body().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_ipv6_selector_body().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_ipv6_selector_body().spec_parse(input@) is None,
        spec_ts_ipv6_selector_body().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_ipv6_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_ipv6_selector_body<'a>(v: <TsIpv6SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_ipv6_selector_body().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_ipv6_selector_body().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_ipv6_selector_body().spec_serialize(v@))
        },
{
    let combinator = ts_ipv6_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_ipv6_selector_body_len<'a>(v: <TsIpv6SelectorBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_ipv6_selector_body().wf(v@),
        spec_ts_ipv6_selector_body().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_ipv6_selector_body().spec_serialize(v@).len(),
{
    let combinator = ts_ipv6_selector_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTsUnknownInner {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub selector_data: Seq<u8>,
}

pub type SpecTsUnknownInnerInner = ((u8, u16), Seq<u8>);


impl SpecFrom<SpecTsUnknownInner> for SpecTsUnknownInnerInner {
    open spec fn spec_from(m: SpecTsUnknownInner) -> SpecTsUnknownInnerInner {
        ((m.ip_protocol_id, m.selector_length), m.selector_data)
    }
}

impl SpecFrom<SpecTsUnknownInnerInner> for SpecTsUnknownInner {
    open spec fn spec_from(m: SpecTsUnknownInnerInner) -> SpecTsUnknownInner {
        let ((ip_protocol_id, selector_length), selector_data) = m;
        SpecTsUnknownInner { ip_protocol_id, selector_length, selector_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsUnknownInner<'a> {
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub selector_data: &'a [u8],
}

impl View for TsUnknownInner<'_> {
    type V = SpecTsUnknownInner;

    open spec fn view(&self) -> Self::V {
        SpecTsUnknownInner {
            ip_protocol_id: self.ip_protocol_id@,
            selector_length: self.selector_length@,
            selector_data: self.selector_data@,
        }
    }
}
pub type TsUnknownInnerInner<'a> = ((u8, u16), &'a [u8]);

pub type TsUnknownInnerInnerRef<'a> = ((&'a u8, &'a u16), &'a &'a [u8]);
impl<'a> From<&'a TsUnknownInner<'a>> for TsUnknownInnerInnerRef<'a> {
    fn ex_from(m: &'a TsUnknownInner) -> TsUnknownInnerInnerRef<'a> {
        ((&m.ip_protocol_id, &m.selector_length), &m.selector_data)
    }
}

impl<'a> From<TsUnknownInnerInner<'a>> for TsUnknownInner<'a> {
    fn ex_from(m: TsUnknownInnerInner) -> TsUnknownInner {
        let ((ip_protocol_id, selector_length), selector_data) = m;
        TsUnknownInner { ip_protocol_id, selector_length, selector_data }
    }
}

pub struct TsUnknownInnerMapper;
impl View for TsUnknownInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsUnknownInnerMapper {
    type Src = SpecTsUnknownInnerInner;
    type Dst = SpecTsUnknownInner;
}
impl SpecIsoProof for TsUnknownInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsUnknownInnerMapper {
    type Src = TsUnknownInnerInner<'a>;
    type Dst = TsUnknownInner<'a>;
    type RefSrc = TsUnknownInnerInnerRef<'a>;
}

pub struct SpecTsUnknownInnerCombinator(pub SpecTsUnknownInnerCombinatorAlias);

impl SpecCombinator for SpecTsUnknownInnerCombinator {
    type Type = SpecTsUnknownInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsUnknownInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsUnknownInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecTsUnknownInnerCombinatorAlias = Mapped<SpecPair<(U8, Refined<U16Be, Predicate17149271707383182075>), bytes::Variable>, TsUnknownInnerMapper>;
pub struct Predicate17149271707383182075;
impl View for Predicate17149271707383182075 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate17149271707383182075 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 4 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate17149271707383182075 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 4 && i <= 65535)
    }
}

pub struct TsUnknownInnerCombinator(pub TsUnknownInnerCombinatorAlias);

impl View for TsUnknownInnerCombinator {
    type V = SpecTsUnknownInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecTsUnknownInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsUnknownInnerCombinator {
    type Type = TsUnknownInner<'a>;
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
pub type TsUnknownInnerCombinatorAlias = Mapped<Pair<(U8, Refined<U16Be, Predicate17149271707383182075>), bytes::Variable, TsUnknownInnerCont0>, TsUnknownInnerMapper>;


pub open spec fn spec_ts_unknown_inner() -> SpecTsUnknownInnerCombinator {
    SpecTsUnknownInnerCombinator(
    Mapped {
        inner: Pair::spec_new((U8, Refined { inner: U16Be, predicate: Predicate17149271707383182075 }), |deps| spec_ts_unknown_inner_cont0(deps)),
        mapper: TsUnknownInnerMapper,
    })
}

pub open spec fn spec_ts_unknown_inner_cont0(deps: (u8, u16)) -> bytes::Variable {
    let (_, selector_length) = deps;
    bytes::Variable(((usize::spec_from(selector_length) - 4)) as usize)
}

impl View for TsUnknownInnerCont0 {
    type V = spec_fn((u8, u16)) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, u16)| {
            spec_ts_unknown_inner_cont0(deps)
        }
    }
}

                
pub fn ts_unknown_inner<'a>() -> (o: TsUnknownInnerCombinator)
    ensures o@ == spec_ts_unknown_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsUnknownInnerCombinator(
    Mapped {
        inner: Pair::new((U8, Refined { inner: U16Be, predicate: Predicate17149271707383182075 }), TsUnknownInnerCont0),
        mapper: TsUnknownInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_unknown_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_unknown_inner<'a>(input: &'a [u8]) -> (res: PResult<<TsUnknownInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_unknown_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_unknown_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_unknown_inner().spec_parse(input@) is None,
        spec_ts_unknown_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_unknown_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_unknown_inner<'a>(v: <TsUnknownInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_unknown_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_unknown_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_unknown_inner().spec_serialize(v@))
        },
{
    let combinator = ts_unknown_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_unknown_inner_len<'a>(v: <TsUnknownInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_unknown_inner().wf(v@),
        spec_ts_unknown_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_unknown_inner().spec_serialize(v@).len(),
{
    let combinator = ts_unknown_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TsUnknownInnerCont0;
type TsUnknownInnerCont0Type<'a, 'b> = &'b (u8, u16);
type TsUnknownInnerCont0SType<'a, 'x> = (&'x u8, &'x u16);
type TsUnknownInnerCont0Input<'a, 'b, 'x> = POrSType<TsUnknownInnerCont0Type<'a, 'b>, TsUnknownInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TsUnknownInnerCont0Input<'a, 'b, 'x>> for TsUnknownInnerCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: TsUnknownInnerCont0Input<'a, 'b, 'x>) -> bool {
        &&& ((U8, Refined { inner: U16Be, predicate: Predicate17149271707383182075 })).wf(deps@)
        }

    open spec fn ensures(&self, deps: TsUnknownInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ts_unknown_inner_cont0(deps@)
    }

    fn apply(&self, deps: TsUnknownInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, selector_length) = deps;
                let selector_length = *selector_length;
                bytes::Variable(((usize::ex_from(selector_length) - 4)) as usize)
            }
            POrSType::S(deps) => {
                let (_, selector_length) = deps;
                let selector_length = *selector_length;
                bytes::Variable(((usize::ex_from(selector_length) - 4)) as usize)
            }
        }
    }
}
                

pub enum SpecTrafficSelectorTsBody {
    TS_IPV4_ADDR_RANGE(SpecTsIpv4SelectorBody),
    TS_IPV6_ADDR_RANGE(SpecTsIpv6SelectorBody),
    Unrecognized(SpecTsUnknownInner),
}

pub type SpecTrafficSelectorTsBodyInner = Either<SpecTsIpv4SelectorBody, Either<SpecTsIpv6SelectorBody, SpecTsUnknownInner>>;

impl SpecFrom<SpecTrafficSelectorTsBody> for SpecTrafficSelectorTsBodyInner {
    open spec fn spec_from(m: SpecTrafficSelectorTsBody) -> SpecTrafficSelectorTsBodyInner {
        match m {
            SpecTrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m) => Either::Left(m),
            SpecTrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m) => Either::Right(Either::Left(m)),
            SpecTrafficSelectorTsBody::Unrecognized(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecTrafficSelectorTsBodyInner> for SpecTrafficSelectorTsBody {
    open spec fn spec_from(m: SpecTrafficSelectorTsBodyInner) -> SpecTrafficSelectorTsBody {
        match m {
            Either::Left(m) => SpecTrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m),
            Either::Right(Either::Left(m)) => SpecTrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m),
            Either::Right(Either::Right(m)) => SpecTrafficSelectorTsBody::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrafficSelectorTsBody<'a> {
    TS_IPV4_ADDR_RANGE(TsIpv4SelectorBody<'a>),
    TS_IPV6_ADDR_RANGE(TsIpv6SelectorBody<'a>),
    Unrecognized(TsUnknownInner<'a>),
}

pub type TrafficSelectorTsBodyInner<'a> = Either<TsIpv4SelectorBody<'a>, Either<TsIpv6SelectorBody<'a>, TsUnknownInner<'a>>>;

pub type TrafficSelectorTsBodyInnerRef<'a> = Either<&'a TsIpv4SelectorBody<'a>, Either<&'a TsIpv6SelectorBody<'a>, &'a TsUnknownInner<'a>>>;


impl<'a> View for TrafficSelectorTsBody<'a> {
    type V = SpecTrafficSelectorTsBody;
    open spec fn view(&self) -> Self::V {
        match self {
            TrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m) => SpecTrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m@),
            TrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m) => SpecTrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m@),
            TrafficSelectorTsBody::Unrecognized(m) => SpecTrafficSelectorTsBody::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a TrafficSelectorTsBody<'a>> for TrafficSelectorTsBodyInnerRef<'a> {
    fn ex_from(m: &'a TrafficSelectorTsBody<'a>) -> TrafficSelectorTsBodyInnerRef<'a> {
        match m {
            TrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m) => Either::Left(m),
            TrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m) => Either::Right(Either::Left(m)),
            TrafficSelectorTsBody::Unrecognized(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<TrafficSelectorTsBodyInner<'a>> for TrafficSelectorTsBody<'a> {
    fn ex_from(m: TrafficSelectorTsBodyInner<'a>) -> TrafficSelectorTsBody<'a> {
        match m {
            Either::Left(m) => TrafficSelectorTsBody::TS_IPV4_ADDR_RANGE(m),
            Either::Right(Either::Left(m)) => TrafficSelectorTsBody::TS_IPV6_ADDR_RANGE(m),
            Either::Right(Either::Right(m)) => TrafficSelectorTsBody::Unrecognized(m),
        }
    }
    
}


pub struct TrafficSelectorTsBodyMapper;
impl View for TrafficSelectorTsBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TrafficSelectorTsBodyMapper {
    type Src = SpecTrafficSelectorTsBodyInner;
    type Dst = SpecTrafficSelectorTsBody;
}
impl SpecIsoProof for TrafficSelectorTsBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TrafficSelectorTsBodyMapper {
    type Src = TrafficSelectorTsBodyInner<'a>;
    type Dst = TrafficSelectorTsBody<'a>;
    type RefSrc = TrafficSelectorTsBodyInnerRef<'a>;
}

type SpecTrafficSelectorTsBodyCombinatorAlias1 = Choice<Cond<SpecTsIpv6SelectorBodyCombinator>, Cond<SpecTsUnknownInnerCombinator>>;
type SpecTrafficSelectorTsBodyCombinatorAlias2 = Choice<Cond<SpecTsIpv4SelectorBodyCombinator>, SpecTrafficSelectorTsBodyCombinatorAlias1>;
pub struct SpecTrafficSelectorTsBodyCombinator(pub SpecTrafficSelectorTsBodyCombinatorAlias);

impl SpecCombinator for SpecTrafficSelectorTsBodyCombinator {
    type Type = SpecTrafficSelectorTsBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTrafficSelectorTsBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTrafficSelectorTsBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecTrafficSelectorTsBodyCombinatorAlias = Mapped<SpecTrafficSelectorTsBodyCombinatorAlias2, TrafficSelectorTsBodyMapper>;
type TrafficSelectorTsBodyCombinatorAlias1 = Choice<Cond<TsIpv6SelectorBodyCombinator>, Cond<TsUnknownInnerCombinator>>;
type TrafficSelectorTsBodyCombinatorAlias2 = Choice<Cond<TsIpv4SelectorBodyCombinator>, TrafficSelectorTsBodyCombinator1>;
pub struct TrafficSelectorTsBodyCombinator1(pub TrafficSelectorTsBodyCombinatorAlias1);
impl View for TrafficSelectorTsBodyCombinator1 {
    type V = SpecTrafficSelectorTsBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TrafficSelectorTsBodyCombinator1, TrafficSelectorTsBodyCombinatorAlias1);

pub struct TrafficSelectorTsBodyCombinator2(pub TrafficSelectorTsBodyCombinatorAlias2);
impl View for TrafficSelectorTsBodyCombinator2 {
    type V = SpecTrafficSelectorTsBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TrafficSelectorTsBodyCombinator2, TrafficSelectorTsBodyCombinatorAlias2);

pub struct TrafficSelectorTsBodyCombinator(pub TrafficSelectorTsBodyCombinatorAlias);

impl View for TrafficSelectorTsBodyCombinator {
    type V = SpecTrafficSelectorTsBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecTrafficSelectorTsBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TrafficSelectorTsBodyCombinator {
    type Type = TrafficSelectorTsBody<'a>;
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
pub type TrafficSelectorTsBodyCombinatorAlias = Mapped<TrafficSelectorTsBodyCombinator2, TrafficSelectorTsBodyMapper>;


pub open spec fn spec_traffic_selector_ts_body(ts_type_byte: u8) -> SpecTrafficSelectorTsBodyCombinator {
    SpecTrafficSelectorTsBodyCombinator(Mapped { inner: Choice(Cond { cond: ts_type_byte == TsType::SPEC_TS_IPV4_ADDR_RANGE, inner: spec_ts_ipv4_selector_body() }, Choice(Cond { cond: ts_type_byte == TsType::SPEC_TS_IPV6_ADDR_RANGE, inner: spec_ts_ipv6_selector_body() }, Cond { cond: !(ts_type_byte == TsType::SPEC_TS_IPV4_ADDR_RANGE || ts_type_byte == TsType::SPEC_TS_IPV6_ADDR_RANGE), inner: spec_ts_unknown_inner() })), mapper: TrafficSelectorTsBodyMapper })
}

pub fn traffic_selector_ts_body<'a>(ts_type_byte: u8) -> (o: TrafficSelectorTsBodyCombinator)
    requires
        spec_ts_type().wf(ts_type_byte@),

    ensures o@ == spec_traffic_selector_ts_body(ts_type_byte@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TrafficSelectorTsBodyCombinator(Mapped { inner: TrafficSelectorTsBodyCombinator2(Choice::new(Cond { cond: ts_type_byte == TsType::TS_IPV4_ADDR_RANGE, inner: ts_ipv4_selector_body() }, TrafficSelectorTsBodyCombinator1(Choice::new(Cond { cond: ts_type_byte == TsType::TS_IPV6_ADDR_RANGE, inner: ts_ipv6_selector_body() }, Cond { cond: !(ts_type_byte == TsType::TS_IPV4_ADDR_RANGE || ts_type_byte == TsType::TS_IPV6_ADDR_RANGE), inner: ts_unknown_inner() })))), mapper: TrafficSelectorTsBodyMapper });
    // assert({
    //     &&& combinator@ == spec_traffic_selector_ts_body(ts_type_byte@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_traffic_selector_ts_body<'a>(input: &'a [u8], ts_type_byte: u8) -> (res: PResult<<TrafficSelectorTsBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_ts_type().wf(ts_type_byte@),

    ensures
        res matches Ok((n, v)) ==> spec_traffic_selector_ts_body(ts_type_byte@).spec_parse(input@) == Some((n as int, v@)),
        spec_traffic_selector_ts_body(ts_type_byte@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_traffic_selector_ts_body(ts_type_byte@).spec_parse(input@) is None,
        spec_traffic_selector_ts_body(ts_type_byte@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = traffic_selector_ts_body( ts_type_byte );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_traffic_selector_ts_body<'a>(v: <TrafficSelectorTsBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, ts_type_byte: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_traffic_selector_ts_body(ts_type_byte@).wf(v@),
        spec_ts_type().wf(ts_type_byte@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_traffic_selector_ts_body(ts_type_byte@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_traffic_selector_ts_body(ts_type_byte@).spec_serialize(v@))
        },
{
    let combinator = traffic_selector_ts_body( ts_type_byte );
    combinator.serialize(v, data, pos)
}

pub fn traffic_selector_ts_body_len<'a>(v: <TrafficSelectorTsBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, ts_type_byte: u8) -> (serialize_len: usize)
    requires
        spec_traffic_selector_ts_body(ts_type_byte@).wf(v@),
        spec_traffic_selector_ts_body(ts_type_byte@).spec_serialize(v@).len() <= usize::MAX,
        spec_ts_type().wf(ts_type_byte@),

    ensures
        serialize_len == spec_traffic_selector_ts_body(ts_type_byte@).spec_serialize(v@).len(),
{
    let combinator = traffic_selector_ts_body( ts_type_byte );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecTrafficSelector {
    pub ts_type_byte: u8,
    pub ts_body: SpecTrafficSelectorTsBody,
}

pub type SpecTrafficSelectorInner = (u8, SpecTrafficSelectorTsBody);


impl SpecFrom<SpecTrafficSelector> for SpecTrafficSelectorInner {
    open spec fn spec_from(m: SpecTrafficSelector) -> SpecTrafficSelectorInner {
        (m.ts_type_byte, m.ts_body)
    }
}

impl SpecFrom<SpecTrafficSelectorInner> for SpecTrafficSelector {
    open spec fn spec_from(m: SpecTrafficSelectorInner) -> SpecTrafficSelector {
        let (ts_type_byte, ts_body) = m;
        SpecTrafficSelector { ts_type_byte, ts_body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TrafficSelector<'a> {
    pub ts_type_byte: u8,
    pub ts_body: TrafficSelectorTsBody<'a>,
}

impl View for TrafficSelector<'_> {
    type V = SpecTrafficSelector;

    open spec fn view(&self) -> Self::V {
        SpecTrafficSelector {
            ts_type_byte: self.ts_type_byte@,
            ts_body: self.ts_body@,
        }
    }
}
pub type TrafficSelectorInner<'a> = (u8, TrafficSelectorTsBody<'a>);

pub type TrafficSelectorInnerRef<'a> = (&'a u8, &'a TrafficSelectorTsBody<'a>);
impl<'a> From<&'a TrafficSelector<'a>> for TrafficSelectorInnerRef<'a> {
    fn ex_from(m: &'a TrafficSelector) -> TrafficSelectorInnerRef<'a> {
        (&m.ts_type_byte, &m.ts_body)
    }
}

impl<'a> From<TrafficSelectorInner<'a>> for TrafficSelector<'a> {
    fn ex_from(m: TrafficSelectorInner) -> TrafficSelector {
        let (ts_type_byte, ts_body) = m;
        TrafficSelector { ts_type_byte, ts_body }
    }
}

pub struct TrafficSelectorMapper;
impl View for TrafficSelectorMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TrafficSelectorMapper {
    type Src = SpecTrafficSelectorInner;
    type Dst = SpecTrafficSelector;
}
impl SpecIsoProof for TrafficSelectorMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TrafficSelectorMapper {
    type Src = TrafficSelectorInner<'a>;
    type Dst = TrafficSelector<'a>;
    type RefSrc = TrafficSelectorInnerRef<'a>;
}

pub struct SpecTrafficSelectorCombinator(pub SpecTrafficSelectorCombinatorAlias);

impl SpecCombinator for SpecTrafficSelectorCombinator {
    type Type = SpecTrafficSelector;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTrafficSelectorCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTrafficSelectorCombinatorAlias::is_prefix_secure() }
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
pub type SpecTrafficSelectorCombinatorAlias = Mapped<SpecPair<SpecTsTypeCombinator, SpecTrafficSelectorTsBodyCombinator>, TrafficSelectorMapper>;

pub struct TrafficSelectorCombinator(pub TrafficSelectorCombinatorAlias);

impl View for TrafficSelectorCombinator {
    type V = SpecTrafficSelectorCombinator;
    open spec fn view(&self) -> Self::V { SpecTrafficSelectorCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TrafficSelectorCombinator {
    type Type = TrafficSelector<'a>;
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
pub type TrafficSelectorCombinatorAlias = Mapped<Pair<TsTypeCombinator, TrafficSelectorTsBodyCombinator, TrafficSelectorCont0>, TrafficSelectorMapper>;


pub open spec fn spec_traffic_selector() -> SpecTrafficSelectorCombinator {
    SpecTrafficSelectorCombinator(
    Mapped {
        inner: Pair::spec_new(spec_ts_type(), |deps| spec_traffic_selector_cont0(deps)),
        mapper: TrafficSelectorMapper,
    })
}

pub open spec fn spec_traffic_selector_cont0(deps: u8) -> SpecTrafficSelectorTsBodyCombinator {
    let ts_type_byte = deps;
    spec_traffic_selector_ts_body(ts_type_byte)
}

impl View for TrafficSelectorCont0 {
    type V = spec_fn(u8) -> SpecTrafficSelectorTsBodyCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_traffic_selector_cont0(deps)
        }
    }
}

                
pub fn traffic_selector<'a>() -> (o: TrafficSelectorCombinator)
    ensures o@ == spec_traffic_selector(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TrafficSelectorCombinator(
    Mapped {
        inner: Pair::new(ts_type(), TrafficSelectorCont0),
        mapper: TrafficSelectorMapper,
    });
    // assert({
    //     &&& combinator@ == spec_traffic_selector()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_traffic_selector<'a>(input: &'a [u8]) -> (res: PResult<<TrafficSelectorCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_traffic_selector().spec_parse(input@) == Some((n as int, v@)),
        spec_traffic_selector().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_traffic_selector().spec_parse(input@) is None,
        spec_traffic_selector().spec_parse(input@) is None ==> res is Err,
{
    let combinator = traffic_selector();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_traffic_selector<'a>(v: <TrafficSelectorCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_traffic_selector().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_traffic_selector().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_traffic_selector().spec_serialize(v@))
        },
{
    let combinator = traffic_selector();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn traffic_selector_len<'a>(v: <TrafficSelectorCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_traffic_selector().wf(v@),
        spec_traffic_selector().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_traffic_selector().spec_serialize(v@).len(),
{
    let combinator = traffic_selector();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TrafficSelectorCont0;
type TrafficSelectorCont0Type<'a, 'b> = &'b u8;
type TrafficSelectorCont0SType<'a, 'x> = &'x u8;
type TrafficSelectorCont0Input<'a, 'b, 'x> = POrSType<TrafficSelectorCont0Type<'a, 'b>, TrafficSelectorCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TrafficSelectorCont0Input<'a, 'b, 'x>> for TrafficSelectorCont0 {
    type Output = TrafficSelectorTsBodyCombinator;

    open spec fn requires(&self, deps: TrafficSelectorCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_ts_type()).wf(deps@)
        }

    open spec fn ensures(&self, deps: TrafficSelectorCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_traffic_selector_cont0(deps@)
    }

    fn apply(&self, deps: TrafficSelectorCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ts_type_byte = deps;
                let ts_type_byte = *ts_type_byte;
                traffic_selector_ts_body(ts_type_byte)
            }
            POrSType::S(deps) => {
                let ts_type_byte = deps;
                let ts_type_byte = *ts_type_byte;
                traffic_selector_ts_body(ts_type_byte)
            }
        }
    }
}
                

pub struct SpecIkev2TsPayloadInner {
    pub num_ts: u8,
    pub reserved: Seq<u8>,
    pub selectors: Seq<SpecTrafficSelector>,
}

pub type SpecIkev2TsPayloadInnerInner = (u8, (Seq<u8>, Seq<SpecTrafficSelector>));


impl SpecFrom<SpecIkev2TsPayloadInner> for SpecIkev2TsPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2TsPayloadInner) -> SpecIkev2TsPayloadInnerInner {
        (m.num_ts, (m.reserved, m.selectors))
    }
}

impl SpecFrom<SpecIkev2TsPayloadInnerInner> for SpecIkev2TsPayloadInner {
    open spec fn spec_from(m: SpecIkev2TsPayloadInnerInner) -> SpecIkev2TsPayloadInner {
        let (num_ts, (reserved, selectors)) = m;
        SpecIkev2TsPayloadInner { num_ts, reserved, selectors }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2TsPayloadInner<'a> {
    pub num_ts: u8,
    pub reserved: &'a [u8],
    pub selectors: RepeatResult<TrafficSelector<'a>>,
}

impl View for Ikev2TsPayloadInner<'_> {
    type V = SpecIkev2TsPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2TsPayloadInner {
            num_ts: self.num_ts@,
            reserved: self.reserved@,
            selectors: self.selectors@,
        }
    }
}
pub type Ikev2TsPayloadInnerInner<'a> = (u8, (&'a [u8], RepeatResult<TrafficSelector<'a>>));

pub type Ikev2TsPayloadInnerInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a RepeatResult<TrafficSelector<'a>>));
impl<'a> From<&'a Ikev2TsPayloadInner<'a>> for Ikev2TsPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2TsPayloadInner) -> Ikev2TsPayloadInnerInnerRef<'a> {
        (&m.num_ts, (&m.reserved, &m.selectors))
    }
}

impl<'a> From<Ikev2TsPayloadInnerInner<'a>> for Ikev2TsPayloadInner<'a> {
    fn ex_from(m: Ikev2TsPayloadInnerInner) -> Ikev2TsPayloadInner {
        let (num_ts, (reserved, selectors)) = m;
        Ikev2TsPayloadInner { num_ts, reserved, selectors }
    }
}

pub struct Ikev2TsPayloadInnerMapper;
impl View for Ikev2TsPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2TsPayloadInnerMapper {
    type Src = SpecIkev2TsPayloadInnerInner;
    type Dst = SpecIkev2TsPayloadInner;
}
impl SpecIsoProof for Ikev2TsPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2TsPayloadInnerMapper {
    type Src = Ikev2TsPayloadInnerInner<'a>;
    type Dst = Ikev2TsPayloadInner<'a>;
    type RefSrc = Ikev2TsPayloadInnerInnerRef<'a>;
}
pub spec const SPEC_IKEV2TSPAYLOADINNERRESERVED_CONST: Seq<u8> = seq![0; 3];
pub struct SpecIkev2TsPayloadInnerCombinator(pub SpecIkev2TsPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2TsPayloadInnerCombinator {
    type Type = SpecIkev2TsPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2TsPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2TsPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2TsPayloadInnerCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate3651688686135228051>, (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Tail, RepeatN<SpecTrafficSelectorCombinator>>)>, Ikev2TsPayloadInnerMapper>;
pub exec static IKEV2TSPAYLOADINNERRESERVED_CONST: [u8; 3]
    ensures IKEV2TSPAYLOADINNERRESERVED_CONST@ == SPEC_IKEV2TSPAYLOADINNERRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_IKEV2TSPAYLOADINNERRESERVED_CONST);
    arr
}

pub struct Ikev2TsPayloadInnerCombinator(pub Ikev2TsPayloadInnerCombinatorAlias);

impl View for Ikev2TsPayloadInnerCombinator {
    type V = SpecIkev2TsPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2TsPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2TsPayloadInnerCombinator {
    type Type = Ikev2TsPayloadInner<'a>;
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
pub type Ikev2TsPayloadInnerCombinatorAlias = Mapped<Pair<Refined<U8, Predicate3651688686135228051>, (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Tail, RepeatN<TrafficSelectorCombinator>>), Ikev2TsPayloadInnerCont0>, Ikev2TsPayloadInnerMapper>;


pub open spec fn spec_ikev2_ts_payload_inner() -> SpecIkev2TsPayloadInnerCombinator {
    SpecIkev2TsPayloadInnerCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, |deps| spec_ikev2_ts_payload_inner_cont0(deps)),
        mapper: Ikev2TsPayloadInnerMapper,
    })
}

pub open spec fn spec_ikev2_ts_payload_inner_cont0(deps: u8) -> (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Tail, RepeatN<SpecTrafficSelectorCombinator>>) {
    let num_ts = deps;
    (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_IKEV2TSPAYLOADINNERRESERVED_CONST) }, AndThen(bytes::Tail, RepeatN(spec_traffic_selector(), (usize::spec_from(num_ts)) as usize)))
}

impl View for Ikev2TsPayloadInnerCont0 {
    type V = spec_fn(u8) -> (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Tail, RepeatN<SpecTrafficSelectorCombinator>>);

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_ikev2_ts_payload_inner_cont0(deps)
        }
    }
}

                
pub fn ikev2_ts_payload_inner<'a>() -> (o: Ikev2TsPayloadInnerCombinator)
    ensures o@ == spec_ikev2_ts_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2TsPayloadInnerCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, Ikev2TsPayloadInnerCont0),
        mapper: Ikev2TsPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_ts_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_ts_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2TsPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_ts_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_ts_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_ts_payload_inner().spec_parse(input@) is None,
        spec_ikev2_ts_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_ts_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_ts_payload_inner<'a>(v: <Ikev2TsPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_ts_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_ts_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_ts_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_ts_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_ts_payload_inner_len<'a>(v: <Ikev2TsPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_ts_payload_inner().wf(v@),
        spec_ikev2_ts_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_ts_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_ts_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Ikev2TsPayloadInnerCont0;
type Ikev2TsPayloadInnerCont0Type<'a, 'b> = &'b u8;
type Ikev2TsPayloadInnerCont0SType<'a, 'x> = &'x u8;
type Ikev2TsPayloadInnerCont0Input<'a, 'b, 'x> = POrSType<Ikev2TsPayloadInnerCont0Type<'a, 'b>, Ikev2TsPayloadInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Ikev2TsPayloadInnerCont0Input<'a, 'b, 'x>> for Ikev2TsPayloadInnerCont0 {
    type Output = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Tail, RepeatN<TrafficSelectorCombinator>>);

    open spec fn requires(&self, deps: Ikev2TsPayloadInnerCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Refined { inner: U8, predicate: Predicate3651688686135228051 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: Ikev2TsPayloadInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ikev2_ts_payload_inner_cont0(deps@)
    }

    fn apply(&self, deps: Ikev2TsPayloadInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let num_ts = deps;
                let num_ts = *num_ts;
                (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IKEV2TSPAYLOADINNERRESERVED_CONST) }, AndThen(bytes::Tail, RepeatN(traffic_selector(), (usize::ex_from(num_ts)) as usize)))
            }
            POrSType::S(deps) => {
                let num_ts = deps;
                let num_ts = *num_ts;
                (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IKEV2TSPAYLOADINNERRESERVED_CONST) }, AndThen(bytes::Tail, RepeatN(traffic_selector(), (usize::ex_from(num_ts)) as usize)))
            }
        }
    }
}
                

pub struct SpecEapSuccessRest {
    pub identifier: u8,
    pub eap_length: u16,
}

pub type SpecEapSuccessRestInner = (u8, u16);


impl SpecFrom<SpecEapSuccessRest> for SpecEapSuccessRestInner {
    open spec fn spec_from(m: SpecEapSuccessRest) -> SpecEapSuccessRestInner {
        (m.identifier, m.eap_length)
    }
}

impl SpecFrom<SpecEapSuccessRestInner> for SpecEapSuccessRest {
    open spec fn spec_from(m: SpecEapSuccessRestInner) -> SpecEapSuccessRest {
        let (identifier, eap_length) = m;
        SpecEapSuccessRest { identifier, eap_length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapSuccessRest {
    pub identifier: u8,
    pub eap_length: u16,
}

impl View for EapSuccessRest {
    type V = SpecEapSuccessRest;

    open spec fn view(&self) -> Self::V {
        SpecEapSuccessRest {
            identifier: self.identifier@,
            eap_length: self.eap_length@,
        }
    }
}
pub type EapSuccessRestInner = (u8, u16);

pub type EapSuccessRestInnerRef<'a> = (&'a u8, &'a u16);
impl<'a> From<&'a EapSuccessRest> for EapSuccessRestInnerRef<'a> {
    fn ex_from(m: &'a EapSuccessRest) -> EapSuccessRestInnerRef<'a> {
        (&m.identifier, &m.eap_length)
    }
}

impl From<EapSuccessRestInner> for EapSuccessRest {
    fn ex_from(m: EapSuccessRestInner) -> EapSuccessRest {
        let (identifier, eap_length) = m;
        EapSuccessRest { identifier, eap_length }
    }
}

pub struct EapSuccessRestMapper;
impl View for EapSuccessRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapSuccessRestMapper {
    type Src = SpecEapSuccessRestInner;
    type Dst = SpecEapSuccessRest;
}
impl SpecIsoProof for EapSuccessRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapSuccessRestMapper {
    type Src = EapSuccessRestInner;
    type Dst = EapSuccessRest;
    type RefSrc = EapSuccessRestInnerRef<'a>;
}
pub const EAPSUCCESSRESTEAP_LENGTH_CONST: u16 = 4;
type SpecEapSuccessRestCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
pub struct SpecEapSuccessRestCombinator(pub SpecEapSuccessRestCombinatorAlias);

impl SpecCombinator for SpecEapSuccessRestCombinator {
    type Type = SpecEapSuccessRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapSuccessRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapSuccessRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapSuccessRestCombinatorAlias = Mapped<SpecEapSuccessRestCombinatorAlias1, EapSuccessRestMapper>;
type EapSuccessRestCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
pub struct EapSuccessRestCombinator1(pub EapSuccessRestCombinatorAlias1);
impl View for EapSuccessRestCombinator1 {
    type V = SpecEapSuccessRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapSuccessRestCombinator1, EapSuccessRestCombinatorAlias1);

pub struct EapSuccessRestCombinator(pub EapSuccessRestCombinatorAlias);

impl View for EapSuccessRestCombinator {
    type V = SpecEapSuccessRestCombinator;
    open spec fn view(&self) -> Self::V { SpecEapSuccessRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapSuccessRestCombinator {
    type Type = EapSuccessRest;
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
pub type EapSuccessRestCombinatorAlias = Mapped<EapSuccessRestCombinator1, EapSuccessRestMapper>;


pub open spec fn spec_eap_success_rest() -> SpecEapSuccessRestCombinator {
    SpecEapSuccessRestCombinator(
    Mapped {
        inner: (U8, Refined { inner: U16Be, predicate: TagPred(EAPSUCCESSRESTEAP_LENGTH_CONST) }),
        mapper: EapSuccessRestMapper,
    })
}

                
pub fn eap_success_rest<'a>() -> (o: EapSuccessRestCombinator)
    ensures o@ == spec_eap_success_rest(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapSuccessRestCombinator(
    Mapped {
        inner: EapSuccessRestCombinator1((U8, Refined { inner: U16Be, predicate: TagPred(EAPSUCCESSRESTEAP_LENGTH_CONST) })),
        mapper: EapSuccessRestMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_success_rest()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_success_rest<'a>(input: &'a [u8]) -> (res: PResult<<EapSuccessRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_success_rest().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_success_rest().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_success_rest().spec_parse(input@) is None,
        spec_eap_success_rest().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_success_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_success_rest<'a>(v: <EapSuccessRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_success_rest().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_success_rest().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_success_rest().spec_serialize(v@))
        },
{
    let combinator = eap_success_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_success_rest_len<'a>(v: <EapSuccessRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_success_rest().wf(v@),
        spec_eap_success_rest().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_success_rest().spec_serialize(v@).len(),
{
    let combinator = eap_success_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecIpsecSpiSizeOrNone = u8;
pub type IpsecSpiSizeOrNone = u8;
pub type IpsecSpiSizeOrNoneRef<'a> = &'a u8;


pub struct SpecIpsecSpiSizeOrNoneCombinator(pub SpecIpsecSpiSizeOrNoneCombinatorAlias);

impl SpecCombinator for SpecIpsecSpiSizeOrNoneCombinator {
    type Type = SpecIpsecSpiSizeOrNone;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIpsecSpiSizeOrNoneCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIpsecSpiSizeOrNoneCombinatorAlias::is_prefix_secure() }
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
pub type SpecIpsecSpiSizeOrNoneCombinatorAlias = Refined<U8, Predicate15445621259281350129>;
pub struct Predicate15445621259281350129;
impl View for Predicate15445621259281350129 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15445621259281350129 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 4)
    }
}
impl SpecPred<u8> for Predicate15445621259281350129 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0) || (i == 4)
    }
}

pub struct IpsecSpiSizeOrNoneCombinator(pub IpsecSpiSizeOrNoneCombinatorAlias);

impl View for IpsecSpiSizeOrNoneCombinator {
    type V = SpecIpsecSpiSizeOrNoneCombinator;
    open spec fn view(&self) -> Self::V { SpecIpsecSpiSizeOrNoneCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IpsecSpiSizeOrNoneCombinator {
    type Type = IpsecSpiSizeOrNone;
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
pub type IpsecSpiSizeOrNoneCombinatorAlias = Refined<U8, Predicate15445621259281350129>;


pub open spec fn spec_ipsec_spi_size_or_none() -> SpecIpsecSpiSizeOrNoneCombinator {
    SpecIpsecSpiSizeOrNoneCombinator(Refined { inner: U8, predicate: Predicate15445621259281350129 })
}

                
pub fn ipsec_spi_size_or_none<'a>() -> (o: IpsecSpiSizeOrNoneCombinator)
    ensures o@ == spec_ipsec_spi_size_or_none(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IpsecSpiSizeOrNoneCombinator(Refined { inner: U8, predicate: Predicate15445621259281350129 });
    // assert({
    //     &&& combinator@ == spec_ipsec_spi_size_or_none()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ipsec_spi_size_or_none<'a>(input: &'a [u8]) -> (res: PResult<<IpsecSpiSizeOrNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ipsec_spi_size_or_none().spec_parse(input@) == Some((n as int, v@)),
        spec_ipsec_spi_size_or_none().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ipsec_spi_size_or_none().spec_parse(input@) is None,
        spec_ipsec_spi_size_or_none().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ipsec_spi_size_or_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ipsec_spi_size_or_none<'a>(v: <IpsecSpiSizeOrNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ipsec_spi_size_or_none().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ipsec_spi_size_or_none().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ipsec_spi_size_or_none().spec_serialize(v@))
        },
{
    let combinator = ipsec_spi_size_or_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ipsec_spi_size_or_none_len<'a>(v: <IpsecSpiSizeOrNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ipsec_spi_size_or_none().wf(v@),
        spec_ipsec_spi_size_or_none().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ipsec_spi_size_or_none().spec_serialize(v@).len(),
{
    let combinator = ipsec_spi_size_or_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod EapCode {
    use super::*;
    pub spec const SPEC_Request: u8 = 1;
    pub spec const SPEC_Response: u8 = 2;
    pub spec const SPEC_Success: u8 = 3;
    pub spec const SPEC_Failure: u8 = 4;
    pub exec const Request: u8 ensures Request == SPEC_Request { 1 }
    pub exec const Response: u8 ensures Response == SPEC_Response { 2 }
    pub exec const Success: u8 ensures Success == SPEC_Success { 3 }
    pub exec const Failure: u8 ensures Failure == SPEC_Failure { 4 }
}


pub struct SpecEapCodeCombinator(pub SpecEapCodeCombinatorAlias);

impl SpecCombinator for SpecEapCodeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapCodeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapCodeCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapCodeCombinatorAlias = U8;

pub struct EapCodeCombinator(pub EapCodeCombinatorAlias);

impl View for EapCodeCombinator {
    type V = SpecEapCodeCombinator;
    open spec fn view(&self) -> Self::V { SpecEapCodeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapCodeCombinator {
    type Type = u8;
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
pub type EapCodeCombinatorAlias = U8;


pub open spec fn spec_eap_code() -> SpecEapCodeCombinator {
    SpecEapCodeCombinator(U8)
}

                
pub fn eap_code<'a>() -> (o: EapCodeCombinator)
    ensures o@ == spec_eap_code(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapCodeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_eap_code()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_code<'a>(input: &'a [u8]) -> (res: PResult<<EapCodeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_code().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_code().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_code().spec_parse(input@) is None,
        spec_eap_code().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_code();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_code<'a>(v: <EapCodeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_code().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_code().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_code().spec_serialize(v@))
        },
{
    let combinator = eap_code();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_code_len<'a>(v: <EapCodeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_code().wf(v@),
        spec_eap_code().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_code().spec_serialize(v@).len(),
{
    let combinator = eap_code();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecEapFailureRest {
    pub identifier: u8,
    pub eap_length: u16,
}

pub type SpecEapFailureRestInner = (u8, u16);


impl SpecFrom<SpecEapFailureRest> for SpecEapFailureRestInner {
    open spec fn spec_from(m: SpecEapFailureRest) -> SpecEapFailureRestInner {
        (m.identifier, m.eap_length)
    }
}

impl SpecFrom<SpecEapFailureRestInner> for SpecEapFailureRest {
    open spec fn spec_from(m: SpecEapFailureRestInner) -> SpecEapFailureRest {
        let (identifier, eap_length) = m;
        SpecEapFailureRest { identifier, eap_length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapFailureRest {
    pub identifier: u8,
    pub eap_length: u16,
}

impl View for EapFailureRest {
    type V = SpecEapFailureRest;

    open spec fn view(&self) -> Self::V {
        SpecEapFailureRest {
            identifier: self.identifier@,
            eap_length: self.eap_length@,
        }
    }
}
pub type EapFailureRestInner = (u8, u16);

pub type EapFailureRestInnerRef<'a> = (&'a u8, &'a u16);
impl<'a> From<&'a EapFailureRest> for EapFailureRestInnerRef<'a> {
    fn ex_from(m: &'a EapFailureRest) -> EapFailureRestInnerRef<'a> {
        (&m.identifier, &m.eap_length)
    }
}

impl From<EapFailureRestInner> for EapFailureRest {
    fn ex_from(m: EapFailureRestInner) -> EapFailureRest {
        let (identifier, eap_length) = m;
        EapFailureRest { identifier, eap_length }
    }
}

pub struct EapFailureRestMapper;
impl View for EapFailureRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapFailureRestMapper {
    type Src = SpecEapFailureRestInner;
    type Dst = SpecEapFailureRest;
}
impl SpecIsoProof for EapFailureRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapFailureRestMapper {
    type Src = EapFailureRestInner;
    type Dst = EapFailureRest;
    type RefSrc = EapFailureRestInnerRef<'a>;
}
pub const EAPFAILURERESTEAP_LENGTH_CONST: u16 = 4;
type SpecEapFailureRestCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
pub struct SpecEapFailureRestCombinator(pub SpecEapFailureRestCombinatorAlias);

impl SpecCombinator for SpecEapFailureRestCombinator {
    type Type = SpecEapFailureRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapFailureRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapFailureRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapFailureRestCombinatorAlias = Mapped<SpecEapFailureRestCombinatorAlias1, EapFailureRestMapper>;
type EapFailureRestCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
pub struct EapFailureRestCombinator1(pub EapFailureRestCombinatorAlias1);
impl View for EapFailureRestCombinator1 {
    type V = SpecEapFailureRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapFailureRestCombinator1, EapFailureRestCombinatorAlias1);

pub struct EapFailureRestCombinator(pub EapFailureRestCombinatorAlias);

impl View for EapFailureRestCombinator {
    type V = SpecEapFailureRestCombinator;
    open spec fn view(&self) -> Self::V { SpecEapFailureRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapFailureRestCombinator {
    type Type = EapFailureRest;
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
pub type EapFailureRestCombinatorAlias = Mapped<EapFailureRestCombinator1, EapFailureRestMapper>;


pub open spec fn spec_eap_failure_rest() -> SpecEapFailureRestCombinator {
    SpecEapFailureRestCombinator(
    Mapped {
        inner: (U8, Refined { inner: U16Be, predicate: TagPred(EAPFAILURERESTEAP_LENGTH_CONST) }),
        mapper: EapFailureRestMapper,
    })
}

                
pub fn eap_failure_rest<'a>() -> (o: EapFailureRestCombinator)
    ensures o@ == spec_eap_failure_rest(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapFailureRestCombinator(
    Mapped {
        inner: EapFailureRestCombinator1((U8, Refined { inner: U16Be, predicate: TagPred(EAPFAILURERESTEAP_LENGTH_CONST) })),
        mapper: EapFailureRestMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_failure_rest()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_failure_rest<'a>(input: &'a [u8]) -> (res: PResult<<EapFailureRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_failure_rest().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_failure_rest().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_failure_rest().spec_parse(input@) is None,
        spec_eap_failure_rest().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_failure_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_failure_rest<'a>(v: <EapFailureRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_failure_rest().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_failure_rest().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_failure_rest().spec_serialize(v@))
        },
{
    let combinator = eap_failure_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_failure_rest_len<'a>(v: <EapFailureRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_failure_rest().wf(v@),
        spec_eap_failure_rest().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_failure_rest().spec_serialize(v@).len(),
{
    let combinator = eap_failure_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecEapReqRespRest {
    pub identifier: u8,
    pub eap_length: u16,
    pub eap_type: u8,
    pub type_data: Seq<u8>,
}

pub type SpecEapReqRespRestInner = ((u8, u16), (u8, Seq<u8>));


impl SpecFrom<SpecEapReqRespRest> for SpecEapReqRespRestInner {
    open spec fn spec_from(m: SpecEapReqRespRest) -> SpecEapReqRespRestInner {
        ((m.identifier, m.eap_length), (m.eap_type, m.type_data))
    }
}

impl SpecFrom<SpecEapReqRespRestInner> for SpecEapReqRespRest {
    open spec fn spec_from(m: SpecEapReqRespRestInner) -> SpecEapReqRespRest {
        let ((identifier, eap_length), (eap_type, type_data)) = m;
        SpecEapReqRespRest { identifier, eap_length, eap_type, type_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapReqRespRest<'a> {
    pub identifier: u8,
    pub eap_length: u16,
    pub eap_type: u8,
    pub type_data: &'a [u8],
}

impl View for EapReqRespRest<'_> {
    type V = SpecEapReqRespRest;

    open spec fn view(&self) -> Self::V {
        SpecEapReqRespRest {
            identifier: self.identifier@,
            eap_length: self.eap_length@,
            eap_type: self.eap_type@,
            type_data: self.type_data@,
        }
    }
}
pub type EapReqRespRestInner<'a> = ((u8, u16), (u8, &'a [u8]));

pub type EapReqRespRestInnerRef<'a> = ((&'a u8, &'a u16), (&'a u8, &'a &'a [u8]));
impl<'a> From<&'a EapReqRespRest<'a>> for EapReqRespRestInnerRef<'a> {
    fn ex_from(m: &'a EapReqRespRest) -> EapReqRespRestInnerRef<'a> {
        ((&m.identifier, &m.eap_length), (&m.eap_type, &m.type_data))
    }
}

impl<'a> From<EapReqRespRestInner<'a>> for EapReqRespRest<'a> {
    fn ex_from(m: EapReqRespRestInner) -> EapReqRespRest {
        let ((identifier, eap_length), (eap_type, type_data)) = m;
        EapReqRespRest { identifier, eap_length, eap_type, type_data }
    }
}

pub struct EapReqRespRestMapper;
impl View for EapReqRespRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapReqRespRestMapper {
    type Src = SpecEapReqRespRestInner;
    type Dst = SpecEapReqRespRest;
}
impl SpecIsoProof for EapReqRespRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapReqRespRestMapper {
    type Src = EapReqRespRestInner<'a>;
    type Dst = EapReqRespRest<'a>;
    type RefSrc = EapReqRespRestInnerRef<'a>;
}

pub struct SpecEapReqRespRestCombinator(pub SpecEapReqRespRestCombinatorAlias);

impl SpecCombinator for SpecEapReqRespRestCombinator {
    type Type = SpecEapReqRespRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapReqRespRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapReqRespRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapReqRespRestCombinatorAlias = Mapped<SpecPair<(U8, Refined<U16Be, Predicate7010197279221949030>), (U8, bytes::Variable)>, EapReqRespRestMapper>;
pub struct Predicate7010197279221949030;
impl View for Predicate7010197279221949030 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate7010197279221949030 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 5 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate7010197279221949030 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 5 && i <= 65535)
    }
}

pub struct EapReqRespRestCombinator(pub EapReqRespRestCombinatorAlias);

impl View for EapReqRespRestCombinator {
    type V = SpecEapReqRespRestCombinator;
    open spec fn view(&self) -> Self::V { SpecEapReqRespRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapReqRespRestCombinator {
    type Type = EapReqRespRest<'a>;
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
pub type EapReqRespRestCombinatorAlias = Mapped<Pair<(U8, Refined<U16Be, Predicate7010197279221949030>), (U8, bytes::Variable), EapReqRespRestCont0>, EapReqRespRestMapper>;


pub open spec fn spec_eap_req_resp_rest() -> SpecEapReqRespRestCombinator {
    SpecEapReqRespRestCombinator(
    Mapped {
        inner: Pair::spec_new((U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 }), |deps| spec_eap_req_resp_rest_cont0(deps)),
        mapper: EapReqRespRestMapper,
    })
}

pub open spec fn spec_eap_req_resp_rest_cont0(deps: (u8, u16)) -> (U8, bytes::Variable) {
    let (_, eap_length) = deps;
    (U8, bytes::Variable(((usize::spec_from(eap_length) - 5)) as usize))
}

impl View for EapReqRespRestCont0 {
    type V = spec_fn((u8, u16)) -> (U8, bytes::Variable);

    open spec fn view(&self) -> Self::V {
        |deps: (u8, u16)| {
            spec_eap_req_resp_rest_cont0(deps)
        }
    }
}

                
pub fn eap_req_resp_rest<'a>() -> (o: EapReqRespRestCombinator)
    ensures o@ == spec_eap_req_resp_rest(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapReqRespRestCombinator(
    Mapped {
        inner: Pair::new((U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 }), EapReqRespRestCont0),
        mapper: EapReqRespRestMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_req_resp_rest()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_req_resp_rest<'a>(input: &'a [u8]) -> (res: PResult<<EapReqRespRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_req_resp_rest().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_req_resp_rest().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_req_resp_rest().spec_parse(input@) is None,
        spec_eap_req_resp_rest().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_req_resp_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_req_resp_rest<'a>(v: <EapReqRespRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_req_resp_rest().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_req_resp_rest().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_req_resp_rest().spec_serialize(v@))
        },
{
    let combinator = eap_req_resp_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_req_resp_rest_len<'a>(v: <EapReqRespRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_req_resp_rest().wf(v@),
        spec_eap_req_resp_rest().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_req_resp_rest().spec_serialize(v@).len(),
{
    let combinator = eap_req_resp_rest();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct EapReqRespRestCont0;
type EapReqRespRestCont0Type<'a, 'b> = &'b (u8, u16);
type EapReqRespRestCont0SType<'a, 'x> = (&'x u8, &'x u16);
type EapReqRespRestCont0Input<'a, 'b, 'x> = POrSType<EapReqRespRestCont0Type<'a, 'b>, EapReqRespRestCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EapReqRespRestCont0Input<'a, 'b, 'x>> for EapReqRespRestCont0 {
    type Output = (U8, bytes::Variable);

    open spec fn requires(&self, deps: EapReqRespRestCont0Input<'a, 'b, 'x>) -> bool {
        &&& ((U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 })).wf(deps@)
        }

    open spec fn ensures(&self, deps: EapReqRespRestCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_eap_req_resp_rest_cont0(deps@)
    }

    fn apply(&self, deps: EapReqRespRestCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, eap_length) = deps;
                let eap_length = *eap_length;
                (U8, bytes::Variable(((usize::ex_from(eap_length) - 5)) as usize))
            }
            POrSType::S(deps) => {
                let (_, eap_length) = deps;
                let eap_length = *eap_length;
                (U8, bytes::Variable(((usize::ex_from(eap_length) - 5)) as usize))
            }
        }
    }
}
                

pub enum SpecIkev2EapPayloadInnerEapRest {
    Success(SpecEapSuccessRest),
    Failure(SpecEapFailureRest),
    Request(SpecEapReqRespRest),
    Response(SpecEapReqRespRest),
}

pub type SpecIkev2EapPayloadInnerEapRestInner = Either<SpecEapSuccessRest, Either<SpecEapFailureRest, Either<SpecEapReqRespRest, SpecEapReqRespRest>>>;

impl SpecFrom<SpecIkev2EapPayloadInnerEapRest> for SpecIkev2EapPayloadInnerEapRestInner {
    open spec fn spec_from(m: SpecIkev2EapPayloadInnerEapRest) -> SpecIkev2EapPayloadInnerEapRestInner {
        match m {
            SpecIkev2EapPayloadInnerEapRest::Success(m) => Either::Left(m),
            SpecIkev2EapPayloadInnerEapRest::Failure(m) => Either::Right(Either::Left(m)),
            SpecIkev2EapPayloadInnerEapRest::Request(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecIkev2EapPayloadInnerEapRest::Response(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecIkev2EapPayloadInnerEapRestInner> for SpecIkev2EapPayloadInnerEapRest {
    open spec fn spec_from(m: SpecIkev2EapPayloadInnerEapRestInner) -> SpecIkev2EapPayloadInnerEapRest {
        match m {
            Either::Left(m) => SpecIkev2EapPayloadInnerEapRest::Success(m),
            Either::Right(Either::Left(m)) => SpecIkev2EapPayloadInnerEapRest::Failure(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecIkev2EapPayloadInnerEapRest::Request(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecIkev2EapPayloadInnerEapRest::Response(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ikev2EapPayloadInnerEapRest<'a> {
    Success(EapSuccessRest),
    Failure(EapFailureRest),
    Request(EapReqRespRest<'a>),
    Response(EapReqRespRest<'a>),
}

pub type Ikev2EapPayloadInnerEapRestInner<'a> = Either<EapSuccessRest, Either<EapFailureRest, Either<EapReqRespRest<'a>, EapReqRespRest<'a>>>>;

pub type Ikev2EapPayloadInnerEapRestInnerRef<'a> = Either<&'a EapSuccessRest, Either<&'a EapFailureRest, Either<&'a EapReqRespRest<'a>, &'a EapReqRespRest<'a>>>>;


impl<'a> View for Ikev2EapPayloadInnerEapRest<'a> {
    type V = SpecIkev2EapPayloadInnerEapRest;
    open spec fn view(&self) -> Self::V {
        match self {
            Ikev2EapPayloadInnerEapRest::Success(m) => SpecIkev2EapPayloadInnerEapRest::Success(m@),
            Ikev2EapPayloadInnerEapRest::Failure(m) => SpecIkev2EapPayloadInnerEapRest::Failure(m@),
            Ikev2EapPayloadInnerEapRest::Request(m) => SpecIkev2EapPayloadInnerEapRest::Request(m@),
            Ikev2EapPayloadInnerEapRest::Response(m) => SpecIkev2EapPayloadInnerEapRest::Response(m@),
        }
    }
}


impl<'a> From<&'a Ikev2EapPayloadInnerEapRest<'a>> for Ikev2EapPayloadInnerEapRestInnerRef<'a> {
    fn ex_from(m: &'a Ikev2EapPayloadInnerEapRest<'a>) -> Ikev2EapPayloadInnerEapRestInnerRef<'a> {
        match m {
            Ikev2EapPayloadInnerEapRest::Success(m) => Either::Left(m),
            Ikev2EapPayloadInnerEapRest::Failure(m) => Either::Right(Either::Left(m)),
            Ikev2EapPayloadInnerEapRest::Request(m) => Either::Right(Either::Right(Either::Left(m))),
            Ikev2EapPayloadInnerEapRest::Response(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<Ikev2EapPayloadInnerEapRestInner<'a>> for Ikev2EapPayloadInnerEapRest<'a> {
    fn ex_from(m: Ikev2EapPayloadInnerEapRestInner<'a>) -> Ikev2EapPayloadInnerEapRest<'a> {
        match m {
            Either::Left(m) => Ikev2EapPayloadInnerEapRest::Success(m),
            Either::Right(Either::Left(m)) => Ikev2EapPayloadInnerEapRest::Failure(m),
            Either::Right(Either::Right(Either::Left(m))) => Ikev2EapPayloadInnerEapRest::Request(m),
            Either::Right(Either::Right(Either::Right(m))) => Ikev2EapPayloadInnerEapRest::Response(m),
        }
    }
    
}


pub struct Ikev2EapPayloadInnerEapRestMapper;
impl View for Ikev2EapPayloadInnerEapRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2EapPayloadInnerEapRestMapper {
    type Src = SpecIkev2EapPayloadInnerEapRestInner;
    type Dst = SpecIkev2EapPayloadInnerEapRest;
}
impl SpecIsoProof for Ikev2EapPayloadInnerEapRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2EapPayloadInnerEapRestMapper {
    type Src = Ikev2EapPayloadInnerEapRestInner<'a>;
    type Dst = Ikev2EapPayloadInnerEapRest<'a>;
    type RefSrc = Ikev2EapPayloadInnerEapRestInnerRef<'a>;
}

type SpecIkev2EapPayloadInnerEapRestCombinatorAlias1 = Choice<Cond<SpecEapReqRespRestCombinator>, Cond<SpecEapReqRespRestCombinator>>;
type SpecIkev2EapPayloadInnerEapRestCombinatorAlias2 = Choice<Cond<SpecEapFailureRestCombinator>, SpecIkev2EapPayloadInnerEapRestCombinatorAlias1>;
type SpecIkev2EapPayloadInnerEapRestCombinatorAlias3 = Choice<Cond<SpecEapSuccessRestCombinator>, SpecIkev2EapPayloadInnerEapRestCombinatorAlias2>;
pub struct SpecIkev2EapPayloadInnerEapRestCombinator(pub SpecIkev2EapPayloadInnerEapRestCombinatorAlias);

impl SpecCombinator for SpecIkev2EapPayloadInnerEapRestCombinator {
    type Type = SpecIkev2EapPayloadInnerEapRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2EapPayloadInnerEapRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2EapPayloadInnerEapRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2EapPayloadInnerEapRestCombinatorAlias = Mapped<SpecIkev2EapPayloadInnerEapRestCombinatorAlias3, Ikev2EapPayloadInnerEapRestMapper>;
type Ikev2EapPayloadInnerEapRestCombinatorAlias1 = Choice<Cond<EapReqRespRestCombinator>, Cond<EapReqRespRestCombinator>>;
type Ikev2EapPayloadInnerEapRestCombinatorAlias2 = Choice<Cond<EapFailureRestCombinator>, Ikev2EapPayloadInnerEapRestCombinator1>;
type Ikev2EapPayloadInnerEapRestCombinatorAlias3 = Choice<Cond<EapSuccessRestCombinator>, Ikev2EapPayloadInnerEapRestCombinator2>;
pub struct Ikev2EapPayloadInnerEapRestCombinator1(pub Ikev2EapPayloadInnerEapRestCombinatorAlias1);
impl View for Ikev2EapPayloadInnerEapRestCombinator1 {
    type V = SpecIkev2EapPayloadInnerEapRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2EapPayloadInnerEapRestCombinator1, Ikev2EapPayloadInnerEapRestCombinatorAlias1);

pub struct Ikev2EapPayloadInnerEapRestCombinator2(pub Ikev2EapPayloadInnerEapRestCombinatorAlias2);
impl View for Ikev2EapPayloadInnerEapRestCombinator2 {
    type V = SpecIkev2EapPayloadInnerEapRestCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2EapPayloadInnerEapRestCombinator2, Ikev2EapPayloadInnerEapRestCombinatorAlias2);

pub struct Ikev2EapPayloadInnerEapRestCombinator3(pub Ikev2EapPayloadInnerEapRestCombinatorAlias3);
impl View for Ikev2EapPayloadInnerEapRestCombinator3 {
    type V = SpecIkev2EapPayloadInnerEapRestCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2EapPayloadInnerEapRestCombinator3, Ikev2EapPayloadInnerEapRestCombinatorAlias3);

pub struct Ikev2EapPayloadInnerEapRestCombinator(pub Ikev2EapPayloadInnerEapRestCombinatorAlias);

impl View for Ikev2EapPayloadInnerEapRestCombinator {
    type V = SpecIkev2EapPayloadInnerEapRestCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2EapPayloadInnerEapRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2EapPayloadInnerEapRestCombinator {
    type Type = Ikev2EapPayloadInnerEapRest<'a>;
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
pub type Ikev2EapPayloadInnerEapRestCombinatorAlias = Mapped<Ikev2EapPayloadInnerEapRestCombinator3, Ikev2EapPayloadInnerEapRestMapper>;


pub open spec fn spec_ikev2_eap_payload_inner_eap_rest(code: u8) -> SpecIkev2EapPayloadInnerEapRestCombinator {
    SpecIkev2EapPayloadInnerEapRestCombinator(Mapped { inner: Choice(Cond { cond: code == EapCode::SPEC_Success, inner: spec_eap_success_rest() }, Choice(Cond { cond: code == EapCode::SPEC_Failure, inner: spec_eap_failure_rest() }, Choice(Cond { cond: code == EapCode::SPEC_Request, inner: spec_eap_req_resp_rest() }, Cond { cond: code == EapCode::SPEC_Response, inner: spec_eap_req_resp_rest() }))), mapper: Ikev2EapPayloadInnerEapRestMapper })
}

pub fn ikev2_eap_payload_inner_eap_rest<'a>(code: u8) -> (o: Ikev2EapPayloadInnerEapRestCombinator)
    requires
        spec_eap_code().wf(code@),

    ensures o@ == spec_ikev2_eap_payload_inner_eap_rest(code@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2EapPayloadInnerEapRestCombinator(Mapped { inner: Ikev2EapPayloadInnerEapRestCombinator3(Choice::new(Cond { cond: code == EapCode::Success, inner: eap_success_rest() }, Ikev2EapPayloadInnerEapRestCombinator2(Choice::new(Cond { cond: code == EapCode::Failure, inner: eap_failure_rest() }, Ikev2EapPayloadInnerEapRestCombinator1(Choice::new(Cond { cond: code == EapCode::Request, inner: eap_req_resp_rest() }, Cond { cond: code == EapCode::Response, inner: eap_req_resp_rest() })))))), mapper: Ikev2EapPayloadInnerEapRestMapper });
    // assert({
    //     &&& combinator@ == spec_ikev2_eap_payload_inner_eap_rest(code@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_eap_payload_inner_eap_rest<'a>(input: &'a [u8], code: u8) -> (res: PResult<<Ikev2EapPayloadInnerEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_eap_code().wf(code@),

    ensures
        res matches Ok((n, v)) ==> spec_ikev2_eap_payload_inner_eap_rest(code@).spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_eap_payload_inner_eap_rest(code@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_eap_payload_inner_eap_rest(code@).spec_parse(input@) is None,
        spec_ikev2_eap_payload_inner_eap_rest(code@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_eap_payload_inner_eap_rest( code );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_eap_payload_inner_eap_rest<'a>(v: <Ikev2EapPayloadInnerEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, code: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_eap_payload_inner_eap_rest(code@).wf(v@),
        spec_eap_code().wf(code@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_eap_payload_inner_eap_rest(code@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_eap_payload_inner_eap_rest(code@).spec_serialize(v@))
        },
{
    let combinator = ikev2_eap_payload_inner_eap_rest( code );
    combinator.serialize(v, data, pos)
}

pub fn ikev2_eap_payload_inner_eap_rest_len<'a>(v: <Ikev2EapPayloadInnerEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, code: u8) -> (serialize_len: usize)
    requires
        spec_ikev2_eap_payload_inner_eap_rest(code@).wf(v@),
        spec_ikev2_eap_payload_inner_eap_rest(code@).spec_serialize(v@).len() <= usize::MAX,
        spec_eap_code().wf(code@),

    ensures
        serialize_len == spec_ikev2_eap_payload_inner_eap_rest(code@).spec_serialize(v@).len(),
{
    let combinator = ikev2_eap_payload_inner_eap_rest( code );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecIkev2EapPayloadInner {
    pub code: u8,
    pub eap_rest: SpecIkev2EapPayloadInnerEapRest,
}

pub type SpecIkev2EapPayloadInnerInner = (u8, SpecIkev2EapPayloadInnerEapRest);


impl SpecFrom<SpecIkev2EapPayloadInner> for SpecIkev2EapPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2EapPayloadInner) -> SpecIkev2EapPayloadInnerInner {
        (m.code, m.eap_rest)
    }
}

impl SpecFrom<SpecIkev2EapPayloadInnerInner> for SpecIkev2EapPayloadInner {
    open spec fn spec_from(m: SpecIkev2EapPayloadInnerInner) -> SpecIkev2EapPayloadInner {
        let (code, eap_rest) = m;
        SpecIkev2EapPayloadInner { code, eap_rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2EapPayloadInner<'a> {
    pub code: u8,
    pub eap_rest: Ikev2EapPayloadInnerEapRest<'a>,
}

impl View for Ikev2EapPayloadInner<'_> {
    type V = SpecIkev2EapPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2EapPayloadInner {
            code: self.code@,
            eap_rest: self.eap_rest@,
        }
    }
}
pub type Ikev2EapPayloadInnerInner<'a> = (u8, Ikev2EapPayloadInnerEapRest<'a>);

pub type Ikev2EapPayloadInnerInnerRef<'a> = (&'a u8, &'a Ikev2EapPayloadInnerEapRest<'a>);
impl<'a> From<&'a Ikev2EapPayloadInner<'a>> for Ikev2EapPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2EapPayloadInner) -> Ikev2EapPayloadInnerInnerRef<'a> {
        (&m.code, &m.eap_rest)
    }
}

impl<'a> From<Ikev2EapPayloadInnerInner<'a>> for Ikev2EapPayloadInner<'a> {
    fn ex_from(m: Ikev2EapPayloadInnerInner) -> Ikev2EapPayloadInner {
        let (code, eap_rest) = m;
        Ikev2EapPayloadInner { code, eap_rest }
    }
}

pub struct Ikev2EapPayloadInnerMapper;
impl View for Ikev2EapPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2EapPayloadInnerMapper {
    type Src = SpecIkev2EapPayloadInnerInner;
    type Dst = SpecIkev2EapPayloadInner;
}
impl SpecIsoProof for Ikev2EapPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2EapPayloadInnerMapper {
    type Src = Ikev2EapPayloadInnerInner<'a>;
    type Dst = Ikev2EapPayloadInner<'a>;
    type RefSrc = Ikev2EapPayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2EapPayloadInnerCombinator(pub SpecIkev2EapPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2EapPayloadInnerCombinator {
    type Type = SpecIkev2EapPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2EapPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2EapPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2EapPayloadInnerCombinatorAlias = Mapped<SpecPair<SpecEapCodeCombinator, SpecIkev2EapPayloadInnerEapRestCombinator>, Ikev2EapPayloadInnerMapper>;

pub struct Ikev2EapPayloadInnerCombinator(pub Ikev2EapPayloadInnerCombinatorAlias);

impl View for Ikev2EapPayloadInnerCombinator {
    type V = SpecIkev2EapPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2EapPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2EapPayloadInnerCombinator {
    type Type = Ikev2EapPayloadInner<'a>;
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
pub type Ikev2EapPayloadInnerCombinatorAlias = Mapped<Pair<EapCodeCombinator, Ikev2EapPayloadInnerEapRestCombinator, Ikev2EapPayloadInnerCont0>, Ikev2EapPayloadInnerMapper>;


pub open spec fn spec_ikev2_eap_payload_inner() -> SpecIkev2EapPayloadInnerCombinator {
    SpecIkev2EapPayloadInnerCombinator(
    Mapped {
        inner: Pair::spec_new(spec_eap_code(), |deps| spec_ikev2_eap_payload_inner_cont0(deps)),
        mapper: Ikev2EapPayloadInnerMapper,
    })
}

pub open spec fn spec_ikev2_eap_payload_inner_cont0(deps: u8) -> SpecIkev2EapPayloadInnerEapRestCombinator {
    let code = deps;
    spec_ikev2_eap_payload_inner_eap_rest(code)
}

impl View for Ikev2EapPayloadInnerCont0 {
    type V = spec_fn(u8) -> SpecIkev2EapPayloadInnerEapRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_ikev2_eap_payload_inner_cont0(deps)
        }
    }
}

                
pub fn ikev2_eap_payload_inner<'a>() -> (o: Ikev2EapPayloadInnerCombinator)
    ensures o@ == spec_ikev2_eap_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2EapPayloadInnerCombinator(
    Mapped {
        inner: Pair::new(eap_code(), Ikev2EapPayloadInnerCont0),
        mapper: Ikev2EapPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_eap_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_eap_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2EapPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_eap_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_eap_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_eap_payload_inner().spec_parse(input@) is None,
        spec_ikev2_eap_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_eap_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_eap_payload_inner<'a>(v: <Ikev2EapPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_eap_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_eap_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_eap_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_eap_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_eap_payload_inner_len<'a>(v: <Ikev2EapPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_eap_payload_inner().wf(v@),
        spec_ikev2_eap_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_eap_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_eap_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Ikev2EapPayloadInnerCont0;
type Ikev2EapPayloadInnerCont0Type<'a, 'b> = &'b u8;
type Ikev2EapPayloadInnerCont0SType<'a, 'x> = &'x u8;
type Ikev2EapPayloadInnerCont0Input<'a, 'b, 'x> = POrSType<Ikev2EapPayloadInnerCont0Type<'a, 'b>, Ikev2EapPayloadInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Ikev2EapPayloadInnerCont0Input<'a, 'b, 'x>> for Ikev2EapPayloadInnerCont0 {
    type Output = Ikev2EapPayloadInnerEapRestCombinator;

    open spec fn requires(&self, deps: Ikev2EapPayloadInnerCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_eap_code()).wf(deps@)
        }

    open spec fn ensures(&self, deps: Ikev2EapPayloadInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ikev2_eap_payload_inner_cont0(deps@)
    }

    fn apply(&self, deps: Ikev2EapPayloadInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let code = deps;
                let code = *code;
                ikev2_eap_payload_inner_eap_rest(code)
            }
            POrSType::S(deps) => {
                let code = deps;
                let code = *code;
                ikev2_eap_payload_inner_eap_rest(code)
            }
        }
    }
}
                
pub mod CertEncoding {
    use super::*;
    pub spec const SPEC_PKCS7WrappedX509: u8 = 1;
    pub spec const SPEC_PGPCert: u8 = 2;
    pub spec const SPEC_DNSSignedKey: u8 = 3;
    pub spec const SPEC_X509CertSig: u8 = 4;
    pub spec const SPEC_KerberosToken: u8 = 6;
    pub spec const SPEC_CRL: u8 = 7;
    pub spec const SPEC_ARL: u8 = 8;
    pub spec const SPEC_SPKICert: u8 = 9;
    pub spec const SPEC_X509CertAttr: u8 = 10;
    pub spec const SPEC_RawRSAKey: u8 = 11;
    pub spec const SPEC_HashAndURLX509: u8 = 12;
    pub spec const SPEC_HashAndURLBundle: u8 = 13;
    pub exec const PKCS7WrappedX509: u8 ensures PKCS7WrappedX509 == SPEC_PKCS7WrappedX509 { 1 }
    pub exec const PGPCert: u8 ensures PGPCert == SPEC_PGPCert { 2 }
    pub exec const DNSSignedKey: u8 ensures DNSSignedKey == SPEC_DNSSignedKey { 3 }
    pub exec const X509CertSig: u8 ensures X509CertSig == SPEC_X509CertSig { 4 }
    pub exec const KerberosToken: u8 ensures KerberosToken == SPEC_KerberosToken { 6 }
    pub exec const CRL: u8 ensures CRL == SPEC_CRL { 7 }
    pub exec const ARL: u8 ensures ARL == SPEC_ARL { 8 }
    pub exec const SPKICert: u8 ensures SPKICert == SPEC_SPKICert { 9 }
    pub exec const X509CertAttr: u8 ensures X509CertAttr == SPEC_X509CertAttr { 10 }
    pub exec const RawRSAKey: u8 ensures RawRSAKey == SPEC_RawRSAKey { 11 }
    pub exec const HashAndURLX509: u8 ensures HashAndURLX509 == SPEC_HashAndURLX509 { 12 }
    pub exec const HashAndURLBundle: u8 ensures HashAndURLBundle == SPEC_HashAndURLBundle { 13 }
}


pub struct SpecCertEncodingCombinator(pub SpecCertEncodingCombinatorAlias);

impl SpecCombinator for SpecCertEncodingCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertEncodingCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCertEncodingCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertEncodingCombinatorAlias = U8;

pub struct CertEncodingCombinator(pub CertEncodingCombinatorAlias);

impl View for CertEncodingCombinator {
    type V = SpecCertEncodingCombinator;
    open spec fn view(&self) -> Self::V { SpecCertEncodingCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertEncodingCombinator {
    type Type = u8;
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
pub type CertEncodingCombinatorAlias = U8;


pub open spec fn spec_cert_encoding() -> SpecCertEncodingCombinator {
    SpecCertEncodingCombinator(U8)
}

                
pub fn cert_encoding<'a>() -> (o: CertEncodingCombinator)
    ensures o@ == spec_cert_encoding(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CertEncodingCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_cert_encoding()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cert_encoding<'a>(input: &'a [u8]) -> (res: PResult<<CertEncodingCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_cert_encoding().spec_parse(input@) == Some((n as int, v@)),
        spec_cert_encoding().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cert_encoding().spec_parse(input@) is None,
        spec_cert_encoding().spec_parse(input@) is None ==> res is Err,
{
    let combinator = cert_encoding();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cert_encoding<'a>(v: <CertEncodingCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cert_encoding().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cert_encoding().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cert_encoding().spec_serialize(v@))
        },
{
    let combinator = cert_encoding();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn cert_encoding_len<'a>(v: <CertEncodingCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_cert_encoding().wf(v@),
        spec_cert_encoding().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_cert_encoding().spec_serialize(v@).len(),
{
    let combinator = cert_encoding();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCertreqPayloadBody {
    pub cert_encoding: u8,
    pub ca_data: Seq<u8>,
}

pub type SpecCertreqPayloadBodyInner = (u8, Seq<u8>);


impl SpecFrom<SpecCertreqPayloadBody> for SpecCertreqPayloadBodyInner {
    open spec fn spec_from(m: SpecCertreqPayloadBody) -> SpecCertreqPayloadBodyInner {
        (m.cert_encoding, m.ca_data)
    }
}

impl SpecFrom<SpecCertreqPayloadBodyInner> for SpecCertreqPayloadBody {
    open spec fn spec_from(m: SpecCertreqPayloadBodyInner) -> SpecCertreqPayloadBody {
        let (cert_encoding, ca_data) = m;
        SpecCertreqPayloadBody { cert_encoding, ca_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertreqPayloadBody<'a> {
    pub cert_encoding: u8,
    pub ca_data: &'a [u8],
}

impl View for CertreqPayloadBody<'_> {
    type V = SpecCertreqPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecCertreqPayloadBody {
            cert_encoding: self.cert_encoding@,
            ca_data: self.ca_data@,
        }
    }
}
pub type CertreqPayloadBodyInner<'a> = (u8, &'a [u8]);

pub type CertreqPayloadBodyInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CertreqPayloadBody<'a>> for CertreqPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a CertreqPayloadBody) -> CertreqPayloadBodyInnerRef<'a> {
        (&m.cert_encoding, &m.ca_data)
    }
}

impl<'a> From<CertreqPayloadBodyInner<'a>> for CertreqPayloadBody<'a> {
    fn ex_from(m: CertreqPayloadBodyInner) -> CertreqPayloadBody {
        let (cert_encoding, ca_data) = m;
        CertreqPayloadBody { cert_encoding, ca_data }
    }
}

pub struct CertreqPayloadBodyMapper;
impl View for CertreqPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertreqPayloadBodyMapper {
    type Src = SpecCertreqPayloadBodyInner;
    type Dst = SpecCertreqPayloadBody;
}
impl SpecIsoProof for CertreqPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertreqPayloadBodyMapper {
    type Src = CertreqPayloadBodyInner<'a>;
    type Dst = CertreqPayloadBody<'a>;
    type RefSrc = CertreqPayloadBodyInnerRef<'a>;
}
type SpecCertreqPayloadBodyCombinatorAlias1 = (SpecCertEncodingCombinator, bytes::Variable);
pub struct SpecCertreqPayloadBodyCombinator(pub SpecCertreqPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecCertreqPayloadBodyCombinator {
    type Type = SpecCertreqPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertreqPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCertreqPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertreqPayloadBodyCombinatorAlias = Mapped<SpecCertreqPayloadBodyCombinatorAlias1, CertreqPayloadBodyMapper>;
type CertreqPayloadBodyCombinatorAlias1 = (CertEncodingCombinator, bytes::Variable);
pub struct CertreqPayloadBodyCombinator1(pub CertreqPayloadBodyCombinatorAlias1);
impl View for CertreqPayloadBodyCombinator1 {
    type V = SpecCertreqPayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertreqPayloadBodyCombinator1, CertreqPayloadBodyCombinatorAlias1);

pub struct CertreqPayloadBodyCombinator(pub CertreqPayloadBodyCombinatorAlias);

impl View for CertreqPayloadBodyCombinator {
    type V = SpecCertreqPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecCertreqPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertreqPayloadBodyCombinator {
    type Type = CertreqPayloadBody<'a>;
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
pub type CertreqPayloadBodyCombinatorAlias = Mapped<CertreqPayloadBodyCombinator1, CertreqPayloadBodyMapper>;


pub open spec fn spec_certreq_payload_body(payload_length: u16) -> SpecCertreqPayloadBodyCombinator {
    SpecCertreqPayloadBodyCombinator(
    Mapped {
        inner: (spec_cert_encoding(), bytes::Variable(((usize::spec_from(payload_length) - 5)) as usize)),
        mapper: CertreqPayloadBodyMapper,
    })
}

pub fn certreq_payload_body<'a>(payload_length: u16) -> (o: CertreqPayloadBodyCombinator)
    requires
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures o@ == spec_certreq_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CertreqPayloadBodyCombinator(
    Mapped {
        inner: CertreqPayloadBodyCombinator1((cert_encoding(), bytes::Variable(((usize::ex_from(payload_length) - 5)) as usize))),
        mapper: CertreqPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_certreq_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_certreq_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<CertreqPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_certreq_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_certreq_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_certreq_payload_body(payload_length@).spec_parse(input@) is None,
        spec_certreq_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = certreq_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_certreq_payload_body<'a>(v: <CertreqPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_certreq_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_certreq_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_certreq_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = certreq_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn certreq_payload_body_len<'a>(v: <CertreqPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_certreq_payload_body(payload_length@).wf(v@),
        spec_certreq_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_certreq_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = certreq_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecEapPayloadBodyEapRest {
    Success(SpecEapSuccessRest),
    Failure(SpecEapFailureRest),
    Request(SpecEapReqRespRest),
    Response(SpecEapReqRespRest),
}

pub type SpecEapPayloadBodyEapRestInner = Either<SpecEapSuccessRest, Either<SpecEapFailureRest, Either<SpecEapReqRespRest, SpecEapReqRespRest>>>;

impl SpecFrom<SpecEapPayloadBodyEapRest> for SpecEapPayloadBodyEapRestInner {
    open spec fn spec_from(m: SpecEapPayloadBodyEapRest) -> SpecEapPayloadBodyEapRestInner {
        match m {
            SpecEapPayloadBodyEapRest::Success(m) => Either::Left(m),
            SpecEapPayloadBodyEapRest::Failure(m) => Either::Right(Either::Left(m)),
            SpecEapPayloadBodyEapRest::Request(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecEapPayloadBodyEapRest::Response(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecEapPayloadBodyEapRestInner> for SpecEapPayloadBodyEapRest {
    open spec fn spec_from(m: SpecEapPayloadBodyEapRestInner) -> SpecEapPayloadBodyEapRest {
        match m {
            Either::Left(m) => SpecEapPayloadBodyEapRest::Success(m),
            Either::Right(Either::Left(m)) => SpecEapPayloadBodyEapRest::Failure(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecEapPayloadBodyEapRest::Request(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecEapPayloadBodyEapRest::Response(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EapPayloadBodyEapRest<'a> {
    Success(EapSuccessRest),
    Failure(EapFailureRest),
    Request(EapReqRespRest<'a>),
    Response(EapReqRespRest<'a>),
}

pub type EapPayloadBodyEapRestInner<'a> = Either<EapSuccessRest, Either<EapFailureRest, Either<EapReqRespRest<'a>, EapReqRespRest<'a>>>>;

pub type EapPayloadBodyEapRestInnerRef<'a> = Either<&'a EapSuccessRest, Either<&'a EapFailureRest, Either<&'a EapReqRespRest<'a>, &'a EapReqRespRest<'a>>>>;


impl<'a> View for EapPayloadBodyEapRest<'a> {
    type V = SpecEapPayloadBodyEapRest;
    open spec fn view(&self) -> Self::V {
        match self {
            EapPayloadBodyEapRest::Success(m) => SpecEapPayloadBodyEapRest::Success(m@),
            EapPayloadBodyEapRest::Failure(m) => SpecEapPayloadBodyEapRest::Failure(m@),
            EapPayloadBodyEapRest::Request(m) => SpecEapPayloadBodyEapRest::Request(m@),
            EapPayloadBodyEapRest::Response(m) => SpecEapPayloadBodyEapRest::Response(m@),
        }
    }
}


impl<'a> From<&'a EapPayloadBodyEapRest<'a>> for EapPayloadBodyEapRestInnerRef<'a> {
    fn ex_from(m: &'a EapPayloadBodyEapRest<'a>) -> EapPayloadBodyEapRestInnerRef<'a> {
        match m {
            EapPayloadBodyEapRest::Success(m) => Either::Left(m),
            EapPayloadBodyEapRest::Failure(m) => Either::Right(Either::Left(m)),
            EapPayloadBodyEapRest::Request(m) => Either::Right(Either::Right(Either::Left(m))),
            EapPayloadBodyEapRest::Response(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<EapPayloadBodyEapRestInner<'a>> for EapPayloadBodyEapRest<'a> {
    fn ex_from(m: EapPayloadBodyEapRestInner<'a>) -> EapPayloadBodyEapRest<'a> {
        match m {
            Either::Left(m) => EapPayloadBodyEapRest::Success(m),
            Either::Right(Either::Left(m)) => EapPayloadBodyEapRest::Failure(m),
            Either::Right(Either::Right(Either::Left(m))) => EapPayloadBodyEapRest::Request(m),
            Either::Right(Either::Right(Either::Right(m))) => EapPayloadBodyEapRest::Response(m),
        }
    }
    
}


pub struct EapPayloadBodyEapRestMapper;
impl View for EapPayloadBodyEapRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapPayloadBodyEapRestMapper {
    type Src = SpecEapPayloadBodyEapRestInner;
    type Dst = SpecEapPayloadBodyEapRest;
}
impl SpecIsoProof for EapPayloadBodyEapRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapPayloadBodyEapRestMapper {
    type Src = EapPayloadBodyEapRestInner<'a>;
    type Dst = EapPayloadBodyEapRest<'a>;
    type RefSrc = EapPayloadBodyEapRestInnerRef<'a>;
}

type SpecEapPayloadBodyEapRestCombinatorAlias1 = Choice<Cond<SpecEapReqRespRestCombinator>, Cond<SpecEapReqRespRestCombinator>>;
type SpecEapPayloadBodyEapRestCombinatorAlias2 = Choice<Cond<SpecEapFailureRestCombinator>, SpecEapPayloadBodyEapRestCombinatorAlias1>;
type SpecEapPayloadBodyEapRestCombinatorAlias3 = Choice<Cond<SpecEapSuccessRestCombinator>, SpecEapPayloadBodyEapRestCombinatorAlias2>;
pub struct SpecEapPayloadBodyEapRestCombinator(pub SpecEapPayloadBodyEapRestCombinatorAlias);

impl SpecCombinator for SpecEapPayloadBodyEapRestCombinator {
    type Type = SpecEapPayloadBodyEapRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapPayloadBodyEapRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapPayloadBodyEapRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapPayloadBodyEapRestCombinatorAlias = Mapped<SpecEapPayloadBodyEapRestCombinatorAlias3, EapPayloadBodyEapRestMapper>;
type EapPayloadBodyEapRestCombinatorAlias1 = Choice<Cond<EapReqRespRestCombinator>, Cond<EapReqRespRestCombinator>>;
type EapPayloadBodyEapRestCombinatorAlias2 = Choice<Cond<EapFailureRestCombinator>, EapPayloadBodyEapRestCombinator1>;
type EapPayloadBodyEapRestCombinatorAlias3 = Choice<Cond<EapSuccessRestCombinator>, EapPayloadBodyEapRestCombinator2>;
pub struct EapPayloadBodyEapRestCombinator1(pub EapPayloadBodyEapRestCombinatorAlias1);
impl View for EapPayloadBodyEapRestCombinator1 {
    type V = SpecEapPayloadBodyEapRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapPayloadBodyEapRestCombinator1, EapPayloadBodyEapRestCombinatorAlias1);

pub struct EapPayloadBodyEapRestCombinator2(pub EapPayloadBodyEapRestCombinatorAlias2);
impl View for EapPayloadBodyEapRestCombinator2 {
    type V = SpecEapPayloadBodyEapRestCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapPayloadBodyEapRestCombinator2, EapPayloadBodyEapRestCombinatorAlias2);

pub struct EapPayloadBodyEapRestCombinator3(pub EapPayloadBodyEapRestCombinatorAlias3);
impl View for EapPayloadBodyEapRestCombinator3 {
    type V = SpecEapPayloadBodyEapRestCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapPayloadBodyEapRestCombinator3, EapPayloadBodyEapRestCombinatorAlias3);

pub struct EapPayloadBodyEapRestCombinator(pub EapPayloadBodyEapRestCombinatorAlias);

impl View for EapPayloadBodyEapRestCombinator {
    type V = SpecEapPayloadBodyEapRestCombinator;
    open spec fn view(&self) -> Self::V { SpecEapPayloadBodyEapRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapPayloadBodyEapRestCombinator {
    type Type = EapPayloadBodyEapRest<'a>;
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
pub type EapPayloadBodyEapRestCombinatorAlias = Mapped<EapPayloadBodyEapRestCombinator3, EapPayloadBodyEapRestMapper>;


pub open spec fn spec_eap_payload_body_eap_rest(code: u8) -> SpecEapPayloadBodyEapRestCombinator {
    SpecEapPayloadBodyEapRestCombinator(Mapped { inner: Choice(Cond { cond: code == EapCode::SPEC_Success, inner: spec_eap_success_rest() }, Choice(Cond { cond: code == EapCode::SPEC_Failure, inner: spec_eap_failure_rest() }, Choice(Cond { cond: code == EapCode::SPEC_Request, inner: spec_eap_req_resp_rest() }, Cond { cond: code == EapCode::SPEC_Response, inner: spec_eap_req_resp_rest() }))), mapper: EapPayloadBodyEapRestMapper })
}

pub fn eap_payload_body_eap_rest<'a>(code: u8) -> (o: EapPayloadBodyEapRestCombinator)
    requires
        spec_eap_code().wf(code@),

    ensures o@ == spec_eap_payload_body_eap_rest(code@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapPayloadBodyEapRestCombinator(Mapped { inner: EapPayloadBodyEapRestCombinator3(Choice::new(Cond { cond: code == EapCode::Success, inner: eap_success_rest() }, EapPayloadBodyEapRestCombinator2(Choice::new(Cond { cond: code == EapCode::Failure, inner: eap_failure_rest() }, EapPayloadBodyEapRestCombinator1(Choice::new(Cond { cond: code == EapCode::Request, inner: eap_req_resp_rest() }, Cond { cond: code == EapCode::Response, inner: eap_req_resp_rest() })))))), mapper: EapPayloadBodyEapRestMapper });
    // assert({
    //     &&& combinator@ == spec_eap_payload_body_eap_rest(code@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_payload_body_eap_rest<'a>(input: &'a [u8], code: u8) -> (res: PResult<<EapPayloadBodyEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_eap_code().wf(code@),

    ensures
        res matches Ok((n, v)) ==> spec_eap_payload_body_eap_rest(code@).spec_parse(input@) == Some((n as int, v@)),
        spec_eap_payload_body_eap_rest(code@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_payload_body_eap_rest(code@).spec_parse(input@) is None,
        spec_eap_payload_body_eap_rest(code@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_payload_body_eap_rest( code );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_payload_body_eap_rest<'a>(v: <EapPayloadBodyEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, code: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_payload_body_eap_rest(code@).wf(v@),
        spec_eap_code().wf(code@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_payload_body_eap_rest(code@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_payload_body_eap_rest(code@).spec_serialize(v@))
        },
{
    let combinator = eap_payload_body_eap_rest( code );
    combinator.serialize(v, data, pos)
}

pub fn eap_payload_body_eap_rest_len<'a>(v: <EapPayloadBodyEapRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, code: u8) -> (serialize_len: usize)
    requires
        spec_eap_payload_body_eap_rest(code@).wf(v@),
        spec_eap_payload_body_eap_rest(code@).spec_serialize(v@).len() <= usize::MAX,
        spec_eap_code().wf(code@),

    ensures
        serialize_len == spec_eap_payload_body_eap_rest(code@).spec_serialize(v@).len(),
{
    let combinator = eap_payload_body_eap_rest( code );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub mod CfgType {
    use super::*;
    pub spec const SPEC_CFG_REQUEST: u8 = 1;
    pub spec const SPEC_CFG_REPLY: u8 = 2;
    pub spec const SPEC_CFG_SET: u8 = 3;
    pub spec const SPEC_CFG_ACK: u8 = 4;
    pub exec const CFG_REQUEST: u8 ensures CFG_REQUEST == SPEC_CFG_REQUEST { 1 }
    pub exec const CFG_REPLY: u8 ensures CFG_REPLY == SPEC_CFG_REPLY { 2 }
    pub exec const CFG_SET: u8 ensures CFG_SET == SPEC_CFG_SET { 3 }
    pub exec const CFG_ACK: u8 ensures CFG_ACK == SPEC_CFG_ACK { 4 }
}


pub struct SpecCfgTypeCombinator(pub SpecCfgTypeCombinatorAlias);

impl SpecCombinator for SpecCfgTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCfgTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCfgTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecCfgTypeCombinatorAlias = U8;

pub struct CfgTypeCombinator(pub CfgTypeCombinatorAlias);

impl View for CfgTypeCombinator {
    type V = SpecCfgTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecCfgTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CfgTypeCombinator {
    type Type = u8;
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
pub type CfgTypeCombinatorAlias = U8;


pub open spec fn spec_cfg_type() -> SpecCfgTypeCombinator {
    SpecCfgTypeCombinator(U8)
}

                
pub fn cfg_type<'a>() -> (o: CfgTypeCombinator)
    ensures o@ == spec_cfg_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CfgTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_cfg_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cfg_type<'a>(input: &'a [u8]) -> (res: PResult<<CfgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_cfg_type().spec_parse(input@) == Some((n as int, v@)),
        spec_cfg_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cfg_type().spec_parse(input@) is None,
        spec_cfg_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = cfg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cfg_type<'a>(v: <CfgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cfg_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cfg_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cfg_type().spec_serialize(v@))
        },
{
    let combinator = cfg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn cfg_type_len<'a>(v: <CfgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_cfg_type().wf(v@),
        spec_cfg_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_cfg_type().spec_serialize(v@).len(),
{
    let combinator = cfg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCpPayloadBody {
    pub cfg_type: u8,
    pub reserved: Seq<u8>,
    pub attributes: Seq<SpecCfgAttribute>,
}

pub type SpecCpPayloadBodyInner = (u8, (Seq<u8>, Seq<SpecCfgAttribute>));


impl SpecFrom<SpecCpPayloadBody> for SpecCpPayloadBodyInner {
    open spec fn spec_from(m: SpecCpPayloadBody) -> SpecCpPayloadBodyInner {
        (m.cfg_type, (m.reserved, m.attributes))
    }
}

impl SpecFrom<SpecCpPayloadBodyInner> for SpecCpPayloadBody {
    open spec fn spec_from(m: SpecCpPayloadBodyInner) -> SpecCpPayloadBody {
        let (cfg_type, (reserved, attributes)) = m;
        SpecCpPayloadBody { cfg_type, reserved, attributes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CpPayloadBody<'a> {
    pub cfg_type: u8,
    pub reserved: &'a [u8],
    pub attributes: RepeatResult<CfgAttribute<'a>>,
}

impl View for CpPayloadBody<'_> {
    type V = SpecCpPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecCpPayloadBody {
            cfg_type: self.cfg_type@,
            reserved: self.reserved@,
            attributes: self.attributes@,
        }
    }
}
pub type CpPayloadBodyInner<'a> = (u8, (&'a [u8], RepeatResult<CfgAttribute<'a>>));

pub type CpPayloadBodyInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a RepeatResult<CfgAttribute<'a>>));
impl<'a> From<&'a CpPayloadBody<'a>> for CpPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a CpPayloadBody) -> CpPayloadBodyInnerRef<'a> {
        (&m.cfg_type, (&m.reserved, &m.attributes))
    }
}

impl<'a> From<CpPayloadBodyInner<'a>> for CpPayloadBody<'a> {
    fn ex_from(m: CpPayloadBodyInner) -> CpPayloadBody {
        let (cfg_type, (reserved, attributes)) = m;
        CpPayloadBody { cfg_type, reserved, attributes }
    }
}

pub struct CpPayloadBodyMapper;
impl View for CpPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CpPayloadBodyMapper {
    type Src = SpecCpPayloadBodyInner;
    type Dst = SpecCpPayloadBody;
}
impl SpecIsoProof for CpPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CpPayloadBodyMapper {
    type Src = CpPayloadBodyInner<'a>;
    type Dst = CpPayloadBody<'a>;
    type RefSrc = CpPayloadBodyInnerRef<'a>;
}
pub spec const SPEC_CPPAYLOADBODYRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecCpPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Variable, Repeat<SpecCfgAttributeCombinator>>);
type SpecCpPayloadBodyCombinatorAlias2 = (SpecCfgTypeCombinator, SpecCpPayloadBodyCombinatorAlias1);
pub struct SpecCpPayloadBodyCombinator(pub SpecCpPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecCpPayloadBodyCombinator {
    type Type = SpecCpPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCpPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCpPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCpPayloadBodyCombinatorAlias = Mapped<SpecCpPayloadBodyCombinatorAlias2, CpPayloadBodyMapper>;
pub exec static CPPAYLOADBODYRESERVED_CONST: [u8; 3]
    ensures CPPAYLOADBODYRESERVED_CONST@ == SPEC_CPPAYLOADBODYRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_CPPAYLOADBODYRESERVED_CONST);
    arr
}
type CpPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Variable, Repeat<CfgAttributeCombinator>>);
type CpPayloadBodyCombinatorAlias2 = (CfgTypeCombinator, CpPayloadBodyCombinator1);
pub struct CpPayloadBodyCombinator1(pub CpPayloadBodyCombinatorAlias1);
impl View for CpPayloadBodyCombinator1 {
    type V = SpecCpPayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CpPayloadBodyCombinator1, CpPayloadBodyCombinatorAlias1);

pub struct CpPayloadBodyCombinator2(pub CpPayloadBodyCombinatorAlias2);
impl View for CpPayloadBodyCombinator2 {
    type V = SpecCpPayloadBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CpPayloadBodyCombinator2, CpPayloadBodyCombinatorAlias2);

pub struct CpPayloadBodyCombinator(pub CpPayloadBodyCombinatorAlias);

impl View for CpPayloadBodyCombinator {
    type V = SpecCpPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecCpPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CpPayloadBodyCombinator {
    type Type = CpPayloadBody<'a>;
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
pub type CpPayloadBodyCombinatorAlias = Mapped<CpPayloadBodyCombinator2, CpPayloadBodyMapper>;


pub open spec fn spec_cp_payload_body(payload_length: u16) -> SpecCpPayloadBodyCombinator {
    SpecCpPayloadBodyCombinator(
    Mapped {
        inner: (spec_cfg_type(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_CPPAYLOADBODYRESERVED_CONST) }, AndThen(bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize), Repeat(spec_cfg_attribute())))),
        mapper: CpPayloadBodyMapper,
    })
}

pub fn cp_payload_body<'a>(payload_length: u16) -> (o: CpPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_cp_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CpPayloadBodyCombinator(
    Mapped {
        inner: CpPayloadBodyCombinator2((cfg_type(), CpPayloadBodyCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(CPPAYLOADBODYRESERVED_CONST) }, AndThen(bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize), Repeat::new(cfg_attribute())))))),
        mapper: CpPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_cp_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cp_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<CpPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_cp_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_cp_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cp_payload_body(payload_length@).spec_parse(input@) is None,
        spec_cp_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = cp_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cp_payload_body<'a>(v: <CpPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cp_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cp_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cp_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = cp_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn cp_payload_body_len<'a>(v: <CpPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_cp_payload_body(payload_length@).wf(v@),
        spec_cp_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_cp_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = cp_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecEapPayloadBody {
    pub code: u8,
    pub eap_rest: SpecEapPayloadBodyEapRest,
}

pub type SpecEapPayloadBodyInner = (u8, SpecEapPayloadBodyEapRest);


impl SpecFrom<SpecEapPayloadBody> for SpecEapPayloadBodyInner {
    open spec fn spec_from(m: SpecEapPayloadBody) -> SpecEapPayloadBodyInner {
        (m.code, m.eap_rest)
    }
}

impl SpecFrom<SpecEapPayloadBodyInner> for SpecEapPayloadBody {
    open spec fn spec_from(m: SpecEapPayloadBodyInner) -> SpecEapPayloadBody {
        let (code, eap_rest) = m;
        SpecEapPayloadBody { code, eap_rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapPayloadBody<'a> {
    pub code: u8,
    pub eap_rest: EapPayloadBodyEapRest<'a>,
}

impl View for EapPayloadBody<'_> {
    type V = SpecEapPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecEapPayloadBody {
            code: self.code@,
            eap_rest: self.eap_rest@,
        }
    }
}
pub type EapPayloadBodyInner<'a> = (u8, EapPayloadBodyEapRest<'a>);

pub type EapPayloadBodyInnerRef<'a> = (&'a u8, &'a EapPayloadBodyEapRest<'a>);
impl<'a> From<&'a EapPayloadBody<'a>> for EapPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a EapPayloadBody) -> EapPayloadBodyInnerRef<'a> {
        (&m.code, &m.eap_rest)
    }
}

impl<'a> From<EapPayloadBodyInner<'a>> for EapPayloadBody<'a> {
    fn ex_from(m: EapPayloadBodyInner) -> EapPayloadBody {
        let (code, eap_rest) = m;
        EapPayloadBody { code, eap_rest }
    }
}

pub struct EapPayloadBodyMapper;
impl View for EapPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapPayloadBodyMapper {
    type Src = SpecEapPayloadBodyInner;
    type Dst = SpecEapPayloadBody;
}
impl SpecIsoProof for EapPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapPayloadBodyMapper {
    type Src = EapPayloadBodyInner<'a>;
    type Dst = EapPayloadBody<'a>;
    type RefSrc = EapPayloadBodyInnerRef<'a>;
}

pub struct SpecEapPayloadBodyCombinator(pub SpecEapPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecEapPayloadBodyCombinator {
    type Type = SpecEapPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapPayloadBodyCombinatorAlias = Mapped<SpecPair<SpecEapCodeCombinator, SpecEapPayloadBodyEapRestCombinator>, EapPayloadBodyMapper>;

pub struct EapPayloadBodyCombinator(pub EapPayloadBodyCombinatorAlias);

impl View for EapPayloadBodyCombinator {
    type V = SpecEapPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecEapPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapPayloadBodyCombinator {
    type Type = EapPayloadBody<'a>;
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
pub type EapPayloadBodyCombinatorAlias = Mapped<Pair<EapCodeCombinator, EapPayloadBodyEapRestCombinator, EapPayloadBodyCont0>, EapPayloadBodyMapper>;


pub open spec fn spec_eap_payload_body(payload_length: u16) -> SpecEapPayloadBodyCombinator {
    SpecEapPayloadBodyCombinator(
    Mapped {
        inner: Pair::spec_new(spec_eap_code(), |deps| spec_eap_payload_body_cont0(payload_length, deps)),
        mapper: EapPayloadBodyMapper,
    })
}

pub open spec fn spec_eap_payload_body_cont0(payload_length: u16, deps: u8) -> SpecEapPayloadBodyEapRestCombinator {
    let code = deps;
    spec_eap_payload_body_eap_rest(code)
}

impl View for EapPayloadBodyCont0 {
    type V = spec_fn(u8) -> SpecEapPayloadBodyEapRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_eap_payload_body_cont0(self.payload_length@, deps)
        }
    }
}

pub fn eap_payload_body<'a>(payload_length: u16) -> (o: EapPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_eap_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapPayloadBodyCombinator(
    Mapped {
        inner: Pair::new(eap_code(), EapPayloadBodyCont0 { payload_length }),
        mapper: EapPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<EapPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_eap_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_eap_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_payload_body(payload_length@).spec_parse(input@) is None,
        spec_eap_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_payload_body<'a>(v: <EapPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = eap_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn eap_payload_body_len<'a>(v: <EapPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_eap_payload_body(payload_length@).wf(v@),
        spec_eap_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_eap_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = eap_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct EapPayloadBodyCont0 {
    pub payload_length: u16,
}
type EapPayloadBodyCont0Type<'a, 'b> = &'b u8;
type EapPayloadBodyCont0SType<'a, 'x> = &'x u8;
type EapPayloadBodyCont0Input<'a, 'b, 'x> = POrSType<EapPayloadBodyCont0Type<'a, 'b>, EapPayloadBodyCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EapPayloadBodyCont0Input<'a, 'b, 'x>> for EapPayloadBodyCont0 {
    type Output = EapPayloadBodyEapRestCombinator;

    open spec fn requires(&self, deps: EapPayloadBodyCont0Input<'a, 'b, 'x>) -> bool {        let payload_length = self.payload_length@;

        &&& ((self.payload_length@) >= 8 && (self.payload_length@) <= 65535)
        &&& (spec_eap_code()).wf(deps@)
        }

    open spec fn ensures(&self, deps: EapPayloadBodyCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_eap_payload_body_cont0(self.payload_length@, deps@)
    }

    fn apply(&self, deps: EapPayloadBodyCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let code = deps;
                let payload_length = self.payload_length;
                let code = *code;
                eap_payload_body_eap_rest(code)
            }
            POrSType::S(deps) => {
                let code = deps;
                let payload_length = self.payload_length;
                let code = *code;
                eap_payload_body_eap_rest(code)
            }
        }
    }
}
pub mod ExchangeType {
    use super::*;
    pub spec const SPEC_IKE_SA_INIT: u8 = 34;
    pub spec const SPEC_IKE_AUTH: u8 = 35;
    pub spec const SPEC_CREATE_CHILD_SA: u8 = 36;
    pub spec const SPEC_INFORMATIONAL: u8 = 37;
    pub exec const IKE_SA_INIT: u8 ensures IKE_SA_INIT == SPEC_IKE_SA_INIT { 34 }
    pub exec const IKE_AUTH: u8 ensures IKE_AUTH == SPEC_IKE_AUTH { 35 }
    pub exec const CREATE_CHILD_SA: u8 ensures CREATE_CHILD_SA == SPEC_CREATE_CHILD_SA { 36 }
    pub exec const INFORMATIONAL: u8 ensures INFORMATIONAL == SPEC_INFORMATIONAL { 37 }
}


pub struct SpecExchangeTypeCombinator(pub SpecExchangeTypeCombinatorAlias);

impl SpecCombinator for SpecExchangeTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExchangeTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecExchangeTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecExchangeTypeCombinatorAlias = U8;

pub struct ExchangeTypeCombinator(pub ExchangeTypeCombinatorAlias);

impl View for ExchangeTypeCombinator {
    type V = SpecExchangeTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecExchangeTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExchangeTypeCombinator {
    type Type = u8;
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
pub type ExchangeTypeCombinatorAlias = U8;


pub open spec fn spec_exchange_type() -> SpecExchangeTypeCombinator {
    SpecExchangeTypeCombinator(U8)
}

                
pub fn exchange_type<'a>() -> (o: ExchangeTypeCombinator)
    ensures o@ == spec_exchange_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ExchangeTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_exchange_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_exchange_type<'a>(input: &'a [u8]) -> (res: PResult<<ExchangeTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_exchange_type().spec_parse(input@) == Some((n as int, v@)),
        spec_exchange_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_exchange_type().spec_parse(input@) is None,
        spec_exchange_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = exchange_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_exchange_type<'a>(v: <ExchangeTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_exchange_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_exchange_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_exchange_type().spec_serialize(v@))
        },
{
    let combinator = exchange_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn exchange_type_len<'a>(v: <ExchangeTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_exchange_type().wf(v@),
        spec_exchange_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_exchange_type().spec_serialize(v@).len(),
{
    let combinator = exchange_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod NotifyMsgType {
    use super::*;
    pub spec const SPEC_UNSUPPORTED_CRITICAL_PAYLOAD: u16 = 1;
    pub spec const SPEC_INVALID_IKE_SPI: u16 = 4;
    pub spec const SPEC_INVALID_MAJOR_VERSION: u16 = 5;
    pub spec const SPEC_INVALID_SYNTAX: u16 = 7;
    pub spec const SPEC_INVALID_MESSAGE_ID: u16 = 9;
    pub spec const SPEC_INVALID_SPI: u16 = 11;
    pub spec const SPEC_NO_PROPOSAL_CHOSEN: u16 = 14;
    pub spec const SPEC_INVALID_KE_PAYLOAD: u16 = 17;
    pub spec const SPEC_AUTHENTICATION_FAILED: u16 = 24;
    pub spec const SPEC_SINGLE_PAIR_REQUIRED: u16 = 34;
    pub spec const SPEC_NO_ADDITIONAL_SAS: u16 = 35;
    pub spec const SPEC_INTERNAL_ADDRESS_FAILURE: u16 = 36;
    pub spec const SPEC_FAILED_CP_REQUIRED: u16 = 37;
    pub spec const SPEC_TS_UNACCEPTABLE: u16 = 38;
    pub spec const SPEC_INVALID_SELECTORS: u16 = 39;
    pub spec const SPEC_TEMPORARY_FAILURE: u16 = 43;
    pub spec const SPEC_CHILD_SA_NOT_FOUND: u16 = 44;
    pub spec const SPEC_INITIAL_CONTACT: u16 = 16384;
    pub spec const SPEC_SET_WINDOW_SIZE: u16 = 16385;
    pub spec const SPEC_ADDITIONAL_TS_POSSIBLE: u16 = 16386;
    pub spec const SPEC_IPCOMP_SUPPORTED: u16 = 16387;
    pub spec const SPEC_NAT_DETECTION_SOURCE_IP: u16 = 16388;
    pub spec const SPEC_NAT_DETECTION_DESTINATION_IP: u16 = 16389;
    pub spec const SPEC_COOKIE: u16 = 16390;
    pub spec const SPEC_USE_TRANSPORT_MODE: u16 = 16391;
    pub spec const SPEC_HTTP_CERT_LOOKUP_SUPPORTED: u16 = 16392;
    pub spec const SPEC_REKEY_SA: u16 = 16393;
    pub spec const SPEC_ESP_TFC_PADDING_NOT_SUPPORTED: u16 = 16394;
    pub spec const SPEC_NON_FIRST_FRAGMENTS_ALSO: u16 = 16395;
    pub exec const UNSUPPORTED_CRITICAL_PAYLOAD: u16 ensures UNSUPPORTED_CRITICAL_PAYLOAD == SPEC_UNSUPPORTED_CRITICAL_PAYLOAD { 1 }
    pub exec const INVALID_IKE_SPI: u16 ensures INVALID_IKE_SPI == SPEC_INVALID_IKE_SPI { 4 }
    pub exec const INVALID_MAJOR_VERSION: u16 ensures INVALID_MAJOR_VERSION == SPEC_INVALID_MAJOR_VERSION { 5 }
    pub exec const INVALID_SYNTAX: u16 ensures INVALID_SYNTAX == SPEC_INVALID_SYNTAX { 7 }
    pub exec const INVALID_MESSAGE_ID: u16 ensures INVALID_MESSAGE_ID == SPEC_INVALID_MESSAGE_ID { 9 }
    pub exec const INVALID_SPI: u16 ensures INVALID_SPI == SPEC_INVALID_SPI { 11 }
    pub exec const NO_PROPOSAL_CHOSEN: u16 ensures NO_PROPOSAL_CHOSEN == SPEC_NO_PROPOSAL_CHOSEN { 14 }
    pub exec const INVALID_KE_PAYLOAD: u16 ensures INVALID_KE_PAYLOAD == SPEC_INVALID_KE_PAYLOAD { 17 }
    pub exec const AUTHENTICATION_FAILED: u16 ensures AUTHENTICATION_FAILED == SPEC_AUTHENTICATION_FAILED { 24 }
    pub exec const SINGLE_PAIR_REQUIRED: u16 ensures SINGLE_PAIR_REQUIRED == SPEC_SINGLE_PAIR_REQUIRED { 34 }
    pub exec const NO_ADDITIONAL_SAS: u16 ensures NO_ADDITIONAL_SAS == SPEC_NO_ADDITIONAL_SAS { 35 }
    pub exec const INTERNAL_ADDRESS_FAILURE: u16 ensures INTERNAL_ADDRESS_FAILURE == SPEC_INTERNAL_ADDRESS_FAILURE { 36 }
    pub exec const FAILED_CP_REQUIRED: u16 ensures FAILED_CP_REQUIRED == SPEC_FAILED_CP_REQUIRED { 37 }
    pub exec const TS_UNACCEPTABLE: u16 ensures TS_UNACCEPTABLE == SPEC_TS_UNACCEPTABLE { 38 }
    pub exec const INVALID_SELECTORS: u16 ensures INVALID_SELECTORS == SPEC_INVALID_SELECTORS { 39 }
    pub exec const TEMPORARY_FAILURE: u16 ensures TEMPORARY_FAILURE == SPEC_TEMPORARY_FAILURE { 43 }
    pub exec const CHILD_SA_NOT_FOUND: u16 ensures CHILD_SA_NOT_FOUND == SPEC_CHILD_SA_NOT_FOUND { 44 }
    pub exec const INITIAL_CONTACT: u16 ensures INITIAL_CONTACT == SPEC_INITIAL_CONTACT { 16384 }
    pub exec const SET_WINDOW_SIZE: u16 ensures SET_WINDOW_SIZE == SPEC_SET_WINDOW_SIZE { 16385 }
    pub exec const ADDITIONAL_TS_POSSIBLE: u16 ensures ADDITIONAL_TS_POSSIBLE == SPEC_ADDITIONAL_TS_POSSIBLE { 16386 }
    pub exec const IPCOMP_SUPPORTED: u16 ensures IPCOMP_SUPPORTED == SPEC_IPCOMP_SUPPORTED { 16387 }
    pub exec const NAT_DETECTION_SOURCE_IP: u16 ensures NAT_DETECTION_SOURCE_IP == SPEC_NAT_DETECTION_SOURCE_IP { 16388 }
    pub exec const NAT_DETECTION_DESTINATION_IP: u16 ensures NAT_DETECTION_DESTINATION_IP == SPEC_NAT_DETECTION_DESTINATION_IP { 16389 }
    pub exec const COOKIE: u16 ensures COOKIE == SPEC_COOKIE { 16390 }
    pub exec const USE_TRANSPORT_MODE: u16 ensures USE_TRANSPORT_MODE == SPEC_USE_TRANSPORT_MODE { 16391 }
    pub exec const HTTP_CERT_LOOKUP_SUPPORTED: u16 ensures HTTP_CERT_LOOKUP_SUPPORTED == SPEC_HTTP_CERT_LOOKUP_SUPPORTED { 16392 }
    pub exec const REKEY_SA: u16 ensures REKEY_SA == SPEC_REKEY_SA { 16393 }
    pub exec const ESP_TFC_PADDING_NOT_SUPPORTED: u16 ensures ESP_TFC_PADDING_NOT_SUPPORTED == SPEC_ESP_TFC_PADDING_NOT_SUPPORTED { 16394 }
    pub exec const NON_FIRST_FRAGMENTS_ALSO: u16 ensures NON_FIRST_FRAGMENTS_ALSO == SPEC_NON_FIRST_FRAGMENTS_ALSO { 16395 }
}


pub struct SpecNotifyMsgTypeCombinator(pub SpecNotifyMsgTypeCombinatorAlias);

impl SpecCombinator for SpecNotifyMsgTypeCombinator {
    type Type = u16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyMsgTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyMsgTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyMsgTypeCombinatorAlias = U16Be;

pub struct NotifyMsgTypeCombinator(pub NotifyMsgTypeCombinatorAlias);

impl View for NotifyMsgTypeCombinator {
    type V = SpecNotifyMsgTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecNotifyMsgTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyMsgTypeCombinator {
    type Type = u16;
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
pub type NotifyMsgTypeCombinatorAlias = U16Be;


pub open spec fn spec_notify_msg_type() -> SpecNotifyMsgTypeCombinator {
    SpecNotifyMsgTypeCombinator(U16Be)
}

                
pub fn notify_msg_type<'a>() -> (o: NotifyMsgTypeCombinator)
    ensures o@ == spec_notify_msg_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyMsgTypeCombinator(U16Be);
    // assert({
    //     &&& combinator@ == spec_notify_msg_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_msg_type<'a>(input: &'a [u8]) -> (res: PResult<<NotifyMsgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_notify_msg_type().spec_parse(input@) == Some((n as int, v@)),
        spec_notify_msg_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_msg_type().spec_parse(input@) is None,
        spec_notify_msg_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_msg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_msg_type<'a>(v: <NotifyMsgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_msg_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_msg_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_msg_type().spec_serialize(v@))
        },
{
    let combinator = notify_msg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn notify_msg_type_len<'a>(v: <NotifyMsgTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_notify_msg_type().wf(v@),
        spec_notify_msg_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_notify_msg_type().spec_serialize(v@).len(),
{
    let combinator = notify_msg_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecKePayloadBody {
    pub dh_group_num: u16,
    pub reserved: u16,
    pub ke_data: Seq<u8>,
}

pub type SpecKePayloadBodyInner = (u16, (u16, Seq<u8>));


impl SpecFrom<SpecKePayloadBody> for SpecKePayloadBodyInner {
    open spec fn spec_from(m: SpecKePayloadBody) -> SpecKePayloadBodyInner {
        (m.dh_group_num, (m.reserved, m.ke_data))
    }
}

impl SpecFrom<SpecKePayloadBodyInner> for SpecKePayloadBody {
    open spec fn spec_from(m: SpecKePayloadBodyInner) -> SpecKePayloadBody {
        let (dh_group_num, (reserved, ke_data)) = m;
        SpecKePayloadBody { dh_group_num, reserved, ke_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct KePayloadBody<'a> {
    pub dh_group_num: u16,
    pub reserved: u16,
    pub ke_data: &'a [u8],
}

impl View for KePayloadBody<'_> {
    type V = SpecKePayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecKePayloadBody {
            dh_group_num: self.dh_group_num@,
            reserved: self.reserved@,
            ke_data: self.ke_data@,
        }
    }
}
pub type KePayloadBodyInner<'a> = (u16, (u16, &'a [u8]));

pub type KePayloadBodyInnerRef<'a> = (&'a u16, (&'a u16, &'a &'a [u8]));
impl<'a> From<&'a KePayloadBody<'a>> for KePayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a KePayloadBody) -> KePayloadBodyInnerRef<'a> {
        (&m.dh_group_num, (&m.reserved, &m.ke_data))
    }
}

impl<'a> From<KePayloadBodyInner<'a>> for KePayloadBody<'a> {
    fn ex_from(m: KePayloadBodyInner) -> KePayloadBody {
        let (dh_group_num, (reserved, ke_data)) = m;
        KePayloadBody { dh_group_num, reserved, ke_data }
    }
}

pub struct KePayloadBodyMapper;
impl View for KePayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KePayloadBodyMapper {
    type Src = SpecKePayloadBodyInner;
    type Dst = SpecKePayloadBody;
}
impl SpecIsoProof for KePayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for KePayloadBodyMapper {
    type Src = KePayloadBodyInner<'a>;
    type Dst = KePayloadBody<'a>;
    type RefSrc = KePayloadBodyInnerRef<'a>;
}
pub const KEPAYLOADBODYRESERVED_CONST: u16 = 0;
type SpecKePayloadBodyCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, bytes::Variable);
type SpecKePayloadBodyCombinatorAlias2 = (SpecDhIdCombinator, SpecKePayloadBodyCombinatorAlias1);
pub struct SpecKePayloadBodyCombinator(pub SpecKePayloadBodyCombinatorAlias);

impl SpecCombinator for SpecKePayloadBodyCombinator {
    type Type = SpecKePayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecKePayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecKePayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecKePayloadBodyCombinatorAlias = Mapped<SpecKePayloadBodyCombinatorAlias2, KePayloadBodyMapper>;
type KePayloadBodyCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, bytes::Variable);
type KePayloadBodyCombinatorAlias2 = (DhIdCombinator, KePayloadBodyCombinator1);
pub struct KePayloadBodyCombinator1(pub KePayloadBodyCombinatorAlias1);
impl View for KePayloadBodyCombinator1 {
    type V = SpecKePayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(KePayloadBodyCombinator1, KePayloadBodyCombinatorAlias1);

pub struct KePayloadBodyCombinator2(pub KePayloadBodyCombinatorAlias2);
impl View for KePayloadBodyCombinator2 {
    type V = SpecKePayloadBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(KePayloadBodyCombinator2, KePayloadBodyCombinatorAlias2);

pub struct KePayloadBodyCombinator(pub KePayloadBodyCombinatorAlias);

impl View for KePayloadBodyCombinator {
    type V = SpecKePayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecKePayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for KePayloadBodyCombinator {
    type Type = KePayloadBody<'a>;
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
pub type KePayloadBodyCombinatorAlias = Mapped<KePayloadBodyCombinator2, KePayloadBodyMapper>;


pub open spec fn spec_ke_payload_body(payload_length: u16) -> SpecKePayloadBodyCombinator {
    SpecKePayloadBodyCombinator(
    Mapped {
        inner: (spec_dh_id(), (Refined { inner: U16Be, predicate: TagPred(KEPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize))),
        mapper: KePayloadBodyMapper,
    })
}

pub fn ke_payload_body<'a>(payload_length: u16) -> (o: KePayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_ke_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = KePayloadBodyCombinator(
    Mapped {
        inner: KePayloadBodyCombinator2((dh_id(), KePayloadBodyCombinator1((Refined { inner: U16Be, predicate: TagPred(KEPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize))))),
        mapper: KePayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ke_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ke_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<KePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_ke_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_ke_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ke_payload_body(payload_length@).spec_parse(input@) is None,
        spec_ke_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = ke_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ke_payload_body<'a>(v: <KePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ke_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ke_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ke_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = ke_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn ke_payload_body_len<'a>(v: <KePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_ke_payload_body(payload_length@).wf(v@),
        spec_ke_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_ke_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = ke_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub mod NextPayloadType {
    use super::*;
    pub spec const SPEC_NoNextPayload: u8 = 0;
    pub spec const SPEC_SA: u8 = 33;
    pub spec const SPEC_KE: u8 = 34;
    pub spec const SPEC_IDi: u8 = 35;
    pub spec const SPEC_IDr: u8 = 36;
    pub spec const SPEC_CERT: u8 = 37;
    pub spec const SPEC_CERTREQ: u8 = 38;
    pub spec const SPEC_AUTH: u8 = 39;
    pub spec const SPEC_Nonce: u8 = 40;
    pub spec const SPEC_Notify: u8 = 41;
    pub spec const SPEC_Delete: u8 = 42;
    pub spec const SPEC_VendorID: u8 = 43;
    pub spec const SPEC_TSi: u8 = 44;
    pub spec const SPEC_TSr: u8 = 45;
    pub spec const SPEC_SK: u8 = 46;
    pub spec const SPEC_CP: u8 = 47;
    pub spec const SPEC_EAP: u8 = 48;
    pub exec const NoNextPayload: u8 ensures NoNextPayload == SPEC_NoNextPayload { 0 }
    pub exec const SA: u8 ensures SA == SPEC_SA { 33 }
    pub exec const KE: u8 ensures KE == SPEC_KE { 34 }
    pub exec const IDi: u8 ensures IDi == SPEC_IDi { 35 }
    pub exec const IDr: u8 ensures IDr == SPEC_IDr { 36 }
    pub exec const CERT: u8 ensures CERT == SPEC_CERT { 37 }
    pub exec const CERTREQ: u8 ensures CERTREQ == SPEC_CERTREQ { 38 }
    pub exec const AUTH: u8 ensures AUTH == SPEC_AUTH { 39 }
    pub exec const Nonce: u8 ensures Nonce == SPEC_Nonce { 40 }
    pub exec const Notify: u8 ensures Notify == SPEC_Notify { 41 }
    pub exec const Delete: u8 ensures Delete == SPEC_Delete { 42 }
    pub exec const VendorID: u8 ensures VendorID == SPEC_VendorID { 43 }
    pub exec const TSi: u8 ensures TSi == SPEC_TSi { 44 }
    pub exec const TSr: u8 ensures TSr == SPEC_TSr { 45 }
    pub exec const SK: u8 ensures SK == SPEC_SK { 46 }
    pub exec const CP: u8 ensures CP == SPEC_CP { 47 }
    pub exec const EAP: u8 ensures EAP == SPEC_EAP { 48 }
}


pub struct SpecNextPayloadTypeCombinator(pub SpecNextPayloadTypeCombinatorAlias);

impl SpecCombinator for SpecNextPayloadTypeCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNextPayloadTypeCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNextPayloadTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecNextPayloadTypeCombinatorAlias = U8;

pub struct NextPayloadTypeCombinator(pub NextPayloadTypeCombinatorAlias);

impl View for NextPayloadTypeCombinator {
    type V = SpecNextPayloadTypeCombinator;
    open spec fn view(&self) -> Self::V { SpecNextPayloadTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NextPayloadTypeCombinator {
    type Type = u8;
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
pub type NextPayloadTypeCombinatorAlias = U8;


pub open spec fn spec_next_payload_type() -> SpecNextPayloadTypeCombinator {
    SpecNextPayloadTypeCombinator(U8)
}

                
pub fn next_payload_type<'a>() -> (o: NextPayloadTypeCombinator)
    ensures o@ == spec_next_payload_type(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NextPayloadTypeCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_next_payload_type()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_next_payload_type<'a>(input: &'a [u8]) -> (res: PResult<<NextPayloadTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_next_payload_type().spec_parse(input@) == Some((n as int, v@)),
        spec_next_payload_type().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_next_payload_type().spec_parse(input@) is None,
        spec_next_payload_type().spec_parse(input@) is None ==> res is Err,
{
    let combinator = next_payload_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_next_payload_type<'a>(v: <NextPayloadTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_next_payload_type().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_next_payload_type().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_next_payload_type().spec_serialize(v@))
        },
{
    let combinator = next_payload_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn next_payload_type_len<'a>(v: <NextPayloadTypeCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_next_payload_type().wf(v@),
        spec_next_payload_type().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_next_payload_type().spec_serialize(v@).len(),
{
    let combinator = next_payload_type();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecIkeVersionByte = u8;
pub type IkeVersionByte = u8;
pub type IkeVersionByteRef<'a> = &'a u8;


pub struct SpecIkeVersionByteCombinator(pub SpecIkeVersionByteCombinatorAlias);

impl SpecCombinator for SpecIkeVersionByteCombinator {
    type Type = SpecIkeVersionByte;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkeVersionByteCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkeVersionByteCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkeVersionByteCombinatorAlias = Refined<U8, Predicate10005340194363141588>;
pub struct Predicate10005340194363141588;
impl View for Predicate10005340194363141588 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate10005340194363141588 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 32 && i <= 47)
    }
}
impl SpecPred<u8> for Predicate10005340194363141588 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 32 && i <= 47)
    }
}

pub struct IkeVersionByteCombinator(pub IkeVersionByteCombinatorAlias);

impl View for IkeVersionByteCombinator {
    type V = SpecIkeVersionByteCombinator;
    open spec fn view(&self) -> Self::V { SpecIkeVersionByteCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IkeVersionByteCombinator {
    type Type = IkeVersionByte;
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
pub type IkeVersionByteCombinatorAlias = Refined<U8, Predicate10005340194363141588>;


pub open spec fn spec_ike_version_byte() -> SpecIkeVersionByteCombinator {
    SpecIkeVersionByteCombinator(Refined { inner: U8, predicate: Predicate10005340194363141588 })
}

                
pub fn ike_version_byte<'a>() -> (o: IkeVersionByteCombinator)
    ensures o@ == spec_ike_version_byte(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IkeVersionByteCombinator(Refined { inner: U8, predicate: Predicate10005340194363141588 });
    // assert({
    //     &&& combinator@ == spec_ike_version_byte()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ike_version_byte<'a>(input: &'a [u8]) -> (res: PResult<<IkeVersionByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ike_version_byte().spec_parse(input@) == Some((n as int, v@)),
        spec_ike_version_byte().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ike_version_byte().spec_parse(input@) is None,
        spec_ike_version_byte().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ike_version_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ike_version_byte<'a>(v: <IkeVersionByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ike_version_byte().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ike_version_byte().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ike_version_byte().spec_serialize(v@))
        },
{
    let combinator = ike_version_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ike_version_byte_len<'a>(v: <IkeVersionByteCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ike_version_byte().wf(v@),
        spec_ike_version_byte().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ike_version_byte().spec_serialize(v@).len(),
{
    let combinator = ike_version_byte();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_IkeFlags_ResponderRequest: u8 = 0;
pub spec const SPEC_IkeFlags_InitiatorRequest: u8 = 8;
pub spec const SPEC_IkeFlags_ResponderResponse: u8 = 32;
pub spec const SPEC_IkeFlags_InitiatorResponse: u8 = 40;
pub exec static EXEC_IkeFlags_ResponderRequest: u8 ensures EXEC_IkeFlags_ResponderRequest == SPEC_IkeFlags_ResponderRequest { 0 }
pub exec static EXEC_IkeFlags_InitiatorRequest: u8 ensures EXEC_IkeFlags_InitiatorRequest == SPEC_IkeFlags_InitiatorRequest { 8 }
pub exec static EXEC_IkeFlags_ResponderResponse: u8 ensures EXEC_IkeFlags_ResponderResponse == SPEC_IkeFlags_ResponderResponse { 32 }
pub exec static EXEC_IkeFlags_InitiatorResponse: u8 ensures EXEC_IkeFlags_InitiatorResponse == SPEC_IkeFlags_InitiatorResponse { 40 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum IkeFlags {
    ResponderRequest = 0,
InitiatorRequest = 8,
ResponderResponse = 32,
InitiatorResponse = 40
}
pub type SpecIkeFlags = IkeFlags;

pub type IkeFlagsInner = u8;

pub type IkeFlagsInnerRef<'a> = &'a u8;

impl View for IkeFlags {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<IkeFlagsInner> for IkeFlags {
    type Error = ();

    open spec fn spec_try_from(v: IkeFlagsInner) -> Result<IkeFlags, ()> {
        match v {
            0u8 => Ok(IkeFlags::ResponderRequest),
            8u8 => Ok(IkeFlags::InitiatorRequest),
            32u8 => Ok(IkeFlags::ResponderResponse),
            40u8 => Ok(IkeFlags::InitiatorResponse),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<IkeFlags> for IkeFlagsInner {
    type Error = ();

    open spec fn spec_try_from(v: IkeFlags) -> Result<IkeFlagsInner, ()> {
        match v {
            IkeFlags::ResponderRequest => Ok(SPEC_IkeFlags_ResponderRequest),
            IkeFlags::InitiatorRequest => Ok(SPEC_IkeFlags_InitiatorRequest),
            IkeFlags::ResponderResponse => Ok(SPEC_IkeFlags_ResponderResponse),
            IkeFlags::InitiatorResponse => Ok(SPEC_IkeFlags_InitiatorResponse),
        }
    }
}

impl TryFrom<IkeFlagsInner> for IkeFlags {
    type Error = ();

    fn ex_try_from(v: IkeFlagsInner) -> Result<IkeFlags, ()> {
        match v {
            0u8 => Ok(IkeFlags::ResponderRequest),
            8u8 => Ok(IkeFlags::InitiatorRequest),
            32u8 => Ok(IkeFlags::ResponderResponse),
            40u8 => Ok(IkeFlags::InitiatorResponse),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a IkeFlags> for IkeFlagsInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a IkeFlags) -> Result<IkeFlagsInnerRef<'a>, ()> {
        match v {
            IkeFlags::ResponderRequest => Ok(&EXEC_IkeFlags_ResponderRequest),
            IkeFlags::InitiatorRequest => Ok(&EXEC_IkeFlags_InitiatorRequest),
            IkeFlags::ResponderResponse => Ok(&EXEC_IkeFlags_ResponderResponse),
            IkeFlags::InitiatorResponse => Ok(&EXEC_IkeFlags_InitiatorResponse),
        }
    }
}

pub struct IkeFlagsMapper;

impl View for IkeFlagsMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for IkeFlagsMapper {
    type Src = IkeFlagsInner;
    type Dst = IkeFlags;
}

impl SpecPartialIsoProof for IkeFlagsMapper {
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

impl<'a> PartialIso<'a> for IkeFlagsMapper {
    type Src = IkeFlagsInner;
    type Dst = IkeFlags;
    type RefSrc = IkeFlagsInnerRef<'a>;
}


pub struct SpecIkeFlagsCombinator(pub SpecIkeFlagsCombinatorAlias);

impl SpecCombinator for SpecIkeFlagsCombinator {
    type Type = SpecIkeFlags;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkeFlagsCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkeFlagsCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkeFlagsCombinatorAlias = TryMap<U8, IkeFlagsMapper>;

pub struct IkeFlagsCombinator(pub IkeFlagsCombinatorAlias);

impl View for IkeFlagsCombinator {
    type V = SpecIkeFlagsCombinator;
    open spec fn view(&self) -> Self::V { SpecIkeFlagsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IkeFlagsCombinator {
    type Type = IkeFlags;
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
pub type IkeFlagsCombinatorAlias = TryMap<U8, IkeFlagsMapper>;


pub open spec fn spec_ike_flags() -> SpecIkeFlagsCombinator {
    SpecIkeFlagsCombinator(TryMap { inner: U8, mapper: IkeFlagsMapper })
}

                
pub fn ike_flags<'a>() -> (o: IkeFlagsCombinator)
    ensures o@ == spec_ike_flags(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IkeFlagsCombinator(TryMap { inner: U8, mapper: IkeFlagsMapper });
    // assert({
    //     &&& combinator@ == spec_ike_flags()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ike_flags<'a>(input: &'a [u8]) -> (res: PResult<<IkeFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ike_flags().spec_parse(input@) == Some((n as int, v@)),
        spec_ike_flags().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ike_flags().spec_parse(input@) is None,
        spec_ike_flags().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ike_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ike_flags<'a>(v: <IkeFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ike_flags().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ike_flags().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ike_flags().spec_serialize(v@))
        },
{
    let combinator = ike_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ike_flags_len<'a>(v: <IkeFlagsCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ike_flags().wf(v@),
        spec_ike_flags().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ike_flags().spec_serialize(v@).len(),
{
    let combinator = ike_flags();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkeHeader {
    pub initiator_spi: Seq<u8>,
    pub responder_spi: Seq<u8>,
    pub next_payload: u8,
    pub version: SpecIkeVersionByte,
    pub exchange_type: u8,
    pub flags: SpecIkeFlags,
    pub message_id: u32,
    pub length: u32,
}

pub type SpecIkeHeaderInner = (Seq<u8>, (Seq<u8>, (u8, (SpecIkeVersionByte, (u8, (SpecIkeFlags, (u32, u32)))))));


impl SpecFrom<SpecIkeHeader> for SpecIkeHeaderInner {
    open spec fn spec_from(m: SpecIkeHeader) -> SpecIkeHeaderInner {
        (m.initiator_spi, (m.responder_spi, (m.next_payload, (m.version, (m.exchange_type, (m.flags, (m.message_id, m.length)))))))
    }
}

impl SpecFrom<SpecIkeHeaderInner> for SpecIkeHeader {
    open spec fn spec_from(m: SpecIkeHeaderInner) -> SpecIkeHeader {
        let (initiator_spi, (responder_spi, (next_payload, (version, (exchange_type, (flags, (message_id, length))))))) = m;
        SpecIkeHeader { initiator_spi, responder_spi, next_payload, version, exchange_type, flags, message_id, length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct IkeHeader<'a> {
    pub initiator_spi: &'a [u8],
    pub responder_spi: &'a [u8],
    pub next_payload: u8,
    pub version: IkeVersionByte,
    pub exchange_type: u8,
    pub flags: IkeFlags,
    pub message_id: u32,
    pub length: u32,
}

impl View for IkeHeader<'_> {
    type V = SpecIkeHeader;

    open spec fn view(&self) -> Self::V {
        SpecIkeHeader {
            initiator_spi: self.initiator_spi@,
            responder_spi: self.responder_spi@,
            next_payload: self.next_payload@,
            version: self.version@,
            exchange_type: self.exchange_type@,
            flags: self.flags@,
            message_id: self.message_id@,
            length: self.length@,
        }
    }
}
pub type IkeHeaderInner<'a> = (&'a [u8], (&'a [u8], (u8, (IkeVersionByte, (u8, (IkeFlags, (u32, u32)))))));

pub type IkeHeaderInnerRef<'a> = (&'a &'a [u8], (&'a &'a [u8], (&'a u8, (&'a IkeVersionByte, (&'a u8, (&'a IkeFlags, (&'a u32, &'a u32)))))));
impl<'a> From<&'a IkeHeader<'a>> for IkeHeaderInnerRef<'a> {
    fn ex_from(m: &'a IkeHeader) -> IkeHeaderInnerRef<'a> {
        (&m.initiator_spi, (&m.responder_spi, (&m.next_payload, (&m.version, (&m.exchange_type, (&m.flags, (&m.message_id, &m.length)))))))
    }
}

impl<'a> From<IkeHeaderInner<'a>> for IkeHeader<'a> {
    fn ex_from(m: IkeHeaderInner) -> IkeHeader {
        let (initiator_spi, (responder_spi, (next_payload, (version, (exchange_type, (flags, (message_id, length))))))) = m;
        IkeHeader { initiator_spi, responder_spi, next_payload, version, exchange_type, flags, message_id, length }
    }
}

pub struct IkeHeaderMapper;
impl View for IkeHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for IkeHeaderMapper {
    type Src = SpecIkeHeaderInner;
    type Dst = SpecIkeHeader;
}
impl SpecIsoProof for IkeHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for IkeHeaderMapper {
    type Src = IkeHeaderInner<'a>;
    type Dst = IkeHeader<'a>;
    type RefSrc = IkeHeaderInnerRef<'a>;
}
type SpecIkeHeaderCombinatorAlias1 = (U32Be, Refined<U32Be, Predicate4866237765496934330>);
type SpecIkeHeaderCombinatorAlias2 = (SpecIkeFlagsCombinator, SpecIkeHeaderCombinatorAlias1);
type SpecIkeHeaderCombinatorAlias3 = (SpecExchangeTypeCombinator, SpecIkeHeaderCombinatorAlias2);
type SpecIkeHeaderCombinatorAlias4 = (SpecIkeVersionByteCombinator, SpecIkeHeaderCombinatorAlias3);
type SpecIkeHeaderCombinatorAlias5 = (SpecNextPayloadTypeCombinator, SpecIkeHeaderCombinatorAlias4);
type SpecIkeHeaderCombinatorAlias6 = (bytes::Fixed<8>, SpecIkeHeaderCombinatorAlias5);
type SpecIkeHeaderCombinatorAlias7 = (bytes::Fixed<8>, SpecIkeHeaderCombinatorAlias6);
pub struct SpecIkeHeaderCombinator(pub SpecIkeHeaderCombinatorAlias);

impl SpecCombinator for SpecIkeHeaderCombinator {
    type Type = SpecIkeHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkeHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkeHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkeHeaderCombinatorAlias = Mapped<SpecIkeHeaderCombinatorAlias7, IkeHeaderMapper>;
pub struct Predicate4866237765496934330;
impl View for Predicate4866237765496934330 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u32> for Predicate4866237765496934330 {
    fn apply(&self, i: &u32) -> bool {
        let i = (*i);
        (i >= 28 && i <= 4294967295)
    }
}
impl SpecPred<u32> for Predicate4866237765496934330 {
    open spec fn spec_apply(&self, i: &u32) -> bool {
        let i = (*i);
        (i >= 28 && i <= 4294967295)
    }
}
type IkeHeaderCombinatorAlias1 = (U32Be, Refined<U32Be, Predicate4866237765496934330>);
type IkeHeaderCombinatorAlias2 = (IkeFlagsCombinator, IkeHeaderCombinator1);
type IkeHeaderCombinatorAlias3 = (ExchangeTypeCombinator, IkeHeaderCombinator2);
type IkeHeaderCombinatorAlias4 = (IkeVersionByteCombinator, IkeHeaderCombinator3);
type IkeHeaderCombinatorAlias5 = (NextPayloadTypeCombinator, IkeHeaderCombinator4);
type IkeHeaderCombinatorAlias6 = (bytes::Fixed<8>, IkeHeaderCombinator5);
type IkeHeaderCombinatorAlias7 = (bytes::Fixed<8>, IkeHeaderCombinator6);
pub struct IkeHeaderCombinator1(pub IkeHeaderCombinatorAlias1);
impl View for IkeHeaderCombinator1 {
    type V = SpecIkeHeaderCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator1, IkeHeaderCombinatorAlias1);

pub struct IkeHeaderCombinator2(pub IkeHeaderCombinatorAlias2);
impl View for IkeHeaderCombinator2 {
    type V = SpecIkeHeaderCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator2, IkeHeaderCombinatorAlias2);

pub struct IkeHeaderCombinator3(pub IkeHeaderCombinatorAlias3);
impl View for IkeHeaderCombinator3 {
    type V = SpecIkeHeaderCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator3, IkeHeaderCombinatorAlias3);

pub struct IkeHeaderCombinator4(pub IkeHeaderCombinatorAlias4);
impl View for IkeHeaderCombinator4 {
    type V = SpecIkeHeaderCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator4, IkeHeaderCombinatorAlias4);

pub struct IkeHeaderCombinator5(pub IkeHeaderCombinatorAlias5);
impl View for IkeHeaderCombinator5 {
    type V = SpecIkeHeaderCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator5, IkeHeaderCombinatorAlias5);

pub struct IkeHeaderCombinator6(pub IkeHeaderCombinatorAlias6);
impl View for IkeHeaderCombinator6 {
    type V = SpecIkeHeaderCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator6, IkeHeaderCombinatorAlias6);

pub struct IkeHeaderCombinator7(pub IkeHeaderCombinatorAlias7);
impl View for IkeHeaderCombinator7 {
    type V = SpecIkeHeaderCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IkeHeaderCombinator7, IkeHeaderCombinatorAlias7);

pub struct IkeHeaderCombinator(pub IkeHeaderCombinatorAlias);

impl View for IkeHeaderCombinator {
    type V = SpecIkeHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecIkeHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IkeHeaderCombinator {
    type Type = IkeHeader<'a>;
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
pub type IkeHeaderCombinatorAlias = Mapped<IkeHeaderCombinator7, IkeHeaderMapper>;


pub open spec fn spec_ike_header() -> SpecIkeHeaderCombinator {
    SpecIkeHeaderCombinator(
    Mapped {
        inner: (bytes::Fixed::<8>, (bytes::Fixed::<8>, (spec_next_payload_type(), (spec_ike_version_byte(), (spec_exchange_type(), (spec_ike_flags(), (U32Be, Refined { inner: U32Be, predicate: Predicate4866237765496934330 }))))))),
        mapper: IkeHeaderMapper,
    })
}

                
pub fn ike_header<'a>() -> (o: IkeHeaderCombinator)
    ensures o@ == spec_ike_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IkeHeaderCombinator(
    Mapped {
        inner: IkeHeaderCombinator7((bytes::Fixed::<8>, IkeHeaderCombinator6((bytes::Fixed::<8>, IkeHeaderCombinator5((next_payload_type(), IkeHeaderCombinator4((ike_version_byte(), IkeHeaderCombinator3((exchange_type(), IkeHeaderCombinator2((ike_flags(), IkeHeaderCombinator1((U32Be, Refined { inner: U32Be, predicate: Predicate4866237765496934330 })))))))))))))),
        mapper: IkeHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ike_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ike_header<'a>(input: &'a [u8]) -> (res: PResult<<IkeHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ike_header().spec_parse(input@) == Some((n as int, v@)),
        spec_ike_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ike_header().spec_parse(input@) is None,
        spec_ike_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ike_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ike_header<'a>(v: <IkeHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ike_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ike_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ike_header().spec_serialize(v@))
        },
{
    let combinator = ike_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ike_header_len<'a>(v: <IkeHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ike_header().wf(v@),
        spec_ike_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ike_header().spec_serialize(v@).len(),
{
    let combinator = ike_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecDeletePayloadSpisNone = Seq<u8>;
pub type DeletePayloadSpisNone<'a> = &'a [u8];
pub type DeletePayloadSpisNoneRef<'a> = &'a &'a [u8];


pub struct SpecDeletePayloadSpisNoneCombinator(pub SpecDeletePayloadSpisNoneCombinatorAlias);

impl SpecCombinator for SpecDeletePayloadSpisNoneCombinator {
    type Type = SpecDeletePayloadSpisNone;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDeletePayloadSpisNoneCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDeletePayloadSpisNoneCombinatorAlias::is_prefix_secure() }
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
pub type SpecDeletePayloadSpisNoneCombinatorAlias = bytes::Fixed<0>;

pub struct DeletePayloadSpisNoneCombinator(pub DeletePayloadSpisNoneCombinatorAlias);

impl View for DeletePayloadSpisNoneCombinator {
    type V = SpecDeletePayloadSpisNoneCombinator;
    open spec fn view(&self) -> Self::V { SpecDeletePayloadSpisNoneCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DeletePayloadSpisNoneCombinator {
    type Type = DeletePayloadSpisNone<'a>;
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
pub type DeletePayloadSpisNoneCombinatorAlias = bytes::Fixed<0>;


pub open spec fn spec_delete_payload_spis_none() -> SpecDeletePayloadSpisNoneCombinator {
    SpecDeletePayloadSpisNoneCombinator(bytes::Fixed::<0>)
}

                
pub fn delete_payload_spis_none<'a>() -> (o: DeletePayloadSpisNoneCombinator)
    ensures o@ == spec_delete_payload_spis_none(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DeletePayloadSpisNoneCombinator(bytes::Fixed::<0>);
    // assert({
    //     &&& combinator@ == spec_delete_payload_spis_none()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_delete_payload_spis_none<'a>(input: &'a [u8]) -> (res: PResult<<DeletePayloadSpisNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_delete_payload_spis_none().spec_parse(input@) == Some((n as int, v@)),
        spec_delete_payload_spis_none().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_delete_payload_spis_none().spec_parse(input@) is None,
        spec_delete_payload_spis_none().spec_parse(input@) is None ==> res is Err,
{
    let combinator = delete_payload_spis_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_delete_payload_spis_none<'a>(v: <DeletePayloadSpisNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_delete_payload_spis_none().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_delete_payload_spis_none().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_delete_payload_spis_none().spec_serialize(v@))
        },
{
    let combinator = delete_payload_spis_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn delete_payload_spis_none_len<'a>(v: <DeletePayloadSpisNoneCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_delete_payload_spis_none().wf(v@),
        spec_delete_payload_spis_none().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_delete_payload_spis_none().spec_serialize(v@).len(),
{
    let combinator = delete_payload_spis_none();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecEapMessageSuccessFailure {
    pub code: u8,
    pub identifier: u8,
    pub eap_length: u16,
}

pub type SpecEapMessageSuccessFailureInner = (u8, (u8, u16));


impl SpecFrom<SpecEapMessageSuccessFailure> for SpecEapMessageSuccessFailureInner {
    open spec fn spec_from(m: SpecEapMessageSuccessFailure) -> SpecEapMessageSuccessFailureInner {
        (m.code, (m.identifier, m.eap_length))
    }
}

impl SpecFrom<SpecEapMessageSuccessFailureInner> for SpecEapMessageSuccessFailure {
    open spec fn spec_from(m: SpecEapMessageSuccessFailureInner) -> SpecEapMessageSuccessFailure {
        let (code, (identifier, eap_length)) = m;
        SpecEapMessageSuccessFailure { code, identifier, eap_length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapMessageSuccessFailure {
    pub code: u8,
    pub identifier: u8,
    pub eap_length: u16,
}

impl View for EapMessageSuccessFailure {
    type V = SpecEapMessageSuccessFailure;

    open spec fn view(&self) -> Self::V {
        SpecEapMessageSuccessFailure {
            code: self.code@,
            identifier: self.identifier@,
            eap_length: self.eap_length@,
        }
    }
}
pub type EapMessageSuccessFailureInner = (u8, (u8, u16));

pub type EapMessageSuccessFailureInnerRef<'a> = (&'a u8, (&'a u8, &'a u16));
impl<'a> From<&'a EapMessageSuccessFailure> for EapMessageSuccessFailureInnerRef<'a> {
    fn ex_from(m: &'a EapMessageSuccessFailure) -> EapMessageSuccessFailureInnerRef<'a> {
        (&m.code, (&m.identifier, &m.eap_length))
    }
}

impl From<EapMessageSuccessFailureInner> for EapMessageSuccessFailure {
    fn ex_from(m: EapMessageSuccessFailureInner) -> EapMessageSuccessFailure {
        let (code, (identifier, eap_length)) = m;
        EapMessageSuccessFailure { code, identifier, eap_length }
    }
}

pub struct EapMessageSuccessFailureMapper;
impl View for EapMessageSuccessFailureMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapMessageSuccessFailureMapper {
    type Src = SpecEapMessageSuccessFailureInner;
    type Dst = SpecEapMessageSuccessFailure;
}
impl SpecIsoProof for EapMessageSuccessFailureMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapMessageSuccessFailureMapper {
    type Src = EapMessageSuccessFailureInner;
    type Dst = EapMessageSuccessFailure;
    type RefSrc = EapMessageSuccessFailureInnerRef<'a>;
}
pub const EAPMESSAGESUCCESSFAILUREEAP_LENGTH_CONST: u16 = 4;
type SpecEapMessageSuccessFailureCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
type SpecEapMessageSuccessFailureCombinatorAlias2 = (Refined<SpecEapCodeCombinator, Predicate7863829697870102672>, SpecEapMessageSuccessFailureCombinatorAlias1);
pub struct SpecEapMessageSuccessFailureCombinator(pub SpecEapMessageSuccessFailureCombinatorAlias);

impl SpecCombinator for SpecEapMessageSuccessFailureCombinator {
    type Type = SpecEapMessageSuccessFailure;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapMessageSuccessFailureCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapMessageSuccessFailureCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapMessageSuccessFailureCombinatorAlias = Mapped<SpecEapMessageSuccessFailureCombinatorAlias2, EapMessageSuccessFailureMapper>;
pub struct Predicate7863829697870102672;
impl View for Predicate7863829697870102672 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7863829697870102672 {
    fn apply(&self, e: &u8) -> bool {
        (*e) == 3 || (*e) == 4
    }
}
impl SpecPred<u8> for Predicate7863829697870102672 {
    open spec fn spec_apply(&self, e: &u8) -> bool {
        (*e) == 3 || (*e) == 4
    }
}
type EapMessageSuccessFailureCombinatorAlias1 = (U8, Refined<U16Be, TagPred<u16>>);
type EapMessageSuccessFailureCombinatorAlias2 = (Refined<EapCodeCombinator, Predicate7863829697870102672>, EapMessageSuccessFailureCombinator1);
pub struct EapMessageSuccessFailureCombinator1(pub EapMessageSuccessFailureCombinatorAlias1);
impl View for EapMessageSuccessFailureCombinator1 {
    type V = SpecEapMessageSuccessFailureCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapMessageSuccessFailureCombinator1, EapMessageSuccessFailureCombinatorAlias1);

pub struct EapMessageSuccessFailureCombinator2(pub EapMessageSuccessFailureCombinatorAlias2);
impl View for EapMessageSuccessFailureCombinator2 {
    type V = SpecEapMessageSuccessFailureCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EapMessageSuccessFailureCombinator2, EapMessageSuccessFailureCombinatorAlias2);

pub struct EapMessageSuccessFailureCombinator(pub EapMessageSuccessFailureCombinatorAlias);

impl View for EapMessageSuccessFailureCombinator {
    type V = SpecEapMessageSuccessFailureCombinator;
    open spec fn view(&self) -> Self::V { SpecEapMessageSuccessFailureCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapMessageSuccessFailureCombinator {
    type Type = EapMessageSuccessFailure;
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
pub type EapMessageSuccessFailureCombinatorAlias = Mapped<EapMessageSuccessFailureCombinator2, EapMessageSuccessFailureMapper>;


pub open spec fn spec_eap_message_success_failure() -> SpecEapMessageSuccessFailureCombinator {
    SpecEapMessageSuccessFailureCombinator(
    Mapped {
        inner: (Refined { inner: spec_eap_code(), predicate: Predicate7863829697870102672 }, (U8, Refined { inner: U16Be, predicate: TagPred(EAPMESSAGESUCCESSFAILUREEAP_LENGTH_CONST) })),
        mapper: EapMessageSuccessFailureMapper,
    })
}

                
pub fn eap_message_success_failure<'a>() -> (o: EapMessageSuccessFailureCombinator)
    ensures o@ == spec_eap_message_success_failure(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapMessageSuccessFailureCombinator(
    Mapped {
        inner: EapMessageSuccessFailureCombinator2((Refined { inner: eap_code(), predicate: Predicate7863829697870102672 }, EapMessageSuccessFailureCombinator1((U8, Refined { inner: U16Be, predicate: TagPred(EAPMESSAGESUCCESSFAILUREEAP_LENGTH_CONST) })))),
        mapper: EapMessageSuccessFailureMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_message_success_failure()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_message_success_failure<'a>(input: &'a [u8]) -> (res: PResult<<EapMessageSuccessFailureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_message_success_failure().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_message_success_failure().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_message_success_failure().spec_parse(input@) is None,
        spec_eap_message_success_failure().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_message_success_failure();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_message_success_failure<'a>(v: <EapMessageSuccessFailureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_message_success_failure().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_message_success_failure().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_message_success_failure().spec_serialize(v@))
        },
{
    let combinator = eap_message_success_failure();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_message_success_failure_len<'a>(v: <EapMessageSuccessFailureCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_message_success_failure().wf(v@),
        spec_eap_message_success_failure().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_message_success_failure().spec_serialize(v@).len(),
{
    let combinator = eap_message_success_failure();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2CertPayloadInner {
    pub cert_encoding: u8,
    pub cert_data: Seq<u8>,
}

pub type SpecIkev2CertPayloadInnerInner = (u8, Seq<u8>);


impl SpecFrom<SpecIkev2CertPayloadInner> for SpecIkev2CertPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2CertPayloadInner) -> SpecIkev2CertPayloadInnerInner {
        (m.cert_encoding, m.cert_data)
    }
}

impl SpecFrom<SpecIkev2CertPayloadInnerInner> for SpecIkev2CertPayloadInner {
    open spec fn spec_from(m: SpecIkev2CertPayloadInnerInner) -> SpecIkev2CertPayloadInner {
        let (cert_encoding, cert_data) = m;
        SpecIkev2CertPayloadInner { cert_encoding, cert_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2CertPayloadInner<'a> {
    pub cert_encoding: u8,
    pub cert_data: &'a [u8],
}

impl View for Ikev2CertPayloadInner<'_> {
    type V = SpecIkev2CertPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2CertPayloadInner {
            cert_encoding: self.cert_encoding@,
            cert_data: self.cert_data@,
        }
    }
}
pub type Ikev2CertPayloadInnerInner<'a> = (u8, &'a [u8]);

pub type Ikev2CertPayloadInnerInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a Ikev2CertPayloadInner<'a>> for Ikev2CertPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2CertPayloadInner) -> Ikev2CertPayloadInnerInnerRef<'a> {
        (&m.cert_encoding, &m.cert_data)
    }
}

impl<'a> From<Ikev2CertPayloadInnerInner<'a>> for Ikev2CertPayloadInner<'a> {
    fn ex_from(m: Ikev2CertPayloadInnerInner) -> Ikev2CertPayloadInner {
        let (cert_encoding, cert_data) = m;
        Ikev2CertPayloadInner { cert_encoding, cert_data }
    }
}

pub struct Ikev2CertPayloadInnerMapper;
impl View for Ikev2CertPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2CertPayloadInnerMapper {
    type Src = SpecIkev2CertPayloadInnerInner;
    type Dst = SpecIkev2CertPayloadInner;
}
impl SpecIsoProof for Ikev2CertPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2CertPayloadInnerMapper {
    type Src = Ikev2CertPayloadInnerInner<'a>;
    type Dst = Ikev2CertPayloadInner<'a>;
    type RefSrc = Ikev2CertPayloadInnerInnerRef<'a>;
}
type SpecIkev2CertPayloadInnerCombinatorAlias1 = (SpecCertEncodingCombinator, bytes::Tail);
pub struct SpecIkev2CertPayloadInnerCombinator(pub SpecIkev2CertPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2CertPayloadInnerCombinator {
    type Type = SpecIkev2CertPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2CertPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2CertPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2CertPayloadInnerCombinatorAlias = Mapped<SpecIkev2CertPayloadInnerCombinatorAlias1, Ikev2CertPayloadInnerMapper>;
type Ikev2CertPayloadInnerCombinatorAlias1 = (CertEncodingCombinator, bytes::Tail);
pub struct Ikev2CertPayloadInnerCombinator1(pub Ikev2CertPayloadInnerCombinatorAlias1);
impl View for Ikev2CertPayloadInnerCombinator1 {
    type V = SpecIkev2CertPayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2CertPayloadInnerCombinator1, Ikev2CertPayloadInnerCombinatorAlias1);

pub struct Ikev2CertPayloadInnerCombinator(pub Ikev2CertPayloadInnerCombinatorAlias);

impl View for Ikev2CertPayloadInnerCombinator {
    type V = SpecIkev2CertPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2CertPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2CertPayloadInnerCombinator {
    type Type = Ikev2CertPayloadInner<'a>;
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
pub type Ikev2CertPayloadInnerCombinatorAlias = Mapped<Ikev2CertPayloadInnerCombinator1, Ikev2CertPayloadInnerMapper>;


pub open spec fn spec_ikev2_cert_payload_inner() -> SpecIkev2CertPayloadInnerCombinator {
    SpecIkev2CertPayloadInnerCombinator(
    Mapped {
        inner: (spec_cert_encoding(), bytes::Tail),
        mapper: Ikev2CertPayloadInnerMapper,
    })
}

                
pub fn ikev2_cert_payload_inner<'a>() -> (o: Ikev2CertPayloadInnerCombinator)
    ensures o@ == spec_ikev2_cert_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2CertPayloadInnerCombinator(
    Mapped {
        inner: Ikev2CertPayloadInnerCombinator1((cert_encoding(), bytes::Tail)),
        mapper: Ikev2CertPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_cert_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_cert_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2CertPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_cert_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_cert_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_cert_payload_inner().spec_parse(input@) is None,
        spec_ikev2_cert_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_cert_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_cert_payload_inner<'a>(v: <Ikev2CertPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_cert_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_cert_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_cert_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_cert_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_cert_payload_inner_len<'a>(v: <Ikev2CertPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_cert_payload_inner().wf(v@),
        spec_ikev2_cert_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_cert_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_cert_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub mod AuthMethod {
    use super::*;
    pub spec const SPEC_RSADigitalSignature: u8 = 1;
    pub spec const SPEC_SharedKeyMIC: u8 = 2;
    pub spec const SPEC_DSSDigitalSignature: u8 = 3;
    pub exec const RSADigitalSignature: u8 ensures RSADigitalSignature == SPEC_RSADigitalSignature { 1 }
    pub exec const SharedKeyMIC: u8 ensures SharedKeyMIC == SPEC_SharedKeyMIC { 2 }
    pub exec const DSSDigitalSignature: u8 ensures DSSDigitalSignature == SPEC_DSSDigitalSignature { 3 }
}


pub struct SpecAuthMethodCombinator(pub SpecAuthMethodCombinatorAlias);

impl SpecCombinator for SpecAuthMethodCombinator {
    type Type = u8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAuthMethodCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAuthMethodCombinatorAlias::is_prefix_secure() }
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
pub type SpecAuthMethodCombinatorAlias = U8;

pub struct AuthMethodCombinator(pub AuthMethodCombinatorAlias);

impl View for AuthMethodCombinator {
    type V = SpecAuthMethodCombinator;
    open spec fn view(&self) -> Self::V { SpecAuthMethodCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AuthMethodCombinator {
    type Type = u8;
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
pub type AuthMethodCombinatorAlias = U8;


pub open spec fn spec_auth_method() -> SpecAuthMethodCombinator {
    SpecAuthMethodCombinator(U8)
}

                
pub fn auth_method<'a>() -> (o: AuthMethodCombinator)
    ensures o@ == spec_auth_method(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AuthMethodCombinator(U8);
    // assert({
    //     &&& combinator@ == spec_auth_method()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_auth_method<'a>(input: &'a [u8]) -> (res: PResult<<AuthMethodCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_auth_method().spec_parse(input@) == Some((n as int, v@)),
        spec_auth_method().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_auth_method().spec_parse(input@) is None,
        spec_auth_method().spec_parse(input@) is None ==> res is Err,
{
    let combinator = auth_method();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_auth_method<'a>(v: <AuthMethodCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_auth_method().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_auth_method().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_auth_method().spec_serialize(v@))
        },
{
    let combinator = auth_method();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn auth_method_len<'a>(v: <AuthMethodCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_auth_method().wf(v@),
        spec_auth_method().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_auth_method().spec_serialize(v@).len(),
{
    let combinator = auth_method();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2AuthPayloadInner {
    pub auth_method: u8,
    pub reserved: Seq<u8>,
    pub auth_data: Seq<u8>,
}

pub type SpecIkev2AuthPayloadInnerInner = (u8, (Seq<u8>, Seq<u8>));


impl SpecFrom<SpecIkev2AuthPayloadInner> for SpecIkev2AuthPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2AuthPayloadInner) -> SpecIkev2AuthPayloadInnerInner {
        (m.auth_method, (m.reserved, m.auth_data))
    }
}

impl SpecFrom<SpecIkev2AuthPayloadInnerInner> for SpecIkev2AuthPayloadInner {
    open spec fn spec_from(m: SpecIkev2AuthPayloadInnerInner) -> SpecIkev2AuthPayloadInner {
        let (auth_method, (reserved, auth_data)) = m;
        SpecIkev2AuthPayloadInner { auth_method, reserved, auth_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2AuthPayloadInner<'a> {
    pub auth_method: u8,
    pub reserved: &'a [u8],
    pub auth_data: &'a [u8],
}

impl View for Ikev2AuthPayloadInner<'_> {
    type V = SpecIkev2AuthPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2AuthPayloadInner {
            auth_method: self.auth_method@,
            reserved: self.reserved@,
            auth_data: self.auth_data@,
        }
    }
}
pub type Ikev2AuthPayloadInnerInner<'a> = (u8, (&'a [u8], &'a [u8]));

pub type Ikev2AuthPayloadInnerInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a &'a [u8]));
impl<'a> From<&'a Ikev2AuthPayloadInner<'a>> for Ikev2AuthPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2AuthPayloadInner) -> Ikev2AuthPayloadInnerInnerRef<'a> {
        (&m.auth_method, (&m.reserved, &m.auth_data))
    }
}

impl<'a> From<Ikev2AuthPayloadInnerInner<'a>> for Ikev2AuthPayloadInner<'a> {
    fn ex_from(m: Ikev2AuthPayloadInnerInner) -> Ikev2AuthPayloadInner {
        let (auth_method, (reserved, auth_data)) = m;
        Ikev2AuthPayloadInner { auth_method, reserved, auth_data }
    }
}

pub struct Ikev2AuthPayloadInnerMapper;
impl View for Ikev2AuthPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2AuthPayloadInnerMapper {
    type Src = SpecIkev2AuthPayloadInnerInner;
    type Dst = SpecIkev2AuthPayloadInner;
}
impl SpecIsoProof for Ikev2AuthPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2AuthPayloadInnerMapper {
    type Src = Ikev2AuthPayloadInnerInner<'a>;
    type Dst = Ikev2AuthPayloadInner<'a>;
    type RefSrc = Ikev2AuthPayloadInnerInnerRef<'a>;
}
pub spec const SPEC_IKEV2AUTHPAYLOADINNERRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecIkev2AuthPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, bytes::Tail);
type SpecIkev2AuthPayloadInnerCombinatorAlias2 = (SpecAuthMethodCombinator, SpecIkev2AuthPayloadInnerCombinatorAlias1);
pub struct SpecIkev2AuthPayloadInnerCombinator(pub SpecIkev2AuthPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2AuthPayloadInnerCombinator {
    type Type = SpecIkev2AuthPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2AuthPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2AuthPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2AuthPayloadInnerCombinatorAlias = Mapped<SpecIkev2AuthPayloadInnerCombinatorAlias2, Ikev2AuthPayloadInnerMapper>;
pub exec static IKEV2AUTHPAYLOADINNERRESERVED_CONST: [u8; 3]
    ensures IKEV2AUTHPAYLOADINNERRESERVED_CONST@ == SPEC_IKEV2AUTHPAYLOADINNERRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_IKEV2AUTHPAYLOADINNERRESERVED_CONST);
    arr
}
type Ikev2AuthPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, bytes::Tail);
type Ikev2AuthPayloadInnerCombinatorAlias2 = (AuthMethodCombinator, Ikev2AuthPayloadInnerCombinator1);
pub struct Ikev2AuthPayloadInnerCombinator1(pub Ikev2AuthPayloadInnerCombinatorAlias1);
impl View for Ikev2AuthPayloadInnerCombinator1 {
    type V = SpecIkev2AuthPayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2AuthPayloadInnerCombinator1, Ikev2AuthPayloadInnerCombinatorAlias1);

pub struct Ikev2AuthPayloadInnerCombinator2(pub Ikev2AuthPayloadInnerCombinatorAlias2);
impl View for Ikev2AuthPayloadInnerCombinator2 {
    type V = SpecIkev2AuthPayloadInnerCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2AuthPayloadInnerCombinator2, Ikev2AuthPayloadInnerCombinatorAlias2);

pub struct Ikev2AuthPayloadInnerCombinator(pub Ikev2AuthPayloadInnerCombinatorAlias);

impl View for Ikev2AuthPayloadInnerCombinator {
    type V = SpecIkev2AuthPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2AuthPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2AuthPayloadInnerCombinator {
    type Type = Ikev2AuthPayloadInner<'a>;
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
pub type Ikev2AuthPayloadInnerCombinatorAlias = Mapped<Ikev2AuthPayloadInnerCombinator2, Ikev2AuthPayloadInnerMapper>;


pub open spec fn spec_ikev2_auth_payload_inner() -> SpecIkev2AuthPayloadInnerCombinator {
    SpecIkev2AuthPayloadInnerCombinator(
    Mapped {
        inner: (spec_auth_method(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_IKEV2AUTHPAYLOADINNERRESERVED_CONST) }, bytes::Tail)),
        mapper: Ikev2AuthPayloadInnerMapper,
    })
}

                
pub fn ikev2_auth_payload_inner<'a>() -> (o: Ikev2AuthPayloadInnerCombinator)
    ensures o@ == spec_ikev2_auth_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2AuthPayloadInnerCombinator(
    Mapped {
        inner: Ikev2AuthPayloadInnerCombinator2((auth_method(), Ikev2AuthPayloadInnerCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IKEV2AUTHPAYLOADINNERRESERVED_CONST) }, bytes::Tail)))),
        mapper: Ikev2AuthPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_auth_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_auth_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2AuthPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_auth_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_auth_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_auth_payload_inner().spec_parse(input@) is None,
        spec_ikev2_auth_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_auth_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_auth_payload_inner<'a>(v: <Ikev2AuthPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_auth_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_auth_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_auth_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_auth_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_auth_payload_inner_len<'a>(v: <Ikev2AuthPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_auth_payload_inner().wf(v@),
        spec_ikev2_auth_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_auth_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_auth_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2NoncePayloadInner {
    pub nonce_data: Seq<u8>,
}

pub type SpecIkev2NoncePayloadInnerInner = Seq<u8>;


impl SpecFrom<SpecIkev2NoncePayloadInner> for SpecIkev2NoncePayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2NoncePayloadInner) -> SpecIkev2NoncePayloadInnerInner {
        m.nonce_data
    }
}

impl SpecFrom<SpecIkev2NoncePayloadInnerInner> for SpecIkev2NoncePayloadInner {
    open spec fn spec_from(m: SpecIkev2NoncePayloadInnerInner) -> SpecIkev2NoncePayloadInner {
        let nonce_data = m;
        SpecIkev2NoncePayloadInner { nonce_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2NoncePayloadInner<'a> {
    pub nonce_data: &'a [u8],
}

impl View for Ikev2NoncePayloadInner<'_> {
    type V = SpecIkev2NoncePayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2NoncePayloadInner {
            nonce_data: self.nonce_data@,
        }
    }
}
pub type Ikev2NoncePayloadInnerInner<'a> = &'a [u8];

pub type Ikev2NoncePayloadInnerInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a Ikev2NoncePayloadInner<'a>> for Ikev2NoncePayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2NoncePayloadInner) -> Ikev2NoncePayloadInnerInnerRef<'a> {
        &m.nonce_data
    }
}

impl<'a> From<Ikev2NoncePayloadInnerInner<'a>> for Ikev2NoncePayloadInner<'a> {
    fn ex_from(m: Ikev2NoncePayloadInnerInner) -> Ikev2NoncePayloadInner {
        let nonce_data = m;
        Ikev2NoncePayloadInner { nonce_data }
    }
}

pub struct Ikev2NoncePayloadInnerMapper;
impl View for Ikev2NoncePayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2NoncePayloadInnerMapper {
    type Src = SpecIkev2NoncePayloadInnerInner;
    type Dst = SpecIkev2NoncePayloadInner;
}
impl SpecIsoProof for Ikev2NoncePayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2NoncePayloadInnerMapper {
    type Src = Ikev2NoncePayloadInnerInner<'a>;
    type Dst = Ikev2NoncePayloadInner<'a>;
    type RefSrc = Ikev2NoncePayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2NoncePayloadInnerCombinator(pub SpecIkev2NoncePayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2NoncePayloadInnerCombinator {
    type Type = SpecIkev2NoncePayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2NoncePayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2NoncePayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2NoncePayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2NoncePayloadInnerMapper>;

pub struct Ikev2NoncePayloadInnerCombinator(pub Ikev2NoncePayloadInnerCombinatorAlias);

impl View for Ikev2NoncePayloadInnerCombinator {
    type V = SpecIkev2NoncePayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2NoncePayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2NoncePayloadInnerCombinator {
    type Type = Ikev2NoncePayloadInner<'a>;
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
pub type Ikev2NoncePayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2NoncePayloadInnerMapper>;


pub open spec fn spec_ikev2_nonce_payload_inner() -> SpecIkev2NoncePayloadInnerCombinator {
    SpecIkev2NoncePayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2NoncePayloadInnerMapper,
    })
}

                
pub fn ikev2_nonce_payload_inner<'a>() -> (o: Ikev2NoncePayloadInnerCombinator)
    ensures o@ == spec_ikev2_nonce_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2NoncePayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2NoncePayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_nonce_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_nonce_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2NoncePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_nonce_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_nonce_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_nonce_payload_inner().spec_parse(input@) is None,
        spec_ikev2_nonce_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_nonce_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_nonce_payload_inner<'a>(v: <Ikev2NoncePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_nonce_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_nonce_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_nonce_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_nonce_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_nonce_payload_inner_len<'a>(v: <Ikev2NoncePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_nonce_payload_inner().wf(v@),
        spec_ikev2_nonce_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_nonce_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_nonce_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2VendorIdPayloadInner {
    pub vendor_id: Seq<u8>,
}

pub type SpecIkev2VendorIdPayloadInnerInner = Seq<u8>;


impl SpecFrom<SpecIkev2VendorIdPayloadInner> for SpecIkev2VendorIdPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2VendorIdPayloadInner) -> SpecIkev2VendorIdPayloadInnerInner {
        m.vendor_id
    }
}

impl SpecFrom<SpecIkev2VendorIdPayloadInnerInner> for SpecIkev2VendorIdPayloadInner {
    open spec fn spec_from(m: SpecIkev2VendorIdPayloadInnerInner) -> SpecIkev2VendorIdPayloadInner {
        let vendor_id = m;
        SpecIkev2VendorIdPayloadInner { vendor_id }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2VendorIdPayloadInner<'a> {
    pub vendor_id: &'a [u8],
}

impl View for Ikev2VendorIdPayloadInner<'_> {
    type V = SpecIkev2VendorIdPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2VendorIdPayloadInner {
            vendor_id: self.vendor_id@,
        }
    }
}
pub type Ikev2VendorIdPayloadInnerInner<'a> = &'a [u8];

pub type Ikev2VendorIdPayloadInnerInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a Ikev2VendorIdPayloadInner<'a>> for Ikev2VendorIdPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2VendorIdPayloadInner) -> Ikev2VendorIdPayloadInnerInnerRef<'a> {
        &m.vendor_id
    }
}

impl<'a> From<Ikev2VendorIdPayloadInnerInner<'a>> for Ikev2VendorIdPayloadInner<'a> {
    fn ex_from(m: Ikev2VendorIdPayloadInnerInner) -> Ikev2VendorIdPayloadInner {
        let vendor_id = m;
        Ikev2VendorIdPayloadInner { vendor_id }
    }
}

pub struct Ikev2VendorIdPayloadInnerMapper;
impl View for Ikev2VendorIdPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2VendorIdPayloadInnerMapper {
    type Src = SpecIkev2VendorIdPayloadInnerInner;
    type Dst = SpecIkev2VendorIdPayloadInner;
}
impl SpecIsoProof for Ikev2VendorIdPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2VendorIdPayloadInnerMapper {
    type Src = Ikev2VendorIdPayloadInnerInner<'a>;
    type Dst = Ikev2VendorIdPayloadInner<'a>;
    type RefSrc = Ikev2VendorIdPayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2VendorIdPayloadInnerCombinator(pub SpecIkev2VendorIdPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2VendorIdPayloadInnerCombinator {
    type Type = SpecIkev2VendorIdPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2VendorIdPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2VendorIdPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2VendorIdPayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2VendorIdPayloadInnerMapper>;

pub struct Ikev2VendorIdPayloadInnerCombinator(pub Ikev2VendorIdPayloadInnerCombinatorAlias);

impl View for Ikev2VendorIdPayloadInnerCombinator {
    type V = SpecIkev2VendorIdPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2VendorIdPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2VendorIdPayloadInnerCombinator {
    type Type = Ikev2VendorIdPayloadInner<'a>;
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
pub type Ikev2VendorIdPayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2VendorIdPayloadInnerMapper>;


pub open spec fn spec_ikev2_vendor_id_payload_inner() -> SpecIkev2VendorIdPayloadInnerCombinator {
    SpecIkev2VendorIdPayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2VendorIdPayloadInnerMapper,
    })
}

                
pub fn ikev2_vendor_id_payload_inner<'a>() -> (o: Ikev2VendorIdPayloadInnerCombinator)
    ensures o@ == spec_ikev2_vendor_id_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2VendorIdPayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2VendorIdPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_vendor_id_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_vendor_id_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2VendorIdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_vendor_id_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_vendor_id_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_vendor_id_payload_inner().spec_parse(input@) is None,
        spec_ikev2_vendor_id_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_vendor_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_vendor_id_payload_inner<'a>(v: <Ikev2VendorIdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_vendor_id_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_vendor_id_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_vendor_id_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_vendor_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_vendor_id_payload_inner_len<'a>(v: <Ikev2VendorIdPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_vendor_id_payload_inner().wf(v@),
        spec_ikev2_vendor_id_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_vendor_id_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_vendor_id_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecSkPayloadBody {
    pub encrypted_body: Seq<u8>,
}

pub type SpecSkPayloadBodyInner = Seq<u8>;


impl SpecFrom<SpecSkPayloadBody> for SpecSkPayloadBodyInner {
    open spec fn spec_from(m: SpecSkPayloadBody) -> SpecSkPayloadBodyInner {
        m.encrypted_body
    }
}

impl SpecFrom<SpecSkPayloadBodyInner> for SpecSkPayloadBody {
    open spec fn spec_from(m: SpecSkPayloadBodyInner) -> SpecSkPayloadBody {
        let encrypted_body = m;
        SpecSkPayloadBody { encrypted_body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SkPayloadBody<'a> {
    pub encrypted_body: &'a [u8],
}

impl View for SkPayloadBody<'_> {
    type V = SpecSkPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecSkPayloadBody {
            encrypted_body: self.encrypted_body@,
        }
    }
}
pub type SkPayloadBodyInner<'a> = &'a [u8];

pub type SkPayloadBodyInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a SkPayloadBody<'a>> for SkPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a SkPayloadBody) -> SkPayloadBodyInnerRef<'a> {
        &m.encrypted_body
    }
}

impl<'a> From<SkPayloadBodyInner<'a>> for SkPayloadBody<'a> {
    fn ex_from(m: SkPayloadBodyInner) -> SkPayloadBody {
        let encrypted_body = m;
        SkPayloadBody { encrypted_body }
    }
}

pub struct SkPayloadBodyMapper;
impl View for SkPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SkPayloadBodyMapper {
    type Src = SpecSkPayloadBodyInner;
    type Dst = SpecSkPayloadBody;
}
impl SpecIsoProof for SkPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SkPayloadBodyMapper {
    type Src = SkPayloadBodyInner<'a>;
    type Dst = SkPayloadBody<'a>;
    type RefSrc = SkPayloadBodyInnerRef<'a>;
}

pub struct SpecSkPayloadBodyCombinator(pub SpecSkPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecSkPayloadBodyCombinator {
    type Type = SpecSkPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSkPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecSkPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecSkPayloadBodyCombinatorAlias = Mapped<bytes::Variable, SkPayloadBodyMapper>;

pub struct SkPayloadBodyCombinator(pub SkPayloadBodyCombinatorAlias);

impl View for SkPayloadBodyCombinator {
    type V = SpecSkPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecSkPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SkPayloadBodyCombinator {
    type Type = SkPayloadBody<'a>;
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
pub type SkPayloadBodyCombinatorAlias = Mapped<bytes::Variable, SkPayloadBodyMapper>;


pub open spec fn spec_sk_payload_body(payload_length: u16) -> SpecSkPayloadBodyCombinator {
    SpecSkPayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(payload_length) - 4)) as usize),
        mapper: SkPayloadBodyMapper,
    })
}

pub fn sk_payload_body<'a>(payload_length: u16) -> (o: SkPayloadBodyCombinator)
    requires
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures o@ == spec_sk_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = SkPayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(payload_length) - 4)) as usize),
        mapper: SkPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_sk_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_sk_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<SkPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_sk_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_sk_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_sk_payload_body(payload_length@).spec_parse(input@) is None,
        spec_sk_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = sk_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_sk_payload_body<'a>(v: <SkPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_sk_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_sk_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_sk_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = sk_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn sk_payload_body_len<'a>(v: <SkPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_sk_payload_body(payload_length@).wf(v@),
        spec_sk_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_sk_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = sk_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub spec const SPEC_NotifyProtocolId_NotifyNoSpi: u8 = 0;
pub spec const SPEC_NotifyProtocolId_NotifyAH: u8 = 2;
pub spec const SPEC_NotifyProtocolId_NotifyESP: u8 = 3;
pub exec static EXEC_NotifyProtocolId_NotifyNoSpi: u8 ensures EXEC_NotifyProtocolId_NotifyNoSpi == SPEC_NotifyProtocolId_NotifyNoSpi { 0 }
pub exec static EXEC_NotifyProtocolId_NotifyAH: u8 ensures EXEC_NotifyProtocolId_NotifyAH == SPEC_NotifyProtocolId_NotifyAH { 2 }
pub exec static EXEC_NotifyProtocolId_NotifyESP: u8 ensures EXEC_NotifyProtocolId_NotifyESP == SPEC_NotifyProtocolId_NotifyESP { 3 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum NotifyProtocolId {
    NotifyNoSpi = 0,
NotifyAH = 2,
NotifyESP = 3
}
pub type SpecNotifyProtocolId = NotifyProtocolId;

pub type NotifyProtocolIdInner = u8;

pub type NotifyProtocolIdInnerRef<'a> = &'a u8;

impl View for NotifyProtocolId {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<NotifyProtocolIdInner> for NotifyProtocolId {
    type Error = ();

    open spec fn spec_try_from(v: NotifyProtocolIdInner) -> Result<NotifyProtocolId, ()> {
        match v {
            0u8 => Ok(NotifyProtocolId::NotifyNoSpi),
            2u8 => Ok(NotifyProtocolId::NotifyAH),
            3u8 => Ok(NotifyProtocolId::NotifyESP),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<NotifyProtocolId> for NotifyProtocolIdInner {
    type Error = ();

    open spec fn spec_try_from(v: NotifyProtocolId) -> Result<NotifyProtocolIdInner, ()> {
        match v {
            NotifyProtocolId::NotifyNoSpi => Ok(SPEC_NotifyProtocolId_NotifyNoSpi),
            NotifyProtocolId::NotifyAH => Ok(SPEC_NotifyProtocolId_NotifyAH),
            NotifyProtocolId::NotifyESP => Ok(SPEC_NotifyProtocolId_NotifyESP),
        }
    }
}

impl TryFrom<NotifyProtocolIdInner> for NotifyProtocolId {
    type Error = ();

    fn ex_try_from(v: NotifyProtocolIdInner) -> Result<NotifyProtocolId, ()> {
        match v {
            0u8 => Ok(NotifyProtocolId::NotifyNoSpi),
            2u8 => Ok(NotifyProtocolId::NotifyAH),
            3u8 => Ok(NotifyProtocolId::NotifyESP),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a NotifyProtocolId> for NotifyProtocolIdInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a NotifyProtocolId) -> Result<NotifyProtocolIdInnerRef<'a>, ()> {
        match v {
            NotifyProtocolId::NotifyNoSpi => Ok(&EXEC_NotifyProtocolId_NotifyNoSpi),
            NotifyProtocolId::NotifyAH => Ok(&EXEC_NotifyProtocolId_NotifyAH),
            NotifyProtocolId::NotifyESP => Ok(&EXEC_NotifyProtocolId_NotifyESP),
        }
    }
}

pub struct NotifyProtocolIdMapper;

impl View for NotifyProtocolIdMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for NotifyProtocolIdMapper {
    type Src = NotifyProtocolIdInner;
    type Dst = NotifyProtocolId;
}

impl SpecPartialIsoProof for NotifyProtocolIdMapper {
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

impl<'a> PartialIso<'a> for NotifyProtocolIdMapper {
    type Src = NotifyProtocolIdInner;
    type Dst = NotifyProtocolId;
    type RefSrc = NotifyProtocolIdInnerRef<'a>;
}


pub struct SpecNotifyProtocolIdCombinator(pub SpecNotifyProtocolIdCombinatorAlias);

impl SpecCombinator for SpecNotifyProtocolIdCombinator {
    type Type = SpecNotifyProtocolId;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyProtocolIdCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyProtocolIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyProtocolIdCombinatorAlias = TryMap<U8, NotifyProtocolIdMapper>;

pub struct NotifyProtocolIdCombinator(pub NotifyProtocolIdCombinatorAlias);

impl View for NotifyProtocolIdCombinator {
    type V = SpecNotifyProtocolIdCombinator;
    open spec fn view(&self) -> Self::V { SpecNotifyProtocolIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyProtocolIdCombinator {
    type Type = NotifyProtocolId;
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
pub type NotifyProtocolIdCombinatorAlias = TryMap<U8, NotifyProtocolIdMapper>;


pub open spec fn spec_notify_protocol_id() -> SpecNotifyProtocolIdCombinator {
    SpecNotifyProtocolIdCombinator(TryMap { inner: U8, mapper: NotifyProtocolIdMapper })
}

                
pub fn notify_protocol_id<'a>() -> (o: NotifyProtocolIdCombinator)
    ensures o@ == spec_notify_protocol_id(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyProtocolIdCombinator(TryMap { inner: U8, mapper: NotifyProtocolIdMapper });
    // assert({
    //     &&& combinator@ == spec_notify_protocol_id()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_protocol_id<'a>(input: &'a [u8]) -> (res: PResult<<NotifyProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_notify_protocol_id().spec_parse(input@) == Some((n as int, v@)),
        spec_notify_protocol_id().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_protocol_id().spec_parse(input@) is None,
        spec_notify_protocol_id().spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_protocol_id<'a>(v: <NotifyProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_protocol_id().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_protocol_id().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_protocol_id().spec_serialize(v@))
        },
{
    let combinator = notify_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn notify_protocol_id_len<'a>(v: <NotifyProtocolIdCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_notify_protocol_id().wf(v@),
        spec_notify_protocol_id().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_notify_protocol_id().spec_serialize(v@).len(),
{
    let combinator = notify_protocol_id();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2NotifyPayloadInner {
    pub protocol_id: SpecNotifyProtocolId,
    pub spi_size: SpecIpsecSpiSizeOrNone,
    pub notify_msg_type: u16,
    pub spi: Seq<u8>,
    pub notification_data: Seq<u8>,
}

pub type SpecIkev2NotifyPayloadInnerInner = ((SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone), (u16, (Seq<u8>, Seq<u8>)));


impl SpecFrom<SpecIkev2NotifyPayloadInner> for SpecIkev2NotifyPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2NotifyPayloadInner) -> SpecIkev2NotifyPayloadInnerInner {
        ((m.protocol_id, m.spi_size), (m.notify_msg_type, (m.spi, m.notification_data)))
    }
}

impl SpecFrom<SpecIkev2NotifyPayloadInnerInner> for SpecIkev2NotifyPayloadInner {
    open spec fn spec_from(m: SpecIkev2NotifyPayloadInnerInner) -> SpecIkev2NotifyPayloadInner {
        let ((protocol_id, spi_size), (notify_msg_type, (spi, notification_data))) = m;
        SpecIkev2NotifyPayloadInner { protocol_id, spi_size, notify_msg_type, spi, notification_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2NotifyPayloadInner<'a> {
    pub protocol_id: NotifyProtocolId,
    pub spi_size: IpsecSpiSizeOrNone,
    pub notify_msg_type: u16,
    pub spi: &'a [u8],
    pub notification_data: &'a [u8],
}

impl View for Ikev2NotifyPayloadInner<'_> {
    type V = SpecIkev2NotifyPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2NotifyPayloadInner {
            protocol_id: self.protocol_id@,
            spi_size: self.spi_size@,
            notify_msg_type: self.notify_msg_type@,
            spi: self.spi@,
            notification_data: self.notification_data@,
        }
    }
}
pub type Ikev2NotifyPayloadInnerInner<'a> = ((NotifyProtocolId, IpsecSpiSizeOrNone), (u16, (&'a [u8], &'a [u8])));

pub type Ikev2NotifyPayloadInnerInnerRef<'a> = ((&'a NotifyProtocolId, &'a IpsecSpiSizeOrNone), (&'a u16, (&'a &'a [u8], &'a &'a [u8])));
impl<'a> From<&'a Ikev2NotifyPayloadInner<'a>> for Ikev2NotifyPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2NotifyPayloadInner) -> Ikev2NotifyPayloadInnerInnerRef<'a> {
        ((&m.protocol_id, &m.spi_size), (&m.notify_msg_type, (&m.spi, &m.notification_data)))
    }
}

impl<'a> From<Ikev2NotifyPayloadInnerInner<'a>> for Ikev2NotifyPayloadInner<'a> {
    fn ex_from(m: Ikev2NotifyPayloadInnerInner) -> Ikev2NotifyPayloadInner {
        let ((protocol_id, spi_size), (notify_msg_type, (spi, notification_data))) = m;
        Ikev2NotifyPayloadInner { protocol_id, spi_size, notify_msg_type, spi, notification_data }
    }
}

pub struct Ikev2NotifyPayloadInnerMapper;
impl View for Ikev2NotifyPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2NotifyPayloadInnerMapper {
    type Src = SpecIkev2NotifyPayloadInnerInner;
    type Dst = SpecIkev2NotifyPayloadInner;
}
impl SpecIsoProof for Ikev2NotifyPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2NotifyPayloadInnerMapper {
    type Src = Ikev2NotifyPayloadInnerInner<'a>;
    type Dst = Ikev2NotifyPayloadInner<'a>;
    type RefSrc = Ikev2NotifyPayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2NotifyPayloadInnerCombinator(pub SpecIkev2NotifyPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2NotifyPayloadInnerCombinator {
    type Type = SpecIkev2NotifyPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2NotifyPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2NotifyPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2NotifyPayloadInnerCombinatorAlias = Mapped<SpecPair<SpecPair<SpecNotifyProtocolIdCombinator, SpecIpsecSpiSizeOrNoneCombinator>, (SpecNotifyMsgTypeCombinator, (bytes::Variable, bytes::Tail))>, Ikev2NotifyPayloadInnerMapper>;

pub struct Ikev2NotifyPayloadInnerCombinator(pub Ikev2NotifyPayloadInnerCombinatorAlias);

impl View for Ikev2NotifyPayloadInnerCombinator {
    type V = SpecIkev2NotifyPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2NotifyPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2NotifyPayloadInnerCombinator {
    type Type = Ikev2NotifyPayloadInner<'a>;
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
pub type Ikev2NotifyPayloadInnerCombinatorAlias = Mapped<Pair<Pair<NotifyProtocolIdCombinator, IpsecSpiSizeOrNoneCombinator, Ikev2NotifyPayloadInnerCont1>, (NotifyMsgTypeCombinator, (bytes::Variable, bytes::Tail)), Ikev2NotifyPayloadInnerCont0>, Ikev2NotifyPayloadInnerMapper>;


pub open spec fn spec_ikev2_notify_payload_inner() -> SpecIkev2NotifyPayloadInnerCombinator {
    SpecIkev2NotifyPayloadInnerCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_notify_protocol_id(), |deps| spec_ikev2_notify_payload_inner_cont1(deps)), |deps| spec_ikev2_notify_payload_inner_cont0(deps)),
        mapper: Ikev2NotifyPayloadInnerMapper,
    })
}

pub open spec fn spec_ikev2_notify_payload_inner_cont1(deps: SpecNotifyProtocolId) -> SpecIpsecSpiSizeOrNoneCombinator {
    let protocol_id = deps;
    spec_ipsec_spi_size_or_none()
}

impl View for Ikev2NotifyPayloadInnerCont1 {
    type V = spec_fn(SpecNotifyProtocolId) -> SpecIpsecSpiSizeOrNoneCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecNotifyProtocolId| {
            spec_ikev2_notify_payload_inner_cont1(deps)
        }
    }
}

pub open spec fn spec_ikev2_notify_payload_inner_cont0(deps: (SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)) -> (SpecNotifyMsgTypeCombinator, (bytes::Variable, bytes::Tail)) {
    let (protocol_id, spi_size) = deps;
    (spec_notify_msg_type(), (bytes::Variable((usize::spec_from(spi_size)) as usize), bytes::Tail))
}

impl View for Ikev2NotifyPayloadInnerCont0 {
    type V = spec_fn((SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)) -> (SpecNotifyMsgTypeCombinator, (bytes::Variable, bytes::Tail));

    open spec fn view(&self) -> Self::V {
        |deps: (SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)| {
            spec_ikev2_notify_payload_inner_cont0(deps)
        }
    }
}

                
pub fn ikev2_notify_payload_inner<'a>() -> (o: Ikev2NotifyPayloadInnerCombinator)
    ensures o@ == spec_ikev2_notify_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2NotifyPayloadInnerCombinator(
    Mapped {
        inner: Pair::new(Pair::new(notify_protocol_id(), Ikev2NotifyPayloadInnerCont1), Ikev2NotifyPayloadInnerCont0),
        mapper: Ikev2NotifyPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_notify_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_notify_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2NotifyPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_notify_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_notify_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_notify_payload_inner().spec_parse(input@) is None,
        spec_ikev2_notify_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_notify_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_notify_payload_inner<'a>(v: <Ikev2NotifyPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_notify_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_notify_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_notify_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_notify_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_notify_payload_inner_len<'a>(v: <Ikev2NotifyPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_notify_payload_inner().wf(v@),
        spec_ikev2_notify_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_notify_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_notify_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Ikev2NotifyPayloadInnerCont1;
type Ikev2NotifyPayloadInnerCont1Type<'a, 'b> = &'b NotifyProtocolId;
type Ikev2NotifyPayloadInnerCont1SType<'a, 'x> = &'x NotifyProtocolId;
type Ikev2NotifyPayloadInnerCont1Input<'a, 'b, 'x> = POrSType<Ikev2NotifyPayloadInnerCont1Type<'a, 'b>, Ikev2NotifyPayloadInnerCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Ikev2NotifyPayloadInnerCont1Input<'a, 'b, 'x>> for Ikev2NotifyPayloadInnerCont1 {
    type Output = IpsecSpiSizeOrNoneCombinator;

    open spec fn requires(&self, deps: Ikev2NotifyPayloadInnerCont1Input<'a, 'b, 'x>) -> bool {
        &&& (spec_notify_protocol_id()).wf(deps@)
        }

    open spec fn ensures(&self, deps: Ikev2NotifyPayloadInnerCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ikev2_notify_payload_inner_cont1(deps@)
    }

    fn apply(&self, deps: Ikev2NotifyPayloadInnerCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let protocol_id = deps;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
            POrSType::S(deps) => {
                let protocol_id = deps;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
        }
    }
}
pub struct Ikev2NotifyPayloadInnerCont0;
type Ikev2NotifyPayloadInnerCont0Type<'a, 'b> = &'b (NotifyProtocolId, IpsecSpiSizeOrNone);
type Ikev2NotifyPayloadInnerCont0SType<'a, 'x> = (&'x NotifyProtocolId, &'x IpsecSpiSizeOrNone);
type Ikev2NotifyPayloadInnerCont0Input<'a, 'b, 'x> = POrSType<Ikev2NotifyPayloadInnerCont0Type<'a, 'b>, Ikev2NotifyPayloadInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Ikev2NotifyPayloadInnerCont0Input<'a, 'b, 'x>> for Ikev2NotifyPayloadInnerCont0 {
    type Output = (NotifyMsgTypeCombinator, (bytes::Variable, bytes::Tail));

    open spec fn requires(&self, deps: Ikev2NotifyPayloadInnerCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(spec_notify_protocol_id(), |deps| spec_ikev2_notify_payload_inner_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: Ikev2NotifyPayloadInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ikev2_notify_payload_inner_cont0(deps@)
    }

    fn apply(&self, deps: Ikev2NotifyPayloadInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (protocol_id, spi_size) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                (notify_msg_type(), (bytes::Variable((usize::ex_from(spi_size)) as usize), bytes::Tail))
            }
            POrSType::S(deps) => {
                let (protocol_id, spi_size) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                (notify_msg_type(), (bytes::Variable((usize::ex_from(spi_size)) as usize), bytes::Tail))
            }
        }
    }
}
                
pub type SpecDeletePayloadSpisIpsec = Seq<u32>;
pub type DeletePayloadSpisIpsec = RepeatResult<u32>;
pub type DeletePayloadSpisIpsecRef<'a> = &'a RepeatResult<u32>;


pub struct SpecDeletePayloadSpisIpsecCombinator(pub SpecDeletePayloadSpisIpsecCombinatorAlias);

impl SpecCombinator for SpecDeletePayloadSpisIpsecCombinator {
    type Type = SpecDeletePayloadSpisIpsec;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDeletePayloadSpisIpsecCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDeletePayloadSpisIpsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecDeletePayloadSpisIpsecCombinatorAlias = RepeatN<U32Be>;

pub struct DeletePayloadSpisIpsecCombinator(pub DeletePayloadSpisIpsecCombinatorAlias);

impl View for DeletePayloadSpisIpsecCombinator {
    type V = SpecDeletePayloadSpisIpsecCombinator;
    open spec fn view(&self) -> Self::V { SpecDeletePayloadSpisIpsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DeletePayloadSpisIpsecCombinator {
    type Type = DeletePayloadSpisIpsec;
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
pub type DeletePayloadSpisIpsecCombinatorAlias = RepeatN<U32Be>;


pub open spec fn spec_delete_payload_spis_ipsec(num_spis: u16) -> SpecDeletePayloadSpisIpsecCombinator {
    SpecDeletePayloadSpisIpsecCombinator(RepeatN(U32Be, (usize::spec_from(num_spis)) as usize))
}

pub fn delete_payload_spis_ipsec<'a>(num_spis: u16) -> (o: DeletePayloadSpisIpsecCombinator)

    ensures o@ == spec_delete_payload_spis_ipsec(num_spis@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DeletePayloadSpisIpsecCombinator(RepeatN(U32Be, (usize::ex_from(num_spis)) as usize));
    // assert({
    //     &&& combinator@ == spec_delete_payload_spis_ipsec(num_spis@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_delete_payload_spis_ipsec<'a>(input: &'a [u8], num_spis: u16) -> (res: PResult<<DeletePayloadSpisIpsecCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_delete_payload_spis_ipsec(num_spis@).spec_parse(input@) == Some((n as int, v@)),
        spec_delete_payload_spis_ipsec(num_spis@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_delete_payload_spis_ipsec(num_spis@).spec_parse(input@) is None,
        spec_delete_payload_spis_ipsec(num_spis@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = delete_payload_spis_ipsec( num_spis );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_delete_payload_spis_ipsec<'a>(v: <DeletePayloadSpisIpsecCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, num_spis: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_delete_payload_spis_ipsec(num_spis@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_delete_payload_spis_ipsec(num_spis@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_delete_payload_spis_ipsec(num_spis@).spec_serialize(v@))
        },
{
    let combinator = delete_payload_spis_ipsec( num_spis );
    combinator.serialize(v, data, pos)
}

pub fn delete_payload_spis_ipsec_len<'a>(v: <DeletePayloadSpisIpsecCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, num_spis: u16) -> (serialize_len: usize)
    requires
        spec_delete_payload_spis_ipsec(num_spis@).wf(v@),
        spec_delete_payload_spis_ipsec(num_spis@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_delete_payload_spis_ipsec(num_spis@).spec_serialize(v@).len(),
{
    let combinator = delete_payload_spis_ipsec( num_spis );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecEapMessageReqResp {
    pub code: u8,
    pub identifier: u8,
    pub eap_length: u16,
    pub eap_type: u8,
    pub type_data: Seq<u8>,
}

pub type SpecEapMessageReqRespInner = ((u8, (u8, u16)), (u8, Seq<u8>));


impl SpecFrom<SpecEapMessageReqResp> for SpecEapMessageReqRespInner {
    open spec fn spec_from(m: SpecEapMessageReqResp) -> SpecEapMessageReqRespInner {
        ((m.code, (m.identifier, m.eap_length)), (m.eap_type, m.type_data))
    }
}

impl SpecFrom<SpecEapMessageReqRespInner> for SpecEapMessageReqResp {
    open spec fn spec_from(m: SpecEapMessageReqRespInner) -> SpecEapMessageReqResp {
        let ((code, (identifier, eap_length)), (eap_type, type_data)) = m;
        SpecEapMessageReqResp { code, identifier, eap_length, eap_type, type_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EapMessageReqResp<'a> {
    pub code: u8,
    pub identifier: u8,
    pub eap_length: u16,
    pub eap_type: u8,
    pub type_data: &'a [u8],
}

impl View for EapMessageReqResp<'_> {
    type V = SpecEapMessageReqResp;

    open spec fn view(&self) -> Self::V {
        SpecEapMessageReqResp {
            code: self.code@,
            identifier: self.identifier@,
            eap_length: self.eap_length@,
            eap_type: self.eap_type@,
            type_data: self.type_data@,
        }
    }
}
pub type EapMessageReqRespInner<'a> = ((u8, (u8, u16)), (u8, &'a [u8]));

pub type EapMessageReqRespInnerRef<'a> = ((&'a u8, (&'a u8, &'a u16)), (&'a u8, &'a &'a [u8]));
impl<'a> From<&'a EapMessageReqResp<'a>> for EapMessageReqRespInnerRef<'a> {
    fn ex_from(m: &'a EapMessageReqResp) -> EapMessageReqRespInnerRef<'a> {
        ((&m.code, (&m.identifier, &m.eap_length)), (&m.eap_type, &m.type_data))
    }
}

impl<'a> From<EapMessageReqRespInner<'a>> for EapMessageReqResp<'a> {
    fn ex_from(m: EapMessageReqRespInner) -> EapMessageReqResp {
        let ((code, (identifier, eap_length)), (eap_type, type_data)) = m;
        EapMessageReqResp { code, identifier, eap_length, eap_type, type_data }
    }
}

pub struct EapMessageReqRespMapper;
impl View for EapMessageReqRespMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EapMessageReqRespMapper {
    type Src = SpecEapMessageReqRespInner;
    type Dst = SpecEapMessageReqResp;
}
impl SpecIsoProof for EapMessageReqRespMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EapMessageReqRespMapper {
    type Src = EapMessageReqRespInner<'a>;
    type Dst = EapMessageReqResp<'a>;
    type RefSrc = EapMessageReqRespInnerRef<'a>;
}

pub struct SpecEapMessageReqRespCombinator(pub SpecEapMessageReqRespCombinatorAlias);

impl SpecCombinator for SpecEapMessageReqRespCombinator {
    type Type = SpecEapMessageReqResp;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEapMessageReqRespCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecEapMessageReqRespCombinatorAlias::is_prefix_secure() }
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
pub type SpecEapMessageReqRespCombinatorAlias = Mapped<SpecPair<(Refined<SpecEapCodeCombinator, Predicate8053454275691315570>, (U8, Refined<U16Be, Predicate7010197279221949030>)), (U8, bytes::Variable)>, EapMessageReqRespMapper>;
pub struct Predicate8053454275691315570;
impl View for Predicate8053454275691315570 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8053454275691315570 {
    fn apply(&self, e: &u8) -> bool {
        (*e) == 1 || (*e) == 2
    }
}
impl SpecPred<u8> for Predicate8053454275691315570 {
    open spec fn spec_apply(&self, e: &u8) -> bool {
        (*e) == 1 || (*e) == 2
    }
}

pub struct EapMessageReqRespCombinator(pub EapMessageReqRespCombinatorAlias);

impl View for EapMessageReqRespCombinator {
    type V = SpecEapMessageReqRespCombinator;
    open spec fn view(&self) -> Self::V { SpecEapMessageReqRespCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EapMessageReqRespCombinator {
    type Type = EapMessageReqResp<'a>;
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
pub type EapMessageReqRespCombinatorAlias = Mapped<Pair<(Refined<EapCodeCombinator, Predicate8053454275691315570>, (U8, Refined<U16Be, Predicate7010197279221949030>)), (U8, bytes::Variable), EapMessageReqRespCont0>, EapMessageReqRespMapper>;


pub open spec fn spec_eap_message_req_resp() -> SpecEapMessageReqRespCombinator {
    SpecEapMessageReqRespCombinator(
    Mapped {
        inner: Pair::spec_new((Refined { inner: spec_eap_code(), predicate: Predicate8053454275691315570 }, (U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 })), |deps| spec_eap_message_req_resp_cont0(deps)),
        mapper: EapMessageReqRespMapper,
    })
}

pub open spec fn spec_eap_message_req_resp_cont0(deps: (u8, (u8, u16))) -> (U8, bytes::Variable) {
    let (_, (_, eap_length)) = deps;
    (U8, bytes::Variable(((usize::spec_from(eap_length) - 5)) as usize))
}

impl View for EapMessageReqRespCont0 {
    type V = spec_fn((u8, (u8, u16))) -> (U8, bytes::Variable);

    open spec fn view(&self) -> Self::V {
        |deps: (u8, (u8, u16))| {
            spec_eap_message_req_resp_cont0(deps)
        }
    }
}

                
pub fn eap_message_req_resp<'a>() -> (o: EapMessageReqRespCombinator)
    ensures o@ == spec_eap_message_req_resp(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = EapMessageReqRespCombinator(
    Mapped {
        inner: Pair::new((Refined { inner: eap_code(), predicate: Predicate8053454275691315570 }, (U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 })), EapMessageReqRespCont0),
        mapper: EapMessageReqRespMapper,
    });
    // assert({
    //     &&& combinator@ == spec_eap_message_req_resp()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_eap_message_req_resp<'a>(input: &'a [u8]) -> (res: PResult<<EapMessageReqRespCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_eap_message_req_resp().spec_parse(input@) == Some((n as int, v@)),
        spec_eap_message_req_resp().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_eap_message_req_resp().spec_parse(input@) is None,
        spec_eap_message_req_resp().spec_parse(input@) is None ==> res is Err,
{
    let combinator = eap_message_req_resp();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_eap_message_req_resp<'a>(v: <EapMessageReqRespCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_eap_message_req_resp().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_eap_message_req_resp().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_eap_message_req_resp().spec_serialize(v@))
        },
{
    let combinator = eap_message_req_resp();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn eap_message_req_resp_len<'a>(v: <EapMessageReqRespCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_eap_message_req_resp().wf(v@),
        spec_eap_message_req_resp().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_eap_message_req_resp().spec_serialize(v@).len(),
{
    let combinator = eap_message_req_resp();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct EapMessageReqRespCont0;
type EapMessageReqRespCont0Type<'a, 'b> = &'b (u8, (u8, u16));
type EapMessageReqRespCont0SType<'a, 'x> = (&'x u8, (&'x u8, &'x u16));
type EapMessageReqRespCont0Input<'a, 'b, 'x> = POrSType<EapMessageReqRespCont0Type<'a, 'b>, EapMessageReqRespCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EapMessageReqRespCont0Input<'a, 'b, 'x>> for EapMessageReqRespCont0 {
    type Output = (U8, bytes::Variable);

    open spec fn requires(&self, deps: EapMessageReqRespCont0Input<'a, 'b, 'x>) -> bool {
        &&& ((Refined { inner: spec_eap_code(), predicate: Predicate8053454275691315570 }, (U8, Refined { inner: U16Be, predicate: Predicate7010197279221949030 }))).wf(deps@)
        }

    open spec fn ensures(&self, deps: EapMessageReqRespCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_eap_message_req_resp_cont0(deps@)
    }

    fn apply(&self, deps: EapMessageReqRespCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, (_, eap_length)) = deps;
                let eap_length = *eap_length;
                (U8, bytes::Variable(((usize::ex_from(eap_length) - 5)) as usize))
            }
            POrSType::S(deps) => {
                let (_, (_, eap_length)) = deps;
                let eap_length = *eap_length;
                (U8, bytes::Variable(((usize::ex_from(eap_length) - 5)) as usize))
            }
        }
    }
}
                

pub struct SpecNotifyPayloadBodySpi4 {
    pub spi: Seq<u8>,
    pub notification_data: Seq<u8>,
}

pub type SpecNotifyPayloadBodySpi4Inner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecNotifyPayloadBodySpi4> for SpecNotifyPayloadBodySpi4Inner {
    open spec fn spec_from(m: SpecNotifyPayloadBodySpi4) -> SpecNotifyPayloadBodySpi4Inner {
        (m.spi, m.notification_data)
    }
}

impl SpecFrom<SpecNotifyPayloadBodySpi4Inner> for SpecNotifyPayloadBodySpi4 {
    open spec fn spec_from(m: SpecNotifyPayloadBodySpi4Inner) -> SpecNotifyPayloadBodySpi4 {
        let (spi, notification_data) = m;
        SpecNotifyPayloadBodySpi4 { spi, notification_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NotifyPayloadBodySpi4<'a> {
    pub spi: &'a [u8],
    pub notification_data: &'a [u8],
}

impl View for NotifyPayloadBodySpi4<'_> {
    type V = SpecNotifyPayloadBodySpi4;

    open spec fn view(&self) -> Self::V {
        SpecNotifyPayloadBodySpi4 {
            spi: self.spi@,
            notification_data: self.notification_data@,
        }
    }
}
pub type NotifyPayloadBodySpi4Inner<'a> = (&'a [u8], &'a [u8]);

pub type NotifyPayloadBodySpi4InnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a NotifyPayloadBodySpi4<'a>> for NotifyPayloadBodySpi4InnerRef<'a> {
    fn ex_from(m: &'a NotifyPayloadBodySpi4) -> NotifyPayloadBodySpi4InnerRef<'a> {
        (&m.spi, &m.notification_data)
    }
}

impl<'a> From<NotifyPayloadBodySpi4Inner<'a>> for NotifyPayloadBodySpi4<'a> {
    fn ex_from(m: NotifyPayloadBodySpi4Inner) -> NotifyPayloadBodySpi4 {
        let (spi, notification_data) = m;
        NotifyPayloadBodySpi4 { spi, notification_data }
    }
}

pub struct NotifyPayloadBodySpi4Mapper;
impl View for NotifyPayloadBodySpi4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NotifyPayloadBodySpi4Mapper {
    type Src = SpecNotifyPayloadBodySpi4Inner;
    type Dst = SpecNotifyPayloadBodySpi4;
}
impl SpecIsoProof for NotifyPayloadBodySpi4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NotifyPayloadBodySpi4Mapper {
    type Src = NotifyPayloadBodySpi4Inner<'a>;
    type Dst = NotifyPayloadBodySpi4<'a>;
    type RefSrc = NotifyPayloadBodySpi4InnerRef<'a>;
}
type SpecNotifyPayloadBodySpi4CombinatorAlias1 = (bytes::Fixed<4>, bytes::Tail);
pub struct SpecNotifyPayloadBodySpi4Combinator(pub SpecNotifyPayloadBodySpi4CombinatorAlias);

impl SpecCombinator for SpecNotifyPayloadBodySpi4Combinator {
    type Type = SpecNotifyPayloadBodySpi4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyPayloadBodySpi4Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyPayloadBodySpi4CombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyPayloadBodySpi4CombinatorAlias = Mapped<SpecNotifyPayloadBodySpi4CombinatorAlias1, NotifyPayloadBodySpi4Mapper>;
type NotifyPayloadBodySpi4CombinatorAlias1 = (bytes::Fixed<4>, bytes::Tail);
pub struct NotifyPayloadBodySpi4Combinator1(pub NotifyPayloadBodySpi4CombinatorAlias1);
impl View for NotifyPayloadBodySpi4Combinator1 {
    type V = SpecNotifyPayloadBodySpi4CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NotifyPayloadBodySpi4Combinator1, NotifyPayloadBodySpi4CombinatorAlias1);

pub struct NotifyPayloadBodySpi4Combinator(pub NotifyPayloadBodySpi4CombinatorAlias);

impl View for NotifyPayloadBodySpi4Combinator {
    type V = SpecNotifyPayloadBodySpi4Combinator;
    open spec fn view(&self) -> Self::V { SpecNotifyPayloadBodySpi4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyPayloadBodySpi4Combinator {
    type Type = NotifyPayloadBodySpi4<'a>;
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
pub type NotifyPayloadBodySpi4CombinatorAlias = Mapped<NotifyPayloadBodySpi4Combinator1, NotifyPayloadBodySpi4Mapper>;


pub open spec fn spec_notify_payload_body_spi4() -> SpecNotifyPayloadBodySpi4Combinator {
    SpecNotifyPayloadBodySpi4Combinator(
    Mapped {
        inner: (bytes::Fixed::<4>, bytes::Tail),
        mapper: NotifyPayloadBodySpi4Mapper,
    })
}

                
pub fn notify_payload_body_spi4<'a>() -> (o: NotifyPayloadBodySpi4Combinator)
    ensures o@ == spec_notify_payload_body_spi4(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyPayloadBodySpi4Combinator(
    Mapped {
        inner: NotifyPayloadBodySpi4Combinator1((bytes::Fixed::<4>, bytes::Tail)),
        mapper: NotifyPayloadBodySpi4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_notify_payload_body_spi4()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_payload_body_spi4<'a>(input: &'a [u8]) -> (res: PResult<<NotifyPayloadBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_notify_payload_body_spi4().spec_parse(input@) == Some((n as int, v@)),
        spec_notify_payload_body_spi4().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_payload_body_spi4().spec_parse(input@) is None,
        spec_notify_payload_body_spi4().spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_payload_body_spi4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_payload_body_spi4<'a>(v: <NotifyPayloadBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_payload_body_spi4().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_payload_body_spi4().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_payload_body_spi4().spec_serialize(v@))
        },
{
    let combinator = notify_payload_body_spi4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn notify_payload_body_spi4_len<'a>(v: <NotifyPayloadBodySpi4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_notify_payload_body_spi4().wf(v@),
        spec_notify_payload_body_spi4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_notify_payload_body_spi4().spec_serialize(v@).len(),
{
    let combinator = notify_payload_body_spi4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecNotifyPayloadBodyRest {
    Variant0(SpecNotifyPayloadBodySpi0),
    Variant1(SpecNotifyPayloadBodySpi4),
}

pub type SpecNotifyPayloadBodyRestInner = Either<SpecNotifyPayloadBodySpi0, SpecNotifyPayloadBodySpi4>;

impl SpecFrom<SpecNotifyPayloadBodyRest> for SpecNotifyPayloadBodyRestInner {
    open spec fn spec_from(m: SpecNotifyPayloadBodyRest) -> SpecNotifyPayloadBodyRestInner {
        match m {
            SpecNotifyPayloadBodyRest::Variant0(m) => Either::Left(m),
            SpecNotifyPayloadBodyRest::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecNotifyPayloadBodyRestInner> for SpecNotifyPayloadBodyRest {
    open spec fn spec_from(m: SpecNotifyPayloadBodyRestInner) -> SpecNotifyPayloadBodyRest {
        match m {
            Either::Left(m) => SpecNotifyPayloadBodyRest::Variant0(m),
            Either::Right(m) => SpecNotifyPayloadBodyRest::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NotifyPayloadBodyRest<'a> {
    Variant0(NotifyPayloadBodySpi0<'a>),
    Variant1(NotifyPayloadBodySpi4<'a>),
}

pub type NotifyPayloadBodyRestInner<'a> = Either<NotifyPayloadBodySpi0<'a>, NotifyPayloadBodySpi4<'a>>;

pub type NotifyPayloadBodyRestInnerRef<'a> = Either<&'a NotifyPayloadBodySpi0<'a>, &'a NotifyPayloadBodySpi4<'a>>;


impl<'a> View for NotifyPayloadBodyRest<'a> {
    type V = SpecNotifyPayloadBodyRest;
    open spec fn view(&self) -> Self::V {
        match self {
            NotifyPayloadBodyRest::Variant0(m) => SpecNotifyPayloadBodyRest::Variant0(m@),
            NotifyPayloadBodyRest::Variant1(m) => SpecNotifyPayloadBodyRest::Variant1(m@),
        }
    }
}


impl<'a> From<&'a NotifyPayloadBodyRest<'a>> for NotifyPayloadBodyRestInnerRef<'a> {
    fn ex_from(m: &'a NotifyPayloadBodyRest<'a>) -> NotifyPayloadBodyRestInnerRef<'a> {
        match m {
            NotifyPayloadBodyRest::Variant0(m) => Either::Left(m),
            NotifyPayloadBodyRest::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<NotifyPayloadBodyRestInner<'a>> for NotifyPayloadBodyRest<'a> {
    fn ex_from(m: NotifyPayloadBodyRestInner<'a>) -> NotifyPayloadBodyRest<'a> {
        match m {
            Either::Left(m) => NotifyPayloadBodyRest::Variant0(m),
            Either::Right(m) => NotifyPayloadBodyRest::Variant1(m),
        }
    }
    
}


pub struct NotifyPayloadBodyRestMapper;
impl View for NotifyPayloadBodyRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NotifyPayloadBodyRestMapper {
    type Src = SpecNotifyPayloadBodyRestInner;
    type Dst = SpecNotifyPayloadBodyRest;
}
impl SpecIsoProof for NotifyPayloadBodyRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NotifyPayloadBodyRestMapper {
    type Src = NotifyPayloadBodyRestInner<'a>;
    type Dst = NotifyPayloadBodyRest<'a>;
    type RefSrc = NotifyPayloadBodyRestInnerRef<'a>;
}

type SpecNotifyPayloadBodyRestCombinatorAlias1 = Choice<Cond<SpecNotifyPayloadBodySpi0Combinator>, Cond<SpecNotifyPayloadBodySpi4Combinator>>;
pub struct SpecNotifyPayloadBodyRestCombinator(pub SpecNotifyPayloadBodyRestCombinatorAlias);

impl SpecCombinator for SpecNotifyPayloadBodyRestCombinator {
    type Type = SpecNotifyPayloadBodyRest;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyPayloadBodyRestCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyPayloadBodyRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyPayloadBodyRestCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecNotifyPayloadBodyRestCombinatorAlias1, NotifyPayloadBodyRestMapper>>;
type NotifyPayloadBodyRestCombinatorAlias1 = Choice<Cond<NotifyPayloadBodySpi0Combinator>, Cond<NotifyPayloadBodySpi4Combinator>>;
pub struct NotifyPayloadBodyRestCombinator1(pub NotifyPayloadBodyRestCombinatorAlias1);
impl View for NotifyPayloadBodyRestCombinator1 {
    type V = SpecNotifyPayloadBodyRestCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NotifyPayloadBodyRestCombinator1, NotifyPayloadBodyRestCombinatorAlias1);

pub struct NotifyPayloadBodyRestCombinator(pub NotifyPayloadBodyRestCombinatorAlias);

impl View for NotifyPayloadBodyRestCombinator {
    type V = SpecNotifyPayloadBodyRestCombinator;
    open spec fn view(&self) -> Self::V { SpecNotifyPayloadBodyRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyPayloadBodyRestCombinator {
    type Type = NotifyPayloadBodyRest<'a>;
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
pub type NotifyPayloadBodyRestCombinatorAlias = AndThen<bytes::Variable, Mapped<NotifyPayloadBodyRestCombinator1, NotifyPayloadBodyRestMapper>>;


pub open spec fn spec_notify_payload_body_rest(spi_size: SpecIpsecSpiSizeOrNone, payload_length: u16) -> SpecNotifyPayloadBodyRestCombinator {
    SpecNotifyPayloadBodyRestCombinator(AndThen(bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize), Mapped { inner: Choice(Cond { cond: spi_size == 0, inner: spec_notify_payload_body_spi0() }, Cond { cond: spi_size == 4, inner: spec_notify_payload_body_spi4() }), mapper: NotifyPayloadBodyRestMapper }))
}

pub fn notify_payload_body_rest<'a>(spi_size: IpsecSpiSizeOrNone, payload_length: u16) -> (o: NotifyPayloadBodyRestCombinator)
    requires
        spec_ipsec_spi_size_or_none().wf(spi_size@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_notify_payload_body_rest(spi_size@, payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyPayloadBodyRestCombinator(AndThen(bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize), Mapped { inner: NotifyPayloadBodyRestCombinator1(Choice::new(Cond { cond: spi_size == 0, inner: notify_payload_body_spi0() }, Cond { cond: spi_size == 4, inner: notify_payload_body_spi4() })), mapper: NotifyPayloadBodyRestMapper }));
    // assert({
    //     &&& combinator@ == spec_notify_payload_body_rest(spi_size@, payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_payload_body_rest<'a>(input: &'a [u8], spi_size: IpsecSpiSizeOrNone, payload_length: u16) -> (res: PResult<<NotifyPayloadBodyRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_ipsec_spi_size_or_none().wf(spi_size@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_notify_payload_body_rest(spi_size@, payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_notify_payload_body_rest(spi_size@, payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_payload_body_rest(spi_size@, payload_length@).spec_parse(input@) is None,
        spec_notify_payload_body_rest(spi_size@, payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_payload_body_rest( spi_size, payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_payload_body_rest<'a>(v: <NotifyPayloadBodyRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, spi_size: IpsecSpiSizeOrNone, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_payload_body_rest(spi_size@, payload_length@).wf(v@),
        spec_ipsec_spi_size_or_none().wf(spi_size@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_payload_body_rest(spi_size@, payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_payload_body_rest(spi_size@, payload_length@).spec_serialize(v@))
        },
{
    let combinator = notify_payload_body_rest( spi_size, payload_length );
    combinator.serialize(v, data, pos)
}

pub fn notify_payload_body_rest_len<'a>(v: <NotifyPayloadBodyRestCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, spi_size: IpsecSpiSizeOrNone, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_notify_payload_body_rest(spi_size@, payload_length@).wf(v@),
        spec_notify_payload_body_rest(spi_size@, payload_length@).spec_serialize(v@).len() <= usize::MAX,
        spec_ipsec_spi_size_or_none().wf(spi_size@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_notify_payload_body_rest(spi_size@, payload_length@).spec_serialize(v@).len(),
{
    let combinator = notify_payload_body_rest( spi_size, payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecNotifyPayloadBody {
    pub protocol_id: SpecNotifyProtocolId,
    pub spi_size: SpecIpsecSpiSizeOrNone,
    pub notify_msg_type: u16,
    pub rest: SpecNotifyPayloadBodyRest,
}

pub type SpecNotifyPayloadBodyInner = ((SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone), (u16, SpecNotifyPayloadBodyRest));


impl SpecFrom<SpecNotifyPayloadBody> for SpecNotifyPayloadBodyInner {
    open spec fn spec_from(m: SpecNotifyPayloadBody) -> SpecNotifyPayloadBodyInner {
        ((m.protocol_id, m.spi_size), (m.notify_msg_type, m.rest))
    }
}

impl SpecFrom<SpecNotifyPayloadBodyInner> for SpecNotifyPayloadBody {
    open spec fn spec_from(m: SpecNotifyPayloadBodyInner) -> SpecNotifyPayloadBody {
        let ((protocol_id, spi_size), (notify_msg_type, rest)) = m;
        SpecNotifyPayloadBody { protocol_id, spi_size, notify_msg_type, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NotifyPayloadBody<'a> {
    pub protocol_id: NotifyProtocolId,
    pub spi_size: IpsecSpiSizeOrNone,
    pub notify_msg_type: u16,
    pub rest: NotifyPayloadBodyRest<'a>,
}

impl View for NotifyPayloadBody<'_> {
    type V = SpecNotifyPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecNotifyPayloadBody {
            protocol_id: self.protocol_id@,
            spi_size: self.spi_size@,
            notify_msg_type: self.notify_msg_type@,
            rest: self.rest@,
        }
    }
}
pub type NotifyPayloadBodyInner<'a> = ((NotifyProtocolId, IpsecSpiSizeOrNone), (u16, NotifyPayloadBodyRest<'a>));

pub type NotifyPayloadBodyInnerRef<'a> = ((&'a NotifyProtocolId, &'a IpsecSpiSizeOrNone), (&'a u16, &'a NotifyPayloadBodyRest<'a>));
impl<'a> From<&'a NotifyPayloadBody<'a>> for NotifyPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a NotifyPayloadBody) -> NotifyPayloadBodyInnerRef<'a> {
        ((&m.protocol_id, &m.spi_size), (&m.notify_msg_type, &m.rest))
    }
}

impl<'a> From<NotifyPayloadBodyInner<'a>> for NotifyPayloadBody<'a> {
    fn ex_from(m: NotifyPayloadBodyInner) -> NotifyPayloadBody {
        let ((protocol_id, spi_size), (notify_msg_type, rest)) = m;
        NotifyPayloadBody { protocol_id, spi_size, notify_msg_type, rest }
    }
}

pub struct NotifyPayloadBodyMapper;
impl View for NotifyPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NotifyPayloadBodyMapper {
    type Src = SpecNotifyPayloadBodyInner;
    type Dst = SpecNotifyPayloadBody;
}
impl SpecIsoProof for NotifyPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NotifyPayloadBodyMapper {
    type Src = NotifyPayloadBodyInner<'a>;
    type Dst = NotifyPayloadBody<'a>;
    type RefSrc = NotifyPayloadBodyInnerRef<'a>;
}

pub struct SpecNotifyPayloadBodyCombinator(pub SpecNotifyPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecNotifyPayloadBodyCombinator {
    type Type = SpecNotifyPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNotifyPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNotifyPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecNotifyPayloadBodyCombinatorAlias = Mapped<SpecPair<SpecPair<SpecNotifyProtocolIdCombinator, SpecIpsecSpiSizeOrNoneCombinator>, (SpecNotifyMsgTypeCombinator, SpecNotifyPayloadBodyRestCombinator)>, NotifyPayloadBodyMapper>;

pub struct NotifyPayloadBodyCombinator(pub NotifyPayloadBodyCombinatorAlias);

impl View for NotifyPayloadBodyCombinator {
    type V = SpecNotifyPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecNotifyPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NotifyPayloadBodyCombinator {
    type Type = NotifyPayloadBody<'a>;
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
pub type NotifyPayloadBodyCombinatorAlias = Mapped<Pair<Pair<NotifyProtocolIdCombinator, IpsecSpiSizeOrNoneCombinator, NotifyPayloadBodyCont1>, (NotifyMsgTypeCombinator, NotifyPayloadBodyRestCombinator), NotifyPayloadBodyCont0>, NotifyPayloadBodyMapper>;


pub open spec fn spec_notify_payload_body(payload_length: u16) -> SpecNotifyPayloadBodyCombinator {
    SpecNotifyPayloadBodyCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_notify_protocol_id(), |deps| spec_notify_payload_body_cont1(payload_length, deps)), |deps| spec_notify_payload_body_cont0(payload_length, deps)),
        mapper: NotifyPayloadBodyMapper,
    })
}

pub open spec fn spec_notify_payload_body_cont1(payload_length: u16, deps: SpecNotifyProtocolId) -> SpecIpsecSpiSizeOrNoneCombinator {
    let protocol_id = deps;
    spec_ipsec_spi_size_or_none()
}

impl View for NotifyPayloadBodyCont1 {
    type V = spec_fn(SpecNotifyProtocolId) -> SpecIpsecSpiSizeOrNoneCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecNotifyProtocolId| {
            spec_notify_payload_body_cont1(self.payload_length@, deps)
        }
    }
}

pub open spec fn spec_notify_payload_body_cont0(payload_length: u16, deps: (SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)) -> (SpecNotifyMsgTypeCombinator, SpecNotifyPayloadBodyRestCombinator) {
    let (protocol_id, spi_size) = deps;
    (spec_notify_msg_type(), spec_notify_payload_body_rest(spi_size, payload_length))
}

impl View for NotifyPayloadBodyCont0 {
    type V = spec_fn((SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)) -> (SpecNotifyMsgTypeCombinator, SpecNotifyPayloadBodyRestCombinator);

    open spec fn view(&self) -> Self::V {
        |deps: (SpecNotifyProtocolId, SpecIpsecSpiSizeOrNone)| {
            spec_notify_payload_body_cont0(self.payload_length@, deps)
        }
    }
}

pub fn notify_payload_body<'a>(payload_length: u16) -> (o: NotifyPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_notify_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NotifyPayloadBodyCombinator(
    Mapped {
        inner: Pair::new(Pair::new(notify_protocol_id(), NotifyPayloadBodyCont1 { payload_length }), NotifyPayloadBodyCont0 { payload_length }),
        mapper: NotifyPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_notify_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_notify_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<NotifyPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_notify_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_notify_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_notify_payload_body(payload_length@).spec_parse(input@) is None,
        spec_notify_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = notify_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_notify_payload_body<'a>(v: <NotifyPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_notify_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_notify_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_notify_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = notify_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn notify_payload_body_len<'a>(v: <NotifyPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_notify_payload_body(payload_length@).wf(v@),
        spec_notify_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_notify_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = notify_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct NotifyPayloadBodyCont1 {
    pub payload_length: u16,
}
type NotifyPayloadBodyCont1Type<'a, 'b> = &'b NotifyProtocolId;
type NotifyPayloadBodyCont1SType<'a, 'x> = &'x NotifyProtocolId;
type NotifyPayloadBodyCont1Input<'a, 'b, 'x> = POrSType<NotifyPayloadBodyCont1Type<'a, 'b>, NotifyPayloadBodyCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NotifyPayloadBodyCont1Input<'a, 'b, 'x>> for NotifyPayloadBodyCont1 {
    type Output = IpsecSpiSizeOrNoneCombinator;

    open spec fn requires(&self, deps: NotifyPayloadBodyCont1Input<'a, 'b, 'x>) -> bool {        let payload_length = self.payload_length@;

        &&& ((self.payload_length@) >= 8 && (self.payload_length@) <= 65535)
        &&& (spec_notify_protocol_id()).wf(deps@)
        }

    open spec fn ensures(&self, deps: NotifyPayloadBodyCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_notify_payload_body_cont1(self.payload_length@, deps@)
    }

    fn apply(&self, deps: NotifyPayloadBodyCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let protocol_id = deps;
                let payload_length = self.payload_length;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
            POrSType::S(deps) => {
                let protocol_id = deps;
                let payload_length = self.payload_length;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
        }
    }
}
pub struct NotifyPayloadBodyCont0 {
    pub payload_length: u16,
}
type NotifyPayloadBodyCont0Type<'a, 'b> = &'b (NotifyProtocolId, IpsecSpiSizeOrNone);
type NotifyPayloadBodyCont0SType<'a, 'x> = (&'x NotifyProtocolId, &'x IpsecSpiSizeOrNone);
type NotifyPayloadBodyCont0Input<'a, 'b, 'x> = POrSType<NotifyPayloadBodyCont0Type<'a, 'b>, NotifyPayloadBodyCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NotifyPayloadBodyCont0Input<'a, 'b, 'x>> for NotifyPayloadBodyCont0 {
    type Output = (NotifyMsgTypeCombinator, NotifyPayloadBodyRestCombinator);

    open spec fn requires(&self, deps: NotifyPayloadBodyCont0Input<'a, 'b, 'x>) -> bool {        let payload_length = self.payload_length@;

        &&& ((self.payload_length@) >= 8 && (self.payload_length@) <= 65535)
        &&& (Pair::spec_new(spec_notify_protocol_id(), |deps| spec_notify_payload_body_cont1(payload_length, deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: NotifyPayloadBodyCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_notify_payload_body_cont0(self.payload_length@, deps@)
    }

    fn apply(&self, deps: NotifyPayloadBodyCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (protocol_id, spi_size) = deps;
                let payload_length = self.payload_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                (notify_msg_type(), notify_payload_body_rest(spi_size, payload_length))
            }
            POrSType::S(deps) => {
                let (protocol_id, spi_size) = deps;
                let payload_length = self.payload_length;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                (notify_msg_type(), notify_payload_body_rest(spi_size, payload_length))
            }
        }
    }
}

pub struct SpecCertPayloadBody {
    pub cert_encoding: u8,
    pub cert_data: Seq<u8>,
}

pub type SpecCertPayloadBodyInner = (u8, Seq<u8>);


impl SpecFrom<SpecCertPayloadBody> for SpecCertPayloadBodyInner {
    open spec fn spec_from(m: SpecCertPayloadBody) -> SpecCertPayloadBodyInner {
        (m.cert_encoding, m.cert_data)
    }
}

impl SpecFrom<SpecCertPayloadBodyInner> for SpecCertPayloadBody {
    open spec fn spec_from(m: SpecCertPayloadBodyInner) -> SpecCertPayloadBody {
        let (cert_encoding, cert_data) = m;
        SpecCertPayloadBody { cert_encoding, cert_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertPayloadBody<'a> {
    pub cert_encoding: u8,
    pub cert_data: &'a [u8],
}

impl View for CertPayloadBody<'_> {
    type V = SpecCertPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecCertPayloadBody {
            cert_encoding: self.cert_encoding@,
            cert_data: self.cert_data@,
        }
    }
}
pub type CertPayloadBodyInner<'a> = (u8, &'a [u8]);

pub type CertPayloadBodyInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CertPayloadBody<'a>> for CertPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a CertPayloadBody) -> CertPayloadBodyInnerRef<'a> {
        (&m.cert_encoding, &m.cert_data)
    }
}

impl<'a> From<CertPayloadBodyInner<'a>> for CertPayloadBody<'a> {
    fn ex_from(m: CertPayloadBodyInner) -> CertPayloadBody {
        let (cert_encoding, cert_data) = m;
        CertPayloadBody { cert_encoding, cert_data }
    }
}

pub struct CertPayloadBodyMapper;
impl View for CertPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertPayloadBodyMapper {
    type Src = SpecCertPayloadBodyInner;
    type Dst = SpecCertPayloadBody;
}
impl SpecIsoProof for CertPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertPayloadBodyMapper {
    type Src = CertPayloadBodyInner<'a>;
    type Dst = CertPayloadBody<'a>;
    type RefSrc = CertPayloadBodyInnerRef<'a>;
}
type SpecCertPayloadBodyCombinatorAlias1 = (SpecCertEncodingCombinator, bytes::Variable);
pub struct SpecCertPayloadBodyCombinator(pub SpecCertPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecCertPayloadBodyCombinator {
    type Type = SpecCertPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCertPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertPayloadBodyCombinatorAlias = Mapped<SpecCertPayloadBodyCombinatorAlias1, CertPayloadBodyMapper>;
type CertPayloadBodyCombinatorAlias1 = (CertEncodingCombinator, bytes::Variable);
pub struct CertPayloadBodyCombinator1(pub CertPayloadBodyCombinatorAlias1);
impl View for CertPayloadBodyCombinator1 {
    type V = SpecCertPayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertPayloadBodyCombinator1, CertPayloadBodyCombinatorAlias1);

pub struct CertPayloadBodyCombinator(pub CertPayloadBodyCombinatorAlias);

impl View for CertPayloadBodyCombinator {
    type V = SpecCertPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecCertPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertPayloadBodyCombinator {
    type Type = CertPayloadBody<'a>;
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
pub type CertPayloadBodyCombinatorAlias = Mapped<CertPayloadBodyCombinator1, CertPayloadBodyMapper>;


pub open spec fn spec_cert_payload_body(payload_length: u16) -> SpecCertPayloadBodyCombinator {
    SpecCertPayloadBodyCombinator(
    Mapped {
        inner: (spec_cert_encoding(), bytes::Variable(((usize::spec_from(payload_length) - 5)) as usize)),
        mapper: CertPayloadBodyMapper,
    })
}

pub fn cert_payload_body<'a>(payload_length: u16) -> (o: CertPayloadBodyCombinator)
    requires
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures o@ == spec_cert_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CertPayloadBodyCombinator(
    Mapped {
        inner: CertPayloadBodyCombinator1((cert_encoding(), bytes::Variable(((usize::ex_from(payload_length) - 5)) as usize))),
        mapper: CertPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_cert_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_cert_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<CertPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_cert_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_cert_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_cert_payload_body(payload_length@).spec_parse(input@) is None,
        spec_cert_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = cert_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_cert_payload_body<'a>(v: <CertPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_cert_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_cert_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_cert_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = cert_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn cert_payload_body_len<'a>(v: <CertPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_cert_payload_body(payload_length@).wf(v@),
        spec_cert_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 5 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_cert_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = cert_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecTsPayloadBody {
    pub num_ts: u8,
    pub reserved: Seq<u8>,
    pub selectors: Seq<SpecTrafficSelector>,
}

pub type SpecTsPayloadBodyInner = (u8, (Seq<u8>, Seq<SpecTrafficSelector>));


impl SpecFrom<SpecTsPayloadBody> for SpecTsPayloadBodyInner {
    open spec fn spec_from(m: SpecTsPayloadBody) -> SpecTsPayloadBodyInner {
        (m.num_ts, (m.reserved, m.selectors))
    }
}

impl SpecFrom<SpecTsPayloadBodyInner> for SpecTsPayloadBody {
    open spec fn spec_from(m: SpecTsPayloadBodyInner) -> SpecTsPayloadBody {
        let (num_ts, (reserved, selectors)) = m;
        SpecTsPayloadBody { num_ts, reserved, selectors }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsPayloadBody<'a> {
    pub num_ts: u8,
    pub reserved: &'a [u8],
    pub selectors: RepeatResult<TrafficSelector<'a>>,
}

impl View for TsPayloadBody<'_> {
    type V = SpecTsPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecTsPayloadBody {
            num_ts: self.num_ts@,
            reserved: self.reserved@,
            selectors: self.selectors@,
        }
    }
}
pub type TsPayloadBodyInner<'a> = (u8, (&'a [u8], RepeatResult<TrafficSelector<'a>>));

pub type TsPayloadBodyInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a RepeatResult<TrafficSelector<'a>>));
impl<'a> From<&'a TsPayloadBody<'a>> for TsPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a TsPayloadBody) -> TsPayloadBodyInnerRef<'a> {
        (&m.num_ts, (&m.reserved, &m.selectors))
    }
}

impl<'a> From<TsPayloadBodyInner<'a>> for TsPayloadBody<'a> {
    fn ex_from(m: TsPayloadBodyInner) -> TsPayloadBody {
        let (num_ts, (reserved, selectors)) = m;
        TsPayloadBody { num_ts, reserved, selectors }
    }
}

pub struct TsPayloadBodyMapper;
impl View for TsPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsPayloadBodyMapper {
    type Src = SpecTsPayloadBodyInner;
    type Dst = SpecTsPayloadBody;
}
impl SpecIsoProof for TsPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsPayloadBodyMapper {
    type Src = TsPayloadBodyInner<'a>;
    type Dst = TsPayloadBody<'a>;
    type RefSrc = TsPayloadBodyInnerRef<'a>;
}
pub spec const SPEC_TSPAYLOADBODYRESERVED_CONST: Seq<u8> = seq![0; 3];
pub struct SpecTsPayloadBodyCombinator(pub SpecTsPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecTsPayloadBodyCombinator {
    type Type = SpecTsPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecTsPayloadBodyCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate3651688686135228051>, (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Variable, RepeatN<SpecTrafficSelectorCombinator>>)>, TsPayloadBodyMapper>;
pub exec static TSPAYLOADBODYRESERVED_CONST: [u8; 3]
    ensures TSPAYLOADBODYRESERVED_CONST@ == SPEC_TSPAYLOADBODYRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_TSPAYLOADBODYRESERVED_CONST);
    arr
}

pub struct TsPayloadBodyCombinator(pub TsPayloadBodyCombinatorAlias);

impl View for TsPayloadBodyCombinator {
    type V = SpecTsPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecTsPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsPayloadBodyCombinator {
    type Type = TsPayloadBody<'a>;
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
pub type TsPayloadBodyCombinatorAlias = Mapped<Pair<Refined<U8, Predicate3651688686135228051>, (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Variable, RepeatN<TrafficSelectorCombinator>>), TsPayloadBodyCont0>, TsPayloadBodyMapper>;


pub open spec fn spec_ts_payload_body(payload_length: u16) -> SpecTsPayloadBodyCombinator {
    SpecTsPayloadBodyCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, |deps| spec_ts_payload_body_cont0(payload_length, deps)),
        mapper: TsPayloadBodyMapper,
    })
}

pub open spec fn spec_ts_payload_body_cont0(payload_length: u16, deps: u8) -> (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Variable, RepeatN<SpecTrafficSelectorCombinator>>) {
    let num_ts = deps;
    (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_TSPAYLOADBODYRESERVED_CONST) }, AndThen(bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize), RepeatN(spec_traffic_selector(), (usize::spec_from(num_ts)) as usize)))
}

impl View for TsPayloadBodyCont0 {
    type V = spec_fn(u8) -> (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Variable, RepeatN<SpecTrafficSelectorCombinator>>);

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_ts_payload_body_cont0(self.payload_length@, deps)
        }
    }
}

pub fn ts_payload_body<'a>(payload_length: u16) -> (o: TsPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_ts_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsPayloadBodyCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, TsPayloadBodyCont0 { payload_length }),
        mapper: TsPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<TsPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_ts_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_ts_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_payload_body(payload_length@).spec_parse(input@) is None,
        spec_ts_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_payload_body<'a>(v: <TsPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = ts_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn ts_payload_body_len<'a>(v: <TsPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_ts_payload_body(payload_length@).wf(v@),
        spec_ts_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_ts_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = ts_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct TsPayloadBodyCont0 {
    pub payload_length: u16,
}
type TsPayloadBodyCont0Type<'a, 'b> = &'b u8;
type TsPayloadBodyCont0SType<'a, 'x> = &'x u8;
type TsPayloadBodyCont0Input<'a, 'b, 'x> = POrSType<TsPayloadBodyCont0Type<'a, 'b>, TsPayloadBodyCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TsPayloadBodyCont0Input<'a, 'b, 'x>> for TsPayloadBodyCont0 {
    type Output = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Variable, RepeatN<TrafficSelectorCombinator>>);

    open spec fn requires(&self, deps: TsPayloadBodyCont0Input<'a, 'b, 'x>) -> bool {        let payload_length = self.payload_length@;

        &&& ((self.payload_length@) >= 8 && (self.payload_length@) <= 65535)
        &&& (Refined { inner: U8, predicate: Predicate3651688686135228051 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: TsPayloadBodyCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ts_payload_body_cont0(self.payload_length@, deps@)
    }

    fn apply(&self, deps: TsPayloadBodyCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let num_ts = deps;
                let payload_length = self.payload_length;
                let num_ts = *num_ts;
                (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(TSPAYLOADBODYRESERVED_CONST) }, AndThen(bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize), RepeatN(traffic_selector(), (usize::ex_from(num_ts)) as usize)))
            }
            POrSType::S(deps) => {
                let num_ts = deps;
                let payload_length = self.payload_length;
                let num_ts = *num_ts;
                (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(TSPAYLOADBODYRESERVED_CONST) }, AndThen(bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize), RepeatN(traffic_selector(), (usize::ex_from(num_ts)) as usize)))
            }
        }
    }
}

pub struct SpecVendorIdPayloadBody {
    pub vendor_id: Seq<u8>,
}

pub type SpecVendorIdPayloadBodyInner = Seq<u8>;


impl SpecFrom<SpecVendorIdPayloadBody> for SpecVendorIdPayloadBodyInner {
    open spec fn spec_from(m: SpecVendorIdPayloadBody) -> SpecVendorIdPayloadBodyInner {
        m.vendor_id
    }
}

impl SpecFrom<SpecVendorIdPayloadBodyInner> for SpecVendorIdPayloadBody {
    open spec fn spec_from(m: SpecVendorIdPayloadBodyInner) -> SpecVendorIdPayloadBody {
        let vendor_id = m;
        SpecVendorIdPayloadBody { vendor_id }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct VendorIdPayloadBody<'a> {
    pub vendor_id: &'a [u8],
}

impl View for VendorIdPayloadBody<'_> {
    type V = SpecVendorIdPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecVendorIdPayloadBody {
            vendor_id: self.vendor_id@,
        }
    }
}
pub type VendorIdPayloadBodyInner<'a> = &'a [u8];

pub type VendorIdPayloadBodyInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a VendorIdPayloadBody<'a>> for VendorIdPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a VendorIdPayloadBody) -> VendorIdPayloadBodyInnerRef<'a> {
        &m.vendor_id
    }
}

impl<'a> From<VendorIdPayloadBodyInner<'a>> for VendorIdPayloadBody<'a> {
    fn ex_from(m: VendorIdPayloadBodyInner) -> VendorIdPayloadBody {
        let vendor_id = m;
        VendorIdPayloadBody { vendor_id }
    }
}

pub struct VendorIdPayloadBodyMapper;
impl View for VendorIdPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for VendorIdPayloadBodyMapper {
    type Src = SpecVendorIdPayloadBodyInner;
    type Dst = SpecVendorIdPayloadBody;
}
impl SpecIsoProof for VendorIdPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for VendorIdPayloadBodyMapper {
    type Src = VendorIdPayloadBodyInner<'a>;
    type Dst = VendorIdPayloadBody<'a>;
    type RefSrc = VendorIdPayloadBodyInnerRef<'a>;
}

pub struct SpecVendorIdPayloadBodyCombinator(pub SpecVendorIdPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecVendorIdPayloadBodyCombinator {
    type Type = SpecVendorIdPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecVendorIdPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecVendorIdPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecVendorIdPayloadBodyCombinatorAlias = Mapped<bytes::Variable, VendorIdPayloadBodyMapper>;

pub struct VendorIdPayloadBodyCombinator(pub VendorIdPayloadBodyCombinatorAlias);

impl View for VendorIdPayloadBodyCombinator {
    type V = SpecVendorIdPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecVendorIdPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VendorIdPayloadBodyCombinator {
    type Type = VendorIdPayloadBody<'a>;
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
pub type VendorIdPayloadBodyCombinatorAlias = Mapped<bytes::Variable, VendorIdPayloadBodyMapper>;


pub open spec fn spec_vendor_id_payload_body(payload_length: u16) -> SpecVendorIdPayloadBodyCombinator {
    SpecVendorIdPayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::spec_from(payload_length) - 4)) as usize),
        mapper: VendorIdPayloadBodyMapper,
    })
}

pub fn vendor_id_payload_body<'a>(payload_length: u16) -> (o: VendorIdPayloadBodyCombinator)
    requires
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures o@ == spec_vendor_id_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = VendorIdPayloadBodyCombinator(
    Mapped {
        inner: bytes::Variable(((usize::ex_from(payload_length) - 4)) as usize),
        mapper: VendorIdPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_vendor_id_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_vendor_id_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<VendorIdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_vendor_id_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_vendor_id_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_vendor_id_payload_body(payload_length@).spec_parse(input@) is None,
        spec_vendor_id_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = vendor_id_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_vendor_id_payload_body<'a>(v: <VendorIdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_vendor_id_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_vendor_id_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_vendor_id_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = vendor_id_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn vendor_id_payload_body_len<'a>(v: <VendorIdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_vendor_id_payload_body(payload_length@).wf(v@),
        spec_vendor_id_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 4 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_vendor_id_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = vendor_id_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub spec const SPEC_PayloadCritical_NonCritical: u8 = 0;
pub spec const SPEC_PayloadCritical_Critical: u8 = 128;
pub exec static EXEC_PayloadCritical_NonCritical: u8 ensures EXEC_PayloadCritical_NonCritical == SPEC_PayloadCritical_NonCritical { 0 }
pub exec static EXEC_PayloadCritical_Critical: u8 ensures EXEC_PayloadCritical_Critical == SPEC_PayloadCritical_Critical { 128 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum PayloadCritical {
    NonCritical = 0,
Critical = 128
}
pub type SpecPayloadCritical = PayloadCritical;

pub type PayloadCriticalInner = u8;

pub type PayloadCriticalInnerRef<'a> = &'a u8;

impl View for PayloadCritical {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<PayloadCriticalInner> for PayloadCritical {
    type Error = ();

    open spec fn spec_try_from(v: PayloadCriticalInner) -> Result<PayloadCritical, ()> {
        match v {
            0u8 => Ok(PayloadCritical::NonCritical),
            128u8 => Ok(PayloadCritical::Critical),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<PayloadCritical> for PayloadCriticalInner {
    type Error = ();

    open spec fn spec_try_from(v: PayloadCritical) -> Result<PayloadCriticalInner, ()> {
        match v {
            PayloadCritical::NonCritical => Ok(SPEC_PayloadCritical_NonCritical),
            PayloadCritical::Critical => Ok(SPEC_PayloadCritical_Critical),
        }
    }
}

impl TryFrom<PayloadCriticalInner> for PayloadCritical {
    type Error = ();

    fn ex_try_from(v: PayloadCriticalInner) -> Result<PayloadCritical, ()> {
        match v {
            0u8 => Ok(PayloadCritical::NonCritical),
            128u8 => Ok(PayloadCritical::Critical),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a PayloadCritical> for PayloadCriticalInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a PayloadCritical) -> Result<PayloadCriticalInnerRef<'a>, ()> {
        match v {
            PayloadCritical::NonCritical => Ok(&EXEC_PayloadCritical_NonCritical),
            PayloadCritical::Critical => Ok(&EXEC_PayloadCritical_Critical),
        }
    }
}

pub struct PayloadCriticalMapper;

impl View for PayloadCriticalMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for PayloadCriticalMapper {
    type Src = PayloadCriticalInner;
    type Dst = PayloadCritical;
}

impl SpecPartialIsoProof for PayloadCriticalMapper {
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

impl<'a> PartialIso<'a> for PayloadCriticalMapper {
    type Src = PayloadCriticalInner;
    type Dst = PayloadCritical;
    type RefSrc = PayloadCriticalInnerRef<'a>;
}


pub struct SpecPayloadCriticalCombinator(pub SpecPayloadCriticalCombinatorAlias);

impl SpecCombinator for SpecPayloadCriticalCombinator {
    type Type = SpecPayloadCritical;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPayloadCriticalCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecPayloadCriticalCombinatorAlias::is_prefix_secure() }
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
pub type SpecPayloadCriticalCombinatorAlias = TryMap<U8, PayloadCriticalMapper>;

pub struct PayloadCriticalCombinator(pub PayloadCriticalCombinatorAlias);

impl View for PayloadCriticalCombinator {
    type V = SpecPayloadCriticalCombinator;
    open spec fn view(&self) -> Self::V { SpecPayloadCriticalCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PayloadCriticalCombinator {
    type Type = PayloadCritical;
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
pub type PayloadCriticalCombinatorAlias = TryMap<U8, PayloadCriticalMapper>;


pub open spec fn spec_payload_critical() -> SpecPayloadCriticalCombinator {
    SpecPayloadCriticalCombinator(TryMap { inner: U8, mapper: PayloadCriticalMapper })
}

                
pub fn payload_critical<'a>() -> (o: PayloadCriticalCombinator)
    ensures o@ == spec_payload_critical(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = PayloadCriticalCombinator(TryMap { inner: U8, mapper: PayloadCriticalMapper });
    // assert({
    //     &&& combinator@ == spec_payload_critical()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_payload_critical<'a>(input: &'a [u8]) -> (res: PResult<<PayloadCriticalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_payload_critical().spec_parse(input@) == Some((n as int, v@)),
        spec_payload_critical().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_payload_critical().spec_parse(input@) is None,
        spec_payload_critical().spec_parse(input@) is None ==> res is Err,
{
    let combinator = payload_critical();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_payload_critical<'a>(v: <PayloadCriticalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_payload_critical().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_payload_critical().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_payload_critical().spec_serialize(v@))
        },
{
    let combinator = payload_critical();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn payload_critical_len<'a>(v: <PayloadCriticalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_payload_critical().wf(v@),
        spec_payload_critical().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_payload_critical().spec_serialize(v@).len(),
{
    let combinator = payload_critical();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecDeletePayloadBodySpis {
    Variant0(SpecDeletePayloadSpisNone),
    Variant1(SpecDeletePayloadSpisIpsec),
}

pub type SpecDeletePayloadBodySpisInner = Either<SpecDeletePayloadSpisNone, SpecDeletePayloadSpisIpsec>;

impl SpecFrom<SpecDeletePayloadBodySpis> for SpecDeletePayloadBodySpisInner {
    open spec fn spec_from(m: SpecDeletePayloadBodySpis) -> SpecDeletePayloadBodySpisInner {
        match m {
            SpecDeletePayloadBodySpis::Variant0(m) => Either::Left(m),
            SpecDeletePayloadBodySpis::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecDeletePayloadBodySpisInner> for SpecDeletePayloadBodySpis {
    open spec fn spec_from(m: SpecDeletePayloadBodySpisInner) -> SpecDeletePayloadBodySpis {
        match m {
            Either::Left(m) => SpecDeletePayloadBodySpis::Variant0(m),
            Either::Right(m) => SpecDeletePayloadBodySpis::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeletePayloadBodySpis<'a> {
    Variant0(DeletePayloadSpisNone<'a>),
    Variant1(DeletePayloadSpisIpsec),
}

pub type DeletePayloadBodySpisInner<'a> = Either<DeletePayloadSpisNone<'a>, DeletePayloadSpisIpsec>;

pub type DeletePayloadBodySpisInnerRef<'a> = Either<&'a DeletePayloadSpisNone<'a>, &'a DeletePayloadSpisIpsec>;


impl<'a> View for DeletePayloadBodySpis<'a> {
    type V = SpecDeletePayloadBodySpis;
    open spec fn view(&self) -> Self::V {
        match self {
            DeletePayloadBodySpis::Variant0(m) => SpecDeletePayloadBodySpis::Variant0(m@),
            DeletePayloadBodySpis::Variant1(m) => SpecDeletePayloadBodySpis::Variant1(m@),
        }
    }
}


impl<'a> From<&'a DeletePayloadBodySpis<'a>> for DeletePayloadBodySpisInnerRef<'a> {
    fn ex_from(m: &'a DeletePayloadBodySpis<'a>) -> DeletePayloadBodySpisInnerRef<'a> {
        match m {
            DeletePayloadBodySpis::Variant0(m) => Either::Left(m),
            DeletePayloadBodySpis::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<DeletePayloadBodySpisInner<'a>> for DeletePayloadBodySpis<'a> {
    fn ex_from(m: DeletePayloadBodySpisInner<'a>) -> DeletePayloadBodySpis<'a> {
        match m {
            Either::Left(m) => DeletePayloadBodySpis::Variant0(m),
            Either::Right(m) => DeletePayloadBodySpis::Variant1(m),
        }
    }
    
}


pub struct DeletePayloadBodySpisMapper;
impl View for DeletePayloadBodySpisMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DeletePayloadBodySpisMapper {
    type Src = SpecDeletePayloadBodySpisInner;
    type Dst = SpecDeletePayloadBodySpis;
}
impl SpecIsoProof for DeletePayloadBodySpisMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DeletePayloadBodySpisMapper {
    type Src = DeletePayloadBodySpisInner<'a>;
    type Dst = DeletePayloadBodySpis<'a>;
    type RefSrc = DeletePayloadBodySpisInnerRef<'a>;
}

type SpecDeletePayloadBodySpisCombinatorAlias1 = Choice<Cond<SpecDeletePayloadSpisNoneCombinator>, Cond<SpecDeletePayloadSpisIpsecCombinator>>;
pub struct SpecDeletePayloadBodySpisCombinator(pub SpecDeletePayloadBodySpisCombinatorAlias);

impl SpecCombinator for SpecDeletePayloadBodySpisCombinator {
    type Type = SpecDeletePayloadBodySpis;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDeletePayloadBodySpisCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDeletePayloadBodySpisCombinatorAlias::is_prefix_secure() }
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
pub type SpecDeletePayloadBodySpisCombinatorAlias = Mapped<SpecDeletePayloadBodySpisCombinatorAlias1, DeletePayloadBodySpisMapper>;
type DeletePayloadBodySpisCombinatorAlias1 = Choice<Cond<DeletePayloadSpisNoneCombinator>, Cond<DeletePayloadSpisIpsecCombinator>>;
pub struct DeletePayloadBodySpisCombinator1(pub DeletePayloadBodySpisCombinatorAlias1);
impl View for DeletePayloadBodySpisCombinator1 {
    type V = SpecDeletePayloadBodySpisCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(DeletePayloadBodySpisCombinator1, DeletePayloadBodySpisCombinatorAlias1);

pub struct DeletePayloadBodySpisCombinator(pub DeletePayloadBodySpisCombinatorAlias);

impl View for DeletePayloadBodySpisCombinator {
    type V = SpecDeletePayloadBodySpisCombinator;
    open spec fn view(&self) -> Self::V { SpecDeletePayloadBodySpisCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DeletePayloadBodySpisCombinator {
    type Type = DeletePayloadBodySpis<'a>;
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
pub type DeletePayloadBodySpisCombinatorAlias = Mapped<DeletePayloadBodySpisCombinator1, DeletePayloadBodySpisMapper>;


pub open spec fn spec_delete_payload_body_spis(spi_size: SpecIpsecSpiSizeOrNone, num_spis: u16) -> SpecDeletePayloadBodySpisCombinator {
    SpecDeletePayloadBodySpisCombinator(Mapped { inner: Choice(Cond { cond: spi_size == 0, inner: spec_delete_payload_spis_none() }, Cond { cond: spi_size == 4, inner: spec_delete_payload_spis_ipsec(num_spis) }), mapper: DeletePayloadBodySpisMapper })
}

pub fn delete_payload_body_spis<'a>(spi_size: IpsecSpiSizeOrNone, num_spis: u16) -> (o: DeletePayloadBodySpisCombinator)
    requires
        spec_ipsec_spi_size_or_none().wf(spi_size@),

    ensures o@ == spec_delete_payload_body_spis(spi_size@, num_spis@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DeletePayloadBodySpisCombinator(Mapped { inner: DeletePayloadBodySpisCombinator1(Choice::new(Cond { cond: spi_size == 0, inner: delete_payload_spis_none() }, Cond { cond: spi_size == 4, inner: delete_payload_spis_ipsec(num_spis) })), mapper: DeletePayloadBodySpisMapper });
    // assert({
    //     &&& combinator@ == spec_delete_payload_body_spis(spi_size@, num_spis@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_delete_payload_body_spis<'a>(input: &'a [u8], spi_size: IpsecSpiSizeOrNone, num_spis: u16) -> (res: PResult<<DeletePayloadBodySpisCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_ipsec_spi_size_or_none().wf(spi_size@),

    ensures
        res matches Ok((n, v)) ==> spec_delete_payload_body_spis(spi_size@, num_spis@).spec_parse(input@) == Some((n as int, v@)),
        spec_delete_payload_body_spis(spi_size@, num_spis@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_delete_payload_body_spis(spi_size@, num_spis@).spec_parse(input@) is None,
        spec_delete_payload_body_spis(spi_size@, num_spis@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = delete_payload_body_spis( spi_size, num_spis );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_delete_payload_body_spis<'a>(v: <DeletePayloadBodySpisCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, spi_size: IpsecSpiSizeOrNone, num_spis: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_delete_payload_body_spis(spi_size@, num_spis@).wf(v@),
        spec_ipsec_spi_size_or_none().wf(spi_size@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_delete_payload_body_spis(spi_size@, num_spis@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_delete_payload_body_spis(spi_size@, num_spis@).spec_serialize(v@))
        },
{
    let combinator = delete_payload_body_spis( spi_size, num_spis );
    combinator.serialize(v, data, pos)
}

pub fn delete_payload_body_spis_len<'a>(v: <DeletePayloadBodySpisCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, spi_size: IpsecSpiSizeOrNone, num_spis: u16) -> (serialize_len: usize)
    requires
        spec_delete_payload_body_spis(spi_size@, num_spis@).wf(v@),
        spec_delete_payload_body_spis(spi_size@, num_spis@).spec_serialize(v@).len() <= usize::MAX,
        spec_ipsec_spi_size_or_none().wf(spi_size@),

    ensures
        serialize_len == spec_delete_payload_body_spis(spi_size@, num_spis@).spec_serialize(v@).len(),
{
    let combinator = delete_payload_body_spis( spi_size, num_spis );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecDeletePayloadBody {
    pub protocol_id: u8,
    pub spi_size: SpecIpsecSpiSizeOrNone,
    pub num_spis: u16,
    pub spis: SpecDeletePayloadBodySpis,
}

pub type SpecDeletePayloadBodyInner = (((u8, SpecIpsecSpiSizeOrNone), u16), SpecDeletePayloadBodySpis);


impl SpecFrom<SpecDeletePayloadBody> for SpecDeletePayloadBodyInner {
    open spec fn spec_from(m: SpecDeletePayloadBody) -> SpecDeletePayloadBodyInner {
        (((m.protocol_id, m.spi_size), m.num_spis), m.spis)
    }
}

impl SpecFrom<SpecDeletePayloadBodyInner> for SpecDeletePayloadBody {
    open spec fn spec_from(m: SpecDeletePayloadBodyInner) -> SpecDeletePayloadBody {
        let (((protocol_id, spi_size), num_spis), spis) = m;
        SpecDeletePayloadBody { protocol_id, spi_size, num_spis, spis }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct DeletePayloadBody<'a> {
    pub protocol_id: u8,
    pub spi_size: IpsecSpiSizeOrNone,
    pub num_spis: u16,
    pub spis: DeletePayloadBodySpis<'a>,
}

impl View for DeletePayloadBody<'_> {
    type V = SpecDeletePayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecDeletePayloadBody {
            protocol_id: self.protocol_id@,
            spi_size: self.spi_size@,
            num_spis: self.num_spis@,
            spis: self.spis@,
        }
    }
}
pub type DeletePayloadBodyInner<'a> = (((u8, IpsecSpiSizeOrNone), u16), DeletePayloadBodySpis<'a>);

pub type DeletePayloadBodyInnerRef<'a> = (((&'a u8, &'a IpsecSpiSizeOrNone), &'a u16), &'a DeletePayloadBodySpis<'a>);
impl<'a> From<&'a DeletePayloadBody<'a>> for DeletePayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a DeletePayloadBody) -> DeletePayloadBodyInnerRef<'a> {
        (((&m.protocol_id, &m.spi_size), &m.num_spis), &m.spis)
    }
}

impl<'a> From<DeletePayloadBodyInner<'a>> for DeletePayloadBody<'a> {
    fn ex_from(m: DeletePayloadBodyInner) -> DeletePayloadBody {
        let (((protocol_id, spi_size), num_spis), spis) = m;
        DeletePayloadBody { protocol_id, spi_size, num_spis, spis }
    }
}

pub struct DeletePayloadBodyMapper;
impl View for DeletePayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DeletePayloadBodyMapper {
    type Src = SpecDeletePayloadBodyInner;
    type Dst = SpecDeletePayloadBody;
}
impl SpecIsoProof for DeletePayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DeletePayloadBodyMapper {
    type Src = DeletePayloadBodyInner<'a>;
    type Dst = DeletePayloadBody<'a>;
    type RefSrc = DeletePayloadBodyInnerRef<'a>;
}

pub struct SpecDeletePayloadBodyCombinator(pub SpecDeletePayloadBodyCombinatorAlias);

impl SpecCombinator for SpecDeletePayloadBodyCombinator {
    type Type = SpecDeletePayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDeletePayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDeletePayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecDeletePayloadBodyCombinatorAlias = Mapped<SpecPair<SpecPair<SpecPair<SpecIkeProtocolIdCombinator, SpecIpsecSpiSizeOrNoneCombinator>, U16Be>, SpecDeletePayloadBodySpisCombinator>, DeletePayloadBodyMapper>;

pub struct DeletePayloadBodyCombinator(pub DeletePayloadBodyCombinatorAlias);

impl View for DeletePayloadBodyCombinator {
    type V = SpecDeletePayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecDeletePayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DeletePayloadBodyCombinator {
    type Type = DeletePayloadBody<'a>;
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
pub type DeletePayloadBodyCombinatorAlias = Mapped<Pair<Pair<Pair<IkeProtocolIdCombinator, IpsecSpiSizeOrNoneCombinator, DeletePayloadBodyCont2>, U16Be, DeletePayloadBodyCont1>, DeletePayloadBodySpisCombinator, DeletePayloadBodyCont0>, DeletePayloadBodyMapper>;


pub open spec fn spec_delete_payload_body() -> SpecDeletePayloadBodyCombinator {
    SpecDeletePayloadBodyCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(Pair::spec_new(spec_ike_protocol_id(), |deps| spec_delete_payload_body_cont2(deps)), |deps| spec_delete_payload_body_cont1(deps)), |deps| spec_delete_payload_body_cont0(deps)),
        mapper: DeletePayloadBodyMapper,
    })
}

pub open spec fn spec_delete_payload_body_cont2(deps: u8) -> SpecIpsecSpiSizeOrNoneCombinator {
    let protocol_id = deps;
    spec_ipsec_spi_size_or_none()
}

impl View for DeletePayloadBodyCont2 {
    type V = spec_fn(u8) -> SpecIpsecSpiSizeOrNoneCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_delete_payload_body_cont2(deps)
        }
    }
}

pub open spec fn spec_delete_payload_body_cont1(deps: (u8, SpecIpsecSpiSizeOrNone)) -> U16Be {
    let (protocol_id, spi_size) = deps;
    U16Be
}

impl View for DeletePayloadBodyCont1 {
    type V = spec_fn((u8, SpecIpsecSpiSizeOrNone)) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, SpecIpsecSpiSizeOrNone)| {
            spec_delete_payload_body_cont1(deps)
        }
    }
}

pub open spec fn spec_delete_payload_body_cont0(deps: ((u8, SpecIpsecSpiSizeOrNone), u16)) -> SpecDeletePayloadBodySpisCombinator {
    let ((protocol_id, spi_size), num_spis) = deps;
    spec_delete_payload_body_spis(spi_size, num_spis)
}

impl View for DeletePayloadBodyCont0 {
    type V = spec_fn(((u8, SpecIpsecSpiSizeOrNone), u16)) -> SpecDeletePayloadBodySpisCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: ((u8, SpecIpsecSpiSizeOrNone), u16)| {
            spec_delete_payload_body_cont0(deps)
        }
    }
}

                
pub fn delete_payload_body<'a>() -> (o: DeletePayloadBodyCombinator)
    ensures o@ == spec_delete_payload_body(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = DeletePayloadBodyCombinator(
    Mapped {
        inner: Pair::new(Pair::new(Pair::new(ike_protocol_id(), DeletePayloadBodyCont2), DeletePayloadBodyCont1), DeletePayloadBodyCont0),
        mapper: DeletePayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_delete_payload_body()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_delete_payload_body<'a>(input: &'a [u8]) -> (res: PResult<<DeletePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_delete_payload_body().spec_parse(input@) == Some((n as int, v@)),
        spec_delete_payload_body().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_delete_payload_body().spec_parse(input@) is None,
        spec_delete_payload_body().spec_parse(input@) is None ==> res is Err,
{
    let combinator = delete_payload_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_delete_payload_body<'a>(v: <DeletePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_delete_payload_body().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_delete_payload_body().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_delete_payload_body().spec_serialize(v@))
        },
{
    let combinator = delete_payload_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn delete_payload_body_len<'a>(v: <DeletePayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_delete_payload_body().wf(v@),
        spec_delete_payload_body().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_delete_payload_body().spec_serialize(v@).len(),
{
    let combinator = delete_payload_body();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct DeletePayloadBodyCont2;
type DeletePayloadBodyCont2Type<'a, 'b> = &'b u8;
type DeletePayloadBodyCont2SType<'a, 'x> = &'x u8;
type DeletePayloadBodyCont2Input<'a, 'b, 'x> = POrSType<DeletePayloadBodyCont2Type<'a, 'b>, DeletePayloadBodyCont2SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DeletePayloadBodyCont2Input<'a, 'b, 'x>> for DeletePayloadBodyCont2 {
    type Output = IpsecSpiSizeOrNoneCombinator;

    open spec fn requires(&self, deps: DeletePayloadBodyCont2Input<'a, 'b, 'x>) -> bool {
        &&& (spec_ike_protocol_id()).wf(deps@)
        }

    open spec fn ensures(&self, deps: DeletePayloadBodyCont2Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_delete_payload_body_cont2(deps@)
    }

    fn apply(&self, deps: DeletePayloadBodyCont2Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let protocol_id = deps;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
            POrSType::S(deps) => {
                let protocol_id = deps;
                let protocol_id = *protocol_id;
                ipsec_spi_size_or_none()
            }
        }
    }
}
pub struct DeletePayloadBodyCont1;
type DeletePayloadBodyCont1Type<'a, 'b> = &'b (u8, IpsecSpiSizeOrNone);
type DeletePayloadBodyCont1SType<'a, 'x> = (&'x u8, &'x IpsecSpiSizeOrNone);
type DeletePayloadBodyCont1Input<'a, 'b, 'x> = POrSType<DeletePayloadBodyCont1Type<'a, 'b>, DeletePayloadBodyCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DeletePayloadBodyCont1Input<'a, 'b, 'x>> for DeletePayloadBodyCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: DeletePayloadBodyCont1Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(spec_ike_protocol_id(), |deps| spec_delete_payload_body_cont2(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: DeletePayloadBodyCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_delete_payload_body_cont1(deps@)
    }

    fn apply(&self, deps: DeletePayloadBodyCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (protocol_id, spi_size) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                U16Be
            }
            POrSType::S(deps) => {
                let (protocol_id, spi_size) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                U16Be
            }
        }
    }
}
pub struct DeletePayloadBodyCont0;
type DeletePayloadBodyCont0Type<'a, 'b> = &'b ((u8, IpsecSpiSizeOrNone), u16);
type DeletePayloadBodyCont0SType<'a, 'x> = ((&'x u8, &'x IpsecSpiSizeOrNone), &'x u16);
type DeletePayloadBodyCont0Input<'a, 'b, 'x> = POrSType<DeletePayloadBodyCont0Type<'a, 'b>, DeletePayloadBodyCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DeletePayloadBodyCont0Input<'a, 'b, 'x>> for DeletePayloadBodyCont0 {
    type Output = DeletePayloadBodySpisCombinator;

    open spec fn requires(&self, deps: DeletePayloadBodyCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Pair::spec_new(Pair::spec_new(spec_ike_protocol_id(), |deps| spec_delete_payload_body_cont2(deps)), |deps| spec_delete_payload_body_cont1(deps))).wf(deps@)
        }

    open spec fn ensures(&self, deps: DeletePayloadBodyCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_delete_payload_body_cont0(deps@)
    }

    fn apply(&self, deps: DeletePayloadBodyCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let ((protocol_id, spi_size), num_spis) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                let num_spis = *num_spis;
                delete_payload_body_spis(spi_size, num_spis)
            }
            POrSType::S(deps) => {
                let ((protocol_id, spi_size), num_spis) = deps;
                let protocol_id = *protocol_id;
                let spi_size = *spi_size;
                let num_spis = *num_spis;
                delete_payload_body_spis(spi_size, num_spis)
            }
        }
    }
}
                

pub struct SpecIkeMessage {
    pub header: SpecIkeHeader,
    pub payloads: Seq<u8>,
}

pub type SpecIkeMessageInner = (SpecIkeHeader, Seq<u8>);


impl SpecFrom<SpecIkeMessage> for SpecIkeMessageInner {
    open spec fn spec_from(m: SpecIkeMessage) -> SpecIkeMessageInner {
        (m.header, m.payloads)
    }
}

impl SpecFrom<SpecIkeMessageInner> for SpecIkeMessage {
    open spec fn spec_from(m: SpecIkeMessageInner) -> SpecIkeMessage {
        let (header, payloads) = m;
        SpecIkeMessage { header, payloads }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct IkeMessage<'a> {
    pub header: IkeHeader<'a>,
    pub payloads: &'a [u8],
}

impl View for IkeMessage<'_> {
    type V = SpecIkeMessage;

    open spec fn view(&self) -> Self::V {
        SpecIkeMessage {
            header: self.header@,
            payloads: self.payloads@,
        }
    }
}
pub type IkeMessageInner<'a> = (IkeHeader<'a>, &'a [u8]);

pub type IkeMessageInnerRef<'a> = (&'a IkeHeader<'a>, &'a &'a [u8]);
impl<'a> From<&'a IkeMessage<'a>> for IkeMessageInnerRef<'a> {
    fn ex_from(m: &'a IkeMessage) -> IkeMessageInnerRef<'a> {
        (&m.header, &m.payloads)
    }
}

impl<'a> From<IkeMessageInner<'a>> for IkeMessage<'a> {
    fn ex_from(m: IkeMessageInner) -> IkeMessage {
        let (header, payloads) = m;
        IkeMessage { header, payloads }
    }
}

pub struct IkeMessageMapper;
impl View for IkeMessageMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for IkeMessageMapper {
    type Src = SpecIkeMessageInner;
    type Dst = SpecIkeMessage;
}
impl SpecIsoProof for IkeMessageMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for IkeMessageMapper {
    type Src = IkeMessageInner<'a>;
    type Dst = IkeMessage<'a>;
    type RefSrc = IkeMessageInnerRef<'a>;
}

pub struct SpecIkeMessageCombinator(pub SpecIkeMessageCombinatorAlias);

impl SpecCombinator for SpecIkeMessageCombinator {
    type Type = SpecIkeMessage;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkeMessageCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkeMessageCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkeMessageCombinatorAlias = Mapped<SpecPair<SpecIkeHeaderCombinator, bytes::Variable>, IkeMessageMapper>;

pub struct IkeMessageCombinator(pub IkeMessageCombinatorAlias);

impl View for IkeMessageCombinator {
    type V = SpecIkeMessageCombinator;
    open spec fn view(&self) -> Self::V { SpecIkeMessageCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IkeMessageCombinator {
    type Type = IkeMessage<'a>;
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
pub type IkeMessageCombinatorAlias = Mapped<Pair<IkeHeaderCombinator, bytes::Variable, IkeMessageCont0>, IkeMessageMapper>;


pub open spec fn spec_ike_message() -> SpecIkeMessageCombinator {
    SpecIkeMessageCombinator(
    Mapped {
        inner: Pair::spec_new(spec_ike_header(), |deps| spec_ike_message_cont0(deps)),
        mapper: IkeMessageMapper,
    })
}

pub open spec fn spec_ike_message_cont0(deps: SpecIkeHeader) -> bytes::Variable {
    let header = deps;
    bytes::Variable(((usize::spec_from(header.length) - 28)) as usize)
}

impl View for IkeMessageCont0 {
    type V = spec_fn(SpecIkeHeader) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: SpecIkeHeader| {
            spec_ike_message_cont0(deps)
        }
    }
}

                
pub fn ike_message<'a>() -> (o: IkeMessageCombinator)
    ensures o@ == spec_ike_message(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IkeMessageCombinator(
    Mapped {
        inner: Pair::new(ike_header(), IkeMessageCont0),
        mapper: IkeMessageMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ike_message()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ike_message<'a>(input: &'a [u8]) -> (res: PResult<<IkeMessageCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ike_message().spec_parse(input@) == Some((n as int, v@)),
        spec_ike_message().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ike_message().spec_parse(input@) is None,
        spec_ike_message().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ike_message();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ike_message<'a>(v: <IkeMessageCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ike_message().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ike_message().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ike_message().spec_serialize(v@))
        },
{
    let combinator = ike_message();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ike_message_len<'a>(v: <IkeMessageCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ike_message().wf(v@),
        spec_ike_message().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ike_message().spec_serialize(v@).len(),
{
    let combinator = ike_message();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct IkeMessageCont0;
type IkeMessageCont0Type<'a, 'b> = &'b IkeHeader<'a>;
type IkeMessageCont0SType<'a, 'x> = &'x IkeHeader<'a>;
type IkeMessageCont0Input<'a, 'b, 'x> = POrSType<IkeMessageCont0Type<'a, 'b>, IkeMessageCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<IkeMessageCont0Input<'a, 'b, 'x>> for IkeMessageCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: IkeMessageCont0Input<'a, 'b, 'x>) -> bool {
        &&& (spec_ike_header()).wf(deps@)
        }

    open spec fn ensures(&self, deps: IkeMessageCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ike_message_cont0(deps@)
    }

    fn apply(&self, deps: IkeMessageCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let header = deps;
                bytes::Variable(((usize::ex_from(header.length) - 28)) as usize)
            }
            POrSType::S(deps) => {
                let header = deps;
                bytes::Variable(((usize::ex_from(header.length) - 28)) as usize)
            }
        }
    }
}
                

pub struct SpecGenericPayloadHeader {
    pub next_payload: u8,
    pub critical_reserved: SpecPayloadCritical,
    pub payload_length: u16,
}

pub type SpecGenericPayloadHeaderInner = (u8, (SpecPayloadCritical, u16));


impl SpecFrom<SpecGenericPayloadHeader> for SpecGenericPayloadHeaderInner {
    open spec fn spec_from(m: SpecGenericPayloadHeader) -> SpecGenericPayloadHeaderInner {
        (m.next_payload, (m.critical_reserved, m.payload_length))
    }
}

impl SpecFrom<SpecGenericPayloadHeaderInner> for SpecGenericPayloadHeader {
    open spec fn spec_from(m: SpecGenericPayloadHeaderInner) -> SpecGenericPayloadHeader {
        let (next_payload, (critical_reserved, payload_length)) = m;
        SpecGenericPayloadHeader { next_payload, critical_reserved, payload_length }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct GenericPayloadHeader {
    pub next_payload: u8,
    pub critical_reserved: PayloadCritical,
    pub payload_length: u16,
}

impl View for GenericPayloadHeader {
    type V = SpecGenericPayloadHeader;

    open spec fn view(&self) -> Self::V {
        SpecGenericPayloadHeader {
            next_payload: self.next_payload@,
            critical_reserved: self.critical_reserved@,
            payload_length: self.payload_length@,
        }
    }
}
pub type GenericPayloadHeaderInner = (u8, (PayloadCritical, u16));

pub type GenericPayloadHeaderInnerRef<'a> = (&'a u8, (&'a PayloadCritical, &'a u16));
impl<'a> From<&'a GenericPayloadHeader> for GenericPayloadHeaderInnerRef<'a> {
    fn ex_from(m: &'a GenericPayloadHeader) -> GenericPayloadHeaderInnerRef<'a> {
        (&m.next_payload, (&m.critical_reserved, &m.payload_length))
    }
}

impl From<GenericPayloadHeaderInner> for GenericPayloadHeader {
    fn ex_from(m: GenericPayloadHeaderInner) -> GenericPayloadHeader {
        let (next_payload, (critical_reserved, payload_length)) = m;
        GenericPayloadHeader { next_payload, critical_reserved, payload_length }
    }
}

pub struct GenericPayloadHeaderMapper;
impl View for GenericPayloadHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GenericPayloadHeaderMapper {
    type Src = SpecGenericPayloadHeaderInner;
    type Dst = SpecGenericPayloadHeader;
}
impl SpecIsoProof for GenericPayloadHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GenericPayloadHeaderMapper {
    type Src = GenericPayloadHeaderInner;
    type Dst = GenericPayloadHeader;
    type RefSrc = GenericPayloadHeaderInnerRef<'a>;
}
type SpecGenericPayloadHeaderCombinatorAlias1 = (SpecPayloadCriticalCombinator, Refined<U16Be, Predicate17149271707383182075>);
type SpecGenericPayloadHeaderCombinatorAlias2 = (SpecNextPayloadTypeCombinator, SpecGenericPayloadHeaderCombinatorAlias1);
pub struct SpecGenericPayloadHeaderCombinator(pub SpecGenericPayloadHeaderCombinatorAlias);

impl SpecCombinator for SpecGenericPayloadHeaderCombinator {
    type Type = SpecGenericPayloadHeader;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGenericPayloadHeaderCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecGenericPayloadHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecGenericPayloadHeaderCombinatorAlias = Mapped<SpecGenericPayloadHeaderCombinatorAlias2, GenericPayloadHeaderMapper>;
type GenericPayloadHeaderCombinatorAlias1 = (PayloadCriticalCombinator, Refined<U16Be, Predicate17149271707383182075>);
type GenericPayloadHeaderCombinatorAlias2 = (NextPayloadTypeCombinator, GenericPayloadHeaderCombinator1);
pub struct GenericPayloadHeaderCombinator1(pub GenericPayloadHeaderCombinatorAlias1);
impl View for GenericPayloadHeaderCombinator1 {
    type V = SpecGenericPayloadHeaderCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(GenericPayloadHeaderCombinator1, GenericPayloadHeaderCombinatorAlias1);

pub struct GenericPayloadHeaderCombinator2(pub GenericPayloadHeaderCombinatorAlias2);
impl View for GenericPayloadHeaderCombinator2 {
    type V = SpecGenericPayloadHeaderCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(GenericPayloadHeaderCombinator2, GenericPayloadHeaderCombinatorAlias2);

pub struct GenericPayloadHeaderCombinator(pub GenericPayloadHeaderCombinatorAlias);

impl View for GenericPayloadHeaderCombinator {
    type V = SpecGenericPayloadHeaderCombinator;
    open spec fn view(&self) -> Self::V { SpecGenericPayloadHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GenericPayloadHeaderCombinator {
    type Type = GenericPayloadHeader;
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
pub type GenericPayloadHeaderCombinatorAlias = Mapped<GenericPayloadHeaderCombinator2, GenericPayloadHeaderMapper>;


pub open spec fn spec_generic_payload_header() -> SpecGenericPayloadHeaderCombinator {
    SpecGenericPayloadHeaderCombinator(
    Mapped {
        inner: (spec_next_payload_type(), (spec_payload_critical(), Refined { inner: U16Be, predicate: Predicate17149271707383182075 })),
        mapper: GenericPayloadHeaderMapper,
    })
}

                
pub fn generic_payload_header<'a>() -> (o: GenericPayloadHeaderCombinator)
    ensures o@ == spec_generic_payload_header(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = GenericPayloadHeaderCombinator(
    Mapped {
        inner: GenericPayloadHeaderCombinator2((next_payload_type(), GenericPayloadHeaderCombinator1((payload_critical(), Refined { inner: U16Be, predicate: Predicate17149271707383182075 })))),
        mapper: GenericPayloadHeaderMapper,
    });
    // assert({
    //     &&& combinator@ == spec_generic_payload_header()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_generic_payload_header<'a>(input: &'a [u8]) -> (res: PResult<<GenericPayloadHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_generic_payload_header().spec_parse(input@) == Some((n as int, v@)),
        spec_generic_payload_header().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_generic_payload_header().spec_parse(input@) is None,
        spec_generic_payload_header().spec_parse(input@) is None ==> res is Err,
{
    let combinator = generic_payload_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_generic_payload_header<'a>(v: <GenericPayloadHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_generic_payload_header().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_generic_payload_header().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_generic_payload_header().spec_serialize(v@))
        },
{
    let combinator = generic_payload_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn generic_payload_header_len<'a>(v: <GenericPayloadHeaderCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_generic_payload_header().wf(v@),
        spec_generic_payload_header().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_generic_payload_header().spec_serialize(v@).len(),
{
    let combinator = generic_payload_header();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2SkPayloadInner {
    pub encrypted_body: Seq<u8>,
}

pub type SpecIkev2SkPayloadInnerInner = Seq<u8>;


impl SpecFrom<SpecIkev2SkPayloadInner> for SpecIkev2SkPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2SkPayloadInner) -> SpecIkev2SkPayloadInnerInner {
        m.encrypted_body
    }
}

impl SpecFrom<SpecIkev2SkPayloadInnerInner> for SpecIkev2SkPayloadInner {
    open spec fn spec_from(m: SpecIkev2SkPayloadInnerInner) -> SpecIkev2SkPayloadInner {
        let encrypted_body = m;
        SpecIkev2SkPayloadInner { encrypted_body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2SkPayloadInner<'a> {
    pub encrypted_body: &'a [u8],
}

impl View for Ikev2SkPayloadInner<'_> {
    type V = SpecIkev2SkPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2SkPayloadInner {
            encrypted_body: self.encrypted_body@,
        }
    }
}
pub type Ikev2SkPayloadInnerInner<'a> = &'a [u8];

pub type Ikev2SkPayloadInnerInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a Ikev2SkPayloadInner<'a>> for Ikev2SkPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2SkPayloadInner) -> Ikev2SkPayloadInnerInnerRef<'a> {
        &m.encrypted_body
    }
}

impl<'a> From<Ikev2SkPayloadInnerInner<'a>> for Ikev2SkPayloadInner<'a> {
    fn ex_from(m: Ikev2SkPayloadInnerInner) -> Ikev2SkPayloadInner {
        let encrypted_body = m;
        Ikev2SkPayloadInner { encrypted_body }
    }
}

pub struct Ikev2SkPayloadInnerMapper;
impl View for Ikev2SkPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2SkPayloadInnerMapper {
    type Src = SpecIkev2SkPayloadInnerInner;
    type Dst = SpecIkev2SkPayloadInner;
}
impl SpecIsoProof for Ikev2SkPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2SkPayloadInnerMapper {
    type Src = Ikev2SkPayloadInnerInner<'a>;
    type Dst = Ikev2SkPayloadInner<'a>;
    type RefSrc = Ikev2SkPayloadInnerInnerRef<'a>;
}

pub struct SpecIkev2SkPayloadInnerCombinator(pub SpecIkev2SkPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2SkPayloadInnerCombinator {
    type Type = SpecIkev2SkPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2SkPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2SkPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2SkPayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2SkPayloadInnerMapper>;

pub struct Ikev2SkPayloadInnerCombinator(pub Ikev2SkPayloadInnerCombinatorAlias);

impl View for Ikev2SkPayloadInnerCombinator {
    type V = SpecIkev2SkPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2SkPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2SkPayloadInnerCombinator {
    type Type = Ikev2SkPayloadInner<'a>;
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
pub type Ikev2SkPayloadInnerCombinatorAlias = Mapped<bytes::Tail, Ikev2SkPayloadInnerMapper>;


pub open spec fn spec_ikev2_sk_payload_inner() -> SpecIkev2SkPayloadInnerCombinator {
    SpecIkev2SkPayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2SkPayloadInnerMapper,
    })
}

                
pub fn ikev2_sk_payload_inner<'a>() -> (o: Ikev2SkPayloadInnerCombinator)
    ensures o@ == spec_ikev2_sk_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2SkPayloadInnerCombinator(
    Mapped {
        inner: bytes::Tail,
        mapper: Ikev2SkPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_sk_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_sk_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2SkPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_sk_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_sk_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_sk_payload_inner().spec_parse(input@) is None,
        spec_ikev2_sk_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_sk_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_sk_payload_inner<'a>(v: <Ikev2SkPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_sk_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_sk_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_sk_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_sk_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_sk_payload_inner_len<'a>(v: <Ikev2SkPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_sk_payload_inner().wf(v@),
        spec_ikev2_sk_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_sk_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_sk_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecTsIpv4 {
    pub ts_type: u8,
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: Seq<u8>,
    pub end_address: Seq<u8>,
}

pub type SpecTsIpv4Inner = (u8, (u8, (u16, (u16, (u16, (Seq<u8>, Seq<u8>))))));


impl SpecFrom<SpecTsIpv4> for SpecTsIpv4Inner {
    open spec fn spec_from(m: SpecTsIpv4) -> SpecTsIpv4Inner {
        (m.ts_type, (m.ip_protocol_id, (m.selector_length, (m.start_port, (m.end_port, (m.start_address, m.end_address))))))
    }
}

impl SpecFrom<SpecTsIpv4Inner> for SpecTsIpv4 {
    open spec fn spec_from(m: SpecTsIpv4Inner) -> SpecTsIpv4 {
        let (ts_type, (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address)))))) = m;
        SpecTsIpv4 { ts_type, ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TsIpv4<'a> {
    pub ts_type: u8,
    pub ip_protocol_id: u8,
    pub selector_length: u16,
    pub start_port: u16,
    pub end_port: u16,
    pub start_address: &'a [u8],
    pub end_address: &'a [u8],
}

impl View for TsIpv4<'_> {
    type V = SpecTsIpv4;

    open spec fn view(&self) -> Self::V {
        SpecTsIpv4 {
            ts_type: self.ts_type@,
            ip_protocol_id: self.ip_protocol_id@,
            selector_length: self.selector_length@,
            start_port: self.start_port@,
            end_port: self.end_port@,
            start_address: self.start_address@,
            end_address: self.end_address@,
        }
    }
}
pub type TsIpv4Inner<'a> = (u8, (u8, (u16, (u16, (u16, (&'a [u8], &'a [u8]))))));

pub type TsIpv4InnerRef<'a> = (&'a u8, (&'a u8, (&'a u16, (&'a u16, (&'a u16, (&'a &'a [u8], &'a &'a [u8]))))));
impl<'a> From<&'a TsIpv4<'a>> for TsIpv4InnerRef<'a> {
    fn ex_from(m: &'a TsIpv4) -> TsIpv4InnerRef<'a> {
        (&m.ts_type, (&m.ip_protocol_id, (&m.selector_length, (&m.start_port, (&m.end_port, (&m.start_address, &m.end_address))))))
    }
}

impl<'a> From<TsIpv4Inner<'a>> for TsIpv4<'a> {
    fn ex_from(m: TsIpv4Inner) -> TsIpv4 {
        let (ts_type, (ip_protocol_id, (selector_length, (start_port, (end_port, (start_address, end_address)))))) = m;
        TsIpv4 { ts_type, ip_protocol_id, selector_length, start_port, end_port, start_address, end_address }
    }
}

pub struct TsIpv4Mapper;
impl View for TsIpv4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TsIpv4Mapper {
    type Src = SpecTsIpv4Inner;
    type Dst = SpecTsIpv4;
}
impl SpecIsoProof for TsIpv4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TsIpv4Mapper {
    type Src = TsIpv4Inner<'a>;
    type Dst = TsIpv4<'a>;
    type RefSrc = TsIpv4InnerRef<'a>;
}
pub const TSIPV4TS_TYPE_CONST: u8 = 7;
pub const TSIPV4SELECTOR_LENGTH_CONST: u16 = 16;
type SpecTsIpv4CombinatorAlias1 = (bytes::Fixed<4>, bytes::Fixed<4>);
type SpecTsIpv4CombinatorAlias2 = (U16Be, SpecTsIpv4CombinatorAlias1);
type SpecTsIpv4CombinatorAlias3 = (U16Be, SpecTsIpv4CombinatorAlias2);
type SpecTsIpv4CombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, SpecTsIpv4CombinatorAlias3);
type SpecTsIpv4CombinatorAlias5 = (U8, SpecTsIpv4CombinatorAlias4);
type SpecTsIpv4CombinatorAlias6 = (Refined<U8, TagPred<u8>>, SpecTsIpv4CombinatorAlias5);
pub struct SpecTsIpv4Combinator(pub SpecTsIpv4CombinatorAlias);

impl SpecCombinator for SpecTsIpv4Combinator {
    type Type = SpecTsIpv4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTsIpv4Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecTsIpv4CombinatorAlias::is_prefix_secure() }
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
pub type SpecTsIpv4CombinatorAlias = Mapped<SpecTsIpv4CombinatorAlias6, TsIpv4Mapper>;
type TsIpv4CombinatorAlias1 = (bytes::Fixed<4>, bytes::Fixed<4>);
type TsIpv4CombinatorAlias2 = (U16Be, TsIpv4Combinator1);
type TsIpv4CombinatorAlias3 = (U16Be, TsIpv4Combinator2);
type TsIpv4CombinatorAlias4 = (Refined<U16Be, TagPred<u16>>, TsIpv4Combinator3);
type TsIpv4CombinatorAlias5 = (U8, TsIpv4Combinator4);
type TsIpv4CombinatorAlias6 = (Refined<U8, TagPred<u8>>, TsIpv4Combinator5);
pub struct TsIpv4Combinator1(pub TsIpv4CombinatorAlias1);
impl View for TsIpv4Combinator1 {
    type V = SpecTsIpv4CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator1, TsIpv4CombinatorAlias1);

pub struct TsIpv4Combinator2(pub TsIpv4CombinatorAlias2);
impl View for TsIpv4Combinator2 {
    type V = SpecTsIpv4CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator2, TsIpv4CombinatorAlias2);

pub struct TsIpv4Combinator3(pub TsIpv4CombinatorAlias3);
impl View for TsIpv4Combinator3 {
    type V = SpecTsIpv4CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator3, TsIpv4CombinatorAlias3);

pub struct TsIpv4Combinator4(pub TsIpv4CombinatorAlias4);
impl View for TsIpv4Combinator4 {
    type V = SpecTsIpv4CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator4, TsIpv4CombinatorAlias4);

pub struct TsIpv4Combinator5(pub TsIpv4CombinatorAlias5);
impl View for TsIpv4Combinator5 {
    type V = SpecTsIpv4CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator5, TsIpv4CombinatorAlias5);

pub struct TsIpv4Combinator6(pub TsIpv4CombinatorAlias6);
impl View for TsIpv4Combinator6 {
    type V = SpecTsIpv4CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TsIpv4Combinator6, TsIpv4CombinatorAlias6);

pub struct TsIpv4Combinator(pub TsIpv4CombinatorAlias);

impl View for TsIpv4Combinator {
    type V = SpecTsIpv4Combinator;
    open spec fn view(&self) -> Self::V { SpecTsIpv4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TsIpv4Combinator {
    type Type = TsIpv4<'a>;
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
pub type TsIpv4CombinatorAlias = Mapped<TsIpv4Combinator6, TsIpv4Mapper>;


pub open spec fn spec_ts_ipv4() -> SpecTsIpv4Combinator {
    SpecTsIpv4Combinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(TSIPV4TS_TYPE_CONST) }, (U8, (Refined { inner: U16Be, predicate: TagPred(TSIPV4SELECTOR_LENGTH_CONST) }, (U16Be, (U16Be, (bytes::Fixed::<4>, bytes::Fixed::<4>)))))),
        mapper: TsIpv4Mapper,
    })
}

                
pub fn ts_ipv4<'a>() -> (o: TsIpv4Combinator)
    ensures o@ == spec_ts_ipv4(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = TsIpv4Combinator(
    Mapped {
        inner: TsIpv4Combinator6((Refined { inner: U8, predicate: TagPred(TSIPV4TS_TYPE_CONST) }, TsIpv4Combinator5((U8, TsIpv4Combinator4((Refined { inner: U16Be, predicate: TagPred(TSIPV4SELECTOR_LENGTH_CONST) }, TsIpv4Combinator3((U16Be, TsIpv4Combinator2((U16Be, TsIpv4Combinator1((bytes::Fixed::<4>, bytes::Fixed::<4>)))))))))))),
        mapper: TsIpv4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_ts_ipv4()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ts_ipv4<'a>(input: &'a [u8]) -> (res: PResult<<TsIpv4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ts_ipv4().spec_parse(input@) == Some((n as int, v@)),
        spec_ts_ipv4().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ts_ipv4().spec_parse(input@) is None,
        spec_ts_ipv4().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ts_ipv4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ts_ipv4<'a>(v: <TsIpv4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ts_ipv4().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ts_ipv4().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ts_ipv4().spec_serialize(v@))
        },
{
    let combinator = ts_ipv4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ts_ipv4_len<'a>(v: <TsIpv4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ts_ipv4().wf(v@),
        spec_ts_ipv4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ts_ipv4().spec_serialize(v@).len(),
{
    let combinator = ts_ipv4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2CpPayloadInner {
    pub cfg_type: u8,
    pub reserved: Seq<u8>,
    pub attributes: Seq<SpecCfgAttribute>,
}

pub type SpecIkev2CpPayloadInnerInner = (u8, (Seq<u8>, Seq<SpecCfgAttribute>));


impl SpecFrom<SpecIkev2CpPayloadInner> for SpecIkev2CpPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2CpPayloadInner) -> SpecIkev2CpPayloadInnerInner {
        (m.cfg_type, (m.reserved, m.attributes))
    }
}

impl SpecFrom<SpecIkev2CpPayloadInnerInner> for SpecIkev2CpPayloadInner {
    open spec fn spec_from(m: SpecIkev2CpPayloadInnerInner) -> SpecIkev2CpPayloadInner {
        let (cfg_type, (reserved, attributes)) = m;
        SpecIkev2CpPayloadInner { cfg_type, reserved, attributes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2CpPayloadInner<'a> {
    pub cfg_type: u8,
    pub reserved: &'a [u8],
    pub attributes: RepeatResult<CfgAttribute<'a>>,
}

impl View for Ikev2CpPayloadInner<'_> {
    type V = SpecIkev2CpPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2CpPayloadInner {
            cfg_type: self.cfg_type@,
            reserved: self.reserved@,
            attributes: self.attributes@,
        }
    }
}
pub type Ikev2CpPayloadInnerInner<'a> = (u8, (&'a [u8], RepeatResult<CfgAttribute<'a>>));

pub type Ikev2CpPayloadInnerInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a RepeatResult<CfgAttribute<'a>>));
impl<'a> From<&'a Ikev2CpPayloadInner<'a>> for Ikev2CpPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2CpPayloadInner) -> Ikev2CpPayloadInnerInnerRef<'a> {
        (&m.cfg_type, (&m.reserved, &m.attributes))
    }
}

impl<'a> From<Ikev2CpPayloadInnerInner<'a>> for Ikev2CpPayloadInner<'a> {
    fn ex_from(m: Ikev2CpPayloadInnerInner) -> Ikev2CpPayloadInner {
        let (cfg_type, (reserved, attributes)) = m;
        Ikev2CpPayloadInner { cfg_type, reserved, attributes }
    }
}

pub struct Ikev2CpPayloadInnerMapper;
impl View for Ikev2CpPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2CpPayloadInnerMapper {
    type Src = SpecIkev2CpPayloadInnerInner;
    type Dst = SpecIkev2CpPayloadInner;
}
impl SpecIsoProof for Ikev2CpPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2CpPayloadInnerMapper {
    type Src = Ikev2CpPayloadInnerInner<'a>;
    type Dst = Ikev2CpPayloadInner<'a>;
    type RefSrc = Ikev2CpPayloadInnerInnerRef<'a>;
}
pub spec const SPEC_IKEV2CPPAYLOADINNERRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecIkev2CpPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, AndThen<bytes::Tail, Repeat<SpecCfgAttributeCombinator>>);
type SpecIkev2CpPayloadInnerCombinatorAlias2 = (SpecCfgTypeCombinator, SpecIkev2CpPayloadInnerCombinatorAlias1);
pub struct SpecIkev2CpPayloadInnerCombinator(pub SpecIkev2CpPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2CpPayloadInnerCombinator {
    type Type = SpecIkev2CpPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2CpPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2CpPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2CpPayloadInnerCombinatorAlias = Mapped<SpecIkev2CpPayloadInnerCombinatorAlias2, Ikev2CpPayloadInnerMapper>;
pub exec static IKEV2CPPAYLOADINNERRESERVED_CONST: [u8; 3]
    ensures IKEV2CPPAYLOADINNERRESERVED_CONST@ == SPEC_IKEV2CPPAYLOADINNERRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_IKEV2CPPAYLOADINNERRESERVED_CONST);
    arr
}
type Ikev2CpPayloadInnerCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, AndThen<bytes::Tail, Repeat<CfgAttributeCombinator>>);
type Ikev2CpPayloadInnerCombinatorAlias2 = (CfgTypeCombinator, Ikev2CpPayloadInnerCombinator1);
pub struct Ikev2CpPayloadInnerCombinator1(pub Ikev2CpPayloadInnerCombinatorAlias1);
impl View for Ikev2CpPayloadInnerCombinator1 {
    type V = SpecIkev2CpPayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2CpPayloadInnerCombinator1, Ikev2CpPayloadInnerCombinatorAlias1);

pub struct Ikev2CpPayloadInnerCombinator2(pub Ikev2CpPayloadInnerCombinatorAlias2);
impl View for Ikev2CpPayloadInnerCombinator2 {
    type V = SpecIkev2CpPayloadInnerCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2CpPayloadInnerCombinator2, Ikev2CpPayloadInnerCombinatorAlias2);

pub struct Ikev2CpPayloadInnerCombinator(pub Ikev2CpPayloadInnerCombinatorAlias);

impl View for Ikev2CpPayloadInnerCombinator {
    type V = SpecIkev2CpPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2CpPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2CpPayloadInnerCombinator {
    type Type = Ikev2CpPayloadInner<'a>;
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
pub type Ikev2CpPayloadInnerCombinatorAlias = Mapped<Ikev2CpPayloadInnerCombinator2, Ikev2CpPayloadInnerMapper>;


pub open spec fn spec_ikev2_cp_payload_inner() -> SpecIkev2CpPayloadInnerCombinator {
    SpecIkev2CpPayloadInnerCombinator(
    Mapped {
        inner: (spec_cfg_type(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_IKEV2CPPAYLOADINNERRESERVED_CONST) }, AndThen(bytes::Tail, Repeat(spec_cfg_attribute())))),
        mapper: Ikev2CpPayloadInnerMapper,
    })
}

                
pub fn ikev2_cp_payload_inner<'a>() -> (o: Ikev2CpPayloadInnerCombinator)
    ensures o@ == spec_ikev2_cp_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2CpPayloadInnerCombinator(
    Mapped {
        inner: Ikev2CpPayloadInnerCombinator2((cfg_type(), Ikev2CpPayloadInnerCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IKEV2CPPAYLOADINNERRESERVED_CONST) }, AndThen(bytes::Tail, Repeat::new(cfg_attribute())))))),
        mapper: Ikev2CpPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_cp_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_cp_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2CpPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_cp_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_cp_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_cp_payload_inner().spec_parse(input@) is None,
        spec_ikev2_cp_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_cp_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_cp_payload_inner<'a>(v: <Ikev2CpPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_cp_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_cp_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_cp_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_cp_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_cp_payload_inner_len<'a>(v: <Ikev2CpPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_cp_payload_inner().wf(v@),
        spec_ikev2_cp_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_cp_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_cp_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecIkev2KePayloadInner {
    pub dh_group_num: u16,
    pub reserved: u16,
    pub ke_data: Seq<u8>,
}

pub type SpecIkev2KePayloadInnerInner = (u16, (u16, Seq<u8>));


impl SpecFrom<SpecIkev2KePayloadInner> for SpecIkev2KePayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2KePayloadInner) -> SpecIkev2KePayloadInnerInner {
        (m.dh_group_num, (m.reserved, m.ke_data))
    }
}

impl SpecFrom<SpecIkev2KePayloadInnerInner> for SpecIkev2KePayloadInner {
    open spec fn spec_from(m: SpecIkev2KePayloadInnerInner) -> SpecIkev2KePayloadInner {
        let (dh_group_num, (reserved, ke_data)) = m;
        SpecIkev2KePayloadInner { dh_group_num, reserved, ke_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2KePayloadInner<'a> {
    pub dh_group_num: u16,
    pub reserved: u16,
    pub ke_data: &'a [u8],
}

impl View for Ikev2KePayloadInner<'_> {
    type V = SpecIkev2KePayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2KePayloadInner {
            dh_group_num: self.dh_group_num@,
            reserved: self.reserved@,
            ke_data: self.ke_data@,
        }
    }
}
pub type Ikev2KePayloadInnerInner<'a> = (u16, (u16, &'a [u8]));

pub type Ikev2KePayloadInnerInnerRef<'a> = (&'a u16, (&'a u16, &'a &'a [u8]));
impl<'a> From<&'a Ikev2KePayloadInner<'a>> for Ikev2KePayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2KePayloadInner) -> Ikev2KePayloadInnerInnerRef<'a> {
        (&m.dh_group_num, (&m.reserved, &m.ke_data))
    }
}

impl<'a> From<Ikev2KePayloadInnerInner<'a>> for Ikev2KePayloadInner<'a> {
    fn ex_from(m: Ikev2KePayloadInnerInner) -> Ikev2KePayloadInner {
        let (dh_group_num, (reserved, ke_data)) = m;
        Ikev2KePayloadInner { dh_group_num, reserved, ke_data }
    }
}

pub struct Ikev2KePayloadInnerMapper;
impl View for Ikev2KePayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2KePayloadInnerMapper {
    type Src = SpecIkev2KePayloadInnerInner;
    type Dst = SpecIkev2KePayloadInner;
}
impl SpecIsoProof for Ikev2KePayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2KePayloadInnerMapper {
    type Src = Ikev2KePayloadInnerInner<'a>;
    type Dst = Ikev2KePayloadInner<'a>;
    type RefSrc = Ikev2KePayloadInnerInnerRef<'a>;
}
pub const IKEV2KEPAYLOADINNERRESERVED_CONST: u16 = 0;
type SpecIkev2KePayloadInnerCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, bytes::Tail);
type SpecIkev2KePayloadInnerCombinatorAlias2 = (SpecDhIdCombinator, SpecIkev2KePayloadInnerCombinatorAlias1);
pub struct SpecIkev2KePayloadInnerCombinator(pub SpecIkev2KePayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2KePayloadInnerCombinator {
    type Type = SpecIkev2KePayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2KePayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2KePayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2KePayloadInnerCombinatorAlias = Mapped<SpecIkev2KePayloadInnerCombinatorAlias2, Ikev2KePayloadInnerMapper>;
type Ikev2KePayloadInnerCombinatorAlias1 = (Refined<U16Be, TagPred<u16>>, bytes::Tail);
type Ikev2KePayloadInnerCombinatorAlias2 = (DhIdCombinator, Ikev2KePayloadInnerCombinator1);
pub struct Ikev2KePayloadInnerCombinator1(pub Ikev2KePayloadInnerCombinatorAlias1);
impl View for Ikev2KePayloadInnerCombinator1 {
    type V = SpecIkev2KePayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2KePayloadInnerCombinator1, Ikev2KePayloadInnerCombinatorAlias1);

pub struct Ikev2KePayloadInnerCombinator2(pub Ikev2KePayloadInnerCombinatorAlias2);
impl View for Ikev2KePayloadInnerCombinator2 {
    type V = SpecIkev2KePayloadInnerCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2KePayloadInnerCombinator2, Ikev2KePayloadInnerCombinatorAlias2);

pub struct Ikev2KePayloadInnerCombinator(pub Ikev2KePayloadInnerCombinatorAlias);

impl View for Ikev2KePayloadInnerCombinator {
    type V = SpecIkev2KePayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2KePayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2KePayloadInnerCombinator {
    type Type = Ikev2KePayloadInner<'a>;
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
pub type Ikev2KePayloadInnerCombinatorAlias = Mapped<Ikev2KePayloadInnerCombinator2, Ikev2KePayloadInnerMapper>;


pub open spec fn spec_ikev2_ke_payload_inner() -> SpecIkev2KePayloadInnerCombinator {
    SpecIkev2KePayloadInnerCombinator(
    Mapped {
        inner: (spec_dh_id(), (Refined { inner: U16Be, predicate: TagPred(IKEV2KEPAYLOADINNERRESERVED_CONST) }, bytes::Tail)),
        mapper: Ikev2KePayloadInnerMapper,
    })
}

                
pub fn ikev2_ke_payload_inner<'a>() -> (o: Ikev2KePayloadInnerCombinator)
    ensures o@ == spec_ikev2_ke_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2KePayloadInnerCombinator(
    Mapped {
        inner: Ikev2KePayloadInnerCombinator2((dh_id(), Ikev2KePayloadInnerCombinator1((Refined { inner: U16Be, predicate: TagPred(IKEV2KEPAYLOADINNERRESERVED_CONST) }, bytes::Tail)))),
        mapper: Ikev2KePayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_ke_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_ke_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2KePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_ke_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_ke_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_ke_payload_inner().spec_parse(input@) is None,
        spec_ikev2_ke_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_ke_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_ke_payload_inner<'a>(v: <Ikev2KePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_ke_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_ke_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_ke_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_ke_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_ke_payload_inner_len<'a>(v: <Ikev2KePayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_ke_payload_inner().wf(v@),
        spec_ikev2_ke_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_ke_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_ke_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecAuthPayloadBody {
    pub auth_method: u8,
    pub reserved: Seq<u8>,
    pub auth_data: Seq<u8>,
}

pub type SpecAuthPayloadBodyInner = (u8, (Seq<u8>, Seq<u8>));


impl SpecFrom<SpecAuthPayloadBody> for SpecAuthPayloadBodyInner {
    open spec fn spec_from(m: SpecAuthPayloadBody) -> SpecAuthPayloadBodyInner {
        (m.auth_method, (m.reserved, m.auth_data))
    }
}

impl SpecFrom<SpecAuthPayloadBodyInner> for SpecAuthPayloadBody {
    open spec fn spec_from(m: SpecAuthPayloadBodyInner) -> SpecAuthPayloadBody {
        let (auth_method, (reserved, auth_data)) = m;
        SpecAuthPayloadBody { auth_method, reserved, auth_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct AuthPayloadBody<'a> {
    pub auth_method: u8,
    pub reserved: &'a [u8],
    pub auth_data: &'a [u8],
}

impl View for AuthPayloadBody<'_> {
    type V = SpecAuthPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecAuthPayloadBody {
            auth_method: self.auth_method@,
            reserved: self.reserved@,
            auth_data: self.auth_data@,
        }
    }
}
pub type AuthPayloadBodyInner<'a> = (u8, (&'a [u8], &'a [u8]));

pub type AuthPayloadBodyInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a &'a [u8]));
impl<'a> From<&'a AuthPayloadBody<'a>> for AuthPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a AuthPayloadBody) -> AuthPayloadBodyInnerRef<'a> {
        (&m.auth_method, (&m.reserved, &m.auth_data))
    }
}

impl<'a> From<AuthPayloadBodyInner<'a>> for AuthPayloadBody<'a> {
    fn ex_from(m: AuthPayloadBodyInner) -> AuthPayloadBody {
        let (auth_method, (reserved, auth_data)) = m;
        AuthPayloadBody { auth_method, reserved, auth_data }
    }
}

pub struct AuthPayloadBodyMapper;
impl View for AuthPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AuthPayloadBodyMapper {
    type Src = SpecAuthPayloadBodyInner;
    type Dst = SpecAuthPayloadBody;
}
impl SpecIsoProof for AuthPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for AuthPayloadBodyMapper {
    type Src = AuthPayloadBodyInner<'a>;
    type Dst = AuthPayloadBody<'a>;
    type RefSrc = AuthPayloadBodyInnerRef<'a>;
}
pub spec const SPEC_AUTHPAYLOADBODYRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecAuthPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, bytes::Variable);
type SpecAuthPayloadBodyCombinatorAlias2 = (SpecAuthMethodCombinator, SpecAuthPayloadBodyCombinatorAlias1);
pub struct SpecAuthPayloadBodyCombinator(pub SpecAuthPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecAuthPayloadBodyCombinator {
    type Type = SpecAuthPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAuthPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAuthPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecAuthPayloadBodyCombinatorAlias = Mapped<SpecAuthPayloadBodyCombinatorAlias2, AuthPayloadBodyMapper>;
pub exec static AUTHPAYLOADBODYRESERVED_CONST: [u8; 3]
    ensures AUTHPAYLOADBODYRESERVED_CONST@ == SPEC_AUTHPAYLOADBODYRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_AUTHPAYLOADBODYRESERVED_CONST);
    arr
}
type AuthPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, bytes::Variable);
type AuthPayloadBodyCombinatorAlias2 = (AuthMethodCombinator, AuthPayloadBodyCombinator1);
pub struct AuthPayloadBodyCombinator1(pub AuthPayloadBodyCombinatorAlias1);
impl View for AuthPayloadBodyCombinator1 {
    type V = SpecAuthPayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AuthPayloadBodyCombinator1, AuthPayloadBodyCombinatorAlias1);

pub struct AuthPayloadBodyCombinator2(pub AuthPayloadBodyCombinatorAlias2);
impl View for AuthPayloadBodyCombinator2 {
    type V = SpecAuthPayloadBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AuthPayloadBodyCombinator2, AuthPayloadBodyCombinatorAlias2);

pub struct AuthPayloadBodyCombinator(pub AuthPayloadBodyCombinatorAlias);

impl View for AuthPayloadBodyCombinator {
    type V = SpecAuthPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecAuthPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AuthPayloadBodyCombinator {
    type Type = AuthPayloadBody<'a>;
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
pub type AuthPayloadBodyCombinatorAlias = Mapped<AuthPayloadBodyCombinator2, AuthPayloadBodyMapper>;


pub open spec fn spec_auth_payload_body(payload_length: u16) -> SpecAuthPayloadBodyCombinator {
    SpecAuthPayloadBodyCombinator(
    Mapped {
        inner: (spec_auth_method(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_AUTHPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize))),
        mapper: AuthPayloadBodyMapper,
    })
}

pub fn auth_payload_body<'a>(payload_length: u16) -> (o: AuthPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_auth_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AuthPayloadBodyCombinator(
    Mapped {
        inner: AuthPayloadBodyCombinator2((auth_method(), AuthPayloadBodyCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(AUTHPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize))))),
        mapper: AuthPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_auth_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_auth_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<AuthPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_auth_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_auth_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_auth_payload_body(payload_length@).spec_parse(input@) is None,
        spec_auth_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = auth_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_auth_payload_body<'a>(v: <AuthPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_auth_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_auth_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_auth_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = auth_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn auth_payload_body_len<'a>(v: <AuthPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_auth_payload_body(payload_length@).wf(v@),
        spec_auth_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_auth_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = auth_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecIdPayloadBody {
    pub id_type: u8,
    pub reserved: Seq<u8>,
    pub id_data: Seq<u8>,
}

pub type SpecIdPayloadBodyInner = (u8, (Seq<u8>, Seq<u8>));


impl SpecFrom<SpecIdPayloadBody> for SpecIdPayloadBodyInner {
    open spec fn spec_from(m: SpecIdPayloadBody) -> SpecIdPayloadBodyInner {
        (m.id_type, (m.reserved, m.id_data))
    }
}

impl SpecFrom<SpecIdPayloadBodyInner> for SpecIdPayloadBody {
    open spec fn spec_from(m: SpecIdPayloadBodyInner) -> SpecIdPayloadBody {
        let (id_type, (reserved, id_data)) = m;
        SpecIdPayloadBody { id_type, reserved, id_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct IdPayloadBody<'a> {
    pub id_type: u8,
    pub reserved: &'a [u8],
    pub id_data: &'a [u8],
}

impl View for IdPayloadBody<'_> {
    type V = SpecIdPayloadBody;

    open spec fn view(&self) -> Self::V {
        SpecIdPayloadBody {
            id_type: self.id_type@,
            reserved: self.reserved@,
            id_data: self.id_data@,
        }
    }
}
pub type IdPayloadBodyInner<'a> = (u8, (&'a [u8], &'a [u8]));

pub type IdPayloadBodyInnerRef<'a> = (&'a u8, (&'a &'a [u8], &'a &'a [u8]));
impl<'a> From<&'a IdPayloadBody<'a>> for IdPayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a IdPayloadBody) -> IdPayloadBodyInnerRef<'a> {
        (&m.id_type, (&m.reserved, &m.id_data))
    }
}

impl<'a> From<IdPayloadBodyInner<'a>> for IdPayloadBody<'a> {
    fn ex_from(m: IdPayloadBodyInner) -> IdPayloadBody {
        let (id_type, (reserved, id_data)) = m;
        IdPayloadBody { id_type, reserved, id_data }
    }
}

pub struct IdPayloadBodyMapper;
impl View for IdPayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for IdPayloadBodyMapper {
    type Src = SpecIdPayloadBodyInner;
    type Dst = SpecIdPayloadBody;
}
impl SpecIsoProof for IdPayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for IdPayloadBodyMapper {
    type Src = IdPayloadBodyInner<'a>;
    type Dst = IdPayloadBody<'a>;
    type RefSrc = IdPayloadBodyInnerRef<'a>;
}
pub spec const SPEC_IDPAYLOADBODYRESERVED_CONST: Seq<u8> = seq![0; 3];type SpecIdPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<Seq<u8>>>, bytes::Variable);
type SpecIdPayloadBodyCombinatorAlias2 = (SpecIdTypeCombinator, SpecIdPayloadBodyCombinatorAlias1);
pub struct SpecIdPayloadBodyCombinator(pub SpecIdPayloadBodyCombinatorAlias);

impl SpecCombinator for SpecIdPayloadBodyCombinator {
    type Type = SpecIdPayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIdPayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIdPayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecIdPayloadBodyCombinatorAlias = Mapped<SpecIdPayloadBodyCombinatorAlias2, IdPayloadBodyMapper>;
pub exec static IDPAYLOADBODYRESERVED_CONST: [u8; 3]
    ensures IDPAYLOADBODYRESERVED_CONST@ == SPEC_IDPAYLOADBODYRESERVED_CONST,
{
    let arr: [u8; 3] = [0; 3];
    assert(arr@ == SPEC_IDPAYLOADBODYRESERVED_CONST);
    arr
}
type IdPayloadBodyCombinatorAlias1 = (Refined<bytes::Fixed<3>, TagPred<[u8; 3]>>, bytes::Variable);
type IdPayloadBodyCombinatorAlias2 = (IdTypeCombinator, IdPayloadBodyCombinator1);
pub struct IdPayloadBodyCombinator1(pub IdPayloadBodyCombinatorAlias1);
impl View for IdPayloadBodyCombinator1 {
    type V = SpecIdPayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IdPayloadBodyCombinator1, IdPayloadBodyCombinatorAlias1);

pub struct IdPayloadBodyCombinator2(pub IdPayloadBodyCombinatorAlias2);
impl View for IdPayloadBodyCombinator2 {
    type V = SpecIdPayloadBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(IdPayloadBodyCombinator2, IdPayloadBodyCombinatorAlias2);

pub struct IdPayloadBodyCombinator(pub IdPayloadBodyCombinatorAlias);

impl View for IdPayloadBodyCombinator {
    type V = SpecIdPayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecIdPayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for IdPayloadBodyCombinator {
    type Type = IdPayloadBody<'a>;
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
pub type IdPayloadBodyCombinatorAlias = Mapped<IdPayloadBodyCombinator2, IdPayloadBodyMapper>;


pub open spec fn spec_id_payload_body(payload_length: u16) -> SpecIdPayloadBodyCombinator {
    SpecIdPayloadBodyCombinator(
    Mapped {
        inner: (spec_id_type(), (Refined { inner: bytes::Fixed::<3>, predicate: TagPred(SPEC_IDPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::spec_from(payload_length) - 8)) as usize))),
        mapper: IdPayloadBodyMapper,
    })
}

pub fn id_payload_body<'a>(payload_length: u16) -> (o: IdPayloadBodyCombinator)
    requires
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures o@ == spec_id_payload_body(payload_length@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = IdPayloadBodyCombinator(
    Mapped {
        inner: IdPayloadBodyCombinator2((id_type(), IdPayloadBodyCombinator1((Refined { inner: bytes::Fixed::<3>, predicate: TagPred(IDPAYLOADBODYRESERVED_CONST) }, bytes::Variable(((usize::ex_from(payload_length) - 8)) as usize))))),
        mapper: IdPayloadBodyMapper,
    });
    // assert({
    //     &&& combinator@ == spec_id_payload_body(payload_length@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_id_payload_body<'a>(input: &'a [u8], payload_length: u16) -> (res: PResult<<IdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        res matches Ok((n, v)) ==> spec_id_payload_body(payload_length@).spec_parse(input@) == Some((n as int, v@)),
        spec_id_payload_body(payload_length@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_id_payload_body(payload_length@).spec_parse(input@) is None,
        spec_id_payload_body(payload_length@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = id_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_id_payload_body<'a>(v: <IdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, payload_length: u16) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_id_payload_body(payload_length@).wf(v@),
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_id_payload_body(payload_length@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_id_payload_body(payload_length@).spec_serialize(v@))
        },
{
    let combinator = id_payload_body( payload_length );
    combinator.serialize(v, data, pos)
}

pub fn id_payload_body_len<'a>(v: <IdPayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, payload_length: u16) -> (serialize_len: usize)
    requires
        spec_id_payload_body(payload_length@).wf(v@),
        spec_id_payload_body(payload_length@).spec_serialize(v@).len() <= usize::MAX,
        ((payload_length) >= 8 && (payload_length) <= 65535),

    ensures
        serialize_len == spec_id_payload_body(payload_length@).spec_serialize(v@).len(),
{
    let combinator = id_payload_body( payload_length );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecIkev2CertreqPayloadInner {
    pub cert_encoding: u8,
    pub ca_data: Seq<u8>,
}

pub type SpecIkev2CertreqPayloadInnerInner = (u8, Seq<u8>);


impl SpecFrom<SpecIkev2CertreqPayloadInner> for SpecIkev2CertreqPayloadInnerInner {
    open spec fn spec_from(m: SpecIkev2CertreqPayloadInner) -> SpecIkev2CertreqPayloadInnerInner {
        (m.cert_encoding, m.ca_data)
    }
}

impl SpecFrom<SpecIkev2CertreqPayloadInnerInner> for SpecIkev2CertreqPayloadInner {
    open spec fn spec_from(m: SpecIkev2CertreqPayloadInnerInner) -> SpecIkev2CertreqPayloadInner {
        let (cert_encoding, ca_data) = m;
        SpecIkev2CertreqPayloadInner { cert_encoding, ca_data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2CertreqPayloadInner<'a> {
    pub cert_encoding: u8,
    pub ca_data: &'a [u8],
}

impl View for Ikev2CertreqPayloadInner<'_> {
    type V = SpecIkev2CertreqPayloadInner;

    open spec fn view(&self) -> Self::V {
        SpecIkev2CertreqPayloadInner {
            cert_encoding: self.cert_encoding@,
            ca_data: self.ca_data@,
        }
    }
}
pub type Ikev2CertreqPayloadInnerInner<'a> = (u8, &'a [u8]);

pub type Ikev2CertreqPayloadInnerInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a Ikev2CertreqPayloadInner<'a>> for Ikev2CertreqPayloadInnerInnerRef<'a> {
    fn ex_from(m: &'a Ikev2CertreqPayloadInner) -> Ikev2CertreqPayloadInnerInnerRef<'a> {
        (&m.cert_encoding, &m.ca_data)
    }
}

impl<'a> From<Ikev2CertreqPayloadInnerInner<'a>> for Ikev2CertreqPayloadInner<'a> {
    fn ex_from(m: Ikev2CertreqPayloadInnerInner) -> Ikev2CertreqPayloadInner {
        let (cert_encoding, ca_data) = m;
        Ikev2CertreqPayloadInner { cert_encoding, ca_data }
    }
}

pub struct Ikev2CertreqPayloadInnerMapper;
impl View for Ikev2CertreqPayloadInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2CertreqPayloadInnerMapper {
    type Src = SpecIkev2CertreqPayloadInnerInner;
    type Dst = SpecIkev2CertreqPayloadInner;
}
impl SpecIsoProof for Ikev2CertreqPayloadInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2CertreqPayloadInnerMapper {
    type Src = Ikev2CertreqPayloadInnerInner<'a>;
    type Dst = Ikev2CertreqPayloadInner<'a>;
    type RefSrc = Ikev2CertreqPayloadInnerInnerRef<'a>;
}
type SpecIkev2CertreqPayloadInnerCombinatorAlias1 = (SpecCertEncodingCombinator, bytes::Tail);
pub struct SpecIkev2CertreqPayloadInnerCombinator(pub SpecIkev2CertreqPayloadInnerCombinatorAlias);

impl SpecCombinator for SpecIkev2CertreqPayloadInnerCombinator {
    type Type = SpecIkev2CertreqPayloadInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2CertreqPayloadInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2CertreqPayloadInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2CertreqPayloadInnerCombinatorAlias = Mapped<SpecIkev2CertreqPayloadInnerCombinatorAlias1, Ikev2CertreqPayloadInnerMapper>;
type Ikev2CertreqPayloadInnerCombinatorAlias1 = (CertEncodingCombinator, bytes::Tail);
pub struct Ikev2CertreqPayloadInnerCombinator1(pub Ikev2CertreqPayloadInnerCombinatorAlias1);
impl View for Ikev2CertreqPayloadInnerCombinator1 {
    type V = SpecIkev2CertreqPayloadInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2CertreqPayloadInnerCombinator1, Ikev2CertreqPayloadInnerCombinatorAlias1);

pub struct Ikev2CertreqPayloadInnerCombinator(pub Ikev2CertreqPayloadInnerCombinatorAlias);

impl View for Ikev2CertreqPayloadInnerCombinator {
    type V = SpecIkev2CertreqPayloadInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2CertreqPayloadInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2CertreqPayloadInnerCombinator {
    type Type = Ikev2CertreqPayloadInner<'a>;
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
pub type Ikev2CertreqPayloadInnerCombinatorAlias = Mapped<Ikev2CertreqPayloadInnerCombinator1, Ikev2CertreqPayloadInnerMapper>;


pub open spec fn spec_ikev2_certreq_payload_inner() -> SpecIkev2CertreqPayloadInnerCombinator {
    SpecIkev2CertreqPayloadInnerCombinator(
    Mapped {
        inner: (spec_cert_encoding(), bytes::Tail),
        mapper: Ikev2CertreqPayloadInnerMapper,
    })
}

                
pub fn ikev2_certreq_payload_inner<'a>() -> (o: Ikev2CertreqPayloadInnerCombinator)
    ensures o@ == spec_ikev2_certreq_payload_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2CertreqPayloadInnerCombinator(
    Mapped {
        inner: Ikev2CertreqPayloadInnerCombinator1((cert_encoding(), bytes::Tail)),
        mapper: Ikev2CertreqPayloadInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_certreq_payload_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_certreq_payload_inner<'a>(input: &'a [u8]) -> (res: PResult<<Ikev2CertreqPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_ikev2_certreq_payload_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_certreq_payload_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_certreq_payload_inner().spec_parse(input@) is None,
        spec_ikev2_certreq_payload_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_certreq_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_certreq_payload_inner<'a>(v: <Ikev2CertreqPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_certreq_payload_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_certreq_payload_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_certreq_payload_inner().spec_serialize(v@))
        },
{
    let combinator = ikev2_certreq_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn ikev2_certreq_payload_inner_len<'a>(v: <Ikev2CertreqPayloadInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_ikev2_certreq_payload_inner().wf(v@),
        spec_ikev2_certreq_payload_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_ikev2_certreq_payload_inner().spec_serialize(v@).len(),
{
    let combinator = ikev2_certreq_payload_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub enum SpecIkev2PayloadBody {
    SA(SpecIkev2SaPayloadInner),
    KE(SpecIkev2KePayloadInner),
    IDi(SpecIkev2IdPayloadInner),
    IDr(SpecIkev2IdPayloadInner),
    CERT(SpecIkev2CertPayloadInner),
    CERTREQ(SpecIkev2CertreqPayloadInner),
    AUTH(SpecIkev2AuthPayloadInner),
    Nonce(SpecIkev2NoncePayloadInner),
    Notify(SpecIkev2NotifyPayloadInner),
    Delete(SpecDeletePayloadBody),
    VendorID(SpecIkev2VendorIdPayloadInner),
    TSi(SpecIkev2TsPayloadInner),
    TSr(SpecIkev2TsPayloadInner),
    SK(SpecIkev2SkPayloadInner),
    CP(SpecIkev2CpPayloadInner),
    EAP(SpecIkev2EapPayloadInner),
    Unrecognized(Seq<u8>),
}

pub type SpecIkev2PayloadBodyInner = Either<SpecIkev2SaPayloadInner, Either<SpecIkev2KePayloadInner, Either<SpecIkev2IdPayloadInner, Either<SpecIkev2IdPayloadInner, Either<SpecIkev2CertPayloadInner, Either<SpecIkev2CertreqPayloadInner, Either<SpecIkev2AuthPayloadInner, Either<SpecIkev2NoncePayloadInner, Either<SpecIkev2NotifyPayloadInner, Either<SpecDeletePayloadBody, Either<SpecIkev2VendorIdPayloadInner, Either<SpecIkev2TsPayloadInner, Either<SpecIkev2TsPayloadInner, Either<SpecIkev2SkPayloadInner, Either<SpecIkev2CpPayloadInner, Either<SpecIkev2EapPayloadInner, Seq<u8>>>>>>>>>>>>>>>>>;

impl SpecFrom<SpecIkev2PayloadBody> for SpecIkev2PayloadBodyInner {
    open spec fn spec_from(m: SpecIkev2PayloadBody) -> SpecIkev2PayloadBodyInner {
        match m {
            SpecIkev2PayloadBody::SA(m) => Either::Left(m),
            SpecIkev2PayloadBody::KE(m) => Either::Right(Either::Left(m)),
            SpecIkev2PayloadBody::IDi(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecIkev2PayloadBody::IDr(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecIkev2PayloadBody::CERT(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecIkev2PayloadBody::CERTREQ(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecIkev2PayloadBody::AUTH(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecIkev2PayloadBody::Nonce(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecIkev2PayloadBody::Notify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecIkev2PayloadBody::Delete(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecIkev2PayloadBody::VendorID(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecIkev2PayloadBody::TSi(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecIkev2PayloadBody::TSr(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecIkev2PayloadBody::SK(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecIkev2PayloadBody::CP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecIkev2PayloadBody::EAP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecIkev2PayloadBody::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecIkev2PayloadBodyInner> for SpecIkev2PayloadBody {
    open spec fn spec_from(m: SpecIkev2PayloadBodyInner) -> SpecIkev2PayloadBody {
        match m {
            Either::Left(m) => SpecIkev2PayloadBody::SA(m),
            Either::Right(Either::Left(m)) => SpecIkev2PayloadBody::KE(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecIkev2PayloadBody::IDi(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecIkev2PayloadBody::IDr(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecIkev2PayloadBody::CERT(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecIkev2PayloadBody::CERTREQ(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecIkev2PayloadBody::AUTH(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecIkev2PayloadBody::Nonce(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecIkev2PayloadBody::Notify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecIkev2PayloadBody::Delete(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecIkev2PayloadBody::VendorID(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecIkev2PayloadBody::TSi(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecIkev2PayloadBody::TSr(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecIkev2PayloadBody::SK(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecIkev2PayloadBody::CP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecIkev2PayloadBody::EAP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))) => SpecIkev2PayloadBody::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ikev2PayloadBody<'a> {
    SA(Ikev2SaPayloadInner<'a>),
    KE(Ikev2KePayloadInner<'a>),
    IDi(Ikev2IdPayloadInner<'a>),
    IDr(Ikev2IdPayloadInner<'a>),
    CERT(Ikev2CertPayloadInner<'a>),
    CERTREQ(Ikev2CertreqPayloadInner<'a>),
    AUTH(Ikev2AuthPayloadInner<'a>),
    Nonce(Ikev2NoncePayloadInner<'a>),
    Notify(Ikev2NotifyPayloadInner<'a>),
    Delete(DeletePayloadBody<'a>),
    VendorID(Ikev2VendorIdPayloadInner<'a>),
    TSi(Ikev2TsPayloadInner<'a>),
    TSr(Ikev2TsPayloadInner<'a>),
    SK(Ikev2SkPayloadInner<'a>),
    CP(Ikev2CpPayloadInner<'a>),
    EAP(Ikev2EapPayloadInner<'a>),
    Unrecognized(&'a [u8]),
}

pub type Ikev2PayloadBodyInner<'a> = Either<Ikev2SaPayloadInner<'a>, Either<Ikev2KePayloadInner<'a>, Either<Ikev2IdPayloadInner<'a>, Either<Ikev2IdPayloadInner<'a>, Either<Ikev2CertPayloadInner<'a>, Either<Ikev2CertreqPayloadInner<'a>, Either<Ikev2AuthPayloadInner<'a>, Either<Ikev2NoncePayloadInner<'a>, Either<Ikev2NotifyPayloadInner<'a>, Either<DeletePayloadBody<'a>, Either<Ikev2VendorIdPayloadInner<'a>, Either<Ikev2TsPayloadInner<'a>, Either<Ikev2TsPayloadInner<'a>, Either<Ikev2SkPayloadInner<'a>, Either<Ikev2CpPayloadInner<'a>, Either<Ikev2EapPayloadInner<'a>, &'a [u8]>>>>>>>>>>>>>>>>;

pub type Ikev2PayloadBodyInnerRef<'a> = Either<&'a Ikev2SaPayloadInner<'a>, Either<&'a Ikev2KePayloadInner<'a>, Either<&'a Ikev2IdPayloadInner<'a>, Either<&'a Ikev2IdPayloadInner<'a>, Either<&'a Ikev2CertPayloadInner<'a>, Either<&'a Ikev2CertreqPayloadInner<'a>, Either<&'a Ikev2AuthPayloadInner<'a>, Either<&'a Ikev2NoncePayloadInner<'a>, Either<&'a Ikev2NotifyPayloadInner<'a>, Either<&'a DeletePayloadBody<'a>, Either<&'a Ikev2VendorIdPayloadInner<'a>, Either<&'a Ikev2TsPayloadInner<'a>, Either<&'a Ikev2TsPayloadInner<'a>, Either<&'a Ikev2SkPayloadInner<'a>, Either<&'a Ikev2CpPayloadInner<'a>, Either<&'a Ikev2EapPayloadInner<'a>, &'a &'a [u8]>>>>>>>>>>>>>>>>;


impl<'a> View for Ikev2PayloadBody<'a> {
    type V = SpecIkev2PayloadBody;
    open spec fn view(&self) -> Self::V {
        match self {
            Ikev2PayloadBody::SA(m) => SpecIkev2PayloadBody::SA(m@),
            Ikev2PayloadBody::KE(m) => SpecIkev2PayloadBody::KE(m@),
            Ikev2PayloadBody::IDi(m) => SpecIkev2PayloadBody::IDi(m@),
            Ikev2PayloadBody::IDr(m) => SpecIkev2PayloadBody::IDr(m@),
            Ikev2PayloadBody::CERT(m) => SpecIkev2PayloadBody::CERT(m@),
            Ikev2PayloadBody::CERTREQ(m) => SpecIkev2PayloadBody::CERTREQ(m@),
            Ikev2PayloadBody::AUTH(m) => SpecIkev2PayloadBody::AUTH(m@),
            Ikev2PayloadBody::Nonce(m) => SpecIkev2PayloadBody::Nonce(m@),
            Ikev2PayloadBody::Notify(m) => SpecIkev2PayloadBody::Notify(m@),
            Ikev2PayloadBody::Delete(m) => SpecIkev2PayloadBody::Delete(m@),
            Ikev2PayloadBody::VendorID(m) => SpecIkev2PayloadBody::VendorID(m@),
            Ikev2PayloadBody::TSi(m) => SpecIkev2PayloadBody::TSi(m@),
            Ikev2PayloadBody::TSr(m) => SpecIkev2PayloadBody::TSr(m@),
            Ikev2PayloadBody::SK(m) => SpecIkev2PayloadBody::SK(m@),
            Ikev2PayloadBody::CP(m) => SpecIkev2PayloadBody::CP(m@),
            Ikev2PayloadBody::EAP(m) => SpecIkev2PayloadBody::EAP(m@),
            Ikev2PayloadBody::Unrecognized(m) => SpecIkev2PayloadBody::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a Ikev2PayloadBody<'a>> for Ikev2PayloadBodyInnerRef<'a> {
    fn ex_from(m: &'a Ikev2PayloadBody<'a>) -> Ikev2PayloadBodyInnerRef<'a> {
        match m {
            Ikev2PayloadBody::SA(m) => Either::Left(m),
            Ikev2PayloadBody::KE(m) => Either::Right(Either::Left(m)),
            Ikev2PayloadBody::IDi(m) => Either::Right(Either::Right(Either::Left(m))),
            Ikev2PayloadBody::IDr(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            Ikev2PayloadBody::CERT(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            Ikev2PayloadBody::CERTREQ(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            Ikev2PayloadBody::AUTH(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            Ikev2PayloadBody::Nonce(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            Ikev2PayloadBody::Notify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            Ikev2PayloadBody::Delete(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            Ikev2PayloadBody::VendorID(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            Ikev2PayloadBody::TSi(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            Ikev2PayloadBody::TSr(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            Ikev2PayloadBody::SK(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            Ikev2PayloadBody::CP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            Ikev2PayloadBody::EAP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            Ikev2PayloadBody::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))),
        }
    }

}

impl<'a> From<Ikev2PayloadBodyInner<'a>> for Ikev2PayloadBody<'a> {
    fn ex_from(m: Ikev2PayloadBodyInner<'a>) -> Ikev2PayloadBody<'a> {
        match m {
            Either::Left(m) => Ikev2PayloadBody::SA(m),
            Either::Right(Either::Left(m)) => Ikev2PayloadBody::KE(m),
            Either::Right(Either::Right(Either::Left(m))) => Ikev2PayloadBody::IDi(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => Ikev2PayloadBody::IDr(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => Ikev2PayloadBody::CERT(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => Ikev2PayloadBody::CERTREQ(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => Ikev2PayloadBody::AUTH(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => Ikev2PayloadBody::Nonce(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => Ikev2PayloadBody::Notify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => Ikev2PayloadBody::Delete(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => Ikev2PayloadBody::VendorID(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => Ikev2PayloadBody::TSi(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => Ikev2PayloadBody::TSr(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => Ikev2PayloadBody::SK(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => Ikev2PayloadBody::CP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => Ikev2PayloadBody::EAP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))) => Ikev2PayloadBody::Unrecognized(m),
        }
    }
    
}


pub struct Ikev2PayloadBodyMapper;
impl View for Ikev2PayloadBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2PayloadBodyMapper {
    type Src = SpecIkev2PayloadBodyInner;
    type Dst = SpecIkev2PayloadBody;
}
impl SpecIsoProof for Ikev2PayloadBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2PayloadBodyMapper {
    type Src = Ikev2PayloadBodyInner<'a>;
    type Dst = Ikev2PayloadBody<'a>;
    type RefSrc = Ikev2PayloadBodyInnerRef<'a>;
}

type SpecIkev2PayloadBodyCombinatorAlias1 = Choice<Cond<SpecIkev2EapPayloadInnerCombinator>, Cond<bytes::Tail>>;
type SpecIkev2PayloadBodyCombinatorAlias2 = Choice<Cond<SpecIkev2CpPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias1>;
type SpecIkev2PayloadBodyCombinatorAlias3 = Choice<Cond<SpecIkev2SkPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias2>;
type SpecIkev2PayloadBodyCombinatorAlias4 = Choice<Cond<SpecIkev2TsPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias3>;
type SpecIkev2PayloadBodyCombinatorAlias5 = Choice<Cond<SpecIkev2TsPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias4>;
type SpecIkev2PayloadBodyCombinatorAlias6 = Choice<Cond<SpecIkev2VendorIdPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias5>;
type SpecIkev2PayloadBodyCombinatorAlias7 = Choice<Cond<SpecDeletePayloadBodyCombinator>, SpecIkev2PayloadBodyCombinatorAlias6>;
type SpecIkev2PayloadBodyCombinatorAlias8 = Choice<Cond<SpecIkev2NotifyPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias7>;
type SpecIkev2PayloadBodyCombinatorAlias9 = Choice<Cond<SpecIkev2NoncePayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias8>;
type SpecIkev2PayloadBodyCombinatorAlias10 = Choice<Cond<SpecIkev2AuthPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias9>;
type SpecIkev2PayloadBodyCombinatorAlias11 = Choice<Cond<SpecIkev2CertreqPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias10>;
type SpecIkev2PayloadBodyCombinatorAlias12 = Choice<Cond<SpecIkev2CertPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias11>;
type SpecIkev2PayloadBodyCombinatorAlias13 = Choice<Cond<SpecIkev2IdPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias12>;
type SpecIkev2PayloadBodyCombinatorAlias14 = Choice<Cond<SpecIkev2IdPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias13>;
type SpecIkev2PayloadBodyCombinatorAlias15 = Choice<Cond<SpecIkev2KePayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias14>;
type SpecIkev2PayloadBodyCombinatorAlias16 = Choice<Cond<SpecIkev2SaPayloadInnerCombinator>, SpecIkev2PayloadBodyCombinatorAlias15>;
pub struct SpecIkev2PayloadBodyCombinator(pub SpecIkev2PayloadBodyCombinatorAlias);

impl SpecCombinator for SpecIkev2PayloadBodyCombinator {
    type Type = SpecIkev2PayloadBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2PayloadBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2PayloadBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2PayloadBodyCombinatorAlias = Mapped<SpecIkev2PayloadBodyCombinatorAlias16, Ikev2PayloadBodyMapper>;
type Ikev2PayloadBodyCombinatorAlias1 = Choice<Cond<Ikev2EapPayloadInnerCombinator>, Cond<bytes::Tail>>;
type Ikev2PayloadBodyCombinatorAlias2 = Choice<Cond<Ikev2CpPayloadInnerCombinator>, Ikev2PayloadBodyCombinator1>;
type Ikev2PayloadBodyCombinatorAlias3 = Choice<Cond<Ikev2SkPayloadInnerCombinator>, Ikev2PayloadBodyCombinator2>;
type Ikev2PayloadBodyCombinatorAlias4 = Choice<Cond<Ikev2TsPayloadInnerCombinator>, Ikev2PayloadBodyCombinator3>;
type Ikev2PayloadBodyCombinatorAlias5 = Choice<Cond<Ikev2TsPayloadInnerCombinator>, Ikev2PayloadBodyCombinator4>;
type Ikev2PayloadBodyCombinatorAlias6 = Choice<Cond<Ikev2VendorIdPayloadInnerCombinator>, Ikev2PayloadBodyCombinator5>;
type Ikev2PayloadBodyCombinatorAlias7 = Choice<Cond<DeletePayloadBodyCombinator>, Ikev2PayloadBodyCombinator6>;
type Ikev2PayloadBodyCombinatorAlias8 = Choice<Cond<Ikev2NotifyPayloadInnerCombinator>, Ikev2PayloadBodyCombinator7>;
type Ikev2PayloadBodyCombinatorAlias9 = Choice<Cond<Ikev2NoncePayloadInnerCombinator>, Ikev2PayloadBodyCombinator8>;
type Ikev2PayloadBodyCombinatorAlias10 = Choice<Cond<Ikev2AuthPayloadInnerCombinator>, Ikev2PayloadBodyCombinator9>;
type Ikev2PayloadBodyCombinatorAlias11 = Choice<Cond<Ikev2CertreqPayloadInnerCombinator>, Ikev2PayloadBodyCombinator10>;
type Ikev2PayloadBodyCombinatorAlias12 = Choice<Cond<Ikev2CertPayloadInnerCombinator>, Ikev2PayloadBodyCombinator11>;
type Ikev2PayloadBodyCombinatorAlias13 = Choice<Cond<Ikev2IdPayloadInnerCombinator>, Ikev2PayloadBodyCombinator12>;
type Ikev2PayloadBodyCombinatorAlias14 = Choice<Cond<Ikev2IdPayloadInnerCombinator>, Ikev2PayloadBodyCombinator13>;
type Ikev2PayloadBodyCombinatorAlias15 = Choice<Cond<Ikev2KePayloadInnerCombinator>, Ikev2PayloadBodyCombinator14>;
type Ikev2PayloadBodyCombinatorAlias16 = Choice<Cond<Ikev2SaPayloadInnerCombinator>, Ikev2PayloadBodyCombinator15>;
pub struct Ikev2PayloadBodyCombinator1(pub Ikev2PayloadBodyCombinatorAlias1);
impl View for Ikev2PayloadBodyCombinator1 {
    type V = SpecIkev2PayloadBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator1, Ikev2PayloadBodyCombinatorAlias1);

pub struct Ikev2PayloadBodyCombinator2(pub Ikev2PayloadBodyCombinatorAlias2);
impl View for Ikev2PayloadBodyCombinator2 {
    type V = SpecIkev2PayloadBodyCombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator2, Ikev2PayloadBodyCombinatorAlias2);

pub struct Ikev2PayloadBodyCombinator3(pub Ikev2PayloadBodyCombinatorAlias3);
impl View for Ikev2PayloadBodyCombinator3 {
    type V = SpecIkev2PayloadBodyCombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator3, Ikev2PayloadBodyCombinatorAlias3);

pub struct Ikev2PayloadBodyCombinator4(pub Ikev2PayloadBodyCombinatorAlias4);
impl View for Ikev2PayloadBodyCombinator4 {
    type V = SpecIkev2PayloadBodyCombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator4, Ikev2PayloadBodyCombinatorAlias4);

pub struct Ikev2PayloadBodyCombinator5(pub Ikev2PayloadBodyCombinatorAlias5);
impl View for Ikev2PayloadBodyCombinator5 {
    type V = SpecIkev2PayloadBodyCombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator5, Ikev2PayloadBodyCombinatorAlias5);

pub struct Ikev2PayloadBodyCombinator6(pub Ikev2PayloadBodyCombinatorAlias6);
impl View for Ikev2PayloadBodyCombinator6 {
    type V = SpecIkev2PayloadBodyCombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator6, Ikev2PayloadBodyCombinatorAlias6);

pub struct Ikev2PayloadBodyCombinator7(pub Ikev2PayloadBodyCombinatorAlias7);
impl View for Ikev2PayloadBodyCombinator7 {
    type V = SpecIkev2PayloadBodyCombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator7, Ikev2PayloadBodyCombinatorAlias7);

pub struct Ikev2PayloadBodyCombinator8(pub Ikev2PayloadBodyCombinatorAlias8);
impl View for Ikev2PayloadBodyCombinator8 {
    type V = SpecIkev2PayloadBodyCombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator8, Ikev2PayloadBodyCombinatorAlias8);

pub struct Ikev2PayloadBodyCombinator9(pub Ikev2PayloadBodyCombinatorAlias9);
impl View for Ikev2PayloadBodyCombinator9 {
    type V = SpecIkev2PayloadBodyCombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator9, Ikev2PayloadBodyCombinatorAlias9);

pub struct Ikev2PayloadBodyCombinator10(pub Ikev2PayloadBodyCombinatorAlias10);
impl View for Ikev2PayloadBodyCombinator10 {
    type V = SpecIkev2PayloadBodyCombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator10, Ikev2PayloadBodyCombinatorAlias10);

pub struct Ikev2PayloadBodyCombinator11(pub Ikev2PayloadBodyCombinatorAlias11);
impl View for Ikev2PayloadBodyCombinator11 {
    type V = SpecIkev2PayloadBodyCombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator11, Ikev2PayloadBodyCombinatorAlias11);

pub struct Ikev2PayloadBodyCombinator12(pub Ikev2PayloadBodyCombinatorAlias12);
impl View for Ikev2PayloadBodyCombinator12 {
    type V = SpecIkev2PayloadBodyCombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator12, Ikev2PayloadBodyCombinatorAlias12);

pub struct Ikev2PayloadBodyCombinator13(pub Ikev2PayloadBodyCombinatorAlias13);
impl View for Ikev2PayloadBodyCombinator13 {
    type V = SpecIkev2PayloadBodyCombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator13, Ikev2PayloadBodyCombinatorAlias13);

pub struct Ikev2PayloadBodyCombinator14(pub Ikev2PayloadBodyCombinatorAlias14);
impl View for Ikev2PayloadBodyCombinator14 {
    type V = SpecIkev2PayloadBodyCombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator14, Ikev2PayloadBodyCombinatorAlias14);

pub struct Ikev2PayloadBodyCombinator15(pub Ikev2PayloadBodyCombinatorAlias15);
impl View for Ikev2PayloadBodyCombinator15 {
    type V = SpecIkev2PayloadBodyCombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator15, Ikev2PayloadBodyCombinatorAlias15);

pub struct Ikev2PayloadBodyCombinator16(pub Ikev2PayloadBodyCombinatorAlias16);
impl View for Ikev2PayloadBodyCombinator16 {
    type V = SpecIkev2PayloadBodyCombinatorAlias16;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(Ikev2PayloadBodyCombinator16, Ikev2PayloadBodyCombinatorAlias16);

pub struct Ikev2PayloadBodyCombinator(pub Ikev2PayloadBodyCombinatorAlias);

impl View for Ikev2PayloadBodyCombinator {
    type V = SpecIkev2PayloadBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2PayloadBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2PayloadBodyCombinator {
    type Type = Ikev2PayloadBody<'a>;
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
pub type Ikev2PayloadBodyCombinatorAlias = Mapped<Ikev2PayloadBodyCombinator16, Ikev2PayloadBodyMapper>;


pub open spec fn spec_ikev2_payload_body(next_pt: u8) -> SpecIkev2PayloadBodyCombinator {
    SpecIkev2PayloadBodyCombinator(Mapped { inner: Choice(Cond { cond: next_pt == NextPayloadType::SPEC_SA, inner: spec_ikev2_sa_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_KE, inner: spec_ikev2_ke_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_IDi, inner: spec_ikev2_id_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_IDr, inner: spec_ikev2_id_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_CERT, inner: spec_ikev2_cert_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_CERTREQ, inner: spec_ikev2_certreq_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_AUTH, inner: spec_ikev2_auth_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_Nonce, inner: spec_ikev2_nonce_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_Notify, inner: spec_ikev2_notify_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_Delete, inner: spec_delete_payload_body() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_VendorID, inner: spec_ikev2_vendor_id_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_TSi, inner: spec_ikev2_ts_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_TSr, inner: spec_ikev2_ts_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_SK, inner: spec_ikev2_sk_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_CP, inner: spec_ikev2_cp_payload_inner() }, Choice(Cond { cond: next_pt == NextPayloadType::SPEC_EAP, inner: spec_ikev2_eap_payload_inner() }, Cond { cond: !(next_pt == NextPayloadType::SPEC_SA || next_pt == NextPayloadType::SPEC_KE || next_pt == NextPayloadType::SPEC_IDi || next_pt == NextPayloadType::SPEC_IDr || next_pt == NextPayloadType::SPEC_CERT || next_pt == NextPayloadType::SPEC_CERTREQ || next_pt == NextPayloadType::SPEC_AUTH || next_pt == NextPayloadType::SPEC_Nonce || next_pt == NextPayloadType::SPEC_Notify || next_pt == NextPayloadType::SPEC_Delete || next_pt == NextPayloadType::SPEC_VendorID || next_pt == NextPayloadType::SPEC_TSi || next_pt == NextPayloadType::SPEC_TSr || next_pt == NextPayloadType::SPEC_SK || next_pt == NextPayloadType::SPEC_CP || next_pt == NextPayloadType::SPEC_EAP), inner: bytes::Tail })))))))))))))))), mapper: Ikev2PayloadBodyMapper })
}

pub fn ikev2_payload_body<'a>(next_pt: u8) -> (o: Ikev2PayloadBodyCombinator)
    requires
        spec_next_payload_type().wf(next_pt@),

    ensures o@ == spec_ikev2_payload_body(next_pt@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2PayloadBodyCombinator(Mapped { inner: Ikev2PayloadBodyCombinator16(Choice::new(Cond { cond: next_pt == NextPayloadType::SA, inner: ikev2_sa_payload_inner() }, Ikev2PayloadBodyCombinator15(Choice::new(Cond { cond: next_pt == NextPayloadType::KE, inner: ikev2_ke_payload_inner() }, Ikev2PayloadBodyCombinator14(Choice::new(Cond { cond: next_pt == NextPayloadType::IDi, inner: ikev2_id_payload_inner() }, Ikev2PayloadBodyCombinator13(Choice::new(Cond { cond: next_pt == NextPayloadType::IDr, inner: ikev2_id_payload_inner() }, Ikev2PayloadBodyCombinator12(Choice::new(Cond { cond: next_pt == NextPayloadType::CERT, inner: ikev2_cert_payload_inner() }, Ikev2PayloadBodyCombinator11(Choice::new(Cond { cond: next_pt == NextPayloadType::CERTREQ, inner: ikev2_certreq_payload_inner() }, Ikev2PayloadBodyCombinator10(Choice::new(Cond { cond: next_pt == NextPayloadType::AUTH, inner: ikev2_auth_payload_inner() }, Ikev2PayloadBodyCombinator9(Choice::new(Cond { cond: next_pt == NextPayloadType::Nonce, inner: ikev2_nonce_payload_inner() }, Ikev2PayloadBodyCombinator8(Choice::new(Cond { cond: next_pt == NextPayloadType::Notify, inner: ikev2_notify_payload_inner() }, Ikev2PayloadBodyCombinator7(Choice::new(Cond { cond: next_pt == NextPayloadType::Delete, inner: delete_payload_body() }, Ikev2PayloadBodyCombinator6(Choice::new(Cond { cond: next_pt == NextPayloadType::VendorID, inner: ikev2_vendor_id_payload_inner() }, Ikev2PayloadBodyCombinator5(Choice::new(Cond { cond: next_pt == NextPayloadType::TSi, inner: ikev2_ts_payload_inner() }, Ikev2PayloadBodyCombinator4(Choice::new(Cond { cond: next_pt == NextPayloadType::TSr, inner: ikev2_ts_payload_inner() }, Ikev2PayloadBodyCombinator3(Choice::new(Cond { cond: next_pt == NextPayloadType::SK, inner: ikev2_sk_payload_inner() }, Ikev2PayloadBodyCombinator2(Choice::new(Cond { cond: next_pt == NextPayloadType::CP, inner: ikev2_cp_payload_inner() }, Ikev2PayloadBodyCombinator1(Choice::new(Cond { cond: next_pt == NextPayloadType::EAP, inner: ikev2_eap_payload_inner() }, Cond { cond: !(next_pt == NextPayloadType::SA || next_pt == NextPayloadType::KE || next_pt == NextPayloadType::IDi || next_pt == NextPayloadType::IDr || next_pt == NextPayloadType::CERT || next_pt == NextPayloadType::CERTREQ || next_pt == NextPayloadType::AUTH || next_pt == NextPayloadType::Nonce || next_pt == NextPayloadType::Notify || next_pt == NextPayloadType::Delete || next_pt == NextPayloadType::VendorID || next_pt == NextPayloadType::TSi || next_pt == NextPayloadType::TSr || next_pt == NextPayloadType::SK || next_pt == NextPayloadType::CP || next_pt == NextPayloadType::EAP), inner: bytes::Tail })))))))))))))))))))))))))))))))), mapper: Ikev2PayloadBodyMapper });
    // assert({
    //     &&& combinator@ == spec_ikev2_payload_body(next_pt@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_payload_body<'a>(input: &'a [u8], next_pt: u8) -> (res: PResult<<Ikev2PayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_next_payload_type().wf(next_pt@),

    ensures
        res matches Ok((n, v)) ==> spec_ikev2_payload_body(next_pt@).spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_payload_body(next_pt@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_payload_body(next_pt@).spec_parse(input@) is None,
        spec_ikev2_payload_body(next_pt@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_payload_body( next_pt );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_payload_body<'a>(v: <Ikev2PayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, next_pt: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_payload_body(next_pt@).wf(v@),
        spec_next_payload_type().wf(next_pt@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_payload_body(next_pt@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_payload_body(next_pt@).spec_serialize(v@))
        },
{
    let combinator = ikev2_payload_body( next_pt );
    combinator.serialize(v, data, pos)
}

pub fn ikev2_payload_body_len<'a>(v: <Ikev2PayloadBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, next_pt: u8) -> (serialize_len: usize)
    requires
        spec_ikev2_payload_body(next_pt@).wf(v@),
        spec_ikev2_payload_body(next_pt@).spec_serialize(v@).len() <= usize::MAX,
        spec_next_payload_type().wf(next_pt@),

    ensures
        serialize_len == spec_ikev2_payload_body(next_pt@).spec_serialize(v@).len(),
{
    let combinator = ikev2_payload_body( next_pt );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecIkev2Payload {
    pub hdr: SpecGenericPayloadHeader,
    pub body: SpecIkev2PayloadBody,
}

pub type SpecIkev2PayloadInner = (SpecGenericPayloadHeader, SpecIkev2PayloadBody);


impl SpecFrom<SpecIkev2Payload> for SpecIkev2PayloadInner {
    open spec fn spec_from(m: SpecIkev2Payload) -> SpecIkev2PayloadInner {
        (m.hdr, m.body)
    }
}

impl SpecFrom<SpecIkev2PayloadInner> for SpecIkev2Payload {
    open spec fn spec_from(m: SpecIkev2PayloadInner) -> SpecIkev2Payload {
        let (hdr, body) = m;
        SpecIkev2Payload { hdr, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Ikev2Payload<'a> {
    pub hdr: GenericPayloadHeader,
    pub body: Ikev2PayloadBody<'a>,
}

impl View for Ikev2Payload<'_> {
    type V = SpecIkev2Payload;

    open spec fn view(&self) -> Self::V {
        SpecIkev2Payload {
            hdr: self.hdr@,
            body: self.body@,
        }
    }
}
pub type Ikev2PayloadInner<'a> = (GenericPayloadHeader, Ikev2PayloadBody<'a>);

pub type Ikev2PayloadInnerRef<'a> = (&'a GenericPayloadHeader, &'a Ikev2PayloadBody<'a>);
impl<'a> From<&'a Ikev2Payload<'a>> for Ikev2PayloadInnerRef<'a> {
    fn ex_from(m: &'a Ikev2Payload) -> Ikev2PayloadInnerRef<'a> {
        (&m.hdr, &m.body)
    }
}

impl<'a> From<Ikev2PayloadInner<'a>> for Ikev2Payload<'a> {
    fn ex_from(m: Ikev2PayloadInner) -> Ikev2Payload {
        let (hdr, body) = m;
        Ikev2Payload { hdr, body }
    }
}

pub struct Ikev2PayloadMapper;
impl View for Ikev2PayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Ikev2PayloadMapper {
    type Src = SpecIkev2PayloadInner;
    type Dst = SpecIkev2Payload;
}
impl SpecIsoProof for Ikev2PayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Ikev2PayloadMapper {
    type Src = Ikev2PayloadInner<'a>;
    type Dst = Ikev2Payload<'a>;
    type RefSrc = Ikev2PayloadInnerRef<'a>;
}

pub struct SpecIkev2PayloadCombinator(pub SpecIkev2PayloadCombinatorAlias);

impl SpecCombinator for SpecIkev2PayloadCombinator {
    type Type = SpecIkev2Payload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecIkev2PayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecIkev2PayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecIkev2PayloadCombinatorAlias = Mapped<SpecPair<SpecGenericPayloadHeaderCombinator, AndThen<bytes::Variable, SpecIkev2PayloadBodyCombinator>>, Ikev2PayloadMapper>;

pub struct Ikev2PayloadCombinator(pub Ikev2PayloadCombinatorAlias);

impl View for Ikev2PayloadCombinator {
    type V = SpecIkev2PayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecIkev2PayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Ikev2PayloadCombinator {
    type Type = Ikev2Payload<'a>;
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
pub type Ikev2PayloadCombinatorAlias = Mapped<Pair<GenericPayloadHeaderCombinator, AndThen<bytes::Variable, Ikev2PayloadBodyCombinator>, Ikev2PayloadCont0>, Ikev2PayloadMapper>;


pub open spec fn spec_ikev2_payload(next_pt: u8) -> SpecIkev2PayloadCombinator {
    SpecIkev2PayloadCombinator(
    Mapped {
        inner: Pair::spec_new(spec_generic_payload_header(), |deps| spec_ikev2_payload_cont0(next_pt, deps)),
        mapper: Ikev2PayloadMapper,
    })
}

pub open spec fn spec_ikev2_payload_cont0(next_pt: u8, deps: SpecGenericPayloadHeader) -> AndThen<bytes::Variable, SpecIkev2PayloadBodyCombinator> {
    let hdr = deps;
    AndThen(bytes::Variable(((usize::spec_from(hdr.payload_length) - 4)) as usize), spec_ikev2_payload_body(next_pt))
}

impl View for Ikev2PayloadCont0 {
    type V = spec_fn(SpecGenericPayloadHeader) -> AndThen<bytes::Variable, SpecIkev2PayloadBodyCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: SpecGenericPayloadHeader| {
            spec_ikev2_payload_cont0(self.next_pt@, deps)
        }
    }
}

pub fn ikev2_payload<'a>(next_pt: u8) -> (o: Ikev2PayloadCombinator)
    requires
        spec_next_payload_type().wf(next_pt@),

    ensures o@ == spec_ikev2_payload(next_pt@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Ikev2PayloadCombinator(
    Mapped {
        inner: Pair::new(generic_payload_header(), Ikev2PayloadCont0 { next_pt }),
        mapper: Ikev2PayloadMapper,
    });
    // assert({
    //     &&& combinator@ == spec_ikev2_payload(next_pt@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_ikev2_payload<'a>(input: &'a [u8], next_pt: u8) -> (res: PResult<<Ikev2PayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_next_payload_type().wf(next_pt@),

    ensures
        res matches Ok((n, v)) ==> spec_ikev2_payload(next_pt@).spec_parse(input@) == Some((n as int, v@)),
        spec_ikev2_payload(next_pt@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_ikev2_payload(next_pt@).spec_parse(input@) is None,
        spec_ikev2_payload(next_pt@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = ikev2_payload( next_pt );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_ikev2_payload<'a>(v: <Ikev2PayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, next_pt: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_ikev2_payload(next_pt@).wf(v@),
        spec_next_payload_type().wf(next_pt@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_ikev2_payload(next_pt@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_ikev2_payload(next_pt@).spec_serialize(v@))
        },
{
    let combinator = ikev2_payload( next_pt );
    combinator.serialize(v, data, pos)
}

pub fn ikev2_payload_len<'a>(v: <Ikev2PayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, next_pt: u8) -> (serialize_len: usize)
    requires
        spec_ikev2_payload(next_pt@).wf(v@),
        spec_ikev2_payload(next_pt@).spec_serialize(v@).len() <= usize::MAX,
        spec_next_payload_type().wf(next_pt@),

    ensures
        serialize_len == spec_ikev2_payload(next_pt@).spec_serialize(v@).len(),
{
    let combinator = ikev2_payload( next_pt );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct Ikev2PayloadCont0 {
    pub next_pt: u8,
}
type Ikev2PayloadCont0Type<'a, 'b> = &'b GenericPayloadHeader;
type Ikev2PayloadCont0SType<'a, 'x> = &'x GenericPayloadHeader;
type Ikev2PayloadCont0Input<'a, 'b, 'x> = POrSType<Ikev2PayloadCont0Type<'a, 'b>, Ikev2PayloadCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Ikev2PayloadCont0Input<'a, 'b, 'x>> for Ikev2PayloadCont0 {
    type Output = AndThen<bytes::Variable, Ikev2PayloadBodyCombinator>;

    open spec fn requires(&self, deps: Ikev2PayloadCont0Input<'a, 'b, 'x>) -> bool {        let next_pt = self.next_pt@;

        &&& spec_next_payload_type().wf(self.next_pt@)
        &&& (spec_generic_payload_header()).wf(deps@)
        }

    open spec fn ensures(&self, deps: Ikev2PayloadCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ikev2_payload_cont0(self.next_pt@, deps@)
    }

    fn apply(&self, deps: Ikev2PayloadCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let hdr = deps;
                let next_pt = self.next_pt;
                AndThen(bytes::Variable(((usize::ex_from(hdr.payload_length) - 4)) as usize), ikev2_payload_body(next_pt))
            }
            POrSType::S(deps) => {
                let hdr = deps;
                let next_pt = self.next_pt;
                AndThen(bytes::Variable(((usize::ex_from(hdr.payload_length) - 4)) as usize), ikev2_payload_body(next_pt))
            }
        }
    }
}

}
