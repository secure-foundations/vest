
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

pub type EarlyDataIndicationNewSessionTicketInnerRef<'a> = &'a u32;
impl<'a> From<&'a EarlyDataIndicationNewSessionTicket> for EarlyDataIndicationNewSessionTicketInnerRef<'a> {
    fn ex_from(m: &'a EarlyDataIndicationNewSessionTicket) -> EarlyDataIndicationNewSessionTicketInnerRef<'a> {
        &m.max_early_data_size
    }
}

impl From<EarlyDataIndicationNewSessionTicketInner> for EarlyDataIndicationNewSessionTicket {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketInner) -> EarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        EarlyDataIndicationNewSessionTicket { max_early_data_size }
    }
}

pub struct EarlyDataIndicationNewSessionTicketMapper;
impl View for EarlyDataIndicationNewSessionTicketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EarlyDataIndicationNewSessionTicketMapper {
    type Src = SpecEarlyDataIndicationNewSessionTicketInner;
    type Dst = SpecEarlyDataIndicationNewSessionTicket;
}
impl SpecIsoProof for EarlyDataIndicationNewSessionTicketMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EarlyDataIndicationNewSessionTicketMapper {
    type Src = EarlyDataIndicationNewSessionTicketInner;
    type Dst = EarlyDataIndicationNewSessionTicket;
    type RefSrc = EarlyDataIndicationNewSessionTicketInnerRef<'a>;
}

pub struct SpecEarlyDataIndicationNewSessionTicketCombinator(SpecEarlyDataIndicationNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    type Type = SpecEarlyDataIndicationNewSessionTicket;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEarlyDataIndicationNewSessionTicketCombinatorAlias::is_prefix_secure() }
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
pub type SpecEarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;

pub struct EarlyDataIndicationNewSessionTicketCombinator(EarlyDataIndicationNewSessionTicketCombinatorAlias);

impl View for EarlyDataIndicationNewSessionTicketCombinator {
    type V = SpecEarlyDataIndicationNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecEarlyDataIndicationNewSessionTicketCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EarlyDataIndicationNewSessionTicketCombinator {
    type Type = EarlyDataIndicationNewSessionTicket;
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
pub type EarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;


pub closed spec fn spec_early_data_indication_new_session_ticket() -> SpecEarlyDataIndicationNewSessionTicketCombinator {
    SpecEarlyDataIndicationNewSessionTicketCombinator(
    Mapped {
        inner: U32Be,
        mapper: EarlyDataIndicationNewSessionTicketMapper,
    })
}

                
pub fn early_data_indication_new_session_ticket() -> (o: EarlyDataIndicationNewSessionTicketCombinator)
    ensures o@ == spec_early_data_indication_new_session_ticket(),
{
    EarlyDataIndicationNewSessionTicketCombinator(
    Mapped {
        inner: U32Be,
        mapper: EarlyDataIndicationNewSessionTicketMapper,
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

pub type NewSessionTicketExtensionExtensionDataInnerRef<'a> = Either<&'a EarlyDataIndicationNewSessionTicket, &'a &'a [u8]>;


impl<'a> View for NewSessionTicketExtensionExtensionData<'a> {
    type V = SpecNewSessionTicketExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            NewSessionTicketExtensionExtensionData::EarlyData(m) => SpecNewSessionTicketExtensionExtensionData::EarlyData(m@),
            NewSessionTicketExtensionExtensionData::Unrecognized(m) => SpecNewSessionTicketExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a NewSessionTicketExtensionExtensionData<'a>> for NewSessionTicketExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a NewSessionTicketExtensionExtensionData<'a>) -> NewSessionTicketExtensionExtensionDataInnerRef<'a> {
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


pub struct NewSessionTicketExtensionExtensionDataMapper;
impl View for NewSessionTicketExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionExtensionDataMapper {
    type Src = SpecNewSessionTicketExtensionExtensionDataInner;
    type Dst = SpecNewSessionTicketExtensionExtensionData;
}
impl SpecIsoProof for NewSessionTicketExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NewSessionTicketExtensionExtensionDataMapper {
    type Src = NewSessionTicketExtensionExtensionDataInner<'a>;
    type Dst = NewSessionTicketExtensionExtensionData<'a>;
    type RefSrc = NewSessionTicketExtensionExtensionDataInnerRef<'a>;
}

type SpecNewSessionTicketExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecEarlyDataIndicationNewSessionTicketCombinator>, Cond<bytes::Variable>>;
pub struct SpecNewSessionTicketExtensionExtensionDataCombinator(SpecNewSessionTicketExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionExtensionDataCombinator {
    type Type = SpecNewSessionTicketExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecNewSessionTicketExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecNewSessionTicketExtensionExtensionDataCombinatorAlias1, NewSessionTicketExtensionExtensionDataMapper>>;
type NewSessionTicketExtensionExtensionDataCombinatorAlias1 = Choice<Cond<EarlyDataIndicationNewSessionTicketCombinator>, Cond<bytes::Variable>>;
struct NewSessionTicketExtensionExtensionDataCombinator1(NewSessionTicketExtensionExtensionDataCombinatorAlias1);
impl View for NewSessionTicketExtensionExtensionDataCombinator1 {
    type V = SpecNewSessionTicketExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NewSessionTicketExtensionExtensionDataCombinator1, NewSessionTicketExtensionExtensionDataCombinatorAlias1);

pub struct NewSessionTicketExtensionExtensionDataCombinator(NewSessionTicketExtensionExtensionDataCombinatorAlias);

impl View for NewSessionTicketExtensionExtensionDataCombinator {
    type V = SpecNewSessionTicketExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NewSessionTicketExtensionExtensionDataCombinator {
    type Type = NewSessionTicketExtensionExtensionData<'a>;
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
pub type NewSessionTicketExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<NewSessionTicketExtensionExtensionDataCombinator1, NewSessionTicketExtensionExtensionDataMapper>>;


pub closed spec fn spec_new_session_ticket_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecNewSessionTicketExtensionExtensionDataCombinator {
    SpecNewSessionTicketExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 42, inner: spec_early_data_indication_new_session_ticket() }, Cond { cond: !(extension_type == 42), inner: bytes::Variable(ext_len.spec_into()) }), mapper: NewSessionTicketExtensionExtensionDataMapper }))
}

pub fn new_session_ticket_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: NewSessionTicketExtensionExtensionDataCombinator)
    ensures o@ == spec_new_session_ticket_extension_extension_data(ext_len@, extension_type@),
{
    NewSessionTicketExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: NewSessionTicketExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 42, inner: early_data_indication_new_session_ticket() }, Cond { cond: !(extension_type == 42), inner: bytes::Variable(ext_len.ex_into()) })), mapper: NewSessionTicketExtensionExtensionDataMapper }))
}


pub struct SpecOpaque1Ffff {
    pub l: u16,
    pub data: Seq<u8>,
}

pub type SpecOpaque1FfffInner = (u16, Seq<u8>);


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
    pub l: u16,
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
pub type Opaque1FfffInner<'a> = (u16, &'a [u8]);

pub type Opaque1FfffInnerRef<'a> = (&'a u16, &'a &'a [u8]);
impl<'a> From<&'a Opaque1Ffff<'a>> for Opaque1FfffInnerRef<'a> {
    fn ex_from(m: &'a Opaque1Ffff) -> Opaque1FfffInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque1FfffInner<'a>> for Opaque1Ffff<'a> {
    fn ex_from(m: Opaque1FfffInner) -> Opaque1Ffff {
        let (l, data) = m;
        Opaque1Ffff { l, data }
    }
}

pub struct Opaque1FfffMapper;
impl View for Opaque1FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffMapper {
    type Src = SpecOpaque1FfffInner;
    type Dst = SpecOpaque1Ffff;
}
impl SpecIsoProof for Opaque1FfffMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque1FfffMapper {
    type Src = Opaque1FfffInner<'a>;
    type Dst = Opaque1Ffff<'a>;
    type RefSrc = Opaque1FfffInnerRef<'a>;
}

pub struct SpecOpaque1FfffCombinator(SpecOpaque1FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffCombinator {
    type Type = SpecOpaque1Ffff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque1FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque1FfffCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate17626095872143391426>, bytes::Variable>, Opaque1FfffMapper>;
pub struct Predicate17626095872143391426;
impl View for Predicate17626095872143391426 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate17626095872143391426 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate17626095872143391426 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}

pub struct Opaque1FfffCombinator(Opaque1FfffCombinatorAlias);

impl View for Opaque1FfffCombinator {
    type V = SpecOpaque1FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque1FfffCombinator {
    type Type = Opaque1Ffff<'a>;
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
pub type Opaque1FfffCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate17626095872143391426>, bytes::Variable, Opaque1FfffCont0>, Opaque1FfffMapper>;


pub closed spec fn spec_opaque_1_ffff() -> SpecOpaque1FfffCombinator {
    SpecOpaque1FfffCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate17626095872143391426 }, |deps| spec_opaque1_ffff_cont0(deps)),
        mapper: Opaque1FfffMapper,
    })
}

pub open spec fn spec_opaque1_ffff_cont0(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque1FfffCont0 {
    type V = spec_fn(u16) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_opaque1_ffff_cont0(deps)
        }
    }
}

                
pub fn opaque_1_ffff() -> (o: Opaque1FfffCombinator)
    ensures o@ == spec_opaque_1_ffff(),
{
    Opaque1FfffCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate17626095872143391426 }, Opaque1FfffCont0),
        mapper: Opaque1FfffMapper,
    })
}

pub struct Opaque1FfffCont0;
type Opaque1FfffCont0Type<'a, 'b> = &'b u16;
type Opaque1FfffCont0SType<'a, 'x> = &'x u16;
type Opaque1FfffCont0Input<'a, 'b, 'x> = POrSType<Opaque1FfffCont0Type<'a, 'b>, Opaque1FfffCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque1FfffCont0Input<'a, 'b, 'x>> for Opaque1FfffCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque1FfffCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque1FfffCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque1FfffCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                
pub type SpecResponderId = SpecOpaque1Ffff;
pub type ResponderId<'a> = Opaque1Ffff<'a>;
pub type ResponderIdRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type Type = SpecResponderId;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecResponderIdCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct ResponderIdCombinator(ResponderIdCombinatorAlias);

impl View for ResponderIdCombinator {
    type V = SpecResponderIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdCombinator {
    type Type = ResponderId<'a>;
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
pub type ResponderIdCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_1_ffff())
}

                
pub fn responder_id() -> (o: ResponderIdCombinator)
    ensures o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_1_ffff())
}

                

pub struct SpecResponderIdList {
    pub l: u16,
    pub list: Seq<SpecResponderId>,
}

pub type SpecResponderIdListInner = (u16, Seq<SpecResponderId>);


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
    pub list: RepeatResult<ResponderId<'a>>,
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
pub type ResponderIdListInner<'a> = (u16, RepeatResult<ResponderId<'a>>);

pub type ResponderIdListInnerRef<'a> = (&'a u16, &'a RepeatResult<ResponderId<'a>>);
impl<'a> From<&'a ResponderIdList<'a>> for ResponderIdListInnerRef<'a> {
    fn ex_from(m: &'a ResponderIdList) -> ResponderIdListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner) -> ResponderIdList {
        let (l, list) = m;
        ResponderIdList { l, list }
    }
}

pub struct ResponderIdListMapper;
impl View for ResponderIdListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResponderIdListMapper {
    type Src = SpecResponderIdListInner;
    type Dst = SpecResponderIdList;
}
impl SpecIsoProof for ResponderIdListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ResponderIdListMapper {
    type Src = ResponderIdListInner<'a>;
    type Dst = ResponderIdList<'a>;
    type RefSrc = ResponderIdListInnerRef<'a>;
}

pub struct SpecResponderIdListCombinator(SpecResponderIdListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListCombinator {
    type Type = SpecResponderIdList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListCombinatorAlias::is_prefix_secure() }
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
pub type SpecResponderIdListCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>>>, ResponderIdListMapper>;

pub struct ResponderIdListCombinator(ResponderIdListCombinatorAlias);

impl View for ResponderIdListCombinator {
    type V = SpecResponderIdListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResponderIdListCombinator {
    type Type = ResponderIdList<'a>;
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
pub type ResponderIdListCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<ResponderIdCombinator>>, ResponderIdListCont0>, ResponderIdListMapper>;


pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_responder_id_list_cont0(deps)),
        mapper: ResponderIdListMapper,
    })
}

pub open spec fn spec_responder_id_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_responder_id()))
}

impl View for ResponderIdListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecResponderIdCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_responder_id_list_cont0(deps)
        }
    }
}

                
pub fn responder_id_list() -> (o: ResponderIdListCombinator)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Pair::new(U16Be, ResponderIdListCont0),
        mapper: ResponderIdListMapper,
    })
}

pub struct ResponderIdListCont0;
type ResponderIdListCont0Type<'a, 'b> = &'b u16;
type ResponderIdListCont0SType<'a, 'x> = &'x u16;
type ResponderIdListCont0Input<'a, 'b, 'x> = POrSType<ResponderIdListCont0Type<'a, 'b>, ResponderIdListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ResponderIdListCont0Input<'a, 'b, 'x>> for ResponderIdListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ResponderIdCombinator>>;

    open spec fn requires(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont0(deps@)
    }

    fn apply(&self, deps: ResponderIdListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(responder_id()))
            }
        }
    }
}
                

pub struct SpecOpaque0Ffff {
    pub l: u16,
    pub data: Seq<u8>,
}

pub type SpecOpaque0FfffInner = (u16, Seq<u8>);


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
    pub l: u16,
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
pub type Opaque0FfffInner<'a> = (u16, &'a [u8]);

pub type Opaque0FfffInnerRef<'a> = (&'a u16, &'a &'a [u8]);
impl<'a> From<&'a Opaque0Ffff<'a>> for Opaque0FfffInnerRef<'a> {
    fn ex_from(m: &'a Opaque0Ffff) -> Opaque0FfffInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque0FfffInner<'a>> for Opaque0Ffff<'a> {
    fn ex_from(m: Opaque0FfffInner) -> Opaque0Ffff {
        let (l, data) = m;
        Opaque0Ffff { l, data }
    }
}

pub struct Opaque0FfffMapper;
impl View for Opaque0FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffMapper {
    type Src = SpecOpaque0FfffInner;
    type Dst = SpecOpaque0Ffff;
}
impl SpecIsoProof for Opaque0FfffMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque0FfffMapper {
    type Src = Opaque0FfffInner<'a>;
    type Dst = Opaque0Ffff<'a>;
    type RefSrc = Opaque0FfffInnerRef<'a>;
}

pub struct SpecOpaque0FfffCombinator(SpecOpaque0FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffCombinator {
    type Type = SpecOpaque0Ffff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque0FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque0FfffCombinatorAlias = Mapped<SpecPair<U16Be, bytes::Variable>, Opaque0FfffMapper>;

pub struct Opaque0FfffCombinator(Opaque0FfffCombinatorAlias);

impl View for Opaque0FfffCombinator {
    type V = SpecOpaque0FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque0FfffCombinator {
    type Type = Opaque0Ffff<'a>;
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
pub type Opaque0FfffCombinatorAlias = Mapped<Pair<U16Be, bytes::Variable, Opaque0FfffCont0>, Opaque0FfffMapper>;


pub closed spec fn spec_opaque_0_ffff() -> SpecOpaque0FfffCombinator {
    SpecOpaque0FfffCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_opaque0_ffff_cont0(deps)),
        mapper: Opaque0FfffMapper,
    })
}

pub open spec fn spec_opaque0_ffff_cont0(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque0FfffCont0 {
    type V = spec_fn(u16) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_opaque0_ffff_cont0(deps)
        }
    }
}

                
pub fn opaque_0_ffff() -> (o: Opaque0FfffCombinator)
    ensures o@ == spec_opaque_0_ffff(),
{
    Opaque0FfffCombinator(
    Mapped {
        inner: Pair::new(U16Be, Opaque0FfffCont0),
        mapper: Opaque0FfffMapper,
    })
}

pub struct Opaque0FfffCont0;
type Opaque0FfffCont0Type<'a, 'b> = &'b u16;
type Opaque0FfffCont0SType<'a, 'x> = &'x u16;
type Opaque0FfffCont0Input<'a, 'b, 'x> = POrSType<Opaque0FfffCont0Type<'a, 'b>, Opaque0FfffCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque0FfffCont0Input<'a, 'b, 'x>> for Opaque0FfffCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque0FfffCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque0FfffCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque0FfffCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                
pub type SpecOcspExtensions = SpecOpaque0Ffff;
pub type OcspExtensions<'a> = Opaque0Ffff<'a>;
pub type OcspExtensionsRef<'a> = &'a Opaque0Ffff<'a>;


pub struct SpecOcspExtensionsCombinator(SpecOcspExtensionsCombinatorAlias);

impl SpecCombinator for SpecOcspExtensionsCombinator {
    type Type = SpecOcspExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOcspExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecOcspExtensionsCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct OcspExtensionsCombinator(OcspExtensionsCombinatorAlias);

impl View for OcspExtensionsCombinator {
    type V = SpecOcspExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OcspExtensionsCombinator {
    type Type = OcspExtensions<'a>;
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
pub type OcspExtensionsCombinatorAlias = Opaque0FfffCombinator;


pub closed spec fn spec_ocsp_extensions() -> SpecOcspExtensionsCombinator {
    SpecOcspExtensionsCombinator(spec_opaque_0_ffff())
}

                
pub fn ocsp_extensions() -> (o: OcspExtensionsCombinator)
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

pub type OscpStatusRequestInnerRef<'a> = (&'a ResponderIdList<'a>, &'a OcspExtensions<'a>);
impl<'a> From<&'a OscpStatusRequest<'a>> for OscpStatusRequestInnerRef<'a> {
    fn ex_from(m: &'a OscpStatusRequest) -> OscpStatusRequestInnerRef<'a> {
        (&m.responder_id_list, &m.extensions)
    }
}

impl<'a> From<OscpStatusRequestInner<'a>> for OscpStatusRequest<'a> {
    fn ex_from(m: OscpStatusRequestInner) -> OscpStatusRequest {
        let (responder_id_list, extensions) = m;
        OscpStatusRequest { responder_id_list, extensions }
    }
}

pub struct OscpStatusRequestMapper;
impl View for OscpStatusRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OscpStatusRequestMapper {
    type Src = SpecOscpStatusRequestInner;
    type Dst = SpecOscpStatusRequest;
}
impl SpecIsoProof for OscpStatusRequestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OscpStatusRequestMapper {
    type Src = OscpStatusRequestInner<'a>;
    type Dst = OscpStatusRequest<'a>;
    type RefSrc = OscpStatusRequestInnerRef<'a>;
}
type SpecOscpStatusRequestCombinatorAlias1 = (SpecResponderIdListCombinator, SpecOcspExtensionsCombinator);
pub struct SpecOscpStatusRequestCombinator(SpecOscpStatusRequestCombinatorAlias);

impl SpecCombinator for SpecOscpStatusRequestCombinator {
    type Type = SpecOscpStatusRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOscpStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOscpStatusRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecOscpStatusRequestCombinatorAlias = Mapped<SpecOscpStatusRequestCombinatorAlias1, OscpStatusRequestMapper>;
type OscpStatusRequestCombinatorAlias1 = (ResponderIdListCombinator, OcspExtensionsCombinator);
struct OscpStatusRequestCombinator1(OscpStatusRequestCombinatorAlias1);
impl View for OscpStatusRequestCombinator1 {
    type V = SpecOscpStatusRequestCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(OscpStatusRequestCombinator1, OscpStatusRequestCombinatorAlias1);

pub struct OscpStatusRequestCombinator(OscpStatusRequestCombinatorAlias);

impl View for OscpStatusRequestCombinator {
    type V = SpecOscpStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecOscpStatusRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OscpStatusRequestCombinator {
    type Type = OscpStatusRequest<'a>;
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
pub type OscpStatusRequestCombinatorAlias = Mapped<OscpStatusRequestCombinator1, OscpStatusRequestMapper>;


pub closed spec fn spec_oscp_status_request() -> SpecOscpStatusRequestCombinator {
    SpecOscpStatusRequestCombinator(
    Mapped {
        inner: (spec_responder_id_list(), spec_ocsp_extensions()),
        mapper: OscpStatusRequestMapper,
    })
}

                
pub fn oscp_status_request() -> (o: OscpStatusRequestCombinator)
    ensures o@ == spec_oscp_status_request(),
{
    OscpStatusRequestCombinator(
    Mapped {
        inner: OscpStatusRequestCombinator1((responder_id_list(), ocsp_extensions())),
        mapper: OscpStatusRequestMapper,
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

pub type CertificateStatusRequestInnerRef<'a> = (&'a u8, &'a OscpStatusRequest<'a>);
impl<'a> From<&'a CertificateStatusRequest<'a>> for CertificateStatusRequestInnerRef<'a> {
    fn ex_from(m: &'a CertificateStatusRequest) -> CertificateStatusRequestInnerRef<'a> {
        (&m.status_type, &m.request)
    }
}

impl<'a> From<CertificateStatusRequestInner<'a>> for CertificateStatusRequest<'a> {
    fn ex_from(m: CertificateStatusRequestInner) -> CertificateStatusRequest {
        let (status_type, request) = m;
        CertificateStatusRequest { status_type, request }
    }
}

pub struct CertificateStatusRequestMapper;
impl View for CertificateStatusRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusRequestMapper {
    type Src = SpecCertificateStatusRequestInner;
    type Dst = SpecCertificateStatusRequest;
}
impl SpecIsoProof for CertificateStatusRequestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateStatusRequestMapper {
    type Src = CertificateStatusRequestInner<'a>;
    type Dst = CertificateStatusRequest<'a>;
    type RefSrc = CertificateStatusRequestInnerRef<'a>;
}
pub const CERTIFICATESTATUSREQUESTSTATUS_TYPE_CONST: u8 = 1;
type SpecCertificateStatusRequestCombinatorAlias1 = (Refined<U8, TagPred<u8>>, SpecOscpStatusRequestCombinator);
pub struct SpecCertificateStatusRequestCombinator(SpecCertificateStatusRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusRequestCombinator {
    type Type = SpecCertificateStatusRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateStatusRequestCombinatorAlias = Mapped<SpecCertificateStatusRequestCombinatorAlias1, CertificateStatusRequestMapper>;
type CertificateStatusRequestCombinatorAlias1 = (Refined<U8, TagPred<u8>>, OscpStatusRequestCombinator);
struct CertificateStatusRequestCombinator1(CertificateStatusRequestCombinatorAlias1);
impl View for CertificateStatusRequestCombinator1 {
    type V = SpecCertificateStatusRequestCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateStatusRequestCombinator1, CertificateStatusRequestCombinatorAlias1);

pub struct CertificateStatusRequestCombinator(CertificateStatusRequestCombinatorAlias);

impl View for CertificateStatusRequestCombinator {
    type V = SpecCertificateStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateStatusRequestCombinator {
    type Type = CertificateStatusRequest<'a>;
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
pub type CertificateStatusRequestCombinatorAlias = Mapped<CertificateStatusRequestCombinator1, CertificateStatusRequestMapper>;


pub closed spec fn spec_certificate_status_request() -> SpecCertificateStatusRequestCombinator {
    SpecCertificateStatusRequestCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUESTSTATUS_TYPE_CONST) }, spec_oscp_status_request()),
        mapper: CertificateStatusRequestMapper,
    })
}

                
pub fn certificate_status_request() -> (o: CertificateStatusRequestCombinator)
    ensures o@ == spec_certificate_status_request(),
{
    CertificateStatusRequestCombinator(
    Mapped {
        inner: CertificateStatusRequestCombinator1((Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUESTSTATUS_TYPE_CONST) }, oscp_status_request())),
        mapper: CertificateStatusRequestMapper,
    })
}

                
pub type SpecSignatureScheme = u16;
pub type SignatureScheme = u16;
pub type SignatureSchemeRef<'a> = &'a u16;


pub struct SpecSignatureSchemeCombinator(SpecSignatureSchemeCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeCombinator {
    type Type = SpecSignatureScheme;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSignatureSchemeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeCombinatorAlias::is_prefix_secure() }
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
pub type SpecSignatureSchemeCombinatorAlias = U16Be;

pub struct SignatureSchemeCombinator(SignatureSchemeCombinatorAlias);

impl View for SignatureSchemeCombinator {
    type V = SpecSignatureSchemeCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SignatureSchemeCombinator {
    type Type = SignatureScheme;
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
pub type SignatureSchemeCombinatorAlias = U16Be;


pub closed spec fn spec_signature_scheme() -> SpecSignatureSchemeCombinator {
    SpecSignatureSchemeCombinator(U16Be)
}

                
pub fn signature_scheme() -> (o: SignatureSchemeCombinator)
    ensures o@ == spec_signature_scheme(),
{
    SignatureSchemeCombinator(U16Be)
}

                
pub type SpecSrtpProtectionProfile = Seq<u8>;
pub type SrtpProtectionProfile<'a> = &'a [u8];
pub type SrtpProtectionProfileRef<'a> = &'a &'a [u8];


pub struct SpecSrtpProtectionProfileCombinator(SpecSrtpProtectionProfileCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfileCombinator {
    type Type = SpecSrtpProtectionProfile;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSrtpProtectionProfileCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfileCombinatorAlias::is_prefix_secure() }
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
pub type SpecSrtpProtectionProfileCombinatorAlias = bytes::Fixed<2>;

pub struct SrtpProtectionProfileCombinator(SrtpProtectionProfileCombinatorAlias);

impl View for SrtpProtectionProfileCombinator {
    type V = SpecSrtpProtectionProfileCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfileCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SrtpProtectionProfileCombinator {
    type Type = SrtpProtectionProfile<'a>;
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
pub type SrtpProtectionProfileCombinatorAlias = bytes::Fixed<2>;


pub closed spec fn spec_srtp_protection_profile() -> SpecSrtpProtectionProfileCombinator {
    SpecSrtpProtectionProfileCombinator(bytes::Fixed::<2>)
}

                
pub fn srtp_protection_profile() -> (o: SrtpProtectionProfileCombinator)
    ensures o@ == spec_srtp_protection_profile(),
{
    SrtpProtectionProfileCombinator(bytes::Fixed::<2>)
}

                
pub type SpecProtocolVersion = u16;
pub type ProtocolVersion = u16;
pub type ProtocolVersionRef<'a> = &'a u16;


pub struct SpecProtocolVersionCombinator(SpecProtocolVersionCombinatorAlias);

impl SpecCombinator for SpecProtocolVersionCombinator {
    type Type = SpecProtocolVersion;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProtocolVersionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolVersionCombinatorAlias::is_prefix_secure() }
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
pub type SpecProtocolVersionCombinatorAlias = U16Be;

pub struct ProtocolVersionCombinator(ProtocolVersionCombinatorAlias);

impl View for ProtocolVersionCombinator {
    type V = SpecProtocolVersionCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolVersionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProtocolVersionCombinator {
    type Type = ProtocolVersion;
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
pub type ProtocolVersionCombinatorAlias = U16Be;


pub closed spec fn spec_protocol_version() -> SpecProtocolVersionCombinator {
    SpecProtocolVersionCombinator(U16Be)
}

                
pub fn protocol_version() -> (o: ProtocolVersionCombinator)
    ensures o@ == spec_protocol_version(),
{
    ProtocolVersionCombinator(U16Be)
}

                

pub struct SpecSupportedVersionsClient {
    pub l: u8,
    pub list: Seq<SpecProtocolVersion>,
}

pub type SpecSupportedVersionsClientInner = (u8, Seq<SpecProtocolVersion>);


impl SpecFrom<SpecSupportedVersionsClient> for SpecSupportedVersionsClientInner {
    open spec fn spec_from(m: SpecSupportedVersionsClient) -> SpecSupportedVersionsClientInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecSupportedVersionsClientInner> for SpecSupportedVersionsClient {
    open spec fn spec_from(m: SpecSupportedVersionsClientInner) -> SpecSupportedVersionsClient {
        let (l, list) = m;
        SpecSupportedVersionsClient { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SupportedVersionsClient {
    pub l: u8,
    pub list: RepeatResult<ProtocolVersion>,
}

impl View for SupportedVersionsClient {
    type V = SpecSupportedVersionsClient;

    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsClient {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type SupportedVersionsClientInner = (u8, RepeatResult<ProtocolVersion>);

pub type SupportedVersionsClientInnerRef<'a> = (&'a u8, &'a RepeatResult<ProtocolVersion>);
impl<'a> From<&'a SupportedVersionsClient> for SupportedVersionsClientInnerRef<'a> {
    fn ex_from(m: &'a SupportedVersionsClient) -> SupportedVersionsClientInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<SupportedVersionsClientInner> for SupportedVersionsClient {
    fn ex_from(m: SupportedVersionsClientInner) -> SupportedVersionsClient {
        let (l, list) = m;
        SupportedVersionsClient { l, list }
    }
}

pub struct SupportedVersionsClientMapper;
impl View for SupportedVersionsClientMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SupportedVersionsClientMapper {
    type Src = SpecSupportedVersionsClientInner;
    type Dst = SpecSupportedVersionsClient;
}
impl SpecIsoProof for SupportedVersionsClientMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SupportedVersionsClientMapper {
    type Src = SupportedVersionsClientInner;
    type Dst = SupportedVersionsClient;
    type RefSrc = SupportedVersionsClientInnerRef<'a>;
}

pub struct SpecSupportedVersionsClientCombinator(SpecSupportedVersionsClientCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsClientCombinator {
    type Type = SpecSupportedVersionsClient;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSupportedVersionsClientCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsClientCombinatorAlias::is_prefix_secure() }
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
pub type SpecSupportedVersionsClientCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate7470776374180795781>, AndThen<bytes::Variable, Repeat<SpecProtocolVersionCombinator>>>, SupportedVersionsClientMapper>;
pub struct Predicate7470776374180795781;
impl View for Predicate7470776374180795781 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7470776374180795781 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 2 && i <= 254)
    }
}
impl SpecPred<u8> for Predicate7470776374180795781 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 2 && i <= 254)
    }
}

pub struct SupportedVersionsClientCombinator(SupportedVersionsClientCombinatorAlias);

impl View for SupportedVersionsClientCombinator {
    type V = SpecSupportedVersionsClientCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsClientCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SupportedVersionsClientCombinator {
    type Type = SupportedVersionsClient;
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
pub type SupportedVersionsClientCombinatorAlias = Mapped<Pair<Refined<U8, Predicate7470776374180795781>, AndThen<bytes::Variable, Repeat<ProtocolVersionCombinator>>, SupportedVersionsClientCont0>, SupportedVersionsClientMapper>;


pub closed spec fn spec_supported_versions_client() -> SpecSupportedVersionsClientCombinator {
    SpecSupportedVersionsClientCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate7470776374180795781 }, |deps| spec_supported_versions_client_cont0(deps)),
        mapper: SupportedVersionsClientMapper,
    })
}

pub open spec fn spec_supported_versions_client_cont0(deps: u8) -> AndThen<bytes::Variable, Repeat<SpecProtocolVersionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_protocol_version()))
}

impl View for SupportedVersionsClientCont0 {
    type V = spec_fn(u8) -> AndThen<bytes::Variable, Repeat<SpecProtocolVersionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_supported_versions_client_cont0(deps)
        }
    }
}

                
pub fn supported_versions_client() -> (o: SupportedVersionsClientCombinator)
    ensures o@ == spec_supported_versions_client(),
{
    SupportedVersionsClientCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate7470776374180795781 }, SupportedVersionsClientCont0),
        mapper: SupportedVersionsClientMapper,
    })
}

pub struct SupportedVersionsClientCont0;
type SupportedVersionsClientCont0Type<'a, 'b> = &'b u8;
type SupportedVersionsClientCont0SType<'a, 'x> = &'x u8;
type SupportedVersionsClientCont0Input<'a, 'b, 'x> = POrSType<SupportedVersionsClientCont0Type<'a, 'b>, SupportedVersionsClientCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SupportedVersionsClientCont0Input<'a, 'b, 'x>> for SupportedVersionsClientCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ProtocolVersionCombinator>>;

    open spec fn requires(&self, deps: SupportedVersionsClientCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SupportedVersionsClientCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_supported_versions_client_cont0(deps@)
    }

    fn apply(&self, deps: SupportedVersionsClientCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(protocol_version()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(protocol_version()))
            }
        }
    }
}
                

pub spec const SPEC_AlertLevel_Warning: u8 = 1;
pub spec const SPEC_AlertLevel_Fatal: u8 = 2;
pub exec static EXEC_AlertLevel_Warning: u8 ensures EXEC_AlertLevel_Warning == SPEC_AlertLevel_Warning { 1 }
pub exec static EXEC_AlertLevel_Fatal: u8 ensures EXEC_AlertLevel_Fatal == SPEC_AlertLevel_Fatal { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AlertLevel {
    Warning = 1,
Fatal = 2
}
pub type SpecAlertLevel = AlertLevel;

pub type AlertLevelInner = u8;

pub type AlertLevelInnerRef<'a> = &'a u8;

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
            AlertLevel::Warning => Ok(SPEC_AlertLevel_Warning),
            AlertLevel::Fatal => Ok(SPEC_AlertLevel_Fatal),
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

impl<'a> TryFrom<&'a AlertLevel> for AlertLevelInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AlertLevel) -> Result<AlertLevelInnerRef<'a>, ()> {
        match v {
            AlertLevel::Warning => Ok(&EXEC_AlertLevel_Warning),
            AlertLevel::Fatal => Ok(&EXEC_AlertLevel_Fatal),
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

impl SpecPartialIso for AlertLevelMapper {
    type Src = AlertLevelInner;
    type Dst = AlertLevel;
}

impl SpecPartialIsoProof for AlertLevelMapper {
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

impl<'a> PartialIso<'a> for AlertLevelMapper {
    type Src = AlertLevelInner;
    type Dst = AlertLevel;
    type RefSrc = AlertLevelInnerRef<'a>;
}


pub struct SpecAlertLevelCombinator(SpecAlertLevelCombinatorAlias);

impl SpecCombinator for SpecAlertLevelCombinator {
    type Type = SpecAlertLevel;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAlertLevelCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertLevelCombinatorAlias::is_prefix_secure() }
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
pub type SpecAlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;

pub struct AlertLevelCombinator(AlertLevelCombinatorAlias);

impl View for AlertLevelCombinator {
    type V = SpecAlertLevelCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertLevelCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AlertLevelCombinator {
    type Type = AlertLevel;
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
pub type AlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;


pub closed spec fn spec_alert_level() -> SpecAlertLevelCombinator {
    SpecAlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}

                
pub fn alert_level() -> (o: AlertLevelCombinator)
    ensures o@ == spec_alert_level(),
{
    AlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}

                

pub spec const SPEC_AlertDescription_CloseNotify: u8 = 0;
pub spec const SPEC_AlertDescription_UnexpectedMessage: u8 = 10;
pub spec const SPEC_AlertDescription_BadRecordMac: u8 = 20;
pub spec const SPEC_AlertDescription_RecordOverflow: u8 = 22;
pub spec const SPEC_AlertDescription_HandshakeFailure: u8 = 40;
pub spec const SPEC_AlertDescription_BadCertificate: u8 = 42;
pub spec const SPEC_AlertDescription_UnsupportedCertificate: u8 = 43;
pub spec const SPEC_AlertDescription_CertificateRevoked: u8 = 44;
pub spec const SPEC_AlertDescription_CertificateExpired: u8 = 45;
pub spec const SPEC_AlertDescription_CertificateUnknown: u8 = 46;
pub spec const SPEC_AlertDescription_IllegalParameter: u8 = 47;
pub spec const SPEC_AlertDescription_UnknownCA: u8 = 48;
pub spec const SPEC_AlertDescription_AccessDenied: u8 = 49;
pub spec const SPEC_AlertDescription_DecodeError: u8 = 50;
pub spec const SPEC_AlertDescription_DecryptError: u8 = 51;
pub spec const SPEC_AlertDescription_ProtocolVersion: u8 = 70;
pub spec const SPEC_AlertDescription_InsufficientSecurity: u8 = 71;
pub spec const SPEC_AlertDescription_InternalError: u8 = 80;
pub spec const SPEC_AlertDescription_InappropriateFallback: u8 = 86;
pub spec const SPEC_AlertDescription_UserCanceled: u8 = 90;
pub spec const SPEC_AlertDescription_MissingExtension: u8 = 109;
pub spec const SPEC_AlertDescription_UnsupportedExtension: u8 = 110;
pub spec const SPEC_AlertDescription_UnrecognizedName: u8 = 112;
pub spec const SPEC_AlertDescription_BadCertificateStatusResponse: u8 = 113;
pub spec const SPEC_AlertDescription_UnknownPSKIdentity: u8 = 115;
pub spec const SPEC_AlertDescription_CertificateRequired: u8 = 116;
pub spec const SPEC_AlertDescription_NoApplicationProtocol: u8 = 120;
pub exec static EXEC_AlertDescription_CloseNotify: u8 ensures EXEC_AlertDescription_CloseNotify == SPEC_AlertDescription_CloseNotify { 0 }
pub exec static EXEC_AlertDescription_UnexpectedMessage: u8 ensures EXEC_AlertDescription_UnexpectedMessage == SPEC_AlertDescription_UnexpectedMessage { 10 }
pub exec static EXEC_AlertDescription_BadRecordMac: u8 ensures EXEC_AlertDescription_BadRecordMac == SPEC_AlertDescription_BadRecordMac { 20 }
pub exec static EXEC_AlertDescription_RecordOverflow: u8 ensures EXEC_AlertDescription_RecordOverflow == SPEC_AlertDescription_RecordOverflow { 22 }
pub exec static EXEC_AlertDescription_HandshakeFailure: u8 ensures EXEC_AlertDescription_HandshakeFailure == SPEC_AlertDescription_HandshakeFailure { 40 }
pub exec static EXEC_AlertDescription_BadCertificate: u8 ensures EXEC_AlertDescription_BadCertificate == SPEC_AlertDescription_BadCertificate { 42 }
pub exec static EXEC_AlertDescription_UnsupportedCertificate: u8 ensures EXEC_AlertDescription_UnsupportedCertificate == SPEC_AlertDescription_UnsupportedCertificate { 43 }
pub exec static EXEC_AlertDescription_CertificateRevoked: u8 ensures EXEC_AlertDescription_CertificateRevoked == SPEC_AlertDescription_CertificateRevoked { 44 }
pub exec static EXEC_AlertDescription_CertificateExpired: u8 ensures EXEC_AlertDescription_CertificateExpired == SPEC_AlertDescription_CertificateExpired { 45 }
pub exec static EXEC_AlertDescription_CertificateUnknown: u8 ensures EXEC_AlertDescription_CertificateUnknown == SPEC_AlertDescription_CertificateUnknown { 46 }
pub exec static EXEC_AlertDescription_IllegalParameter: u8 ensures EXEC_AlertDescription_IllegalParameter == SPEC_AlertDescription_IllegalParameter { 47 }
pub exec static EXEC_AlertDescription_UnknownCA: u8 ensures EXEC_AlertDescription_UnknownCA == SPEC_AlertDescription_UnknownCA { 48 }
pub exec static EXEC_AlertDescription_AccessDenied: u8 ensures EXEC_AlertDescription_AccessDenied == SPEC_AlertDescription_AccessDenied { 49 }
pub exec static EXEC_AlertDescription_DecodeError: u8 ensures EXEC_AlertDescription_DecodeError == SPEC_AlertDescription_DecodeError { 50 }
pub exec static EXEC_AlertDescription_DecryptError: u8 ensures EXEC_AlertDescription_DecryptError == SPEC_AlertDescription_DecryptError { 51 }
pub exec static EXEC_AlertDescription_ProtocolVersion: u8 ensures EXEC_AlertDescription_ProtocolVersion == SPEC_AlertDescription_ProtocolVersion { 70 }
pub exec static EXEC_AlertDescription_InsufficientSecurity: u8 ensures EXEC_AlertDescription_InsufficientSecurity == SPEC_AlertDescription_InsufficientSecurity { 71 }
pub exec static EXEC_AlertDescription_InternalError: u8 ensures EXEC_AlertDescription_InternalError == SPEC_AlertDescription_InternalError { 80 }
pub exec static EXEC_AlertDescription_InappropriateFallback: u8 ensures EXEC_AlertDescription_InappropriateFallback == SPEC_AlertDescription_InappropriateFallback { 86 }
pub exec static EXEC_AlertDescription_UserCanceled: u8 ensures EXEC_AlertDescription_UserCanceled == SPEC_AlertDescription_UserCanceled { 90 }
pub exec static EXEC_AlertDescription_MissingExtension: u8 ensures EXEC_AlertDescription_MissingExtension == SPEC_AlertDescription_MissingExtension { 109 }
pub exec static EXEC_AlertDescription_UnsupportedExtension: u8 ensures EXEC_AlertDescription_UnsupportedExtension == SPEC_AlertDescription_UnsupportedExtension { 110 }
pub exec static EXEC_AlertDescription_UnrecognizedName: u8 ensures EXEC_AlertDescription_UnrecognizedName == SPEC_AlertDescription_UnrecognizedName { 112 }
pub exec static EXEC_AlertDescription_BadCertificateStatusResponse: u8 ensures EXEC_AlertDescription_BadCertificateStatusResponse == SPEC_AlertDescription_BadCertificateStatusResponse { 113 }
pub exec static EXEC_AlertDescription_UnknownPSKIdentity: u8 ensures EXEC_AlertDescription_UnknownPSKIdentity == SPEC_AlertDescription_UnknownPSKIdentity { 115 }
pub exec static EXEC_AlertDescription_CertificateRequired: u8 ensures EXEC_AlertDescription_CertificateRequired == SPEC_AlertDescription_CertificateRequired { 116 }
pub exec static EXEC_AlertDescription_NoApplicationProtocol: u8 ensures EXEC_AlertDescription_NoApplicationProtocol == SPEC_AlertDescription_NoApplicationProtocol { 120 }

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

pub type AlertDescriptionInnerRef<'a> = &'a u8;

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
            AlertDescription::CloseNotify => Ok(SPEC_AlertDescription_CloseNotify),
            AlertDescription::UnexpectedMessage => Ok(SPEC_AlertDescription_UnexpectedMessage),
            AlertDescription::BadRecordMac => Ok(SPEC_AlertDescription_BadRecordMac),
            AlertDescription::RecordOverflow => Ok(SPEC_AlertDescription_RecordOverflow),
            AlertDescription::HandshakeFailure => Ok(SPEC_AlertDescription_HandshakeFailure),
            AlertDescription::BadCertificate => Ok(SPEC_AlertDescription_BadCertificate),
            AlertDescription::UnsupportedCertificate => Ok(SPEC_AlertDescription_UnsupportedCertificate),
            AlertDescription::CertificateRevoked => Ok(SPEC_AlertDescription_CertificateRevoked),
            AlertDescription::CertificateExpired => Ok(SPEC_AlertDescription_CertificateExpired),
            AlertDescription::CertificateUnknown => Ok(SPEC_AlertDescription_CertificateUnknown),
            AlertDescription::IllegalParameter => Ok(SPEC_AlertDescription_IllegalParameter),
            AlertDescription::UnknownCA => Ok(SPEC_AlertDescription_UnknownCA),
            AlertDescription::AccessDenied => Ok(SPEC_AlertDescription_AccessDenied),
            AlertDescription::DecodeError => Ok(SPEC_AlertDescription_DecodeError),
            AlertDescription::DecryptError => Ok(SPEC_AlertDescription_DecryptError),
            AlertDescription::ProtocolVersion => Ok(SPEC_AlertDescription_ProtocolVersion),
            AlertDescription::InsufficientSecurity => Ok(SPEC_AlertDescription_InsufficientSecurity),
            AlertDescription::InternalError => Ok(SPEC_AlertDescription_InternalError),
            AlertDescription::InappropriateFallback => Ok(SPEC_AlertDescription_InappropriateFallback),
            AlertDescription::UserCanceled => Ok(SPEC_AlertDescription_UserCanceled),
            AlertDescription::MissingExtension => Ok(SPEC_AlertDescription_MissingExtension),
            AlertDescription::UnsupportedExtension => Ok(SPEC_AlertDescription_UnsupportedExtension),
            AlertDescription::UnrecognizedName => Ok(SPEC_AlertDescription_UnrecognizedName),
            AlertDescription::BadCertificateStatusResponse => Ok(SPEC_AlertDescription_BadCertificateStatusResponse),
            AlertDescription::UnknownPSKIdentity => Ok(SPEC_AlertDescription_UnknownPSKIdentity),
            AlertDescription::CertificateRequired => Ok(SPEC_AlertDescription_CertificateRequired),
            AlertDescription::NoApplicationProtocol => Ok(SPEC_AlertDescription_NoApplicationProtocol),
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

impl<'a> TryFrom<&'a AlertDescription> for AlertDescriptionInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AlertDescription) -> Result<AlertDescriptionInnerRef<'a>, ()> {
        match v {
            AlertDescription::CloseNotify => Ok(&EXEC_AlertDescription_CloseNotify),
            AlertDescription::UnexpectedMessage => Ok(&EXEC_AlertDescription_UnexpectedMessage),
            AlertDescription::BadRecordMac => Ok(&EXEC_AlertDescription_BadRecordMac),
            AlertDescription::RecordOverflow => Ok(&EXEC_AlertDescription_RecordOverflow),
            AlertDescription::HandshakeFailure => Ok(&EXEC_AlertDescription_HandshakeFailure),
            AlertDescription::BadCertificate => Ok(&EXEC_AlertDescription_BadCertificate),
            AlertDescription::UnsupportedCertificate => Ok(&EXEC_AlertDescription_UnsupportedCertificate),
            AlertDescription::CertificateRevoked => Ok(&EXEC_AlertDescription_CertificateRevoked),
            AlertDescription::CertificateExpired => Ok(&EXEC_AlertDescription_CertificateExpired),
            AlertDescription::CertificateUnknown => Ok(&EXEC_AlertDescription_CertificateUnknown),
            AlertDescription::IllegalParameter => Ok(&EXEC_AlertDescription_IllegalParameter),
            AlertDescription::UnknownCA => Ok(&EXEC_AlertDescription_UnknownCA),
            AlertDescription::AccessDenied => Ok(&EXEC_AlertDescription_AccessDenied),
            AlertDescription::DecodeError => Ok(&EXEC_AlertDescription_DecodeError),
            AlertDescription::DecryptError => Ok(&EXEC_AlertDescription_DecryptError),
            AlertDescription::ProtocolVersion => Ok(&EXEC_AlertDescription_ProtocolVersion),
            AlertDescription::InsufficientSecurity => Ok(&EXEC_AlertDescription_InsufficientSecurity),
            AlertDescription::InternalError => Ok(&EXEC_AlertDescription_InternalError),
            AlertDescription::InappropriateFallback => Ok(&EXEC_AlertDescription_InappropriateFallback),
            AlertDescription::UserCanceled => Ok(&EXEC_AlertDescription_UserCanceled),
            AlertDescription::MissingExtension => Ok(&EXEC_AlertDescription_MissingExtension),
            AlertDescription::UnsupportedExtension => Ok(&EXEC_AlertDescription_UnsupportedExtension),
            AlertDescription::UnrecognizedName => Ok(&EXEC_AlertDescription_UnrecognizedName),
            AlertDescription::BadCertificateStatusResponse => Ok(&EXEC_AlertDescription_BadCertificateStatusResponse),
            AlertDescription::UnknownPSKIdentity => Ok(&EXEC_AlertDescription_UnknownPSKIdentity),
            AlertDescription::CertificateRequired => Ok(&EXEC_AlertDescription_CertificateRequired),
            AlertDescription::NoApplicationProtocol => Ok(&EXEC_AlertDescription_NoApplicationProtocol),
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

impl SpecPartialIso for AlertDescriptionMapper {
    type Src = AlertDescriptionInner;
    type Dst = AlertDescription;
}

impl SpecPartialIsoProof for AlertDescriptionMapper {
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

impl<'a> PartialIso<'a> for AlertDescriptionMapper {
    type Src = AlertDescriptionInner;
    type Dst = AlertDescription;
    type RefSrc = AlertDescriptionInnerRef<'a>;
}


pub struct SpecAlertDescriptionCombinator(SpecAlertDescriptionCombinatorAlias);

impl SpecCombinator for SpecAlertDescriptionCombinator {
    type Type = SpecAlertDescription;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAlertDescriptionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertDescriptionCombinatorAlias::is_prefix_secure() }
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
pub type SpecAlertDescriptionCombinatorAlias = TryMap<U8, AlertDescriptionMapper>;

pub struct AlertDescriptionCombinator(AlertDescriptionCombinatorAlias);

impl View for AlertDescriptionCombinator {
    type V = SpecAlertDescriptionCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertDescriptionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AlertDescriptionCombinator {
    type Type = AlertDescription;
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

pub type AlertInnerRef<'a> = (&'a AlertLevel, &'a AlertDescription);
impl<'a> From<&'a Alert> for AlertInnerRef<'a> {
    fn ex_from(m: &'a Alert) -> AlertInnerRef<'a> {
        (&m.level, &m.description)
    }
}

impl From<AlertInner> for Alert {
    fn ex_from(m: AlertInner) -> Alert {
        let (level, description) = m;
        Alert { level, description }
    }
}

pub struct AlertMapper;
impl View for AlertMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AlertMapper {
    type Src = SpecAlertInner;
    type Dst = SpecAlert;
}
impl SpecIsoProof for AlertMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for AlertMapper {
    type Src = AlertInner;
    type Dst = Alert;
    type RefSrc = AlertInnerRef<'a>;
}
type SpecAlertCombinatorAlias1 = (SpecAlertLevelCombinator, SpecAlertDescriptionCombinator);
pub struct SpecAlertCombinator(SpecAlertCombinatorAlias);

impl SpecCombinator for SpecAlertCombinator {
    type Type = SpecAlert;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAlertCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertCombinatorAlias::is_prefix_secure() }
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
pub type SpecAlertCombinatorAlias = Mapped<SpecAlertCombinatorAlias1, AlertMapper>;
type AlertCombinatorAlias1 = (AlertLevelCombinator, AlertDescriptionCombinator);
struct AlertCombinator1(AlertCombinatorAlias1);
impl View for AlertCombinator1 {
    type V = SpecAlertCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AlertCombinator1, AlertCombinatorAlias1);

pub struct AlertCombinator(AlertCombinatorAlias);

impl View for AlertCombinator {
    type V = SpecAlertCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AlertCombinator {
    type Type = Alert;
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
pub type AlertCombinatorAlias = Mapped<AlertCombinator1, AlertMapper>;


pub closed spec fn spec_alert() -> SpecAlertCombinator {
    SpecAlertCombinator(
    Mapped {
        inner: (spec_alert_level(), spec_alert_description()),
        mapper: AlertMapper,
    })
}

                
pub fn alert() -> (o: AlertCombinator)
    ensures o@ == spec_alert(),
{
    AlertCombinator(
    Mapped {
        inner: AlertCombinator1((alert_level(), alert_description())),
        mapper: AlertMapper,
    })
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

pub type SessionIdInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a SessionId<'a>> for SessionIdInnerRef<'a> {
    fn ex_from(m: &'a SessionId) -> SessionIdInnerRef<'a> {
        (&m.l, &m.id)
    }
}

impl<'a> From<SessionIdInner<'a>> for SessionId<'a> {
    fn ex_from(m: SessionIdInner) -> SessionId {
        let (l, id) = m;
        SessionId { l, id }
    }
}

pub struct SessionIdMapper;
impl View for SessionIdMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SessionIdMapper {
    type Src = SpecSessionIdInner;
    type Dst = SpecSessionId;
}
impl SpecIsoProof for SessionIdMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SessionIdMapper {
    type Src = SessionIdInner<'a>;
    type Dst = SessionId<'a>;
    type RefSrc = SessionIdInnerRef<'a>;
}

pub struct SpecSessionIdCombinator(SpecSessionIdCombinatorAlias);

impl SpecCombinator for SpecSessionIdCombinator {
    type Type = SpecSessionId;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSessionIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSessionIdCombinatorAlias::is_prefix_secure() }
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
pub type SpecSessionIdCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate14254733753739482027>, bytes::Variable>, SessionIdMapper>;
pub struct Predicate14254733753739482027;
impl View for Predicate14254733753739482027 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14254733753739482027 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32)
    }
}
impl SpecPred<u8> for Predicate14254733753739482027 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 32)
    }
}

pub struct SessionIdCombinator(SessionIdCombinatorAlias);

impl View for SessionIdCombinator {
    type V = SpecSessionIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecSessionIdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SessionIdCombinator {
    type Type = SessionId<'a>;
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
pub type SessionIdCombinatorAlias = Mapped<Pair<Refined<U8, Predicate14254733753739482027>, bytes::Variable, SessionIdCont0>, SessionIdMapper>;


pub closed spec fn spec_session_id() -> SpecSessionIdCombinator {
    SpecSessionIdCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate14254733753739482027 }, |deps| spec_session_id_cont0(deps)),
        mapper: SessionIdMapper,
    })
}

pub open spec fn spec_session_id_cont0(deps: u8) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for SessionIdCont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_session_id_cont0(deps)
        }
    }
}

                
pub fn session_id() -> (o: SessionIdCombinator)
    ensures o@ == spec_session_id(),
{
    SessionIdCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate14254733753739482027 }, SessionIdCont0),
        mapper: SessionIdMapper,
    })
}

pub struct SessionIdCont0;
type SessionIdCont0Type<'a, 'b> = &'b u8;
type SessionIdCont0SType<'a, 'x> = &'x u8;
type SessionIdCont0Input<'a, 'b, 'x> = POrSType<SessionIdCont0Type<'a, 'b>, SessionIdCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SessionIdCont0Input<'a, 'b, 'x>> for SessionIdCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: SessionIdCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SessionIdCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_session_id_cont0(deps@)
    }

    fn apply(&self, deps: SessionIdCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                
pub type SpecCipherSuite = u16;
pub type CipherSuite = u16;
pub type CipherSuiteRef<'a> = &'a u16;


pub struct SpecCipherSuiteCombinator(SpecCipherSuiteCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteCombinator {
    type Type = SpecCipherSuite;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCipherSuiteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteCombinatorAlias::is_prefix_secure() }
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
pub type SpecCipherSuiteCombinatorAlias = U16Be;

pub struct CipherSuiteCombinator(CipherSuiteCombinatorAlias);

impl View for CipherSuiteCombinator {
    type V = SpecCipherSuiteCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CipherSuiteCombinator {
    type Type = CipherSuite;
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
pub type CipherSuiteCombinatorAlias = U16Be;


pub closed spec fn spec_cipher_suite() -> SpecCipherSuiteCombinator {
    SpecCipherSuiteCombinator(U16Be)
}

                
pub fn cipher_suite() -> (o: CipherSuiteCombinator)
    ensures o@ == spec_cipher_suite(),
{
    CipherSuiteCombinator(U16Be)
}

                
pub type SpecExtensionType = u16;
pub type ExtensionType = u16;
pub type ExtensionTypeRef<'a> = &'a u16;


pub struct SpecExtensionTypeCombinator(SpecExtensionTypeCombinatorAlias);

impl SpecCombinator for SpecExtensionTypeCombinator {
    type Type = SpecExtensionType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExtensionTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecExtensionTypeCombinatorAlias = U16Be;

pub struct ExtensionTypeCombinator(ExtensionTypeCombinatorAlias);

impl View for ExtensionTypeCombinator {
    type V = SpecExtensionTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExtensionTypeCombinator {
    type Type = ExtensionType;
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
pub type ExtensionTypeCombinatorAlias = U16Be;


pub closed spec fn spec_extension_type() -> SpecExtensionTypeCombinator {
    SpecExtensionTypeCombinator(U16Be)
}

                
pub fn extension_type() -> (o: ExtensionTypeCombinator)
    ensures o@ == spec_extension_type(),
{
    ExtensionTypeCombinator(U16Be)
}

                
pub type SpecSupportedVersionsServer = SpecProtocolVersion;
pub type SupportedVersionsServer = ProtocolVersion;
pub type SupportedVersionsServerRef<'a> = &'a ProtocolVersion;


pub struct SpecSupportedVersionsServerCombinator(SpecSupportedVersionsServerCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsServerCombinator {
    type Type = SpecSupportedVersionsServer;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSupportedVersionsServerCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsServerCombinatorAlias::is_prefix_secure() }
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
pub type SpecSupportedVersionsServerCombinatorAlias = SpecProtocolVersionCombinator;

pub struct SupportedVersionsServerCombinator(SupportedVersionsServerCombinatorAlias);

impl View for SupportedVersionsServerCombinator {
    type V = SpecSupportedVersionsServerCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsServerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SupportedVersionsServerCombinator {
    type Type = SupportedVersionsServer;
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
pub type SupportedVersionsServerCombinatorAlias = ProtocolVersionCombinator;


pub closed spec fn spec_supported_versions_server() -> SpecSupportedVersionsServerCombinator {
    SpecSupportedVersionsServerCombinator(spec_protocol_version())
}

                
pub fn supported_versions_server() -> (o: SupportedVersionsServerCombinator)
    ensures o@ == spec_supported_versions_server(),
{
    SupportedVersionsServerCombinator(protocol_version())
}

                
pub type SpecCookie = SpecOpaque1Ffff;
pub type Cookie<'a> = Opaque1Ffff<'a>;
pub type CookieRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecCookieCombinator(SpecCookieCombinatorAlias);

impl SpecCombinator for SpecCookieCombinator {
    type Type = SpecCookie;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCookieCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCookieCombinatorAlias::is_prefix_secure() }
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
pub type SpecCookieCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct CookieCombinator(CookieCombinatorAlias);

impl View for CookieCombinator {
    type V = SpecCookieCombinator;
    closed spec fn view(&self) -> Self::V { SpecCookieCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CookieCombinator {
    type Type = Cookie<'a>;
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
pub type CookieCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_cookie() -> SpecCookieCombinator {
    SpecCookieCombinator(spec_opaque_1_ffff())
}

                
pub fn cookie() -> (o: CookieCombinator)
    ensures o@ == spec_cookie(),
{
    CookieCombinator(opaque_1_ffff())
}

                
pub type SpecNamedGroup = u16;
pub type NamedGroup = u16;
pub type NamedGroupRef<'a> = &'a u16;


pub struct SpecNamedGroupCombinator(SpecNamedGroupCombinatorAlias);

impl SpecCombinator for SpecNamedGroupCombinator {
    type Type = SpecNamedGroup;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNamedGroupCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupCombinatorAlias::is_prefix_secure() }
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
pub type SpecNamedGroupCombinatorAlias = U16Be;

pub struct NamedGroupCombinator(NamedGroupCombinatorAlias);

impl View for NamedGroupCombinator {
    type V = SpecNamedGroupCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NamedGroupCombinator {
    type Type = NamedGroup;
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
pub type NamedGroupCombinatorAlias = U16Be;


pub closed spec fn spec_named_group() -> SpecNamedGroupCombinator {
    SpecNamedGroupCombinator(U16Be)
}

                
pub fn named_group() -> (o: NamedGroupCombinator)
    ensures o@ == spec_named_group(),
{
    NamedGroupCombinator(U16Be)
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

pub type HelloRetryExtensionExtensionDataInnerRef<'a> = Either<&'a SupportedVersionsServer, Either<&'a Cookie<'a>, Either<&'a NamedGroup, &'a &'a [u8]>>>;


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


impl<'a> From<&'a HelloRetryExtensionExtensionData<'a>> for HelloRetryExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a HelloRetryExtensionExtensionData<'a>) -> HelloRetryExtensionExtensionDataInnerRef<'a> {
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


pub struct HelloRetryExtensionExtensionDataMapper;
impl View for HelloRetryExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionExtensionDataMapper {
    type Src = SpecHelloRetryExtensionExtensionDataInner;
    type Dst = SpecHelloRetryExtensionExtensionData;
}
impl SpecIsoProof for HelloRetryExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HelloRetryExtensionExtensionDataMapper {
    type Src = HelloRetryExtensionExtensionDataInner<'a>;
    type Dst = HelloRetryExtensionExtensionData<'a>;
    type RefSrc = HelloRetryExtensionExtensionDataInnerRef<'a>;
}

type SpecHelloRetryExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecNamedGroupCombinator>, Cond<bytes::Variable>>;
type SpecHelloRetryExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecCookieCombinator>, SpecHelloRetryExtensionExtensionDataCombinatorAlias1>;
type SpecHelloRetryExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SpecSupportedVersionsServerCombinator>, SpecHelloRetryExtensionExtensionDataCombinatorAlias2>;
pub struct SpecHelloRetryExtensionExtensionDataCombinator(SpecHelloRetryExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionExtensionDataCombinator {
    type Type = SpecHelloRetryExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHelloRetryExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecHelloRetryExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecHelloRetryExtensionExtensionDataCombinatorAlias3, HelloRetryExtensionExtensionDataMapper>>;
type HelloRetryExtensionExtensionDataCombinatorAlias1 = Choice<Cond<NamedGroupCombinator>, Cond<bytes::Variable>>;
type HelloRetryExtensionExtensionDataCombinatorAlias2 = Choice<Cond<CookieCombinator>, HelloRetryExtensionExtensionDataCombinator1>;
type HelloRetryExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SupportedVersionsServerCombinator>, HelloRetryExtensionExtensionDataCombinator2>;
struct HelloRetryExtensionExtensionDataCombinator1(HelloRetryExtensionExtensionDataCombinatorAlias1);
impl View for HelloRetryExtensionExtensionDataCombinator1 {
    type V = SpecHelloRetryExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryExtensionExtensionDataCombinator1, HelloRetryExtensionExtensionDataCombinatorAlias1);

struct HelloRetryExtensionExtensionDataCombinator2(HelloRetryExtensionExtensionDataCombinatorAlias2);
impl View for HelloRetryExtensionExtensionDataCombinator2 {
    type V = SpecHelloRetryExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryExtensionExtensionDataCombinator2, HelloRetryExtensionExtensionDataCombinatorAlias2);

struct HelloRetryExtensionExtensionDataCombinator3(HelloRetryExtensionExtensionDataCombinatorAlias3);
impl View for HelloRetryExtensionExtensionDataCombinator3 {
    type V = SpecHelloRetryExtensionExtensionDataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryExtensionExtensionDataCombinator3, HelloRetryExtensionExtensionDataCombinatorAlias3);

pub struct HelloRetryExtensionExtensionDataCombinator(HelloRetryExtensionExtensionDataCombinatorAlias);

impl View for HelloRetryExtensionExtensionDataCombinator {
    type V = SpecHelloRetryExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryExtensionExtensionDataCombinator {
    type Type = HelloRetryExtensionExtensionData<'a>;
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
pub type HelloRetryExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<HelloRetryExtensionExtensionDataCombinator3, HelloRetryExtensionExtensionDataMapper>>;


pub closed spec fn spec_hello_retry_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecHelloRetryExtensionExtensionDataCombinator {
    SpecHelloRetryExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 43, inner: spec_supported_versions_server() }, Choice(Cond { cond: extension_type == 44, inner: spec_cookie() }, Choice(Cond { cond: extension_type == 51, inner: spec_named_group() }, Cond { cond: !(extension_type == 43 || extension_type == 44 || extension_type == 51), inner: bytes::Variable(ext_len.spec_into()) }))), mapper: HelloRetryExtensionExtensionDataMapper }))
}

pub fn hello_retry_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: HelloRetryExtensionExtensionDataCombinator)
    ensures o@ == spec_hello_retry_extension_extension_data(extension_type@, ext_len@),
{
    HelloRetryExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: HelloRetryExtensionExtensionDataCombinator3(Choice::new(Cond { cond: extension_type == 43, inner: supported_versions_server() }, HelloRetryExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 44, inner: cookie() }, HelloRetryExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 51, inner: named_group() }, Cond { cond: !(extension_type == 43 || extension_type == 44 || extension_type == 51), inner: bytes::Variable(ext_len.ex_into()) })))))), mapper: HelloRetryExtensionExtensionDataMapper }))
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

pub type HelloRetryExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a HelloRetryExtensionExtensionData<'a>);
impl<'a> From<&'a HelloRetryExtension<'a>> for HelloRetryExtensionInnerRef<'a> {
    fn ex_from(m: &'a HelloRetryExtension) -> HelloRetryExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<HelloRetryExtensionInner<'a>> for HelloRetryExtension<'a> {
    fn ex_from(m: HelloRetryExtensionInner) -> HelloRetryExtension {
        let ((extension_type, ext_len), extension_data) = m;
        HelloRetryExtension { extension_type, ext_len, extension_data }
    }
}

pub struct HelloRetryExtensionMapper;
impl View for HelloRetryExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionMapper {
    type Src = SpecHelloRetryExtensionInner;
    type Dst = SpecHelloRetryExtension;
}
impl SpecIsoProof for HelloRetryExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HelloRetryExtensionMapper {
    type Src = HelloRetryExtensionInner<'a>;
    type Dst = HelloRetryExtension<'a>;
    type RefSrc = HelloRetryExtensionInnerRef<'a>;
}

pub struct SpecHelloRetryExtensionCombinator(SpecHelloRetryExtensionCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionCombinator {
    type Type = SpecHelloRetryExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHelloRetryExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecHelloRetryExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecHelloRetryExtensionExtensionDataCombinator>, HelloRetryExtensionMapper>;

pub struct HelloRetryExtensionCombinator(HelloRetryExtensionCombinatorAlias);

impl View for HelloRetryExtensionCombinator {
    type V = SpecHelloRetryExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryExtensionCombinator {
    type Type = HelloRetryExtension<'a>;
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
pub type HelloRetryExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, HelloRetryExtensionCont1>, HelloRetryExtensionExtensionDataCombinator, HelloRetryExtensionCont0>, HelloRetryExtensionMapper>;


pub closed spec fn spec_hello_retry_extension() -> SpecHelloRetryExtensionCombinator {
    SpecHelloRetryExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_hello_retry_extension_cont1(deps)), |deps| spec_hello_retry_extension_cont0(deps)),
        mapper: HelloRetryExtensionMapper,
    })
}

pub open spec fn spec_hello_retry_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for HelloRetryExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_hello_retry_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_hello_retry_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecHelloRetryExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_hello_retry_extension_extension_data(extension_type, ext_len)
}

impl View for HelloRetryExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecHelloRetryExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_hello_retry_extension_cont0(deps)
        }
    }
}

                
pub fn hello_retry_extension() -> (o: HelloRetryExtensionCombinator)
    ensures o@ == spec_hello_retry_extension(),
{
    HelloRetryExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), HelloRetryExtensionCont1), HelloRetryExtensionCont0),
        mapper: HelloRetryExtensionMapper,
    })
}

pub struct HelloRetryExtensionCont1;
type HelloRetryExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type HelloRetryExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type HelloRetryExtensionCont1Input<'a, 'b, 'x> = POrSType<HelloRetryExtensionCont1Type<'a, 'b>, HelloRetryExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HelloRetryExtensionCont1Input<'a, 'b, 'x>> for HelloRetryExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: HelloRetryExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: HelloRetryExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_hello_retry_extension_cont1(deps@)
    }

    fn apply(&self, deps: HelloRetryExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct HelloRetryExtensionCont0;
type HelloRetryExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type HelloRetryExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type HelloRetryExtensionCont0Input<'a, 'b, 'x> = POrSType<HelloRetryExtensionCont0Type<'a, 'b>, HelloRetryExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HelloRetryExtensionCont0Input<'a, 'b, 'x>> for HelloRetryExtensionCont0 {
    type Output = HelloRetryExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: HelloRetryExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: HelloRetryExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_hello_retry_extension_cont0(deps@)
    }

    fn apply(&self, deps: HelloRetryExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                hello_retry_extension_extension_data(extension_type, ext_len)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                hello_retry_extension_extension_data(extension_type, ext_len)
            }
        }
    }
}
                

pub struct SpecHelloRetryExtensions {
    pub l: u16,
    pub list: Seq<SpecHelloRetryExtension>,
}

pub type SpecHelloRetryExtensionsInner = (u16, Seq<SpecHelloRetryExtension>);


impl SpecFrom<SpecHelloRetryExtensions> for SpecHelloRetryExtensionsInner {
    open spec fn spec_from(m: SpecHelloRetryExtensions) -> SpecHelloRetryExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecHelloRetryExtensionsInner> for SpecHelloRetryExtensions {
    open spec fn spec_from(m: SpecHelloRetryExtensionsInner) -> SpecHelloRetryExtensions {
        let (l, list) = m;
        SpecHelloRetryExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct HelloRetryExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<HelloRetryExtension<'a>>,
}

impl View for HelloRetryExtensions<'_> {
    type V = SpecHelloRetryExtensions;

    open spec fn view(&self) -> Self::V {
        SpecHelloRetryExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type HelloRetryExtensionsInner<'a> = (u16, RepeatResult<HelloRetryExtension<'a>>);

pub type HelloRetryExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<HelloRetryExtension<'a>>);
impl<'a> From<&'a HelloRetryExtensions<'a>> for HelloRetryExtensionsInnerRef<'a> {
    fn ex_from(m: &'a HelloRetryExtensions) -> HelloRetryExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<HelloRetryExtensionsInner<'a>> for HelloRetryExtensions<'a> {
    fn ex_from(m: HelloRetryExtensionsInner) -> HelloRetryExtensions {
        let (l, list) = m;
        HelloRetryExtensions { l, list }
    }
}

pub struct HelloRetryExtensionsMapper;
impl View for HelloRetryExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryExtensionsMapper {
    type Src = SpecHelloRetryExtensionsInner;
    type Dst = SpecHelloRetryExtensions;
}
impl SpecIsoProof for HelloRetryExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HelloRetryExtensionsMapper {
    type Src = HelloRetryExtensionsInner<'a>;
    type Dst = HelloRetryExtensions<'a>;
    type RefSrc = HelloRetryExtensionsInnerRef<'a>;
}

pub struct SpecHelloRetryExtensionsCombinator(SpecHelloRetryExtensionsCombinatorAlias);

impl SpecCombinator for SpecHelloRetryExtensionsCombinator {
    type Type = SpecHelloRetryExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHelloRetryExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHelloRetryExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecHelloRetryExtensionsCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate14496530480760116989>, AndThen<bytes::Variable, Repeat<SpecHelloRetryExtensionCombinator>>>, HelloRetryExtensionsMapper>;
pub struct Predicate14496530480760116989;
impl View for Predicate14496530480760116989 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate14496530480760116989 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 6 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate14496530480760116989 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 6 && i <= 65535)
    }
}

pub struct HelloRetryExtensionsCombinator(HelloRetryExtensionsCombinatorAlias);

impl View for HelloRetryExtensionsCombinator {
    type V = SpecHelloRetryExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryExtensionsCombinator {
    type Type = HelloRetryExtensions<'a>;
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
pub type HelloRetryExtensionsCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate14496530480760116989>, AndThen<bytes::Variable, Repeat<HelloRetryExtensionCombinator>>, HelloRetryExtensionsCont0>, HelloRetryExtensionsMapper>;


pub closed spec fn spec_hello_retry_extensions() -> SpecHelloRetryExtensionsCombinator {
    SpecHelloRetryExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate14496530480760116989 }, |deps| spec_hello_retry_extensions_cont0(deps)),
        mapper: HelloRetryExtensionsMapper,
    })
}

pub open spec fn spec_hello_retry_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecHelloRetryExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_hello_retry_extension()))
}

impl View for HelloRetryExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecHelloRetryExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_hello_retry_extensions_cont0(deps)
        }
    }
}

                
pub fn hello_retry_extensions() -> (o: HelloRetryExtensionsCombinator)
    ensures o@ == spec_hello_retry_extensions(),
{
    HelloRetryExtensionsCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate14496530480760116989 }, HelloRetryExtensionsCont0),
        mapper: HelloRetryExtensionsMapper,
    })
}

pub struct HelloRetryExtensionsCont0;
type HelloRetryExtensionsCont0Type<'a, 'b> = &'b u16;
type HelloRetryExtensionsCont0SType<'a, 'x> = &'x u16;
type HelloRetryExtensionsCont0Input<'a, 'b, 'x> = POrSType<HelloRetryExtensionsCont0Type<'a, 'b>, HelloRetryExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HelloRetryExtensionsCont0Input<'a, 'b, 'x>> for HelloRetryExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<HelloRetryExtensionCombinator>>;

    open spec fn requires(&self, deps: HelloRetryExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: HelloRetryExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_hello_retry_extensions_cont0(deps@)
    }

    fn apply(&self, deps: HelloRetryExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(hello_retry_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(hello_retry_extension()))
            }
        }
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

pub type HelloRetryRequestInnerRef<'a> = (&'a SessionId<'a>, (&'a CipherSuite, (&'a u8, &'a HelloRetryExtensions<'a>)));
impl<'a> From<&'a HelloRetryRequest<'a>> for HelloRetryRequestInnerRef<'a> {
    fn ex_from(m: &'a HelloRetryRequest) -> HelloRetryRequestInnerRef<'a> {
        (&m.legacy_session_id_echo, (&m.cipher_suite, (&m.legacy_compression_method, &m.extensions)))
    }
}

impl<'a> From<HelloRetryRequestInner<'a>> for HelloRetryRequest<'a> {
    fn ex_from(m: HelloRetryRequestInner) -> HelloRetryRequest {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        HelloRetryRequest { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}

pub struct HelloRetryRequestMapper;
impl View for HelloRetryRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HelloRetryRequestMapper {
    type Src = SpecHelloRetryRequestInner;
    type Dst = SpecHelloRetryRequest;
}
impl SpecIsoProof for HelloRetryRequestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HelloRetryRequestMapper {
    type Src = HelloRetryRequestInner<'a>;
    type Dst = HelloRetryRequest<'a>;
    type RefSrc = HelloRetryRequestInnerRef<'a>;
}
pub const HELLORETRYREQUESTLEGACY_COMPRESSION_METHOD_CONST: u8 = 0;
type SpecHelloRetryRequestCombinatorAlias1 = (Refined<U8, TagPred<u8>>, SpecHelloRetryExtensionsCombinator);
type SpecHelloRetryRequestCombinatorAlias2 = (SpecCipherSuiteCombinator, SpecHelloRetryRequestCombinatorAlias1);
type SpecHelloRetryRequestCombinatorAlias3 = (SpecSessionIdCombinator, SpecHelloRetryRequestCombinatorAlias2);
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
pub type SpecHelloRetryRequestCombinatorAlias = Mapped<SpecHelloRetryRequestCombinatorAlias3, HelloRetryRequestMapper>;
type HelloRetryRequestCombinatorAlias1 = (Refined<U8, TagPred<u8>>, HelloRetryExtensionsCombinator);
type HelloRetryRequestCombinatorAlias2 = (CipherSuiteCombinator, HelloRetryRequestCombinator1);
type HelloRetryRequestCombinatorAlias3 = (SessionIdCombinator, HelloRetryRequestCombinator2);
struct HelloRetryRequestCombinator1(HelloRetryRequestCombinatorAlias1);
impl View for HelloRetryRequestCombinator1 {
    type V = SpecHelloRetryRequestCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryRequestCombinator1, HelloRetryRequestCombinatorAlias1);

struct HelloRetryRequestCombinator2(HelloRetryRequestCombinatorAlias2);
impl View for HelloRetryRequestCombinator2 {
    type V = SpecHelloRetryRequestCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryRequestCombinator2, HelloRetryRequestCombinatorAlias2);

struct HelloRetryRequestCombinator3(HelloRetryRequestCombinatorAlias3);
impl View for HelloRetryRequestCombinator3 {
    type V = SpecHelloRetryRequestCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HelloRetryRequestCombinator3, HelloRetryRequestCombinatorAlias3);

pub struct HelloRetryRequestCombinator(HelloRetryRequestCombinatorAlias);

impl View for HelloRetryRequestCombinator {
    type V = SpecHelloRetryRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecHelloRetryRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HelloRetryRequestCombinator {
    type Type = HelloRetryRequest<'a>;
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
pub type HelloRetryRequestCombinatorAlias = Mapped<HelloRetryRequestCombinator3, HelloRetryRequestMapper>;


pub closed spec fn spec_hello_retry_request() -> SpecHelloRetryRequestCombinator {
    SpecHelloRetryRequestCombinator(
    Mapped {
        inner: (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(HELLORETRYREQUESTLEGACY_COMPRESSION_METHOD_CONST) }, spec_hello_retry_extensions()))),
        mapper: HelloRetryRequestMapper,
    })
}

                
pub fn hello_retry_request() -> (o: HelloRetryRequestCombinator)
    ensures o@ == spec_hello_retry_request(),
{
    HelloRetryRequestCombinator(
    Mapped {
        inner: HelloRetryRequestCombinator3((session_id(), HelloRetryRequestCombinator2((cipher_suite(), HelloRetryRequestCombinator1((Refined { inner: U8, predicate: TagPred(HELLORETRYREQUESTLEGACY_COMPRESSION_METHOD_CONST) }, hello_retry_extensions())))))),
        mapper: HelloRetryRequestMapper,
    })
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

pub type PreSharedKeyServerExtensionInnerRef<'a> = &'a u16;
impl<'a> From<&'a PreSharedKeyServerExtension> for PreSharedKeyServerExtensionInnerRef<'a> {
    fn ex_from(m: &'a PreSharedKeyServerExtension) -> PreSharedKeyServerExtensionInnerRef<'a> {
        &m.selected_identity
    }
}

impl From<PreSharedKeyServerExtensionInner> for PreSharedKeyServerExtension {
    fn ex_from(m: PreSharedKeyServerExtensionInner) -> PreSharedKeyServerExtension {
        let selected_identity = m;
        PreSharedKeyServerExtension { selected_identity }
    }
}

pub struct PreSharedKeyServerExtensionMapper;
impl View for PreSharedKeyServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyServerExtensionMapper {
    type Src = SpecPreSharedKeyServerExtensionInner;
    type Dst = SpecPreSharedKeyServerExtension;
}
impl SpecIsoProof for PreSharedKeyServerExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PreSharedKeyServerExtensionMapper {
    type Src = PreSharedKeyServerExtensionInner;
    type Dst = PreSharedKeyServerExtension;
    type RefSrc = PreSharedKeyServerExtensionInnerRef<'a>;
}

pub struct SpecPreSharedKeyServerExtensionCombinator(SpecPreSharedKeyServerExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    type Type = SpecPreSharedKeyServerExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyServerExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecPreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;

pub struct PreSharedKeyServerExtensionCombinator(PreSharedKeyServerExtensionCombinatorAlias);

impl View for PreSharedKeyServerExtensionCombinator {
    type V = SpecPreSharedKeyServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PreSharedKeyServerExtensionCombinator {
    type Type = PreSharedKeyServerExtension;
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
pub type PreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;


pub closed spec fn spec_pre_shared_key_server_extension() -> SpecPreSharedKeyServerExtensionCombinator {
    SpecPreSharedKeyServerExtensionCombinator(
    Mapped {
        inner: U16Be,
        mapper: PreSharedKeyServerExtensionMapper,
    })
}

                
pub fn pre_shared_key_server_extension() -> (o: PreSharedKeyServerExtensionCombinator)
    ensures o@ == spec_pre_shared_key_server_extension(),
{
    PreSharedKeyServerExtensionCombinator(
    Mapped {
        inner: U16Be,
        mapper: PreSharedKeyServerExtensionMapper,
    })
}

                

pub struct SpecKeyShareEntry {
    pub group: SpecNamedGroup,
    pub l: u16,
    pub key_exchange: Seq<u8>,
}

pub type SpecKeyShareEntryInner = ((SpecNamedGroup, u16), Seq<u8>);


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
    pub l: u16,
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
pub type KeyShareEntryInner<'a> = ((NamedGroup, u16), &'a [u8]);

pub type KeyShareEntryInnerRef<'a> = ((&'a NamedGroup, &'a u16), &'a &'a [u8]);
impl<'a> From<&'a KeyShareEntry<'a>> for KeyShareEntryInnerRef<'a> {
    fn ex_from(m: &'a KeyShareEntry) -> KeyShareEntryInnerRef<'a> {
        ((&m.group, &m.l), &m.key_exchange)
    }
}

impl<'a> From<KeyShareEntryInner<'a>> for KeyShareEntry<'a> {
    fn ex_from(m: KeyShareEntryInner) -> KeyShareEntry {
        let ((group, l), key_exchange) = m;
        KeyShareEntry { group, l, key_exchange }
    }
}

pub struct KeyShareEntryMapper;
impl View for KeyShareEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareEntryMapper {
    type Src = SpecKeyShareEntryInner;
    type Dst = SpecKeyShareEntry;
}
impl SpecIsoProof for KeyShareEntryMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for KeyShareEntryMapper {
    type Src = KeyShareEntryInner<'a>;
    type Dst = KeyShareEntry<'a>;
    type RefSrc = KeyShareEntryInnerRef<'a>;
}

pub struct SpecKeyShareEntryCombinator(SpecKeyShareEntryCombinatorAlias);

impl SpecCombinator for SpecKeyShareEntryCombinator {
    type Type = SpecKeyShareEntry;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecKeyShareEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareEntryCombinatorAlias::is_prefix_secure() }
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
pub type SpecKeyShareEntryCombinatorAlias = Mapped<SpecPair<SpecPair<SpecNamedGroupCombinator, Refined<U16Be, Predicate16977634203518580913>>, bytes::Variable>, KeyShareEntryMapper>;
pub struct Predicate16977634203518580913;
impl View for Predicate16977634203518580913 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate16977634203518580913 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate16977634203518580913 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 1 && i <= 65535)
    }
}

pub struct KeyShareEntryCombinator(KeyShareEntryCombinatorAlias);

impl View for KeyShareEntryCombinator {
    type V = SpecKeyShareEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareEntryCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for KeyShareEntryCombinator {
    type Type = KeyShareEntry<'a>;
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
pub type KeyShareEntryCombinatorAlias = Mapped<Pair<Pair<NamedGroupCombinator, Refined<U16Be, Predicate16977634203518580913>, KeyShareEntryCont1>, bytes::Variable, KeyShareEntryCont0>, KeyShareEntryMapper>;


pub closed spec fn spec_key_share_entry() -> SpecKeyShareEntryCombinator {
    SpecKeyShareEntryCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_named_group(), |deps| spec_key_share_entry_cont1(deps)), |deps| spec_key_share_entry_cont0(deps)),
        mapper: KeyShareEntryMapper,
    })
}

pub open spec fn spec_key_share_entry_cont1(deps: SpecNamedGroup) -> Refined<U16Be, Predicate16977634203518580913> {
    let group = deps;
    Refined { inner: U16Be, predicate: Predicate16977634203518580913 }
}

impl View for KeyShareEntryCont1 {
    type V = spec_fn(SpecNamedGroup) -> Refined<U16Be, Predicate16977634203518580913>;

    open spec fn view(&self) -> Self::V {
        |deps: SpecNamedGroup| {
            spec_key_share_entry_cont1(deps)
        }
    }
}

pub open spec fn spec_key_share_entry_cont0(deps: (SpecNamedGroup, u16)) -> bytes::Variable {
    let (group, l) = deps;
    bytes::Variable(l.spec_into())
}

impl View for KeyShareEntryCont0 {
    type V = spec_fn((SpecNamedGroup, u16)) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecNamedGroup, u16)| {
            spec_key_share_entry_cont0(deps)
        }
    }
}

                
pub fn key_share_entry() -> (o: KeyShareEntryCombinator)
    ensures o@ == spec_key_share_entry(),
{
    KeyShareEntryCombinator(
    Mapped {
        inner: Pair::new(Pair::new(named_group(), KeyShareEntryCont1), KeyShareEntryCont0),
        mapper: KeyShareEntryMapper,
    })
}

pub struct KeyShareEntryCont1;
type KeyShareEntryCont1Type<'a, 'b> = &'b NamedGroup;
type KeyShareEntryCont1SType<'a, 'x> = &'x NamedGroup;
type KeyShareEntryCont1Input<'a, 'b, 'x> = POrSType<KeyShareEntryCont1Type<'a, 'b>, KeyShareEntryCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<KeyShareEntryCont1Input<'a, 'b, 'x>> for KeyShareEntryCont1 {
    type Output = Refined<U16Be, Predicate16977634203518580913>;

    open spec fn requires(&self, deps: KeyShareEntryCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: KeyShareEntryCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont1(deps@)
    }

    fn apply(&self, deps: KeyShareEntryCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let group = *deps;
                Refined { inner: U16Be, predicate: Predicate16977634203518580913 }
            }
            POrSType::S(deps) => {
                let group = deps;
                let group = *group;
                Refined { inner: U16Be, predicate: Predicate16977634203518580913 }
            }
        }
    }
}
pub struct KeyShareEntryCont0;
type KeyShareEntryCont0Type<'a, 'b> = &'b (NamedGroup, u16);
type KeyShareEntryCont0SType<'a, 'x> = (&'x NamedGroup, &'x u16);
type KeyShareEntryCont0Input<'a, 'b, 'x> = POrSType<KeyShareEntryCont0Type<'a, 'b>, KeyShareEntryCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<KeyShareEntryCont0Input<'a, 'b, 'x>> for KeyShareEntryCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: KeyShareEntryCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: KeyShareEntryCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont0(deps@)
    }

    fn apply(&self, deps: KeyShareEntryCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (group, l) = *deps;
                bytes::Variable(l.ex_into())
            }
            POrSType::S(deps) => {
                let (group, l) = deps;
                let (group, l) = (*group, *l);
                bytes::Variable(l.ex_into())
            }
        }
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

pub type SeverHelloExtensionExtensionDataInnerRef<'a> = Either<&'a PreSharedKeyServerExtension, Either<&'a SupportedVersionsServer, Either<&'a KeyShareEntry<'a>, &'a &'a [u8]>>>;


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


impl<'a> From<&'a SeverHelloExtensionExtensionData<'a>> for SeverHelloExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a SeverHelloExtensionExtensionData<'a>) -> SeverHelloExtensionExtensionDataInnerRef<'a> {
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


pub struct SeverHelloExtensionExtensionDataMapper;
impl View for SeverHelloExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionExtensionDataMapper {
    type Src = SpecSeverHelloExtensionExtensionDataInner;
    type Dst = SpecSeverHelloExtensionExtensionData;
}
impl SpecIsoProof for SeverHelloExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SeverHelloExtensionExtensionDataMapper {
    type Src = SeverHelloExtensionExtensionDataInner<'a>;
    type Dst = SeverHelloExtensionExtensionData<'a>;
    type RefSrc = SeverHelloExtensionExtensionDataInnerRef<'a>;
}

type SpecSeverHelloExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecKeyShareEntryCombinator>, Cond<bytes::Variable>>;
type SpecSeverHelloExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecSupportedVersionsServerCombinator>, SpecSeverHelloExtensionExtensionDataCombinatorAlias1>;
type SpecSeverHelloExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SpecPreSharedKeyServerExtensionCombinator>, SpecSeverHelloExtensionExtensionDataCombinatorAlias2>;
pub struct SpecSeverHelloExtensionExtensionDataCombinator(SpecSeverHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    type Type = SpecSeverHelloExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecSeverHelloExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecSeverHelloExtensionExtensionDataCombinatorAlias3, SeverHelloExtensionExtensionDataMapper>>;
type SeverHelloExtensionExtensionDataCombinatorAlias1 = Choice<Cond<KeyShareEntryCombinator>, Cond<bytes::Variable>>;
type SeverHelloExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SupportedVersionsServerCombinator>, SeverHelloExtensionExtensionDataCombinator1>;
type SeverHelloExtensionExtensionDataCombinatorAlias3 = Choice<Cond<PreSharedKeyServerExtensionCombinator>, SeverHelloExtensionExtensionDataCombinator2>;
struct SeverHelloExtensionExtensionDataCombinator1(SeverHelloExtensionExtensionDataCombinatorAlias1);
impl View for SeverHelloExtensionExtensionDataCombinator1 {
    type V = SpecSeverHelloExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(SeverHelloExtensionExtensionDataCombinator1, SeverHelloExtensionExtensionDataCombinatorAlias1);

struct SeverHelloExtensionExtensionDataCombinator2(SeverHelloExtensionExtensionDataCombinatorAlias2);
impl View for SeverHelloExtensionExtensionDataCombinator2 {
    type V = SpecSeverHelloExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(SeverHelloExtensionExtensionDataCombinator2, SeverHelloExtensionExtensionDataCombinatorAlias2);

struct SeverHelloExtensionExtensionDataCombinator3(SeverHelloExtensionExtensionDataCombinatorAlias3);
impl View for SeverHelloExtensionExtensionDataCombinator3 {
    type V = SpecSeverHelloExtensionExtensionDataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(SeverHelloExtensionExtensionDataCombinator3, SeverHelloExtensionExtensionDataCombinatorAlias3);

pub struct SeverHelloExtensionExtensionDataCombinator(SeverHelloExtensionExtensionDataCombinatorAlias);

impl View for SeverHelloExtensionExtensionDataCombinator {
    type V = SpecSeverHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SeverHelloExtensionExtensionDataCombinator {
    type Type = SeverHelloExtensionExtensionData<'a>;
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
pub type SeverHelloExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SeverHelloExtensionExtensionDataCombinator3, SeverHelloExtensionExtensionDataMapper>>;


pub closed spec fn spec_sever_hello_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecSeverHelloExtensionExtensionDataCombinator {
    SpecSeverHelloExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_server_extension() }, Choice(Cond { cond: extension_type == 43, inner: spec_supported_versions_server() }, Choice(Cond { cond: extension_type == 51, inner: spec_key_share_entry() }, Cond { cond: !(extension_type == 41 || extension_type == 43 || extension_type == 51), inner: bytes::Variable(ext_len.spec_into()) }))), mapper: SeverHelloExtensionExtensionDataMapper }))
}

pub fn sever_hello_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: SeverHelloExtensionExtensionDataCombinator)
    ensures o@ == spec_sever_hello_extension_extension_data(ext_len@, extension_type@),
{
    SeverHelloExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: SeverHelloExtensionExtensionDataCombinator3(Choice::new(Cond { cond: extension_type == 41, inner: pre_shared_key_server_extension() }, SeverHelloExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 43, inner: supported_versions_server() }, SeverHelloExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 51, inner: key_share_entry() }, Cond { cond: !(extension_type == 41 || extension_type == 43 || extension_type == 51), inner: bytes::Variable(ext_len.ex_into()) })))))), mapper: SeverHelloExtensionExtensionDataMapper }))
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

pub type SeverHelloExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a SeverHelloExtensionExtensionData<'a>);
impl<'a> From<&'a SeverHelloExtension<'a>> for SeverHelloExtensionInnerRef<'a> {
    fn ex_from(m: &'a SeverHelloExtension) -> SeverHelloExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<SeverHelloExtensionInner<'a>> for SeverHelloExtension<'a> {
    fn ex_from(m: SeverHelloExtensionInner) -> SeverHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SeverHelloExtension { extension_type, ext_len, extension_data }
    }
}

pub struct SeverHelloExtensionMapper;
impl View for SeverHelloExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionMapper {
    type Src = SpecSeverHelloExtensionInner;
    type Dst = SpecSeverHelloExtension;
}
impl SpecIsoProof for SeverHelloExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SeverHelloExtensionMapper {
    type Src = SeverHelloExtensionInner<'a>;
    type Dst = SeverHelloExtension<'a>;
    type RefSrc = SeverHelloExtensionInnerRef<'a>;
}

pub struct SpecSeverHelloExtensionCombinator(SpecSeverHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionCombinator {
    type Type = SpecSeverHelloExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSeverHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecSeverHelloExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecSeverHelloExtensionExtensionDataCombinator>, SeverHelloExtensionMapper>;

pub struct SeverHelloExtensionCombinator(SeverHelloExtensionCombinatorAlias);

impl View for SeverHelloExtensionCombinator {
    type V = SpecSeverHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SeverHelloExtensionCombinator {
    type Type = SeverHelloExtension<'a>;
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
pub type SeverHelloExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, SeverHelloExtensionCont1>, SeverHelloExtensionExtensionDataCombinator, SeverHelloExtensionCont0>, SeverHelloExtensionMapper>;


pub closed spec fn spec_sever_hello_extension() -> SpecSeverHelloExtensionCombinator {
    SpecSeverHelloExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_sever_hello_extension_cont1(deps)), |deps| spec_sever_hello_extension_cont0(deps)),
        mapper: SeverHelloExtensionMapper,
    })
}

pub open spec fn spec_sever_hello_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for SeverHelloExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_sever_hello_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_sever_hello_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecSeverHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_sever_hello_extension_extension_data(ext_len, extension_type)
}

impl View for SeverHelloExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecSeverHelloExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_sever_hello_extension_cont0(deps)
        }
    }
}

                
pub fn sever_hello_extension() -> (o: SeverHelloExtensionCombinator)
    ensures o@ == spec_sever_hello_extension(),
{
    SeverHelloExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), SeverHelloExtensionCont1), SeverHelloExtensionCont0),
        mapper: SeverHelloExtensionMapper,
    })
}

pub struct SeverHelloExtensionCont1;
type SeverHelloExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type SeverHelloExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type SeverHelloExtensionCont1Input<'a, 'b, 'x> = POrSType<SeverHelloExtensionCont1Type<'a, 'b>, SeverHelloExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SeverHelloExtensionCont1Input<'a, 'b, 'x>> for SeverHelloExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: SeverHelloExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SeverHelloExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont1(deps@)
    }

    fn apply(&self, deps: SeverHelloExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct SeverHelloExtensionCont0;
type SeverHelloExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type SeverHelloExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type SeverHelloExtensionCont0Input<'a, 'b, 'x> = POrSType<SeverHelloExtensionCont0Type<'a, 'b>, SeverHelloExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SeverHelloExtensionCont0Input<'a, 'b, 'x>> for SeverHelloExtensionCont0 {
    type Output = SeverHelloExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: SeverHelloExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SeverHelloExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont0(deps@)
    }

    fn apply(&self, deps: SeverHelloExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                sever_hello_extension_extension_data(ext_len, extension_type)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                sever_hello_extension_extension_data(ext_len, extension_type)
            }
        }
    }
}
                

pub struct SpecServerExtensions {
    pub l: u16,
    pub list: Seq<SpecSeverHelloExtension>,
}

pub type SpecServerExtensionsInner = (u16, Seq<SpecSeverHelloExtension>);


impl SpecFrom<SpecServerExtensions> for SpecServerExtensionsInner {
    open spec fn spec_from(m: SpecServerExtensions) -> SpecServerExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecServerExtensionsInner> for SpecServerExtensions {
    open spec fn spec_from(m: SpecServerExtensionsInner) -> SpecServerExtensions {
        let (l, list) = m;
        SpecServerExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<SeverHelloExtension<'a>>,
}

impl View for ServerExtensions<'_> {
    type V = SpecServerExtensions;

    open spec fn view(&self) -> Self::V {
        SpecServerExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ServerExtensionsInner<'a> = (u16, RepeatResult<SeverHelloExtension<'a>>);

pub type ServerExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<SeverHelloExtension<'a>>);
impl<'a> From<&'a ServerExtensions<'a>> for ServerExtensionsInnerRef<'a> {
    fn ex_from(m: &'a ServerExtensions) -> ServerExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ServerExtensionsInner<'a>> for ServerExtensions<'a> {
    fn ex_from(m: ServerExtensionsInner) -> ServerExtensions {
        let (l, list) = m;
        ServerExtensions { l, list }
    }
}

pub struct ServerExtensionsMapper;
impl View for ServerExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerExtensionsMapper {
    type Src = SpecServerExtensionsInner;
    type Dst = SpecServerExtensions;
}
impl SpecIsoProof for ServerExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerExtensionsMapper {
    type Src = ServerExtensionsInner<'a>;
    type Dst = ServerExtensions<'a>;
    type RefSrc = ServerExtensionsInnerRef<'a>;
}

pub struct SpecServerExtensionsCombinator(SpecServerExtensionsCombinatorAlias);

impl SpecCombinator for SpecServerExtensionsCombinator {
    type Type = SpecServerExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerExtensionsCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate14496530480760116989>, AndThen<bytes::Variable, Repeat<SpecSeverHelloExtensionCombinator>>>, ServerExtensionsMapper>;

pub struct ServerExtensionsCombinator(ServerExtensionsCombinatorAlias);

impl View for ServerExtensionsCombinator {
    type V = SpecServerExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerExtensionsCombinator {
    type Type = ServerExtensions<'a>;
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
pub type ServerExtensionsCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate14496530480760116989>, AndThen<bytes::Variable, Repeat<SeverHelloExtensionCombinator>>, ServerExtensionsCont0>, ServerExtensionsMapper>;


pub closed spec fn spec_server_extensions() -> SpecServerExtensionsCombinator {
    SpecServerExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate14496530480760116989 }, |deps| spec_server_extensions_cont0(deps)),
        mapper: ServerExtensionsMapper,
    })
}

pub open spec fn spec_server_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecSeverHelloExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_sever_hello_extension()))
}

impl View for ServerExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecSeverHelloExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_server_extensions_cont0(deps)
        }
    }
}

                
pub fn server_extensions() -> (o: ServerExtensionsCombinator)
    ensures o@ == spec_server_extensions(),
{
    ServerExtensionsCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate14496530480760116989 }, ServerExtensionsCont0),
        mapper: ServerExtensionsMapper,
    })
}

pub struct ServerExtensionsCont0;
type ServerExtensionsCont0Type<'a, 'b> = &'b u16;
type ServerExtensionsCont0SType<'a, 'x> = &'x u16;
type ServerExtensionsCont0Input<'a, 'b, 'x> = POrSType<ServerExtensionsCont0Type<'a, 'b>, ServerExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ServerExtensionsCont0Input<'a, 'b, 'x>> for ServerExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<SeverHelloExtensionCombinator>>;

    open spec fn requires(&self, deps: ServerExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ServerExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_server_extensions_cont0(deps@)
    }

    fn apply(&self, deps: ServerExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(sever_hello_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(sever_hello_extension()))
            }
        }
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

pub type ServerHelloInnerRef<'a> = (&'a SessionId<'a>, (&'a CipherSuite, (&'a u8, &'a ServerExtensions<'a>)));
impl<'a> From<&'a ServerHello<'a>> for ServerHelloInnerRef<'a> {
    fn ex_from(m: &'a ServerHello) -> ServerHelloInnerRef<'a> {
        (&m.legacy_session_id_echo, (&m.cipher_suite, (&m.legacy_compression_method, &m.extensions)))
    }
}

impl<'a> From<ServerHelloInner<'a>> for ServerHello<'a> {
    fn ex_from(m: ServerHelloInner) -> ServerHello {
        let (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))) = m;
        ServerHello { legacy_session_id_echo, cipher_suite, legacy_compression_method, extensions }
    }
}

pub struct ServerHelloMapper;
impl View for ServerHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerHelloMapper {
    type Src = SpecServerHelloInner;
    type Dst = SpecServerHello;
}
impl SpecIsoProof for ServerHelloMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerHelloMapper {
    type Src = ServerHelloInner<'a>;
    type Dst = ServerHello<'a>;
    type RefSrc = ServerHelloInnerRef<'a>;
}
pub const SERVERHELLOLEGACY_COMPRESSION_METHOD_CONST: u8 = 0;
type SpecServerHelloCombinatorAlias1 = (Refined<U8, TagPred<u8>>, SpecServerExtensionsCombinator);
type SpecServerHelloCombinatorAlias2 = (SpecCipherSuiteCombinator, SpecServerHelloCombinatorAlias1);
type SpecServerHelloCombinatorAlias3 = (SpecSessionIdCombinator, SpecServerHelloCombinatorAlias2);
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
pub type SpecServerHelloCombinatorAlias = Mapped<SpecServerHelloCombinatorAlias3, ServerHelloMapper>;
type ServerHelloCombinatorAlias1 = (Refined<U8, TagPred<u8>>, ServerExtensionsCombinator);
type ServerHelloCombinatorAlias2 = (CipherSuiteCombinator, ServerHelloCombinator1);
type ServerHelloCombinatorAlias3 = (SessionIdCombinator, ServerHelloCombinator2);
struct ServerHelloCombinator1(ServerHelloCombinatorAlias1);
impl View for ServerHelloCombinator1 {
    type V = SpecServerHelloCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ServerHelloCombinator1, ServerHelloCombinatorAlias1);

struct ServerHelloCombinator2(ServerHelloCombinatorAlias2);
impl View for ServerHelloCombinator2 {
    type V = SpecServerHelloCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ServerHelloCombinator2, ServerHelloCombinatorAlias2);

struct ServerHelloCombinator3(ServerHelloCombinatorAlias3);
impl View for ServerHelloCombinator3 {
    type V = SpecServerHelloCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ServerHelloCombinator3, ServerHelloCombinatorAlias3);

pub struct ServerHelloCombinator(ServerHelloCombinatorAlias);

impl View for ServerHelloCombinator {
    type V = SpecServerHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerHelloCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerHelloCombinator {
    type Type = ServerHello<'a>;
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
pub type ServerHelloCombinatorAlias = Mapped<ServerHelloCombinator3, ServerHelloMapper>;


pub closed spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(
    Mapped {
        inner: (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLOLEGACY_COMPRESSION_METHOD_CONST) }, spec_server_extensions()))),
        mapper: ServerHelloMapper,
    })
}

                
pub fn server_hello() -> (o: ServerHelloCombinator)
    ensures o@ == spec_server_hello(),
{
    ServerHelloCombinator(
    Mapped {
        inner: ServerHelloCombinator3((session_id(), ServerHelloCombinator2((cipher_suite(), ServerHelloCombinator1((Refined { inner: U8, predicate: TagPred(SERVERHELLOLEGACY_COMPRESSION_METHOD_CONST) }, server_extensions())))))),
        mapper: ServerHelloMapper,
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

pub type ShOrHrrPayloadInnerRef<'a> = Either<&'a HelloRetryRequest<'a>, &'a ServerHello<'a>>;


impl<'a> View for ShOrHrrPayload<'a> {
    type V = SpecShOrHrrPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            ShOrHrrPayload::Variant0(m) => SpecShOrHrrPayload::Variant0(m@),
            ShOrHrrPayload::Variant1(m) => SpecShOrHrrPayload::Variant1(m@),
        }
    }
}


impl<'a> From<&'a ShOrHrrPayload<'a>> for ShOrHrrPayloadInnerRef<'a> {
    fn ex_from(m: &'a ShOrHrrPayload<'a>) -> ShOrHrrPayloadInnerRef<'a> {
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


pub struct ShOrHrrPayloadMapper;
impl View for ShOrHrrPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ShOrHrrPayloadMapper {
    type Src = SpecShOrHrrPayloadInner;
    type Dst = SpecShOrHrrPayload;
}
impl SpecIsoProof for ShOrHrrPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ShOrHrrPayloadMapper {
    type Src = ShOrHrrPayloadInner<'a>;
    type Dst = ShOrHrrPayload<'a>;
    type RefSrc = ShOrHrrPayloadInnerRef<'a>;
}

type SpecShOrHrrPayloadCombinatorAlias1 = Choice<Cond<SpecHelloRetryRequestCombinator>, Cond<SpecServerHelloCombinator>>;
pub struct SpecShOrHrrPayloadCombinator(SpecShOrHrrPayloadCombinatorAlias);

impl SpecCombinator for SpecShOrHrrPayloadCombinator {
    type Type = SpecShOrHrrPayload;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecShOrHrrPayloadCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShOrHrrPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecShOrHrrPayloadCombinatorAlias = Mapped<SpecShOrHrrPayloadCombinatorAlias1, ShOrHrrPayloadMapper>;
type ShOrHrrPayloadCombinatorAlias1 = Choice<Cond<HelloRetryRequestCombinator>, Cond<ServerHelloCombinator>>;
struct ShOrHrrPayloadCombinator1(ShOrHrrPayloadCombinatorAlias1);
impl View for ShOrHrrPayloadCombinator1 {
    type V = SpecShOrHrrPayloadCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ShOrHrrPayloadCombinator1, ShOrHrrPayloadCombinatorAlias1);

pub struct ShOrHrrPayloadCombinator(ShOrHrrPayloadCombinatorAlias);

impl View for ShOrHrrPayloadCombinator {
    type V = SpecShOrHrrPayloadCombinator;
    closed spec fn view(&self) -> Self::V { SpecShOrHrrPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ShOrHrrPayloadCombinator {
    type Type = ShOrHrrPayload<'a>;
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
pub type ShOrHrrPayloadCombinatorAlias = Mapped<ShOrHrrPayloadCombinator1, ShOrHrrPayloadMapper>;


pub closed spec fn spec_sh_or_hrr_payload(random: Seq<u8>) -> SpecShOrHrrPayloadCombinator {
    SpecShOrHrrPayloadCombinator(Mapped { inner: Choice(Cond { cond: random == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8], inner: spec_hello_retry_request() }, Cond { cond: !(random == seq![207u8, 33u8, 173u8, 116u8, 229u8, 154u8, 97u8, 17u8, 190u8, 29u8, 140u8, 2u8, 30u8, 101u8, 184u8, 145u8, 194u8, 162u8, 17u8, 22u8, 122u8, 187u8, 140u8, 94u8, 7u8, 158u8, 9u8, 226u8, 200u8, 168u8, 51u8, 156u8]), inner: spec_server_hello() }), mapper: ShOrHrrPayloadMapper })
}

pub fn sh_or_hrr_payload<'a>(random: &'a [u8]) -> (o: ShOrHrrPayloadCombinator)
    ensures o@ == spec_sh_or_hrr_payload(random@),
{
    ShOrHrrPayloadCombinator(Mapped { inner: ShOrHrrPayloadCombinator1(Choice::new(Cond { cond: compare_slice(random, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice()), inner: hello_retry_request() }, Cond { cond: !(compare_slice(random, [207, 33, 173, 116, 229, 154, 97, 17, 190, 29, 140, 2, 30, 101, 184, 145, 194, 162, 17, 22, 122, 187, 140, 94, 7, 158, 9, 226, 200, 168, 51, 156].as_slice())), inner: server_hello() })), mapper: ShOrHrrPayloadMapper })
}

pub type SpecEcPointFormat = u8;
pub type EcPointFormat = u8;
pub type EcPointFormatRef<'a> = &'a u8;


pub struct SpecEcPointFormatCombinator(SpecEcPointFormatCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatCombinator {
    type Type = SpecEcPointFormat;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEcPointFormatCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatCombinatorAlias::is_prefix_secure() }
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
pub type SpecEcPointFormatCombinatorAlias = U8;

pub struct EcPointFormatCombinator(EcPointFormatCombinatorAlias);

impl View for EcPointFormatCombinator {
    type V = SpecEcPointFormatCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EcPointFormatCombinator {
    type Type = EcPointFormat;
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
pub type EcPointFormatCombinatorAlias = U8;


pub closed spec fn spec_ec_point_format() -> SpecEcPointFormatCombinator {
    SpecEcPointFormatCombinator(U8)
}

                
pub fn ec_point_format() -> (o: EcPointFormatCombinator)
    ensures o@ == spec_ec_point_format(),
{
    EcPointFormatCombinator(U8)
}

                

pub struct SpecSrtpProtectionProfiles {
    pub l: u16,
    pub list: Seq<SpecSrtpProtectionProfile>,
}

pub type SpecSrtpProtectionProfilesInner = (u16, Seq<SpecSrtpProtectionProfile>);


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
    pub l: u16,
    pub list: RepeatResult<SrtpProtectionProfile<'a>>,
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
pub type SrtpProtectionProfilesInner<'a> = (u16, RepeatResult<SrtpProtectionProfile<'a>>);

pub type SrtpProtectionProfilesInnerRef<'a> = (&'a u16, &'a RepeatResult<SrtpProtectionProfile<'a>>);
impl<'a> From<&'a SrtpProtectionProfiles<'a>> for SrtpProtectionProfilesInnerRef<'a> {
    fn ex_from(m: &'a SrtpProtectionProfiles) -> SrtpProtectionProfilesInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<SrtpProtectionProfilesInner<'a>> for SrtpProtectionProfiles<'a> {
    fn ex_from(m: SrtpProtectionProfilesInner) -> SrtpProtectionProfiles {
        let (l, list) = m;
        SrtpProtectionProfiles { l, list }
    }
}

pub struct SrtpProtectionProfilesMapper;
impl View for SrtpProtectionProfilesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SrtpProtectionProfilesMapper {
    type Src = SpecSrtpProtectionProfilesInner;
    type Dst = SpecSrtpProtectionProfiles;
}
impl SpecIsoProof for SrtpProtectionProfilesMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SrtpProtectionProfilesMapper {
    type Src = SrtpProtectionProfilesInner<'a>;
    type Dst = SrtpProtectionProfiles<'a>;
    type RefSrc = SrtpProtectionProfilesInnerRef<'a>;
}

pub struct SpecSrtpProtectionProfilesCombinator(SpecSrtpProtectionProfilesCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfilesCombinator {
    type Type = SpecSrtpProtectionProfiles;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSrtpProtectionProfilesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfilesCombinatorAlias::is_prefix_secure() }
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
pub type SpecSrtpProtectionProfilesCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<SpecSrtpProtectionProfileCombinator>>>, SrtpProtectionProfilesMapper>;
pub struct Predicate8195707947578446211;
impl View for Predicate8195707947578446211 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate8195707947578446211 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate8195707947578446211 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}

pub struct SrtpProtectionProfilesCombinator(SrtpProtectionProfilesCombinatorAlias);

impl View for SrtpProtectionProfilesCombinator {
    type V = SpecSrtpProtectionProfilesCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfilesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SrtpProtectionProfilesCombinator {
    type Type = SrtpProtectionProfiles<'a>;
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
pub type SrtpProtectionProfilesCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<SrtpProtectionProfileCombinator>>, SrtpProtectionProfilesCont0>, SrtpProtectionProfilesMapper>;


pub closed spec fn spec_srtp_protection_profiles() -> SpecSrtpProtectionProfilesCombinator {
    SpecSrtpProtectionProfilesCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, |deps| spec_srtp_protection_profiles_cont0(deps)),
        mapper: SrtpProtectionProfilesMapper,
    })
}

pub open spec fn spec_srtp_protection_profiles_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecSrtpProtectionProfileCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_srtp_protection_profile()))
}

impl View for SrtpProtectionProfilesCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecSrtpProtectionProfileCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_srtp_protection_profiles_cont0(deps)
        }
    }
}

                
pub fn srtp_protection_profiles() -> (o: SrtpProtectionProfilesCombinator)
    ensures o@ == spec_srtp_protection_profiles(),
{
    SrtpProtectionProfilesCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, SrtpProtectionProfilesCont0),
        mapper: SrtpProtectionProfilesMapper,
    })
}

pub struct SrtpProtectionProfilesCont0;
type SrtpProtectionProfilesCont0Type<'a, 'b> = &'b u16;
type SrtpProtectionProfilesCont0SType<'a, 'x> = &'x u16;
type SrtpProtectionProfilesCont0Input<'a, 'b, 'x> = POrSType<SrtpProtectionProfilesCont0Type<'a, 'b>, SrtpProtectionProfilesCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SrtpProtectionProfilesCont0Input<'a, 'b, 'x>> for SrtpProtectionProfilesCont0 {
    type Output = AndThen<bytes::Variable, Repeat<SrtpProtectionProfileCombinator>>;

    open spec fn requires(&self, deps: SrtpProtectionProfilesCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SrtpProtectionProfilesCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_srtp_protection_profiles_cont0(deps@)
    }

    fn apply(&self, deps: SrtpProtectionProfilesCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(srtp_protection_profile()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(srtp_protection_profile()))
            }
        }
    }
}
                

pub struct SpecOpaque0Ff {
    pub l: u8,
    pub data: Seq<u8>,
}

pub type SpecOpaque0FfInner = (u8, Seq<u8>);


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
    pub l: u8,
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
pub type Opaque0FfInner<'a> = (u8, &'a [u8]);

pub type Opaque0FfInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a Opaque0Ff<'a>> for Opaque0FfInnerRef<'a> {
    fn ex_from(m: &'a Opaque0Ff) -> Opaque0FfInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque0FfInner<'a>> for Opaque0Ff<'a> {
    fn ex_from(m: Opaque0FfInner) -> Opaque0Ff {
        let (l, data) = m;
        Opaque0Ff { l, data }
    }
}

pub struct Opaque0FfMapper;
impl View for Opaque0FfMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfMapper {
    type Src = SpecOpaque0FfInner;
    type Dst = SpecOpaque0Ff;
}
impl SpecIsoProof for Opaque0FfMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque0FfMapper {
    type Src = Opaque0FfInner<'a>;
    type Dst = Opaque0Ff<'a>;
    type RefSrc = Opaque0FfInnerRef<'a>;
}

pub struct SpecOpaque0FfCombinator(SpecOpaque0FfCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfCombinator {
    type Type = SpecOpaque0Ff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque0FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque0FfCombinatorAlias = Mapped<SpecPair<U8, bytes::Variable>, Opaque0FfMapper>;

pub struct Opaque0FfCombinator(Opaque0FfCombinatorAlias);

impl View for Opaque0FfCombinator {
    type V = SpecOpaque0FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque0FfCombinator {
    type Type = Opaque0Ff<'a>;
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
pub type Opaque0FfCombinatorAlias = Mapped<Pair<U8, bytes::Variable, Opaque0FfCont0>, Opaque0FfMapper>;


pub closed spec fn spec_opaque_0_ff() -> SpecOpaque0FfCombinator {
    SpecOpaque0FfCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_opaque0_ff_cont0(deps)),
        mapper: Opaque0FfMapper,
    })
}

pub open spec fn spec_opaque0_ff_cont0(deps: u8) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque0FfCont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_opaque0_ff_cont0(deps)
        }
    }
}

                
pub fn opaque_0_ff() -> (o: Opaque0FfCombinator)
    ensures o@ == spec_opaque_0_ff(),
{
    Opaque0FfCombinator(
    Mapped {
        inner: Pair::new(U8, Opaque0FfCont0),
        mapper: Opaque0FfMapper,
    })
}

pub struct Opaque0FfCont0;
type Opaque0FfCont0Type<'a, 'b> = &'b u8;
type Opaque0FfCont0SType<'a, 'x> = &'x u8;
type Opaque0FfCont0Input<'a, 'b, 'x> = POrSType<Opaque0FfCont0Type<'a, 'b>, Opaque0FfCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque0FfCont0Input<'a, 'b, 'x>> for Opaque0FfCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque0FfCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque0FfCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque0_ff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque0FfCont0Input<'a, 'b, 'x>) -> Self::Output {
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

pub type UseSrtpDataInnerRef<'a> = (&'a SrtpProtectionProfiles<'a>, &'a Opaque0Ff<'a>);
impl<'a> From<&'a UseSrtpData<'a>> for UseSrtpDataInnerRef<'a> {
    fn ex_from(m: &'a UseSrtpData) -> UseSrtpDataInnerRef<'a> {
        (&m.profiles, &m.srtp_mki)
    }
}

impl<'a> From<UseSrtpDataInner<'a>> for UseSrtpData<'a> {
    fn ex_from(m: UseSrtpDataInner) -> UseSrtpData {
        let (profiles, srtp_mki) = m;
        UseSrtpData { profiles, srtp_mki }
    }
}

pub struct UseSrtpDataMapper;
impl View for UseSrtpDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UseSrtpDataMapper {
    type Src = SpecUseSrtpDataInner;
    type Dst = SpecUseSrtpData;
}
impl SpecIsoProof for UseSrtpDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for UseSrtpDataMapper {
    type Src = UseSrtpDataInner<'a>;
    type Dst = UseSrtpData<'a>;
    type RefSrc = UseSrtpDataInnerRef<'a>;
}
type SpecUseSrtpDataCombinatorAlias1 = (SpecSrtpProtectionProfilesCombinator, SpecOpaque0FfCombinator);
pub struct SpecUseSrtpDataCombinator(SpecUseSrtpDataCombinatorAlias);

impl SpecCombinator for SpecUseSrtpDataCombinator {
    type Type = SpecUseSrtpData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecUseSrtpDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUseSrtpDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecUseSrtpDataCombinatorAlias = Mapped<SpecUseSrtpDataCombinatorAlias1, UseSrtpDataMapper>;
type UseSrtpDataCombinatorAlias1 = (SrtpProtectionProfilesCombinator, Opaque0FfCombinator);
struct UseSrtpDataCombinator1(UseSrtpDataCombinatorAlias1);
impl View for UseSrtpDataCombinator1 {
    type V = SpecUseSrtpDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(UseSrtpDataCombinator1, UseSrtpDataCombinatorAlias1);

pub struct UseSrtpDataCombinator(UseSrtpDataCombinatorAlias);

impl View for UseSrtpDataCombinator {
    type V = SpecUseSrtpDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecUseSrtpDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for UseSrtpDataCombinator {
    type Type = UseSrtpData<'a>;
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
pub type UseSrtpDataCombinatorAlias = Mapped<UseSrtpDataCombinator1, UseSrtpDataMapper>;


pub closed spec fn spec_use_srtp_data() -> SpecUseSrtpDataCombinator {
    SpecUseSrtpDataCombinator(
    Mapped {
        inner: (spec_srtp_protection_profiles(), spec_opaque_0_ff()),
        mapper: UseSrtpDataMapper,
    })
}

                
pub fn use_srtp_data() -> (o: UseSrtpDataCombinator)
    ensures o@ == spec_use_srtp_data(),
{
    UseSrtpDataCombinator(
    Mapped {
        inner: UseSrtpDataCombinator1((srtp_protection_profiles(), opaque_0_ff())),
        mapper: UseSrtpDataMapper,
    })
}

                

pub spec const SPEC_ContentType_Invalid: u8 = 0;
pub spec const SPEC_ContentType_ChangeCipherSpec: u8 = 20;
pub spec const SPEC_ContentType_Alert: u8 = 21;
pub spec const SPEC_ContentType_Handshake: u8 = 22;
pub spec const SPEC_ContentType_ApplicationData: u8 = 23;
pub exec static EXEC_ContentType_Invalid: u8 ensures EXEC_ContentType_Invalid == SPEC_ContentType_Invalid { 0 }
pub exec static EXEC_ContentType_ChangeCipherSpec: u8 ensures EXEC_ContentType_ChangeCipherSpec == SPEC_ContentType_ChangeCipherSpec { 20 }
pub exec static EXEC_ContentType_Alert: u8 ensures EXEC_ContentType_Alert == SPEC_ContentType_Alert { 21 }
pub exec static EXEC_ContentType_Handshake: u8 ensures EXEC_ContentType_Handshake == SPEC_ContentType_Handshake { 22 }
pub exec static EXEC_ContentType_ApplicationData: u8 ensures EXEC_ContentType_ApplicationData == SPEC_ContentType_ApplicationData { 23 }

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

pub type ContentTypeInnerRef<'a> = &'a u8;

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
            ContentType::Invalid => Ok(SPEC_ContentType_Invalid),
            ContentType::ChangeCipherSpec => Ok(SPEC_ContentType_ChangeCipherSpec),
            ContentType::Alert => Ok(SPEC_ContentType_Alert),
            ContentType::Handshake => Ok(SPEC_ContentType_Handshake),
            ContentType::ApplicationData => Ok(SPEC_ContentType_ApplicationData),
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

impl<'a> TryFrom<&'a ContentType> for ContentTypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a ContentType) -> Result<ContentTypeInnerRef<'a>, ()> {
        match v {
            ContentType::Invalid => Ok(&EXEC_ContentType_Invalid),
            ContentType::ChangeCipherSpec => Ok(&EXEC_ContentType_ChangeCipherSpec),
            ContentType::Alert => Ok(&EXEC_ContentType_Alert),
            ContentType::Handshake => Ok(&EXEC_ContentType_Handshake),
            ContentType::ApplicationData => Ok(&EXEC_ContentType_ApplicationData),
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

impl SpecPartialIso for ContentTypeMapper {
    type Src = ContentTypeInner;
    type Dst = ContentType;
}

impl SpecPartialIsoProof for ContentTypeMapper {
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

impl<'a> PartialIso<'a> for ContentTypeMapper {
    type Src = ContentTypeInner;
    type Dst = ContentType;
    type RefSrc = ContentTypeInnerRef<'a>;
}


pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type Type = SpecContentType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecContentTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;

pub struct ContentTypeCombinator(ContentTypeCombinatorAlias);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecContentTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ContentTypeCombinator {
    type Type = ContentType;
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
pub type ContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;


pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}

                
pub fn content_type() -> (o: ContentTypeCombinator)
    ensures o@ == spec_content_type(),
{
    ContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}

                

pub struct SpecSignatureSchemeList {
    pub l: u16,
    pub list: Seq<SpecSignatureScheme>,
}

pub type SpecSignatureSchemeListInner = (u16, Seq<SpecSignatureScheme>);


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
    pub l: u16,
    pub list: RepeatResult<SignatureScheme>,
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
pub type SignatureSchemeListInner = (u16, RepeatResult<SignatureScheme>);

pub type SignatureSchemeListInnerRef<'a> = (&'a u16, &'a RepeatResult<SignatureScheme>);
impl<'a> From<&'a SignatureSchemeList> for SignatureSchemeListInnerRef<'a> {
    fn ex_from(m: &'a SignatureSchemeList) -> SignatureSchemeListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<SignatureSchemeListInner> for SignatureSchemeList {
    fn ex_from(m: SignatureSchemeListInner) -> SignatureSchemeList {
        let (l, list) = m;
        SignatureSchemeList { l, list }
    }
}

pub struct SignatureSchemeListMapper;
impl View for SignatureSchemeListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignatureSchemeListMapper {
    type Src = SpecSignatureSchemeListInner;
    type Dst = SpecSignatureSchemeList;
}
impl SpecIsoProof for SignatureSchemeListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SignatureSchemeListMapper {
    type Src = SignatureSchemeListInner;
    type Dst = SignatureSchemeList;
    type RefSrc = SignatureSchemeListInnerRef<'a>;
}

pub struct SpecSignatureSchemeListCombinator(SpecSignatureSchemeListCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeListCombinator {
    type Type = SpecSignatureSchemeList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSignatureSchemeListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeListCombinatorAlias::is_prefix_secure() }
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
pub type SpecSignatureSchemeListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate15206902916018849611>, AndThen<bytes::Variable, Repeat<SpecSignatureSchemeCombinator>>>, SignatureSchemeListMapper>;
pub struct Predicate15206902916018849611;
impl View for Predicate15206902916018849611 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate15206902916018849611 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65534)
    }
}
impl SpecPred<u16> for Predicate15206902916018849611 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65534)
    }
}

pub struct SignatureSchemeListCombinator(SignatureSchemeListCombinatorAlias);

impl View for SignatureSchemeListCombinator {
    type V = SpecSignatureSchemeListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SignatureSchemeListCombinator {
    type Type = SignatureSchemeList;
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
pub type SignatureSchemeListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate15206902916018849611>, AndThen<bytes::Variable, Repeat<SignatureSchemeCombinator>>, SignatureSchemeListCont0>, SignatureSchemeListMapper>;


pub closed spec fn spec_signature_scheme_list() -> SpecSignatureSchemeListCombinator {
    SpecSignatureSchemeListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate15206902916018849611 }, |deps| spec_signature_scheme_list_cont0(deps)),
        mapper: SignatureSchemeListMapper,
    })
}

pub open spec fn spec_signature_scheme_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecSignatureSchemeCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_signature_scheme()))
}

impl View for SignatureSchemeListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecSignatureSchemeCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_signature_scheme_list_cont0(deps)
        }
    }
}

                
pub fn signature_scheme_list() -> (o: SignatureSchemeListCombinator)
    ensures o@ == spec_signature_scheme_list(),
{
    SignatureSchemeListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate15206902916018849611 }, SignatureSchemeListCont0),
        mapper: SignatureSchemeListMapper,
    })
}

pub struct SignatureSchemeListCont0;
type SignatureSchemeListCont0Type<'a, 'b> = &'b u16;
type SignatureSchemeListCont0SType<'a, 'x> = &'x u16;
type SignatureSchemeListCont0Input<'a, 'b, 'x> = POrSType<SignatureSchemeListCont0Type<'a, 'b>, SignatureSchemeListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SignatureSchemeListCont0Input<'a, 'b, 'x>> for SignatureSchemeListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<SignatureSchemeCombinator>>;

    open spec fn requires(&self, deps: SignatureSchemeListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SignatureSchemeListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_signature_scheme_list_cont0(deps@)
    }

    fn apply(&self, deps: SignatureSchemeListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(signature_scheme()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(signature_scheme()))
            }
        }
    }
}
                
pub type SpecHeartbeatMode = u8;
pub type HeartbeatMode = u8;
pub type HeartbeatModeRef<'a> = &'a u8;


pub struct SpecHeartbeatModeCombinator(SpecHeartbeatModeCombinatorAlias);

impl SpecCombinator for SpecHeartbeatModeCombinator {
    type Type = SpecHeartbeatMode;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHeartbeatModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatModeCombinatorAlias::is_prefix_secure() }
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
pub type SpecHeartbeatModeCombinatorAlias = U8;

pub struct HeartbeatModeCombinator(HeartbeatModeCombinatorAlias);

impl View for HeartbeatModeCombinator {
    type V = SpecHeartbeatModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatModeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HeartbeatModeCombinator {
    type Type = HeartbeatMode;
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
pub type HeartbeatModeCombinatorAlias = U8;


pub closed spec fn spec_heartbeat_mode() -> SpecHeartbeatModeCombinator {
    SpecHeartbeatModeCombinator(U8)
}

                
pub fn heartbeat_mode() -> (o: HeartbeatModeCombinator)
    ensures o@ == spec_heartbeat_mode(),
{
    HeartbeatModeCombinator(U8)
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

pub type HeartbeatExtensionInnerRef<'a> = &'a HeartbeatMode;
impl<'a> From<&'a HeartbeatExtension> for HeartbeatExtensionInnerRef<'a> {
    fn ex_from(m: &'a HeartbeatExtension) -> HeartbeatExtensionInnerRef<'a> {
        &m.mode
    }
}

impl From<HeartbeatExtensionInner> for HeartbeatExtension {
    fn ex_from(m: HeartbeatExtensionInner) -> HeartbeatExtension {
        let mode = m;
        HeartbeatExtension { mode }
    }
}

pub struct HeartbeatExtensionMapper;
impl View for HeartbeatExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HeartbeatExtensionMapper {
    type Src = SpecHeartbeatExtensionInner;
    type Dst = SpecHeartbeatExtension;
}
impl SpecIsoProof for HeartbeatExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HeartbeatExtensionMapper {
    type Src = HeartbeatExtensionInner;
    type Dst = HeartbeatExtension;
    type RefSrc = HeartbeatExtensionInnerRef<'a>;
}

pub struct SpecHeartbeatExtensionCombinator(SpecHeartbeatExtensionCombinatorAlias);

impl SpecCombinator for SpecHeartbeatExtensionCombinator {
    type Type = SpecHeartbeatExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHeartbeatExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecHeartbeatExtensionCombinatorAlias = Mapped<SpecHeartbeatModeCombinator, HeartbeatExtensionMapper>;

pub struct HeartbeatExtensionCombinator(HeartbeatExtensionCombinatorAlias);

impl View for HeartbeatExtensionCombinator {
    type V = SpecHeartbeatExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HeartbeatExtensionCombinator {
    type Type = HeartbeatExtension;
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
pub type HeartbeatExtensionCombinatorAlias = Mapped<HeartbeatModeCombinator, HeartbeatExtensionMapper>;


pub closed spec fn spec_heartbeat_extension() -> SpecHeartbeatExtensionCombinator {
    SpecHeartbeatExtensionCombinator(
    Mapped {
        inner: spec_heartbeat_mode(),
        mapper: HeartbeatExtensionMapper,
    })
}

                
pub fn heartbeat_extension() -> (o: HeartbeatExtensionCombinator)
    ensures o@ == spec_heartbeat_extension(),
{
    HeartbeatExtensionCombinator(
    Mapped {
        inner: heartbeat_mode(),
        mapper: HeartbeatExtensionMapper,
    })
}

                
pub type SpecDigestSize = u24;
pub type DigestSize = u24;
pub type DigestSizeRef<'a> = &'a u24;


pub struct SpecDigestSizeCombinator(SpecDigestSizeCombinatorAlias);

impl SpecCombinator for SpecDigestSizeCombinator {
    type Type = SpecDigestSize;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDigestSizeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDigestSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecDigestSizeCombinatorAlias = U24Be;

pub struct DigestSizeCombinator(DigestSizeCombinatorAlias);

impl View for DigestSizeCombinator {
    type V = SpecDigestSizeCombinator;
    closed spec fn view(&self) -> Self::V { SpecDigestSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DigestSizeCombinator {
    type Type = DigestSize;
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
pub type DigestSizeCombinatorAlias = U24Be;


pub closed spec fn spec_digest_size() -> SpecDigestSizeCombinator {
    SpecDigestSizeCombinator(U24Be)
}

                
pub fn digest_size() -> (o: DigestSizeCombinator)
    ensures o@ == spec_digest_size(),
{
    DigestSizeCombinator(U24Be)
}

                

pub struct SpecOpaque1Ff {
    pub l: u8,
    pub data: Seq<u8>,
}

pub type SpecOpaque1FfInner = (u8, Seq<u8>);


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
    pub l: u8,
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
pub type Opaque1FfInner<'a> = (u8, &'a [u8]);

pub type Opaque1FfInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a Opaque1Ff<'a>> for Opaque1FfInnerRef<'a> {
    fn ex_from(m: &'a Opaque1Ff) -> Opaque1FfInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque1FfInner<'a>> for Opaque1Ff<'a> {
    fn ex_from(m: Opaque1FfInner) -> Opaque1Ff {
        let (l, data) = m;
        Opaque1Ff { l, data }
    }
}

pub struct Opaque1FfMapper;
impl View for Opaque1FfMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfMapper {
    type Src = SpecOpaque1FfInner;
    type Dst = SpecOpaque1Ff;
}
impl SpecIsoProof for Opaque1FfMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque1FfMapper {
    type Src = Opaque1FfInner<'a>;
    type Dst = Opaque1Ff<'a>;
    type RefSrc = Opaque1FfInnerRef<'a>;
}

pub struct SpecOpaque1FfCombinator(SpecOpaque1FfCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfCombinator {
    type Type = SpecOpaque1Ff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque1FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque1FfCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate3651688686135228051>, bytes::Variable>, Opaque1FfMapper>;
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

pub struct Opaque1FfCombinator(Opaque1FfCombinatorAlias);

impl View for Opaque1FfCombinator {
    type V = SpecOpaque1FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque1FfCombinator {
    type Type = Opaque1Ff<'a>;
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
pub type Opaque1FfCombinatorAlias = Mapped<Pair<Refined<U8, Predicate3651688686135228051>, bytes::Variable, Opaque1FfCont0>, Opaque1FfMapper>;


pub closed spec fn spec_opaque_1_ff() -> SpecOpaque1FfCombinator {
    SpecOpaque1FfCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, |deps| spec_opaque1_ff_cont0(deps)),
        mapper: Opaque1FfMapper,
    })
}

pub open spec fn spec_opaque1_ff_cont0(deps: u8) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque1FfCont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_opaque1_ff_cont0(deps)
        }
    }
}

                
pub fn opaque_1_ff() -> (o: Opaque1FfCombinator)
    ensures o@ == spec_opaque_1_ff(),
{
    Opaque1FfCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate3651688686135228051 }, Opaque1FfCont0),
        mapper: Opaque1FfMapper,
    })
}

pub struct Opaque1FfCont0;
type Opaque1FfCont0Type<'a, 'b> = &'b u8;
type Opaque1FfCont0SType<'a, 'x> = &'x u8;
type Opaque1FfCont0Input<'a, 'b, 'x> = POrSType<Opaque1FfCont0Type<'a, 'b>, Opaque1FfCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque1FfCont0Input<'a, 'b, 'x>> for Opaque1FfCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque1FfCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque1FfCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque1_ff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque1FfCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                
pub type SpecProtocolName = SpecOpaque1Ff;
pub type ProtocolName<'a> = Opaque1Ff<'a>;
pub type ProtocolNameRef<'a> = &'a Opaque1Ff<'a>;


pub struct SpecProtocolNameCombinator(SpecProtocolNameCombinatorAlias);

impl SpecCombinator for SpecProtocolNameCombinator {
    type Type = SpecProtocolName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProtocolNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecProtocolNameCombinatorAlias = SpecOpaque1FfCombinator;

pub struct ProtocolNameCombinator(ProtocolNameCombinatorAlias);

impl View for ProtocolNameCombinator {
    type V = SpecProtocolNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProtocolNameCombinator {
    type Type = ProtocolName<'a>;
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
pub type ProtocolNameCombinatorAlias = Opaque1FfCombinator;


pub closed spec fn spec_protocol_name() -> SpecProtocolNameCombinator {
    SpecProtocolNameCombinator(spec_opaque_1_ff())
}

                
pub fn protocol_name() -> (o: ProtocolNameCombinator)
    ensures o@ == spec_protocol_name(),
{
    ProtocolNameCombinator(opaque_1_ff())
}

                

pub struct SpecProtocolNameList {
    pub l: u16,
    pub list: Seq<SpecProtocolName>,
}

pub type SpecProtocolNameListInner = (u16, Seq<SpecProtocolName>);


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
    pub l: u16,
    pub list: RepeatResult<ProtocolName<'a>>,
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
pub type ProtocolNameListInner<'a> = (u16, RepeatResult<ProtocolName<'a>>);

pub type ProtocolNameListInnerRef<'a> = (&'a u16, &'a RepeatResult<ProtocolName<'a>>);
impl<'a> From<&'a ProtocolNameList<'a>> for ProtocolNameListInnerRef<'a> {
    fn ex_from(m: &'a ProtocolNameList) -> ProtocolNameListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ProtocolNameListInner<'a>> for ProtocolNameList<'a> {
    fn ex_from(m: ProtocolNameListInner) -> ProtocolNameList {
        let (l, list) = m;
        ProtocolNameList { l, list }
    }
}

pub struct ProtocolNameListMapper;
impl View for ProtocolNameListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProtocolNameListMapper {
    type Src = SpecProtocolNameListInner;
    type Dst = SpecProtocolNameList;
}
impl SpecIsoProof for ProtocolNameListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ProtocolNameListMapper {
    type Src = ProtocolNameListInner<'a>;
    type Dst = ProtocolNameList<'a>;
    type RefSrc = ProtocolNameListInnerRef<'a>;
}

pub struct SpecProtocolNameListCombinator(SpecProtocolNameListCombinatorAlias);

impl SpecCombinator for SpecProtocolNameListCombinator {
    type Type = SpecProtocolNameList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecProtocolNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameListCombinatorAlias::is_prefix_secure() }
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
pub type SpecProtocolNameListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<SpecProtocolNameCombinator>>>, ProtocolNameListMapper>;

pub struct ProtocolNameListCombinator(ProtocolNameListCombinatorAlias);

impl View for ProtocolNameListCombinator {
    type V = SpecProtocolNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ProtocolNameListCombinator {
    type Type = ProtocolNameList<'a>;
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
pub type ProtocolNameListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<ProtocolNameCombinator>>, ProtocolNameListCont0>, ProtocolNameListMapper>;


pub closed spec fn spec_protocol_name_list() -> SpecProtocolNameListCombinator {
    SpecProtocolNameListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, |deps| spec_protocol_name_list_cont0(deps)),
        mapper: ProtocolNameListMapper,
    })
}

pub open spec fn spec_protocol_name_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecProtocolNameCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_protocol_name()))
}

impl View for ProtocolNameListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecProtocolNameCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_protocol_name_list_cont0(deps)
        }
    }
}

                
pub fn protocol_name_list() -> (o: ProtocolNameListCombinator)
    ensures o@ == spec_protocol_name_list(),
{
    ProtocolNameListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, ProtocolNameListCont0),
        mapper: ProtocolNameListMapper,
    })
}

pub struct ProtocolNameListCont0;
type ProtocolNameListCont0Type<'a, 'b> = &'b u16;
type ProtocolNameListCont0SType<'a, 'x> = &'x u16;
type ProtocolNameListCont0Input<'a, 'b, 'x> = POrSType<ProtocolNameListCont0Type<'a, 'b>, ProtocolNameListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ProtocolNameListCont0Input<'a, 'b, 'x>> for ProtocolNameListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ProtocolNameCombinator>>;

    open spec fn requires(&self, deps: ProtocolNameListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ProtocolNameListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_protocol_name_list_cont0(deps@)
    }

    fn apply(&self, deps: ProtocolNameListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(protocol_name()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(protocol_name()))
            }
        }
    }
}
                
pub type SpecSerializedSct = SpecOpaque1Ffff;
pub type SerializedSct<'a> = Opaque1Ffff<'a>;
pub type SerializedSctRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecSerializedSctCombinator(SpecSerializedSctCombinatorAlias);

impl SpecCombinator for SpecSerializedSctCombinator {
    type Type = SpecSerializedSct;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSerializedSctCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSerializedSctCombinatorAlias::is_prefix_secure() }
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
pub type SpecSerializedSctCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct SerializedSctCombinator(SerializedSctCombinatorAlias);

impl View for SerializedSctCombinator {
    type V = SpecSerializedSctCombinator;
    closed spec fn view(&self) -> Self::V { SpecSerializedSctCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SerializedSctCombinator {
    type Type = SerializedSct<'a>;
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
pub type SerializedSctCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_serialized_sct() -> SpecSerializedSctCombinator {
    SpecSerializedSctCombinator(spec_opaque_1_ffff())
}

                
pub fn serialized_sct() -> (o: SerializedSctCombinator)
    ensures o@ == spec_serialized_sct(),
{
    SerializedSctCombinator(opaque_1_ffff())
}

                

pub struct SpecSignedCertificateTimestampList {
    pub l: u16,
    pub list: Seq<SpecSerializedSct>,
}

pub type SpecSignedCertificateTimestampListInner = (u16, Seq<SpecSerializedSct>);


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
    pub l: u16,
    pub list: RepeatResult<SerializedSct<'a>>,
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
pub type SignedCertificateTimestampListInner<'a> = (u16, RepeatResult<SerializedSct<'a>>);

pub type SignedCertificateTimestampListInnerRef<'a> = (&'a u16, &'a RepeatResult<SerializedSct<'a>>);
impl<'a> From<&'a SignedCertificateTimestampList<'a>> for SignedCertificateTimestampListInnerRef<'a> {
    fn ex_from(m: &'a SignedCertificateTimestampList) -> SignedCertificateTimestampListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<SignedCertificateTimestampListInner<'a>> for SignedCertificateTimestampList<'a> {
    fn ex_from(m: SignedCertificateTimestampListInner) -> SignedCertificateTimestampList {
        let (l, list) = m;
        SignedCertificateTimestampList { l, list }
    }
}

pub struct SignedCertificateTimestampListMapper;
impl View for SignedCertificateTimestampListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignedCertificateTimestampListMapper {
    type Src = SpecSignedCertificateTimestampListInner;
    type Dst = SpecSignedCertificateTimestampList;
}
impl SpecIsoProof for SignedCertificateTimestampListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SignedCertificateTimestampListMapper {
    type Src = SignedCertificateTimestampListInner<'a>;
    type Dst = SignedCertificateTimestampList<'a>;
    type RefSrc = SignedCertificateTimestampListInnerRef<'a>;
}

pub struct SpecSignedCertificateTimestampListCombinator(SpecSignedCertificateTimestampListCombinatorAlias);

impl SpecCombinator for SpecSignedCertificateTimestampListCombinator {
    type Type = SpecSignedCertificateTimestampList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSignedCertificateTimestampListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignedCertificateTimestampListCombinatorAlias::is_prefix_secure() }
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
pub type SpecSignedCertificateTimestampListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate16977634203518580913>, AndThen<bytes::Variable, Repeat<SpecSerializedSctCombinator>>>, SignedCertificateTimestampListMapper>;

pub struct SignedCertificateTimestampListCombinator(SignedCertificateTimestampListCombinatorAlias);

impl View for SignedCertificateTimestampListCombinator {
    type V = SpecSignedCertificateTimestampListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignedCertificateTimestampListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SignedCertificateTimestampListCombinator {
    type Type = SignedCertificateTimestampList<'a>;
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
pub type SignedCertificateTimestampListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate16977634203518580913>, AndThen<bytes::Variable, Repeat<SerializedSctCombinator>>, SignedCertificateTimestampListCont0>, SignedCertificateTimestampListMapper>;


pub closed spec fn spec_signed_certificate_timestamp_list() -> SpecSignedCertificateTimestampListCombinator {
    SpecSignedCertificateTimestampListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate16977634203518580913 }, |deps| spec_signed_certificate_timestamp_list_cont0(deps)),
        mapper: SignedCertificateTimestampListMapper,
    })
}

pub open spec fn spec_signed_certificate_timestamp_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecSerializedSctCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_serialized_sct()))
}

impl View for SignedCertificateTimestampListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecSerializedSctCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_signed_certificate_timestamp_list_cont0(deps)
        }
    }
}

                
pub fn signed_certificate_timestamp_list() -> (o: SignedCertificateTimestampListCombinator)
    ensures o@ == spec_signed_certificate_timestamp_list(),
{
    SignedCertificateTimestampListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate16977634203518580913 }, SignedCertificateTimestampListCont0),
        mapper: SignedCertificateTimestampListMapper,
    })
}

pub struct SignedCertificateTimestampListCont0;
type SignedCertificateTimestampListCont0Type<'a, 'b> = &'b u16;
type SignedCertificateTimestampListCont0SType<'a, 'x> = &'x u16;
type SignedCertificateTimestampListCont0Input<'a, 'b, 'x> = POrSType<SignedCertificateTimestampListCont0Type<'a, 'b>, SignedCertificateTimestampListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SignedCertificateTimestampListCont0Input<'a, 'b, 'x>> for SignedCertificateTimestampListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<SerializedSctCombinator>>;

    open spec fn requires(&self, deps: SignedCertificateTimestampListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SignedCertificateTimestampListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_signed_certificate_timestamp_list_cont0(deps@)
    }

    fn apply(&self, deps: SignedCertificateTimestampListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(serialized_sct()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(serialized_sct()))
            }
        }
    }
}
                
pub type SpecCertificateType = u8;
pub type CertificateType = u8;
pub type CertificateTypeRef<'a> = &'a u8;


pub struct SpecCertificateTypeCombinator(SpecCertificateTypeCombinatorAlias);

impl SpecCombinator for SpecCertificateTypeCombinator {
    type Type = SpecCertificateType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateTypeCombinatorAlias = U8;

pub struct CertificateTypeCombinator(CertificateTypeCombinatorAlias);

impl View for CertificateTypeCombinator {
    type V = SpecCertificateTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateTypeCombinator {
    type Type = CertificateType;
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
pub type CertificateTypeCombinatorAlias = U8;


pub closed spec fn spec_certificate_type() -> SpecCertificateTypeCombinator {
    SpecCertificateTypeCombinator(U8)
}

                
pub fn certificate_type() -> (o: CertificateTypeCombinator)
    ensures o@ == spec_certificate_type(),
{
    CertificateTypeCombinator(U8)
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

pub type Opaque1FfffffInnerRef<'a> = (&'a u24, &'a &'a [u8]);
impl<'a> From<&'a Opaque1Ffffff<'a>> for Opaque1FfffffInnerRef<'a> {
    fn ex_from(m: &'a Opaque1Ffffff) -> Opaque1FfffffInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque1FfffffInner<'a>> for Opaque1Ffffff<'a> {
    fn ex_from(m: Opaque1FfffffInner) -> Opaque1Ffffff {
        let (l, data) = m;
        Opaque1Ffffff { l, data }
    }
}

pub struct Opaque1FfffffMapper;
impl View for Opaque1FfffffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffffMapper {
    type Src = SpecOpaque1FfffffInner;
    type Dst = SpecOpaque1Ffffff;
}
impl SpecIsoProof for Opaque1FfffffMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque1FfffffMapper {
    type Src = Opaque1FfffffInner<'a>;
    type Dst = Opaque1Ffffff<'a>;
    type RefSrc = Opaque1FfffffInnerRef<'a>;
}

pub struct SpecOpaque1FfffffCombinator(SpecOpaque1FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffffCombinator {
    type Type = SpecOpaque1Ffffff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque1FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffffCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque1FfffffCombinatorAlias = Mapped<SpecPair<Refined<U24Be, Predicate15036445817960576151>, bytes::Variable>, Opaque1FfffffMapper>;
pub struct Predicate15036445817960576151;
impl View for Predicate15036445817960576151 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u24> for Predicate15036445817960576151 {
    fn apply(&self, i: &u24) -> bool {
        let i = (*i).as_u32();
        (i >= 1 && i <= 16777215)
    }
}
impl SpecPred<u24> for Predicate15036445817960576151 {
    open spec fn spec_apply(&self, i: &u24) -> bool {
        let i = (*i).spec_as_u32();
        (i >= 1 && i <= 16777215)
    }
}

pub struct Opaque1FfffffCombinator(Opaque1FfffffCombinatorAlias);

impl View for Opaque1FfffffCombinator {
    type V = SpecOpaque1FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffffCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque1FfffffCombinator {
    type Type = Opaque1Ffffff<'a>;
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
pub type Opaque1FfffffCombinatorAlias = Mapped<Pair<Refined<U24Be, Predicate15036445817960576151>, bytes::Variable, Opaque1FfffffCont0>, Opaque1FfffffMapper>;


pub closed spec fn spec_opaque_1_ffffff() -> SpecOpaque1FfffffCombinator {
    SpecOpaque1FfffffCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U24Be, predicate: Predicate15036445817960576151 }, |deps| spec_opaque1_ffffff_cont0(deps)),
        mapper: Opaque1FfffffMapper,
    })
}

pub open spec fn spec_opaque1_ffffff_cont0(deps: u24) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque1FfffffCont0 {
    type V = spec_fn(u24) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u24| {
            spec_opaque1_ffffff_cont0(deps)
        }
    }
}

                
pub fn opaque_1_ffffff() -> (o: Opaque1FfffffCombinator)
    ensures o@ == spec_opaque_1_ffffff(),
{
    Opaque1FfffffCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U24Be, predicate: Predicate15036445817960576151 }, Opaque1FfffffCont0),
        mapper: Opaque1FfffffMapper,
    })
}

pub struct Opaque1FfffffCont0;
type Opaque1FfffffCont0Type<'a, 'b> = &'b u24;
type Opaque1FfffffCont0SType<'a, 'x> = &'x u24;
type Opaque1FfffffCont0Input<'a, 'b, 'x> = POrSType<Opaque1FfffffCont0Type<'a, 'b>, Opaque1FfffffCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque1FfffffCont0Input<'a, 'b, 'x>> for Opaque1FfffffCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque1FfffffCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque1FfffffCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffffff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque1FfffffCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                
pub type SpecOcspResponse = SpecOpaque1Ffffff;
pub type OcspResponse<'a> = Opaque1Ffffff<'a>;
pub type OcspResponseRef<'a> = &'a Opaque1Ffffff<'a>;


pub struct SpecOcspResponseCombinator(SpecOcspResponseCombinatorAlias);

impl SpecCombinator for SpecOcspResponseCombinator {
    type Type = SpecOcspResponse;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOcspResponseCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspResponseCombinatorAlias::is_prefix_secure() }
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
pub type SpecOcspResponseCombinatorAlias = SpecOpaque1FfffffCombinator;

pub struct OcspResponseCombinator(OcspResponseCombinatorAlias);

impl View for OcspResponseCombinator {
    type V = SpecOcspResponseCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspResponseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OcspResponseCombinator {
    type Type = OcspResponse<'a>;
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
pub type OcspResponseCombinatorAlias = Opaque1FfffffCombinator;


pub closed spec fn spec_ocsp_response() -> SpecOcspResponseCombinator {
    SpecOcspResponseCombinator(spec_opaque_1_ffffff())
}

                
pub fn ocsp_response() -> (o: OcspResponseCombinator)
    ensures o@ == spec_ocsp_response(),
{
    OcspResponseCombinator(opaque_1_ffffff())
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

pub type PskBinderEntryInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a PskBinderEntry<'a>> for PskBinderEntryInnerRef<'a> {
    fn ex_from(m: &'a PskBinderEntry) -> PskBinderEntryInnerRef<'a> {
        (&m.l, &m.entries)
    }
}

impl<'a> From<PskBinderEntryInner<'a>> for PskBinderEntry<'a> {
    fn ex_from(m: PskBinderEntryInner) -> PskBinderEntry {
        let (l, entries) = m;
        PskBinderEntry { l, entries }
    }
}

pub struct PskBinderEntryMapper;
impl View for PskBinderEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntryMapper {
    type Src = SpecPskBinderEntryInner;
    type Dst = SpecPskBinderEntry;
}
impl SpecIsoProof for PskBinderEntryMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PskBinderEntryMapper {
    type Src = PskBinderEntryInner<'a>;
    type Dst = PskBinderEntry<'a>;
    type RefSrc = PskBinderEntryInnerRef<'a>;
}

pub struct SpecPskBinderEntryCombinator(SpecPskBinderEntryCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntryCombinator {
    type Type = SpecPskBinderEntry;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskBinderEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntryCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskBinderEntryCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate12415296748708102903>, bytes::Variable>, PskBinderEntryMapper>;
pub struct Predicate12415296748708102903;
impl View for Predicate12415296748708102903 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate12415296748708102903 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 32 && i <= 255)
    }
}
impl SpecPred<u8> for Predicate12415296748708102903 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 32 && i <= 255)
    }
}

pub struct PskBinderEntryCombinator(PskBinderEntryCombinatorAlias);

impl View for PskBinderEntryCombinator {
    type V = SpecPskBinderEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntryCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskBinderEntryCombinator {
    type Type = PskBinderEntry<'a>;
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
pub type PskBinderEntryCombinatorAlias = Mapped<Pair<Refined<U8, Predicate12415296748708102903>, bytes::Variable, PskBinderEntryCont0>, PskBinderEntryMapper>;


pub closed spec fn spec_psk_binder_entry() -> SpecPskBinderEntryCombinator {
    SpecPskBinderEntryCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate12415296748708102903 }, |deps| spec_psk_binder_entry_cont0(deps)),
        mapper: PskBinderEntryMapper,
    })
}

pub open spec fn spec_psk_binder_entry_cont0(deps: u8) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for PskBinderEntryCont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_psk_binder_entry_cont0(deps)
        }
    }
}

                
pub fn psk_binder_entry() -> (o: PskBinderEntryCombinator)
    ensures o@ == spec_psk_binder_entry(),
{
    PskBinderEntryCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate12415296748708102903 }, PskBinderEntryCont0),
        mapper: PskBinderEntryMapper,
    })
}

pub struct PskBinderEntryCont0;
type PskBinderEntryCont0Type<'a, 'b> = &'b u8;
type PskBinderEntryCont0SType<'a, 'x> = &'x u8;
type PskBinderEntryCont0Input<'a, 'b, 'x> = POrSType<PskBinderEntryCont0Type<'a, 'b>, PskBinderEntryCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PskBinderEntryCont0Input<'a, 'b, 'x>> for PskBinderEntryCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: PskBinderEntryCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: PskBinderEntryCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entry_cont0(deps@)
    }

    fn apply(&self, deps: PskBinderEntryCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub struct SpecPskBinderEntries {
    pub l: u16,
    pub list: Seq<SpecPskBinderEntry>,
}

pub type SpecPskBinderEntriesInner = (u16, Seq<SpecPskBinderEntry>);


impl SpecFrom<SpecPskBinderEntries> for SpecPskBinderEntriesInner {
    open spec fn spec_from(m: SpecPskBinderEntries) -> SpecPskBinderEntriesInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecPskBinderEntriesInner> for SpecPskBinderEntries {
    open spec fn spec_from(m: SpecPskBinderEntriesInner) -> SpecPskBinderEntries {
        let (l, list) = m;
        SpecPskBinderEntries { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskBinderEntries<'a> {
    pub l: u16,
    pub list: RepeatResult<PskBinderEntry<'a>>,
}

impl View for PskBinderEntries<'_> {
    type V = SpecPskBinderEntries;

    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntries {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type PskBinderEntriesInner<'a> = (u16, RepeatResult<PskBinderEntry<'a>>);

pub type PskBinderEntriesInnerRef<'a> = (&'a u16, &'a RepeatResult<PskBinderEntry<'a>>);
impl<'a> From<&'a PskBinderEntries<'a>> for PskBinderEntriesInnerRef<'a> {
    fn ex_from(m: &'a PskBinderEntries) -> PskBinderEntriesInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<PskBinderEntriesInner<'a>> for PskBinderEntries<'a> {
    fn ex_from(m: PskBinderEntriesInner) -> PskBinderEntries {
        let (l, list) = m;
        PskBinderEntries { l, list }
    }
}

pub struct PskBinderEntriesMapper;
impl View for PskBinderEntriesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntriesMapper {
    type Src = SpecPskBinderEntriesInner;
    type Dst = SpecPskBinderEntries;
}
impl SpecIsoProof for PskBinderEntriesMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PskBinderEntriesMapper {
    type Src = PskBinderEntriesInner<'a>;
    type Dst = PskBinderEntries<'a>;
    type RefSrc = PskBinderEntriesInnerRef<'a>;
}

pub struct SpecPskBinderEntriesCombinator(SpecPskBinderEntriesCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntriesCombinator {
    type Type = SpecPskBinderEntries;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskBinderEntriesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntriesCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskBinderEntriesCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate2895184764579107747>, AndThen<bytes::Variable, Repeat<SpecPskBinderEntryCombinator>>>, PskBinderEntriesMapper>;
pub struct Predicate2895184764579107747;
impl View for Predicate2895184764579107747 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate2895184764579107747 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 33 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate2895184764579107747 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 33 && i <= 65535)
    }
}

pub struct PskBinderEntriesCombinator(PskBinderEntriesCombinatorAlias);

impl View for PskBinderEntriesCombinator {
    type V = SpecPskBinderEntriesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntriesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskBinderEntriesCombinator {
    type Type = PskBinderEntries<'a>;
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
pub type PskBinderEntriesCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate2895184764579107747>, AndThen<bytes::Variable, Repeat<PskBinderEntryCombinator>>, PskBinderEntriesCont0>, PskBinderEntriesMapper>;


pub closed spec fn spec_psk_binder_entries() -> SpecPskBinderEntriesCombinator {
    SpecPskBinderEntriesCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate2895184764579107747 }, |deps| spec_psk_binder_entries_cont0(deps)),
        mapper: PskBinderEntriesMapper,
    })
}

pub open spec fn spec_psk_binder_entries_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecPskBinderEntryCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_psk_binder_entry()))
}

impl View for PskBinderEntriesCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecPskBinderEntryCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_psk_binder_entries_cont0(deps)
        }
    }
}

                
pub fn psk_binder_entries() -> (o: PskBinderEntriesCombinator)
    ensures o@ == spec_psk_binder_entries(),
{
    PskBinderEntriesCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate2895184764579107747 }, PskBinderEntriesCont0),
        mapper: PskBinderEntriesMapper,
    })
}

pub struct PskBinderEntriesCont0;
type PskBinderEntriesCont0Type<'a, 'b> = &'b u16;
type PskBinderEntriesCont0SType<'a, 'x> = &'x u16;
type PskBinderEntriesCont0Input<'a, 'b, 'x> = POrSType<PskBinderEntriesCont0Type<'a, 'b>, PskBinderEntriesCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PskBinderEntriesCont0Input<'a, 'b, 'x>> for PskBinderEntriesCont0 {
    type Output = AndThen<bytes::Variable, Repeat<PskBinderEntryCombinator>>;

    open spec fn requires(&self, deps: PskBinderEntriesCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: PskBinderEntriesCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entries_cont0(deps@)
    }

    fn apply(&self, deps: PskBinderEntriesCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_binder_entry()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_binder_entry()))
            }
        }
    }
}
                
pub type SpecNameType = u8;
pub type NameType = u8;
pub type NameTypeRef<'a> = &'a u8;


pub struct SpecNameTypeCombinator(SpecNameTypeCombinatorAlias);

impl SpecCombinator for SpecNameTypeCombinator {
    type Type = SpecNameType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNameTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNameTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecNameTypeCombinatorAlias = U8;

pub struct NameTypeCombinator(NameTypeCombinatorAlias);

impl View for NameTypeCombinator {
    type V = SpecNameTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecNameTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NameTypeCombinator {
    type Type = NameType;
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
pub type HostNameRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecHostNameCombinator(SpecHostNameCombinatorAlias);

impl SpecCombinator for SpecHostNameCombinator {
    type Type = SpecHostName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHostNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHostNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecHostNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct HostNameCombinator(HostNameCombinatorAlias);

impl View for HostNameCombinator {
    type V = SpecHostNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecHostNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HostNameCombinator {
    type Type = HostName<'a>;
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
pub type HostNameCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_host_name() -> SpecHostNameCombinator {
    SpecHostNameCombinator(spec_opaque_1_ffff())
}

                
pub fn host_name() -> (o: HostNameCombinator)
    ensures o@ == spec_host_name(),
{
    HostNameCombinator(opaque_1_ffff())
}

                
pub type SpecUnknownName = SpecOpaque1Ffff;
pub type UnknownName<'a> = Opaque1Ffff<'a>;
pub type UnknownNameRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecUnknownNameCombinator(SpecUnknownNameCombinatorAlias);

impl SpecCombinator for SpecUnknownNameCombinator {
    type Type = SpecUnknownName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecUnknownNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecUnknownNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct UnknownNameCombinator(UnknownNameCombinatorAlias);

impl View for UnknownNameCombinator {
    type V = SpecUnknownNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for UnknownNameCombinator {
    type Type = UnknownName<'a>;
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
pub type UnknownNameCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_unknown_name() -> SpecUnknownNameCombinator {
    SpecUnknownNameCombinator(spec_opaque_1_ffff())
}

                
pub fn unknown_name() -> (o: UnknownNameCombinator)
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

pub type ServerNameNameInnerRef<'a> = Either<&'a HostName<'a>, &'a UnknownName<'a>>;


impl<'a> View for ServerNameName<'a> {
    type V = SpecServerNameName;
    open spec fn view(&self) -> Self::V {
        match self {
            ServerNameName::HostName(m) => SpecServerNameName::HostName(m@),
            ServerNameName::Unrecognized(m) => SpecServerNameName::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a ServerNameName<'a>> for ServerNameNameInnerRef<'a> {
    fn ex_from(m: &'a ServerNameName<'a>) -> ServerNameNameInnerRef<'a> {
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


pub struct ServerNameNameMapper;
impl View for ServerNameNameMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameNameMapper {
    type Src = SpecServerNameNameInner;
    type Dst = SpecServerNameName;
}
impl SpecIsoProof for ServerNameNameMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerNameNameMapper {
    type Src = ServerNameNameInner<'a>;
    type Dst = ServerNameName<'a>;
    type RefSrc = ServerNameNameInnerRef<'a>;
}

type SpecServerNameNameCombinatorAlias1 = Choice<Cond<SpecHostNameCombinator>, Cond<SpecUnknownNameCombinator>>;
pub struct SpecServerNameNameCombinator(SpecServerNameNameCombinatorAlias);

impl SpecCombinator for SpecServerNameNameCombinator {
    type Type = SpecServerNameName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerNameNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerNameNameCombinatorAlias = Mapped<SpecServerNameNameCombinatorAlias1, ServerNameNameMapper>;
type ServerNameNameCombinatorAlias1 = Choice<Cond<HostNameCombinator>, Cond<UnknownNameCombinator>>;
struct ServerNameNameCombinator1(ServerNameNameCombinatorAlias1);
impl View for ServerNameNameCombinator1 {
    type V = SpecServerNameNameCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ServerNameNameCombinator1, ServerNameNameCombinatorAlias1);

pub struct ServerNameNameCombinator(ServerNameNameCombinatorAlias);

impl View for ServerNameNameCombinator {
    type V = SpecServerNameNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerNameNameCombinator {
    type Type = ServerNameName<'a>;
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
pub type ServerNameNameCombinatorAlias = Mapped<ServerNameNameCombinator1, ServerNameNameMapper>;


pub closed spec fn spec_server_name_name(name_type: SpecNameType) -> SpecServerNameNameCombinator {
    SpecServerNameNameCombinator(Mapped { inner: Choice(Cond { cond: name_type == 0, inner: spec_host_name() }, Cond { cond: !(name_type == 0), inner: spec_unknown_name() }), mapper: ServerNameNameMapper })
}

pub fn server_name_name<'a>(name_type: NameType) -> (o: ServerNameNameCombinator)
    ensures o@ == spec_server_name_name(name_type@),
{
    ServerNameNameCombinator(Mapped { inner: ServerNameNameCombinator1(Choice::new(Cond { cond: name_type == 0, inner: host_name() }, Cond { cond: !(name_type == 0), inner: unknown_name() })), mapper: ServerNameNameMapper })
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

pub type ServerNameInnerRef<'a> = (&'a NameType, &'a ServerNameName<'a>);
impl<'a> From<&'a ServerName<'a>> for ServerNameInnerRef<'a> {
    fn ex_from(m: &'a ServerName) -> ServerNameInnerRef<'a> {
        (&m.name_type, &m.name)
    }
}

impl<'a> From<ServerNameInner<'a>> for ServerName<'a> {
    fn ex_from(m: ServerNameInner) -> ServerName {
        let (name_type, name) = m;
        ServerName { name_type, name }
    }
}

pub struct ServerNameMapper;
impl View for ServerNameMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameMapper {
    type Src = SpecServerNameInner;
    type Dst = SpecServerName;
}
impl SpecIsoProof for ServerNameMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerNameMapper {
    type Src = ServerNameInner<'a>;
    type Dst = ServerName<'a>;
    type RefSrc = ServerNameInnerRef<'a>;
}

pub struct SpecServerNameCombinator(SpecServerNameCombinatorAlias);

impl SpecCombinator for SpecServerNameCombinator {
    type Type = SpecServerName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerNameCombinatorAlias = Mapped<SpecPair<SpecNameTypeCombinator, SpecServerNameNameCombinator>, ServerNameMapper>;

pub struct ServerNameCombinator(ServerNameCombinatorAlias);

impl View for ServerNameCombinator {
    type V = SpecServerNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerNameCombinator {
    type Type = ServerName<'a>;
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
pub type ServerNameCombinatorAlias = Mapped<Pair<NameTypeCombinator, ServerNameNameCombinator, ServerNameCont0>, ServerNameMapper>;


pub closed spec fn spec_server_name() -> SpecServerNameCombinator {
    SpecServerNameCombinator(
    Mapped {
        inner: Pair::spec_new(spec_name_type(), |deps| spec_server_name_cont0(deps)),
        mapper: ServerNameMapper,
    })
}

pub open spec fn spec_server_name_cont0(deps: SpecNameType) -> SpecServerNameNameCombinator {
    let name_type = deps;
    spec_server_name_name(name_type)
}

impl View for ServerNameCont0 {
    type V = spec_fn(SpecNameType) -> SpecServerNameNameCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecNameType| {
            spec_server_name_cont0(deps)
        }
    }
}

                
pub fn server_name() -> (o: ServerNameCombinator)
    ensures o@ == spec_server_name(),
{
    ServerNameCombinator(
    Mapped {
        inner: Pair::new(name_type(), ServerNameCont0),
        mapper: ServerNameMapper,
    })
}

pub struct ServerNameCont0;
type ServerNameCont0Type<'a, 'b> = &'b NameType;
type ServerNameCont0SType<'a, 'x> = &'x NameType;
type ServerNameCont0Input<'a, 'b, 'x> = POrSType<ServerNameCont0Type<'a, 'b>, ServerNameCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ServerNameCont0Input<'a, 'b, 'x>> for ServerNameCont0 {
    type Output = ServerNameNameCombinator;

    open spec fn requires(&self, deps: ServerNameCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ServerNameCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_server_name_cont0(deps@)
    }

    fn apply(&self, deps: ServerNameCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let name_type = *deps;
                server_name_name(name_type)
            }
            POrSType::S(deps) => {
                let name_type = deps;
                let name_type = *name_type;
                server_name_name(name_type)
            }
        }
    }
}
                

pub struct SpecServerNameList {
    pub l: u16,
    pub list: Seq<SpecServerName>,
}

pub type SpecServerNameListInner = (u16, Seq<SpecServerName>);


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
    pub l: u16,
    pub list: RepeatResult<ServerName<'a>>,
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
pub type ServerNameListInner<'a> = (u16, RepeatResult<ServerName<'a>>);

pub type ServerNameListInnerRef<'a> = (&'a u16, &'a RepeatResult<ServerName<'a>>);
impl<'a> From<&'a ServerNameList<'a>> for ServerNameListInnerRef<'a> {
    fn ex_from(m: &'a ServerNameList) -> ServerNameListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ServerNameListInner<'a>> for ServerNameList<'a> {
    fn ex_from(m: ServerNameListInner) -> ServerNameList {
        let (l, list) = m;
        ServerNameList { l, list }
    }
}

pub struct ServerNameListMapper;
impl View for ServerNameListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameListMapper {
    type Src = SpecServerNameListInner;
    type Dst = SpecServerNameList;
}
impl SpecIsoProof for ServerNameListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerNameListMapper {
    type Src = ServerNameListInner<'a>;
    type Dst = ServerNameList<'a>;
    type RefSrc = ServerNameListInnerRef<'a>;
}

pub struct SpecServerNameListCombinator(SpecServerNameListCombinatorAlias);

impl SpecCombinator for SpecServerNameListCombinator {
    type Type = SpecServerNameList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameListCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerNameListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate16977634203518580913>, AndThen<bytes::Variable, Repeat<SpecServerNameCombinator>>>, ServerNameListMapper>;

pub struct ServerNameListCombinator(ServerNameListCombinatorAlias);

impl View for ServerNameListCombinator {
    type V = SpecServerNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerNameListCombinator {
    type Type = ServerNameList<'a>;
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
pub type ServerNameListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate16977634203518580913>, AndThen<bytes::Variable, Repeat<ServerNameCombinator>>, ServerNameListCont0>, ServerNameListMapper>;


pub closed spec fn spec_server_name_list() -> SpecServerNameListCombinator {
    SpecServerNameListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate16977634203518580913 }, |deps| spec_server_name_list_cont0(deps)),
        mapper: ServerNameListMapper,
    })
}

pub open spec fn spec_server_name_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecServerNameCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_server_name()))
}

impl View for ServerNameListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecServerNameCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_server_name_list_cont0(deps)
        }
    }
}

                
pub fn server_name_list() -> (o: ServerNameListCombinator)
    ensures o@ == spec_server_name_list(),
{
    ServerNameListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate16977634203518580913 }, ServerNameListCont0),
        mapper: ServerNameListMapper,
    })
}

pub struct ServerNameListCont0;
type ServerNameListCont0Type<'a, 'b> = &'b u16;
type ServerNameListCont0SType<'a, 'x> = &'x u16;
type ServerNameListCont0Input<'a, 'b, 'x> = POrSType<ServerNameListCont0Type<'a, 'b>, ServerNameListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ServerNameListCont0Input<'a, 'b, 'x>> for ServerNameListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ServerNameCombinator>>;

    open spec fn requires(&self, deps: ServerNameListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ServerNameListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_server_name_list_cont0(deps@)
    }

    fn apply(&self, deps: ServerNameListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(server_name()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(server_name()))
            }
        }
    }
}
                

pub struct SpecNamedGroupList {
    pub l: u16,
    pub list: Seq<SpecNamedGroup>,
}

pub type SpecNamedGroupListInner = (u16, Seq<SpecNamedGroup>);


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
    pub l: u16,
    pub list: RepeatResult<NamedGroup>,
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
pub type NamedGroupListInner = (u16, RepeatResult<NamedGroup>);

pub type NamedGroupListInnerRef<'a> = (&'a u16, &'a RepeatResult<NamedGroup>);
impl<'a> From<&'a NamedGroupList> for NamedGroupListInnerRef<'a> {
    fn ex_from(m: &'a NamedGroupList) -> NamedGroupListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<NamedGroupListInner> for NamedGroupList {
    fn ex_from(m: NamedGroupListInner) -> NamedGroupList {
        let (l, list) = m;
        NamedGroupList { l, list }
    }
}

pub struct NamedGroupListMapper;
impl View for NamedGroupListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NamedGroupListMapper {
    type Src = SpecNamedGroupListInner;
    type Dst = SpecNamedGroupList;
}
impl SpecIsoProof for NamedGroupListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NamedGroupListMapper {
    type Src = NamedGroupListInner;
    type Dst = NamedGroupList;
    type RefSrc = NamedGroupListInnerRef<'a>;
}

pub struct SpecNamedGroupListCombinator(SpecNamedGroupListCombinatorAlias);

impl SpecCombinator for SpecNamedGroupListCombinator {
    type Type = SpecNamedGroupList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNamedGroupListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupListCombinatorAlias::is_prefix_secure() }
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
pub type SpecNamedGroupListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<SpecNamedGroupCombinator>>>, NamedGroupListMapper>;

pub struct NamedGroupListCombinator(NamedGroupListCombinatorAlias);

impl View for NamedGroupListCombinator {
    type V = SpecNamedGroupListCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NamedGroupListCombinator {
    type Type = NamedGroupList;
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
pub type NamedGroupListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<NamedGroupCombinator>>, NamedGroupListCont0>, NamedGroupListMapper>;


pub closed spec fn spec_named_group_list() -> SpecNamedGroupListCombinator {
    SpecNamedGroupListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, |deps| spec_named_group_list_cont0(deps)),
        mapper: NamedGroupListMapper,
    })
}

pub open spec fn spec_named_group_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecNamedGroupCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_named_group()))
}

impl View for NamedGroupListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecNamedGroupCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_named_group_list_cont0(deps)
        }
    }
}

                
pub fn named_group_list() -> (o: NamedGroupListCombinator)
    ensures o@ == spec_named_group_list(),
{
    NamedGroupListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, NamedGroupListCont0),
        mapper: NamedGroupListMapper,
    })
}

pub struct NamedGroupListCont0;
type NamedGroupListCont0Type<'a, 'b> = &'b u16;
type NamedGroupListCont0SType<'a, 'x> = &'x u16;
type NamedGroupListCont0Input<'a, 'b, 'x> = POrSType<NamedGroupListCont0Type<'a, 'b>, NamedGroupListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NamedGroupListCont0Input<'a, 'b, 'x>> for NamedGroupListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<NamedGroupCombinator>>;

    open spec fn requires(&self, deps: NamedGroupListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: NamedGroupListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_named_group_list_cont0(deps@)
    }

    fn apply(&self, deps: NamedGroupListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(named_group()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(named_group()))
            }
        }
    }
}
                

pub struct SpecKeyShareClientHello {
    pub l: u16,
    pub list: Seq<SpecKeyShareEntry>,
}

pub type SpecKeyShareClientHelloInner = (u16, Seq<SpecKeyShareEntry>);


impl SpecFrom<SpecKeyShareClientHello> for SpecKeyShareClientHelloInner {
    open spec fn spec_from(m: SpecKeyShareClientHello) -> SpecKeyShareClientHelloInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecKeyShareClientHelloInner> for SpecKeyShareClientHello {
    open spec fn spec_from(m: SpecKeyShareClientHelloInner) -> SpecKeyShareClientHello {
        let (l, list) = m;
        SpecKeyShareClientHello { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct KeyShareClientHello<'a> {
    pub l: u16,
    pub list: RepeatResult<KeyShareEntry<'a>>,
}

impl View for KeyShareClientHello<'_> {
    type V = SpecKeyShareClientHello;

    open spec fn view(&self) -> Self::V {
        SpecKeyShareClientHello {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type KeyShareClientHelloInner<'a> = (u16, RepeatResult<KeyShareEntry<'a>>);

pub type KeyShareClientHelloInnerRef<'a> = (&'a u16, &'a RepeatResult<KeyShareEntry<'a>>);
impl<'a> From<&'a KeyShareClientHello<'a>> for KeyShareClientHelloInnerRef<'a> {
    fn ex_from(m: &'a KeyShareClientHello) -> KeyShareClientHelloInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<KeyShareClientHelloInner<'a>> for KeyShareClientHello<'a> {
    fn ex_from(m: KeyShareClientHelloInner) -> KeyShareClientHello {
        let (l, list) = m;
        KeyShareClientHello { l, list }
    }
}

pub struct KeyShareClientHelloMapper;
impl View for KeyShareClientHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareClientHelloMapper {
    type Src = SpecKeyShareClientHelloInner;
    type Dst = SpecKeyShareClientHello;
}
impl SpecIsoProof for KeyShareClientHelloMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for KeyShareClientHelloMapper {
    type Src = KeyShareClientHelloInner<'a>;
    type Dst = KeyShareClientHello<'a>;
    type RefSrc = KeyShareClientHelloInnerRef<'a>;
}

pub struct SpecKeyShareClientHelloCombinator(SpecKeyShareClientHelloCombinatorAlias);

impl SpecCombinator for SpecKeyShareClientHelloCombinator {
    type Type = SpecKeyShareClientHello;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecKeyShareClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareClientHelloCombinatorAlias::is_prefix_secure() }
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
pub type SpecKeyShareClientHelloCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecKeyShareEntryCombinator>>>, KeyShareClientHelloMapper>;

pub struct KeyShareClientHelloCombinator(KeyShareClientHelloCombinatorAlias);

impl View for KeyShareClientHelloCombinator {
    type V = SpecKeyShareClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareClientHelloCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for KeyShareClientHelloCombinator {
    type Type = KeyShareClientHello<'a>;
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
pub type KeyShareClientHelloCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<KeyShareEntryCombinator>>, KeyShareClientHelloCont0>, KeyShareClientHelloMapper>;


pub closed spec fn spec_key_share_client_hello() -> SpecKeyShareClientHelloCombinator {
    SpecKeyShareClientHelloCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_key_share_client_hello_cont0(deps)),
        mapper: KeyShareClientHelloMapper,
    })
}

pub open spec fn spec_key_share_client_hello_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecKeyShareEntryCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_key_share_entry()))
}

impl View for KeyShareClientHelloCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecKeyShareEntryCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_key_share_client_hello_cont0(deps)
        }
    }
}

                
pub fn key_share_client_hello() -> (o: KeyShareClientHelloCombinator)
    ensures o@ == spec_key_share_client_hello(),
{
    KeyShareClientHelloCombinator(
    Mapped {
        inner: Pair::new(U16Be, KeyShareClientHelloCont0),
        mapper: KeyShareClientHelloMapper,
    })
}

pub struct KeyShareClientHelloCont0;
type KeyShareClientHelloCont0Type<'a, 'b> = &'b u16;
type KeyShareClientHelloCont0SType<'a, 'x> = &'x u16;
type KeyShareClientHelloCont0Input<'a, 'b, 'x> = POrSType<KeyShareClientHelloCont0Type<'a, 'b>, KeyShareClientHelloCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<KeyShareClientHelloCont0Input<'a, 'b, 'x>> for KeyShareClientHelloCont0 {
    type Output = AndThen<bytes::Variable, Repeat<KeyShareEntryCombinator>>;

    open spec fn requires(&self, deps: KeyShareClientHelloCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: KeyShareClientHelloCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_key_share_client_hello_cont0(deps@)
    }

    fn apply(&self, deps: KeyShareClientHelloCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(key_share_entry()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(key_share_entry()))
            }
        }
    }
}
                
pub type SpecPskKeyExchangeMode = u8;
pub type PskKeyExchangeMode = u8;
pub type PskKeyExchangeModeRef<'a> = &'a u8;


pub struct SpecPskKeyExchangeModeCombinator(SpecPskKeyExchangeModeCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModeCombinator {
    type Type = SpecPskKeyExchangeMode;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskKeyExchangeModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModeCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskKeyExchangeModeCombinatorAlias = U8;

pub struct PskKeyExchangeModeCombinator(PskKeyExchangeModeCombinatorAlias);

impl View for PskKeyExchangeModeCombinator {
    type V = SpecPskKeyExchangeModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskKeyExchangeModeCombinator {
    type Type = PskKeyExchangeMode;
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
pub type PskKeyExchangeModeCombinatorAlias = U8;


pub closed spec fn spec_psk_key_exchange_mode() -> SpecPskKeyExchangeModeCombinator {
    SpecPskKeyExchangeModeCombinator(U8)
}

                
pub fn psk_key_exchange_mode() -> (o: PskKeyExchangeModeCombinator)
    ensures o@ == spec_psk_key_exchange_mode(),
{
    PskKeyExchangeModeCombinator(U8)
}

                

pub struct SpecPskKeyExchangeModes {
    pub l: u8,
    pub list: Seq<SpecPskKeyExchangeMode>,
}

pub type SpecPskKeyExchangeModesInner = (u8, Seq<SpecPskKeyExchangeMode>);


impl SpecFrom<SpecPskKeyExchangeModes> for SpecPskKeyExchangeModesInner {
    open spec fn spec_from(m: SpecPskKeyExchangeModes) -> SpecPskKeyExchangeModesInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecPskKeyExchangeModesInner> for SpecPskKeyExchangeModes {
    open spec fn spec_from(m: SpecPskKeyExchangeModesInner) -> SpecPskKeyExchangeModes {
        let (l, list) = m;
        SpecPskKeyExchangeModes { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskKeyExchangeModes {
    pub l: u8,
    pub list: RepeatResult<PskKeyExchangeMode>,
}

impl View for PskKeyExchangeModes {
    type V = SpecPskKeyExchangeModes;

    open spec fn view(&self) -> Self::V {
        SpecPskKeyExchangeModes {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type PskKeyExchangeModesInner = (u8, RepeatResult<PskKeyExchangeMode>);

pub type PskKeyExchangeModesInnerRef<'a> = (&'a u8, &'a RepeatResult<PskKeyExchangeMode>);
impl<'a> From<&'a PskKeyExchangeModes> for PskKeyExchangeModesInnerRef<'a> {
    fn ex_from(m: &'a PskKeyExchangeModes) -> PskKeyExchangeModesInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<PskKeyExchangeModesInner> for PskKeyExchangeModes {
    fn ex_from(m: PskKeyExchangeModesInner) -> PskKeyExchangeModes {
        let (l, list) = m;
        PskKeyExchangeModes { l, list }
    }
}

pub struct PskKeyExchangeModesMapper;
impl View for PskKeyExchangeModesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskKeyExchangeModesMapper {
    type Src = SpecPskKeyExchangeModesInner;
    type Dst = SpecPskKeyExchangeModes;
}
impl SpecIsoProof for PskKeyExchangeModesMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PskKeyExchangeModesMapper {
    type Src = PskKeyExchangeModesInner;
    type Dst = PskKeyExchangeModes;
    type RefSrc = PskKeyExchangeModesInnerRef<'a>;
}

pub struct SpecPskKeyExchangeModesCombinator(SpecPskKeyExchangeModesCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModesCombinator {
    type Type = SpecPskKeyExchangeModes;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskKeyExchangeModesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModesCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskKeyExchangeModesCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<SpecPskKeyExchangeModeCombinator>>>, PskKeyExchangeModesMapper>;
pub struct Predicate13984338198318635021;
impl View for Predicate13984338198318635021 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13984338198318635021 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}
impl SpecPred<u8> for Predicate13984338198318635021 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 1 && i <= 255)
    }
}

pub struct PskKeyExchangeModesCombinator(PskKeyExchangeModesCombinatorAlias);

impl View for PskKeyExchangeModesCombinator {
    type V = SpecPskKeyExchangeModesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskKeyExchangeModesCombinator {
    type Type = PskKeyExchangeModes;
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
pub type PskKeyExchangeModesCombinatorAlias = Mapped<Pair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<PskKeyExchangeModeCombinator>>, PskKeyExchangeModesCont0>, PskKeyExchangeModesMapper>;


pub closed spec fn spec_psk_key_exchange_modes() -> SpecPskKeyExchangeModesCombinator {
    SpecPskKeyExchangeModesCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, |deps| spec_psk_key_exchange_modes_cont0(deps)),
        mapper: PskKeyExchangeModesMapper,
    })
}

pub open spec fn spec_psk_key_exchange_modes_cont0(deps: u8) -> AndThen<bytes::Variable, Repeat<SpecPskKeyExchangeModeCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_psk_key_exchange_mode()))
}

impl View for PskKeyExchangeModesCont0 {
    type V = spec_fn(u8) -> AndThen<bytes::Variable, Repeat<SpecPskKeyExchangeModeCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_psk_key_exchange_modes_cont0(deps)
        }
    }
}

                
pub fn psk_key_exchange_modes() -> (o: PskKeyExchangeModesCombinator)
    ensures o@ == spec_psk_key_exchange_modes(),
{
    PskKeyExchangeModesCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, PskKeyExchangeModesCont0),
        mapper: PskKeyExchangeModesMapper,
    })
}

pub struct PskKeyExchangeModesCont0;
type PskKeyExchangeModesCont0Type<'a, 'b> = &'b u8;
type PskKeyExchangeModesCont0SType<'a, 'x> = &'x u8;
type PskKeyExchangeModesCont0Input<'a, 'b, 'x> = POrSType<PskKeyExchangeModesCont0Type<'a, 'b>, PskKeyExchangeModesCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PskKeyExchangeModesCont0Input<'a, 'b, 'x>> for PskKeyExchangeModesCont0 {
    type Output = AndThen<bytes::Variable, Repeat<PskKeyExchangeModeCombinator>>;

    open spec fn requires(&self, deps: PskKeyExchangeModesCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: PskKeyExchangeModesCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_psk_key_exchange_modes_cont0(deps@)
    }

    fn apply(&self, deps: PskKeyExchangeModesCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_key_exchange_mode()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_key_exchange_mode()))
            }
        }
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

pub type PskIdentityInnerRef<'a> = (&'a Opaque1Ffff<'a>, &'a u32);
impl<'a> From<&'a PskIdentity<'a>> for PskIdentityInnerRef<'a> {
    fn ex_from(m: &'a PskIdentity) -> PskIdentityInnerRef<'a> {
        (&m.identity, &m.obfuscated_ticket_age)
    }
}

impl<'a> From<PskIdentityInner<'a>> for PskIdentity<'a> {
    fn ex_from(m: PskIdentityInner) -> PskIdentity {
        let (identity, obfuscated_ticket_age) = m;
        PskIdentity { identity, obfuscated_ticket_age }
    }
}

pub struct PskIdentityMapper;
impl View for PskIdentityMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentityMapper {
    type Src = SpecPskIdentityInner;
    type Dst = SpecPskIdentity;
}
impl SpecIsoProof for PskIdentityMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PskIdentityMapper {
    type Src = PskIdentityInner<'a>;
    type Dst = PskIdentity<'a>;
    type RefSrc = PskIdentityInnerRef<'a>;
}
type SpecPskIdentityCombinatorAlias1 = (SpecOpaque1FfffCombinator, U32Be);
pub struct SpecPskIdentityCombinator(SpecPskIdentityCombinatorAlias);

impl SpecCombinator for SpecPskIdentityCombinator {
    type Type = SpecPskIdentity;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskIdentityCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentityCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskIdentityCombinatorAlias = Mapped<SpecPskIdentityCombinatorAlias1, PskIdentityMapper>;
type PskIdentityCombinatorAlias1 = (Opaque1FfffCombinator, U32Be);
struct PskIdentityCombinator1(PskIdentityCombinatorAlias1);
impl View for PskIdentityCombinator1 {
    type V = SpecPskIdentityCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PskIdentityCombinator1, PskIdentityCombinatorAlias1);

pub struct PskIdentityCombinator(PskIdentityCombinatorAlias);

impl View for PskIdentityCombinator {
    type V = SpecPskIdentityCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentityCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskIdentityCombinator {
    type Type = PskIdentity<'a>;
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
pub type PskIdentityCombinatorAlias = Mapped<PskIdentityCombinator1, PskIdentityMapper>;


pub closed spec fn spec_psk_identity() -> SpecPskIdentityCombinator {
    SpecPskIdentityCombinator(
    Mapped {
        inner: (spec_opaque_1_ffff(), U32Be),
        mapper: PskIdentityMapper,
    })
}

                
pub fn psk_identity() -> (o: PskIdentityCombinator)
    ensures o@ == spec_psk_identity(),
{
    PskIdentityCombinator(
    Mapped {
        inner: PskIdentityCombinator1((opaque_1_ffff(), U32Be)),
        mapper: PskIdentityMapper,
    })
}

                

pub struct SpecPskIdentities {
    pub l: u16,
    pub list: Seq<SpecPskIdentity>,
}

pub type SpecPskIdentitiesInner = (u16, Seq<SpecPskIdentity>);


impl SpecFrom<SpecPskIdentities> for SpecPskIdentitiesInner {
    open spec fn spec_from(m: SpecPskIdentities) -> SpecPskIdentitiesInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecPskIdentitiesInner> for SpecPskIdentities {
    open spec fn spec_from(m: SpecPskIdentitiesInner) -> SpecPskIdentities {
        let (l, list) = m;
        SpecPskIdentities { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PskIdentities<'a> {
    pub l: u16,
    pub list: RepeatResult<PskIdentity<'a>>,
}

impl View for PskIdentities<'_> {
    type V = SpecPskIdentities;

    open spec fn view(&self) -> Self::V {
        SpecPskIdentities {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type PskIdentitiesInner<'a> = (u16, RepeatResult<PskIdentity<'a>>);

pub type PskIdentitiesInnerRef<'a> = (&'a u16, &'a RepeatResult<PskIdentity<'a>>);
impl<'a> From<&'a PskIdentities<'a>> for PskIdentitiesInnerRef<'a> {
    fn ex_from(m: &'a PskIdentities) -> PskIdentitiesInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<PskIdentitiesInner<'a>> for PskIdentities<'a> {
    fn ex_from(m: PskIdentitiesInner) -> PskIdentities {
        let (l, list) = m;
        PskIdentities { l, list }
    }
}

pub struct PskIdentitiesMapper;
impl View for PskIdentitiesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentitiesMapper {
    type Src = SpecPskIdentitiesInner;
    type Dst = SpecPskIdentities;
}
impl SpecIsoProof for PskIdentitiesMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PskIdentitiesMapper {
    type Src = PskIdentitiesInner<'a>;
    type Dst = PskIdentities<'a>;
    type RefSrc = PskIdentitiesInnerRef<'a>;
}

pub struct SpecPskIdentitiesCombinator(SpecPskIdentitiesCombinatorAlias);

impl SpecCombinator for SpecPskIdentitiesCombinator {
    type Type = SpecPskIdentities;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPskIdentitiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentitiesCombinatorAlias::is_prefix_secure() }
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
pub type SpecPskIdentitiesCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate22012019403780218>, AndThen<bytes::Variable, Repeat<SpecPskIdentityCombinator>>>, PskIdentitiesMapper>;
pub struct Predicate22012019403780218;
impl View for Predicate22012019403780218 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate22012019403780218 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 7 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate22012019403780218 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 7 && i <= 65535)
    }
}

pub struct PskIdentitiesCombinator(PskIdentitiesCombinatorAlias);

impl View for PskIdentitiesCombinator {
    type V = SpecPskIdentitiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentitiesCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PskIdentitiesCombinator {
    type Type = PskIdentities<'a>;
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
pub type PskIdentitiesCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate22012019403780218>, AndThen<bytes::Variable, Repeat<PskIdentityCombinator>>, PskIdentitiesCont0>, PskIdentitiesMapper>;


pub closed spec fn spec_psk_identities() -> SpecPskIdentitiesCombinator {
    SpecPskIdentitiesCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate22012019403780218 }, |deps| spec_psk_identities_cont0(deps)),
        mapper: PskIdentitiesMapper,
    })
}

pub open spec fn spec_psk_identities_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecPskIdentityCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_psk_identity()))
}

impl View for PskIdentitiesCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecPskIdentityCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_psk_identities_cont0(deps)
        }
    }
}

                
pub fn psk_identities() -> (o: PskIdentitiesCombinator)
    ensures o@ == spec_psk_identities(),
{
    PskIdentitiesCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate22012019403780218 }, PskIdentitiesCont0),
        mapper: PskIdentitiesMapper,
    })
}

pub struct PskIdentitiesCont0;
type PskIdentitiesCont0Type<'a, 'b> = &'b u16;
type PskIdentitiesCont0SType<'a, 'x> = &'x u16;
type PskIdentitiesCont0Input<'a, 'b, 'x> = POrSType<PskIdentitiesCont0Type<'a, 'b>, PskIdentitiesCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PskIdentitiesCont0Input<'a, 'b, 'x>> for PskIdentitiesCont0 {
    type Output = AndThen<bytes::Variable, Repeat<PskIdentityCombinator>>;

    open spec fn requires(&self, deps: PskIdentitiesCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: PskIdentitiesCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_psk_identities_cont0(deps@)
    }

    fn apply(&self, deps: PskIdentitiesCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_identity()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(psk_identity()))
            }
        }
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

pub type OfferedPsksInnerRef<'a> = (&'a PskIdentities<'a>, &'a PskBinderEntries<'a>);
impl<'a> From<&'a OfferedPsks<'a>> for OfferedPsksInnerRef<'a> {
    fn ex_from(m: &'a OfferedPsks) -> OfferedPsksInnerRef<'a> {
        (&m.identities, &m.binders)
    }
}

impl<'a> From<OfferedPsksInner<'a>> for OfferedPsks<'a> {
    fn ex_from(m: OfferedPsksInner) -> OfferedPsks {
        let (identities, binders) = m;
        OfferedPsks { identities, binders }
    }
}

pub struct OfferedPsksMapper;
impl View for OfferedPsksMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OfferedPsksMapper {
    type Src = SpecOfferedPsksInner;
    type Dst = SpecOfferedPsks;
}
impl SpecIsoProof for OfferedPsksMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OfferedPsksMapper {
    type Src = OfferedPsksInner<'a>;
    type Dst = OfferedPsks<'a>;
    type RefSrc = OfferedPsksInnerRef<'a>;
}
type SpecOfferedPsksCombinatorAlias1 = (SpecPskIdentitiesCombinator, SpecPskBinderEntriesCombinator);
pub struct SpecOfferedPsksCombinator(SpecOfferedPsksCombinatorAlias);

impl SpecCombinator for SpecOfferedPsksCombinator {
    type Type = SpecOfferedPsks;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOfferedPsksCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOfferedPsksCombinatorAlias::is_prefix_secure() }
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
pub type SpecOfferedPsksCombinatorAlias = Mapped<SpecOfferedPsksCombinatorAlias1, OfferedPsksMapper>;
type OfferedPsksCombinatorAlias1 = (PskIdentitiesCombinator, PskBinderEntriesCombinator);
struct OfferedPsksCombinator1(OfferedPsksCombinatorAlias1);
impl View for OfferedPsksCombinator1 {
    type V = SpecOfferedPsksCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(OfferedPsksCombinator1, OfferedPsksCombinatorAlias1);

pub struct OfferedPsksCombinator(OfferedPsksCombinatorAlias);

impl View for OfferedPsksCombinator {
    type V = SpecOfferedPsksCombinator;
    closed spec fn view(&self) -> Self::V { SpecOfferedPsksCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OfferedPsksCombinator {
    type Type = OfferedPsks<'a>;
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
pub type OfferedPsksCombinatorAlias = Mapped<OfferedPsksCombinator1, OfferedPsksMapper>;


pub closed spec fn spec_offered_psks() -> SpecOfferedPsksCombinator {
    SpecOfferedPsksCombinator(
    Mapped {
        inner: (spec_psk_identities(), spec_psk_binder_entries()),
        mapper: OfferedPsksMapper,
    })
}

                
pub fn offered_psks() -> (o: OfferedPsksCombinator)
    ensures o@ == spec_offered_psks(),
{
    OfferedPsksCombinator(
    Mapped {
        inner: OfferedPsksCombinator1((psk_identities(), psk_binder_entries())),
        mapper: OfferedPsksMapper,
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

pub type PreSharedKeyClientExtensionInnerRef<'a> = &'a OfferedPsks<'a>;
impl<'a> From<&'a PreSharedKeyClientExtension<'a>> for PreSharedKeyClientExtensionInnerRef<'a> {
    fn ex_from(m: &'a PreSharedKeyClientExtension) -> PreSharedKeyClientExtensionInnerRef<'a> {
        &m.offers
    }
}

impl<'a> From<PreSharedKeyClientExtensionInner<'a>> for PreSharedKeyClientExtension<'a> {
    fn ex_from(m: PreSharedKeyClientExtensionInner) -> PreSharedKeyClientExtension {
        let offers = m;
        PreSharedKeyClientExtension { offers }
    }
}

pub struct PreSharedKeyClientExtensionMapper;
impl View for PreSharedKeyClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyClientExtensionMapper {
    type Src = SpecPreSharedKeyClientExtensionInner;
    type Dst = SpecPreSharedKeyClientExtension;
}
impl SpecIsoProof for PreSharedKeyClientExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PreSharedKeyClientExtensionMapper {
    type Src = PreSharedKeyClientExtensionInner<'a>;
    type Dst = PreSharedKeyClientExtension<'a>;
    type RefSrc = PreSharedKeyClientExtensionInnerRef<'a>;
}

pub struct SpecPreSharedKeyClientExtensionCombinator(SpecPreSharedKeyClientExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    type Type = SpecPreSharedKeyClientExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyClientExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecPreSharedKeyClientExtensionCombinatorAlias = Mapped<SpecOfferedPsksCombinator, PreSharedKeyClientExtensionMapper>;

pub struct PreSharedKeyClientExtensionCombinator(PreSharedKeyClientExtensionCombinatorAlias);

impl View for PreSharedKeyClientExtensionCombinator {
    type V = SpecPreSharedKeyClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PreSharedKeyClientExtensionCombinator {
    type Type = PreSharedKeyClientExtension<'a>;
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
pub type PreSharedKeyClientExtensionCombinatorAlias = Mapped<OfferedPsksCombinator, PreSharedKeyClientExtensionMapper>;


pub closed spec fn spec_pre_shared_key_client_extension() -> SpecPreSharedKeyClientExtensionCombinator {
    SpecPreSharedKeyClientExtensionCombinator(
    Mapped {
        inner: spec_offered_psks(),
        mapper: PreSharedKeyClientExtensionMapper,
    })
}

                
pub fn pre_shared_key_client_extension() -> (o: PreSharedKeyClientExtensionCombinator)
    ensures o@ == spec_pre_shared_key_client_extension(),
{
    PreSharedKeyClientExtensionCombinator(
    Mapped {
        inner: offered_psks(),
        mapper: PreSharedKeyClientExtensionMapper,
    })
}

                
pub type SpecMaxFragmentLength = u8;
pub type MaxFragmentLength = u8;
pub type MaxFragmentLengthRef<'a> = &'a u8;


pub struct SpecMaxFragmentLengthCombinator(SpecMaxFragmentLengthCombinatorAlias);

impl SpecCombinator for SpecMaxFragmentLengthCombinator {
    type Type = SpecMaxFragmentLength;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMaxFragmentLengthCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMaxFragmentLengthCombinatorAlias::is_prefix_secure() }
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
pub type SpecMaxFragmentLengthCombinatorAlias = U8;

pub struct MaxFragmentLengthCombinator(MaxFragmentLengthCombinatorAlias);

impl View for MaxFragmentLengthCombinator {
    type V = SpecMaxFragmentLengthCombinator;
    closed spec fn view(&self) -> Self::V { SpecMaxFragmentLengthCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MaxFragmentLengthCombinator {
    type Type = MaxFragmentLength;
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
pub type MaxFragmentLengthCombinatorAlias = U8;


pub closed spec fn spec_max_fragment_length() -> SpecMaxFragmentLengthCombinator {
    SpecMaxFragmentLengthCombinator(U8)
}

                
pub fn max_fragment_length() -> (o: MaxFragmentLengthCombinator)
    ensures o@ == spec_max_fragment_length(),
{
    MaxFragmentLengthCombinator(U8)
}

                

pub struct SpecClientCertTypeClientExtension {
    pub l: u8,
    pub list: Seq<SpecCertificateType>,
}

pub type SpecClientCertTypeClientExtensionInner = (u8, Seq<SpecCertificateType>);


impl SpecFrom<SpecClientCertTypeClientExtension> for SpecClientCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecClientCertTypeClientExtension) -> SpecClientCertTypeClientExtensionInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecClientCertTypeClientExtensionInner> for SpecClientCertTypeClientExtension {
    open spec fn spec_from(m: SpecClientCertTypeClientExtensionInner) -> SpecClientCertTypeClientExtension {
        let (l, list) = m;
        SpecClientCertTypeClientExtension { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientCertTypeClientExtension {
    pub l: u8,
    pub list: RepeatResult<CertificateType>,
}

impl View for ClientCertTypeClientExtension {
    type V = SpecClientCertTypeClientExtension;

    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeClientExtension {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ClientCertTypeClientExtensionInner = (u8, RepeatResult<CertificateType>);

pub type ClientCertTypeClientExtensionInnerRef<'a> = (&'a u8, &'a RepeatResult<CertificateType>);
impl<'a> From<&'a ClientCertTypeClientExtension> for ClientCertTypeClientExtensionInnerRef<'a> {
    fn ex_from(m: &'a ClientCertTypeClientExtension) -> ClientCertTypeClientExtensionInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<ClientCertTypeClientExtensionInner> for ClientCertTypeClientExtension {
    fn ex_from(m: ClientCertTypeClientExtensionInner) -> ClientCertTypeClientExtension {
        let (l, list) = m;
        ClientCertTypeClientExtension { l, list }
    }
}

pub struct ClientCertTypeClientExtensionMapper;
impl View for ClientCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeClientExtensionMapper {
    type Src = SpecClientCertTypeClientExtensionInner;
    type Dst = SpecClientCertTypeClientExtension;
}
impl SpecIsoProof for ClientCertTypeClientExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientCertTypeClientExtensionMapper {
    type Src = ClientCertTypeClientExtensionInner;
    type Dst = ClientCertTypeClientExtension;
    type RefSrc = ClientCertTypeClientExtensionInnerRef<'a>;
}

pub struct SpecClientCertTypeClientExtensionCombinator(SpecClientCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    type Type = SpecClientCertTypeClientExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientCertTypeClientExtensionCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>>>, ClientCertTypeClientExtensionMapper>;

pub struct ClientCertTypeClientExtensionCombinator(ClientCertTypeClientExtensionCombinatorAlias);

impl View for ClientCertTypeClientExtensionCombinator {
    type V = SpecClientCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientCertTypeClientExtensionCombinator {
    type Type = ClientCertTypeClientExtension;
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
pub type ClientCertTypeClientExtensionCombinatorAlias = Mapped<Pair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<CertificateTypeCombinator>>, ClientCertTypeClientExtensionCont0>, ClientCertTypeClientExtensionMapper>;


pub closed spec fn spec_client_cert_type_client_extension() -> SpecClientCertTypeClientExtensionCombinator {
    SpecClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, |deps| spec_client_cert_type_client_extension_cont0(deps)),
        mapper: ClientCertTypeClientExtensionMapper,
    })
}

pub open spec fn spec_client_cert_type_client_extension_cont0(deps: u8) -> AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_certificate_type()))
}

impl View for ClientCertTypeClientExtensionCont0 {
    type V = spec_fn(u8) -> AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_client_cert_type_client_extension_cont0(deps)
        }
    }
}

                
pub fn client_cert_type_client_extension() -> (o: ClientCertTypeClientExtensionCombinator)
    ensures o@ == spec_client_cert_type_client_extension(),
{
    ClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, ClientCertTypeClientExtensionCont0),
        mapper: ClientCertTypeClientExtensionMapper,
    })
}

pub struct ClientCertTypeClientExtensionCont0;
type ClientCertTypeClientExtensionCont0Type<'a, 'b> = &'b u8;
type ClientCertTypeClientExtensionCont0SType<'a, 'x> = &'x u8;
type ClientCertTypeClientExtensionCont0Input<'a, 'b, 'x> = POrSType<ClientCertTypeClientExtensionCont0Type<'a, 'b>, ClientCertTypeClientExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ClientCertTypeClientExtensionCont0Input<'a, 'b, 'x>> for ClientCertTypeClientExtensionCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CertificateTypeCombinator>>;

    open spec fn requires(&self, deps: ClientCertTypeClientExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ClientCertTypeClientExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_client_cert_type_client_extension_cont0(deps@)
    }

    fn apply(&self, deps: ClientCertTypeClientExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_type()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_type()))
            }
        }
    }
}
                

pub struct SpecServerCertTypeClientExtension {
    pub l: u8,
    pub list: Seq<SpecCertificateType>,
}

pub type SpecServerCertTypeClientExtensionInner = (u8, Seq<SpecCertificateType>);


impl SpecFrom<SpecServerCertTypeClientExtension> for SpecServerCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecServerCertTypeClientExtension) -> SpecServerCertTypeClientExtensionInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecServerCertTypeClientExtensionInner> for SpecServerCertTypeClientExtension {
    open spec fn spec_from(m: SpecServerCertTypeClientExtensionInner) -> SpecServerCertTypeClientExtension {
        let (l, list) = m;
        SpecServerCertTypeClientExtension { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ServerCertTypeClientExtension {
    pub l: u8,
    pub list: RepeatResult<CertificateType>,
}

impl View for ServerCertTypeClientExtension {
    type V = SpecServerCertTypeClientExtension;

    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeClientExtension {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ServerCertTypeClientExtensionInner = (u8, RepeatResult<CertificateType>);

pub type ServerCertTypeClientExtensionInnerRef<'a> = (&'a u8, &'a RepeatResult<CertificateType>);
impl<'a> From<&'a ServerCertTypeClientExtension> for ServerCertTypeClientExtensionInnerRef<'a> {
    fn ex_from(m: &'a ServerCertTypeClientExtension) -> ServerCertTypeClientExtensionInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<ServerCertTypeClientExtensionInner> for ServerCertTypeClientExtension {
    fn ex_from(m: ServerCertTypeClientExtensionInner) -> ServerCertTypeClientExtension {
        let (l, list) = m;
        ServerCertTypeClientExtension { l, list }
    }
}

pub struct ServerCertTypeClientExtensionMapper;
impl View for ServerCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeClientExtensionMapper {
    type Src = SpecServerCertTypeClientExtensionInner;
    type Dst = SpecServerCertTypeClientExtension;
}
impl SpecIsoProof for ServerCertTypeClientExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerCertTypeClientExtensionMapper {
    type Src = ServerCertTypeClientExtensionInner;
    type Dst = ServerCertTypeClientExtension;
    type RefSrc = ServerCertTypeClientExtensionInnerRef<'a>;
}

pub struct SpecServerCertTypeClientExtensionCombinator(SpecServerCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    type Type = SpecServerCertTypeClientExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerCertTypeClientExtensionCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>>>, ServerCertTypeClientExtensionMapper>;

pub struct ServerCertTypeClientExtensionCombinator(ServerCertTypeClientExtensionCombinatorAlias);

impl View for ServerCertTypeClientExtensionCombinator {
    type V = SpecServerCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeClientExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerCertTypeClientExtensionCombinator {
    type Type = ServerCertTypeClientExtension;
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
pub type ServerCertTypeClientExtensionCombinatorAlias = Mapped<Pair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<CertificateTypeCombinator>>, ServerCertTypeClientExtensionCont0>, ServerCertTypeClientExtensionMapper>;


pub closed spec fn spec_server_cert_type_client_extension() -> SpecServerCertTypeClientExtensionCombinator {
    SpecServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, |deps| spec_server_cert_type_client_extension_cont0(deps)),
        mapper: ServerCertTypeClientExtensionMapper,
    })
}

pub open spec fn spec_server_cert_type_client_extension_cont0(deps: u8) -> AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_certificate_type()))
}

impl View for ServerCertTypeClientExtensionCont0 {
    type V = spec_fn(u8) -> AndThen<bytes::Variable, Repeat<SpecCertificateTypeCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_server_cert_type_client_extension_cont0(deps)
        }
    }
}

                
pub fn server_cert_type_client_extension() -> (o: ServerCertTypeClientExtensionCombinator)
    ensures o@ == spec_server_cert_type_client_extension(),
{
    ServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, ServerCertTypeClientExtensionCont0),
        mapper: ServerCertTypeClientExtensionMapper,
    })
}

pub struct ServerCertTypeClientExtensionCont0;
type ServerCertTypeClientExtensionCont0Type<'a, 'b> = &'b u8;
type ServerCertTypeClientExtensionCont0SType<'a, 'x> = &'x u8;
type ServerCertTypeClientExtensionCont0Input<'a, 'b, 'x> = POrSType<ServerCertTypeClientExtensionCont0Type<'a, 'b>, ServerCertTypeClientExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ServerCertTypeClientExtensionCont0Input<'a, 'b, 'x>> for ServerCertTypeClientExtensionCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CertificateTypeCombinator>>;

    open spec fn requires(&self, deps: ServerCertTypeClientExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ServerCertTypeClientExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_server_cert_type_client_extension_cont0(deps@)
    }

    fn apply(&self, deps: ServerCertTypeClientExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_type()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_type()))
            }
        }
    }
}
                
pub type SpecDistinguishedName = SpecOpaque1Ffff;
pub type DistinguishedName<'a> = Opaque1Ffff<'a>;
pub type DistinguishedNameRef<'a> = &'a Opaque1Ffff<'a>;


pub struct SpecDistinguishedNameCombinator(SpecDistinguishedNameCombinatorAlias);

impl SpecCombinator for SpecDistinguishedNameCombinator {
    type Type = SpecDistinguishedName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDistinguishedNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDistinguishedNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecDistinguishedNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct DistinguishedNameCombinator(DistinguishedNameCombinatorAlias);

impl View for DistinguishedNameCombinator {
    type V = SpecDistinguishedNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecDistinguishedNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DistinguishedNameCombinator {
    type Type = DistinguishedName<'a>;
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
pub type DistinguishedNameCombinatorAlias = Opaque1FfffCombinator;


pub closed spec fn spec_distinguished_name() -> SpecDistinguishedNameCombinator {
    SpecDistinguishedNameCombinator(spec_opaque_1_ffff())
}

                
pub fn distinguished_name() -> (o: DistinguishedNameCombinator)
    ensures o@ == spec_distinguished_name(),
{
    DistinguishedNameCombinator(opaque_1_ffff())
}

                

pub struct SpecCertificateAuthoritiesExtension {
    pub l: u16,
    pub list: Seq<SpecDistinguishedName>,
}

pub type SpecCertificateAuthoritiesExtensionInner = (u16, Seq<SpecDistinguishedName>);


impl SpecFrom<SpecCertificateAuthoritiesExtension> for SpecCertificateAuthoritiesExtensionInner {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtension) -> SpecCertificateAuthoritiesExtensionInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecCertificateAuthoritiesExtensionInner> for SpecCertificateAuthoritiesExtension {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtensionInner) -> SpecCertificateAuthoritiesExtension {
        let (l, list) = m;
        SpecCertificateAuthoritiesExtension { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateAuthoritiesExtension<'a> {
    pub l: u16,
    pub list: RepeatResult<DistinguishedName<'a>>,
}

impl View for CertificateAuthoritiesExtension<'_> {
    type V = SpecCertificateAuthoritiesExtension;

    open spec fn view(&self) -> Self::V {
        SpecCertificateAuthoritiesExtension {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type CertificateAuthoritiesExtensionInner<'a> = (u16, RepeatResult<DistinguishedName<'a>>);

pub type CertificateAuthoritiesExtensionInnerRef<'a> = (&'a u16, &'a RepeatResult<DistinguishedName<'a>>);
impl<'a> From<&'a CertificateAuthoritiesExtension<'a>> for CertificateAuthoritiesExtensionInnerRef<'a> {
    fn ex_from(m: &'a CertificateAuthoritiesExtension) -> CertificateAuthoritiesExtensionInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<CertificateAuthoritiesExtensionInner<'a>> for CertificateAuthoritiesExtension<'a> {
    fn ex_from(m: CertificateAuthoritiesExtensionInner) -> CertificateAuthoritiesExtension {
        let (l, list) = m;
        CertificateAuthoritiesExtension { l, list }
    }
}

pub struct CertificateAuthoritiesExtensionMapper;
impl View for CertificateAuthoritiesExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateAuthoritiesExtensionMapper {
    type Src = SpecCertificateAuthoritiesExtensionInner;
    type Dst = SpecCertificateAuthoritiesExtension;
}
impl SpecIsoProof for CertificateAuthoritiesExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateAuthoritiesExtensionMapper {
    type Src = CertificateAuthoritiesExtensionInner<'a>;
    type Dst = CertificateAuthoritiesExtension<'a>;
    type RefSrc = CertificateAuthoritiesExtensionInnerRef<'a>;
}

pub struct SpecCertificateAuthoritiesExtensionCombinator(SpecCertificateAuthoritiesExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    type Type = SpecCertificateAuthoritiesExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateAuthoritiesExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateAuthoritiesExtensionCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate7402808336413996182>, AndThen<bytes::Variable, Repeat<SpecDistinguishedNameCombinator>>>, CertificateAuthoritiesExtensionMapper>;
pub struct Predicate7402808336413996182;
impl View for Predicate7402808336413996182 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate7402808336413996182 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate7402808336413996182 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 3 && i <= 65535)
    }
}

pub struct CertificateAuthoritiesExtensionCombinator(CertificateAuthoritiesExtensionCombinatorAlias);

impl View for CertificateAuthoritiesExtensionCombinator {
    type V = SpecCertificateAuthoritiesExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateAuthoritiesExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateAuthoritiesExtensionCombinator {
    type Type = CertificateAuthoritiesExtension<'a>;
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
pub type CertificateAuthoritiesExtensionCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate7402808336413996182>, AndThen<bytes::Variable, Repeat<DistinguishedNameCombinator>>, CertificateAuthoritiesExtensionCont0>, CertificateAuthoritiesExtensionMapper>;


pub closed spec fn spec_certificate_authorities_extension() -> SpecCertificateAuthoritiesExtensionCombinator {
    SpecCertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate7402808336413996182 }, |deps| spec_certificate_authorities_extension_cont0(deps)),
        mapper: CertificateAuthoritiesExtensionMapper,
    })
}

pub open spec fn spec_certificate_authorities_extension_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecDistinguishedNameCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_distinguished_name()))
}

impl View for CertificateAuthoritiesExtensionCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecDistinguishedNameCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_certificate_authorities_extension_cont0(deps)
        }
    }
}

                
pub fn certificate_authorities_extension() -> (o: CertificateAuthoritiesExtensionCombinator)
    ensures o@ == spec_certificate_authorities_extension(),
{
    CertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate7402808336413996182 }, CertificateAuthoritiesExtensionCont0),
        mapper: CertificateAuthoritiesExtensionMapper,
    })
}

pub struct CertificateAuthoritiesExtensionCont0;
type CertificateAuthoritiesExtensionCont0Type<'a, 'b> = &'b u16;
type CertificateAuthoritiesExtensionCont0SType<'a, 'x> = &'x u16;
type CertificateAuthoritiesExtensionCont0Input<'a, 'b, 'x> = POrSType<CertificateAuthoritiesExtensionCont0Type<'a, 'b>, CertificateAuthoritiesExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateAuthoritiesExtensionCont0Input<'a, 'b, 'x>> for CertificateAuthoritiesExtensionCont0 {
    type Output = AndThen<bytes::Variable, Repeat<DistinguishedNameCombinator>>;

    open spec fn requires(&self, deps: CertificateAuthoritiesExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateAuthoritiesExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_authorities_extension_cont0(deps@)
    }

    fn apply(&self, deps: CertificateAuthoritiesExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(distinguished_name()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(distinguished_name()))
            }
        }
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

pub type OidFilterInnerRef<'a> = (&'a Opaque1Ff<'a>, &'a Opaque0Ffff<'a>);
impl<'a> From<&'a OidFilter<'a>> for OidFilterInnerRef<'a> {
    fn ex_from(m: &'a OidFilter) -> OidFilterInnerRef<'a> {
        (&m.certificate_extension_oid, &m.certificate_extension_values)
    }
}

impl<'a> From<OidFilterInner<'a>> for OidFilter<'a> {
    fn ex_from(m: OidFilterInner) -> OidFilter {
        let (certificate_extension_oid, certificate_extension_values) = m;
        OidFilter { certificate_extension_oid, certificate_extension_values }
    }
}

pub struct OidFilterMapper;
impl View for OidFilterMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterMapper {
    type Src = SpecOidFilterInner;
    type Dst = SpecOidFilter;
}
impl SpecIsoProof for OidFilterMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OidFilterMapper {
    type Src = OidFilterInner<'a>;
    type Dst = OidFilter<'a>;
    type RefSrc = OidFilterInnerRef<'a>;
}
type SpecOidFilterCombinatorAlias1 = (SpecOpaque1FfCombinator, SpecOpaque0FfffCombinator);
pub struct SpecOidFilterCombinator(SpecOidFilterCombinatorAlias);

impl SpecCombinator for SpecOidFilterCombinator {
    type Type = SpecOidFilter;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOidFilterCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterCombinatorAlias::is_prefix_secure() }
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
pub type SpecOidFilterCombinatorAlias = Mapped<SpecOidFilterCombinatorAlias1, OidFilterMapper>;
type OidFilterCombinatorAlias1 = (Opaque1FfCombinator, Opaque0FfffCombinator);
struct OidFilterCombinator1(OidFilterCombinatorAlias1);
impl View for OidFilterCombinator1 {
    type V = SpecOidFilterCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(OidFilterCombinator1, OidFilterCombinatorAlias1);

pub struct OidFilterCombinator(OidFilterCombinatorAlias);

impl View for OidFilterCombinator {
    type V = SpecOidFilterCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OidFilterCombinator {
    type Type = OidFilter<'a>;
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
pub type OidFilterCombinatorAlias = Mapped<OidFilterCombinator1, OidFilterMapper>;


pub closed spec fn spec_oid_filter() -> SpecOidFilterCombinator {
    SpecOidFilterCombinator(
    Mapped {
        inner: (spec_opaque_1_ff(), spec_opaque_0_ffff()),
        mapper: OidFilterMapper,
    })
}

                
pub fn oid_filter() -> (o: OidFilterCombinator)
    ensures o@ == spec_oid_filter(),
{
    OidFilterCombinator(
    Mapped {
        inner: OidFilterCombinator1((opaque_1_ff(), opaque_0_ffff())),
        mapper: OidFilterMapper,
    })
}

                

pub struct SpecOidFilterExtension {
    pub l: u16,
    pub list: Seq<SpecOidFilter>,
}

pub type SpecOidFilterExtensionInner = (u16, Seq<SpecOidFilter>);


impl SpecFrom<SpecOidFilterExtension> for SpecOidFilterExtensionInner {
    open spec fn spec_from(m: SpecOidFilterExtension) -> SpecOidFilterExtensionInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecOidFilterExtensionInner> for SpecOidFilterExtension {
    open spec fn spec_from(m: SpecOidFilterExtensionInner) -> SpecOidFilterExtension {
        let (l, list) = m;
        SpecOidFilterExtension { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct OidFilterExtension<'a> {
    pub l: u16,
    pub list: RepeatResult<OidFilter<'a>>,
}

impl View for OidFilterExtension<'_> {
    type V = SpecOidFilterExtension;

    open spec fn view(&self) -> Self::V {
        SpecOidFilterExtension {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type OidFilterExtensionInner<'a> = (u16, RepeatResult<OidFilter<'a>>);

pub type OidFilterExtensionInnerRef<'a> = (&'a u16, &'a RepeatResult<OidFilter<'a>>);
impl<'a> From<&'a OidFilterExtension<'a>> for OidFilterExtensionInnerRef<'a> {
    fn ex_from(m: &'a OidFilterExtension) -> OidFilterExtensionInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<OidFilterExtensionInner<'a>> for OidFilterExtension<'a> {
    fn ex_from(m: OidFilterExtensionInner) -> OidFilterExtension {
        let (l, list) = m;
        OidFilterExtension { l, list }
    }
}

pub struct OidFilterExtensionMapper;
impl View for OidFilterExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterExtensionMapper {
    type Src = SpecOidFilterExtensionInner;
    type Dst = SpecOidFilterExtension;
}
impl SpecIsoProof for OidFilterExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for OidFilterExtensionMapper {
    type Src = OidFilterExtensionInner<'a>;
    type Dst = OidFilterExtension<'a>;
    type RefSrc = OidFilterExtensionInnerRef<'a>;
}

pub struct SpecOidFilterExtensionCombinator(SpecOidFilterExtensionCombinatorAlias);

impl SpecCombinator for SpecOidFilterExtensionCombinator {
    type Type = SpecOidFilterExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOidFilterExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecOidFilterExtensionCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecOidFilterCombinator>>>, OidFilterExtensionMapper>;

pub struct OidFilterExtensionCombinator(OidFilterExtensionCombinatorAlias);

impl View for OidFilterExtensionCombinator {
    type V = SpecOidFilterExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OidFilterExtensionCombinator {
    type Type = OidFilterExtension<'a>;
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
pub type OidFilterExtensionCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<OidFilterCombinator>>, OidFilterExtensionCont0>, OidFilterExtensionMapper>;


pub closed spec fn spec_oid_filter_extension() -> SpecOidFilterExtensionCombinator {
    SpecOidFilterExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_oid_filter_extension_cont0(deps)),
        mapper: OidFilterExtensionMapper,
    })
}

pub open spec fn spec_oid_filter_extension_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecOidFilterCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_oid_filter()))
}

impl View for OidFilterExtensionCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecOidFilterCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_oid_filter_extension_cont0(deps)
        }
    }
}

                
pub fn oid_filter_extension() -> (o: OidFilterExtensionCombinator)
    ensures o@ == spec_oid_filter_extension(),
{
    OidFilterExtensionCombinator(
    Mapped {
        inner: Pair::new(U16Be, OidFilterExtensionCont0),
        mapper: OidFilterExtensionMapper,
    })
}

pub struct OidFilterExtensionCont0;
type OidFilterExtensionCont0Type<'a, 'b> = &'b u16;
type OidFilterExtensionCont0SType<'a, 'x> = &'x u16;
type OidFilterExtensionCont0Input<'a, 'b, 'x> = POrSType<OidFilterExtensionCont0Type<'a, 'b>, OidFilterExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<OidFilterExtensionCont0Input<'a, 'b, 'x>> for OidFilterExtensionCont0 {
    type Output = AndThen<bytes::Variable, Repeat<OidFilterCombinator>>;

    open spec fn requires(&self, deps: OidFilterExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: OidFilterExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_oid_filter_extension_cont0(deps@)
    }

    fn apply(&self, deps: OidFilterExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(oid_filter()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(oid_filter()))
            }
        }
    }
}
                

pub enum SpecClientHelloExtensionRest {
    MaxFragmentLength(SpecMaxFragmentLength),
    Heartbeat(SpecHeartbeatMode),
    SignedCertificateTimeStamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(Seq<u8>),
    Cookie(SpecCookie),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    Unrecognized(Seq<u8>),
}

pub type SpecClientHelloExtensionRestInner = Either<SpecMaxFragmentLength, Either<SpecHeartbeatMode, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<Seq<u8>, Either<SpecCookie, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecSignatureSchemeList, Seq<u8>>>>>>>>>>>;

impl SpecFrom<SpecClientHelloExtensionRest> for SpecClientHelloExtensionRestInner {
    open spec fn spec_from(m: SpecClientHelloExtensionRest) -> SpecClientHelloExtensionRestInner {
        match m {
            SpecClientHelloExtensionRest::MaxFragmentLength(m) => Either::Left(m),
            SpecClientHelloExtensionRest::Heartbeat(m) => Either::Right(Either::Left(m)),
            SpecClientHelloExtensionRest::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecClientHelloExtensionRest::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecClientHelloExtensionRest::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecClientHelloExtensionRest::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecClientHelloExtensionRest::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecClientHelloExtensionRest::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecClientHelloExtensionRest::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecClientHelloExtensionRest::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecClientHelloExtensionRest::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

                
impl SpecFrom<SpecClientHelloExtensionRestInner> for SpecClientHelloExtensionRest {
    open spec fn spec_from(m: SpecClientHelloExtensionRestInner) -> SpecClientHelloExtensionRest {
        match m {
            Either::Left(m) => SpecClientHelloExtensionRest::MaxFragmentLength(m),
            Either::Right(Either::Left(m)) => SpecClientHelloExtensionRest::Heartbeat(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecClientHelloExtensionRest::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecClientHelloExtensionRest::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecClientHelloExtensionRest::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecClientHelloExtensionRest::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecClientHelloExtensionRest::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecClientHelloExtensionRest::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecClientHelloExtensionRest::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecClientHelloExtensionRest::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecClientHelloExtensionRest::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClientHelloExtensionRest<'a> {
    MaxFragmentLength(MaxFragmentLength),
    Heartbeat(HeartbeatMode),
    SignedCertificateTimeStamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(&'a [u8]),
    Cookie(Cookie<'a>),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    Unrecognized(&'a [u8]),
}

pub type ClientHelloExtensionRestInner<'a> = Either<MaxFragmentLength, Either<HeartbeatMode, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<&'a [u8], Either<Cookie<'a>, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<SignatureSchemeList, &'a [u8]>>>>>>>>>>;

pub type ClientHelloExtensionRestInnerRef<'a> = Either<&'a MaxFragmentLength, Either<&'a HeartbeatMode, Either<&'a SignedCertificateTimestampList<'a>, Either<&'a ClientCertTypeClientExtension, Either<&'a ServerCertTypeClientExtension, Either<&'a &'a [u8], Either<&'a Cookie<'a>, Either<&'a CertificateAuthoritiesExtension<'a>, Either<&'a OidFilterExtension<'a>, Either<&'a SignatureSchemeList, &'a &'a [u8]>>>>>>>>>>;


impl<'a> View for ClientHelloExtensionRest<'a> {
    type V = SpecClientHelloExtensionRest;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionRest::MaxFragmentLength(m) => SpecClientHelloExtensionRest::MaxFragmentLength(m@),
            ClientHelloExtensionRest::Heartbeat(m) => SpecClientHelloExtensionRest::Heartbeat(m@),
            ClientHelloExtensionRest::SignedCertificateTimeStamp(m) => SpecClientHelloExtensionRest::SignedCertificateTimeStamp(m@),
            ClientHelloExtensionRest::ClientCertificateType(m) => SpecClientHelloExtensionRest::ClientCertificateType(m@),
            ClientHelloExtensionRest::ServerCertificateType(m) => SpecClientHelloExtensionRest::ServerCertificateType(m@),
            ClientHelloExtensionRest::Padding(m) => SpecClientHelloExtensionRest::Padding(m@),
            ClientHelloExtensionRest::Cookie(m) => SpecClientHelloExtensionRest::Cookie(m@),
            ClientHelloExtensionRest::CertificateAuthorities(m) => SpecClientHelloExtensionRest::CertificateAuthorities(m@),
            ClientHelloExtensionRest::OidFilters(m) => SpecClientHelloExtensionRest::OidFilters(m@),
            ClientHelloExtensionRest::SignatureAlgorithmsCert(m) => SpecClientHelloExtensionRest::SignatureAlgorithmsCert(m@),
            ClientHelloExtensionRest::Unrecognized(m) => SpecClientHelloExtensionRest::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a ClientHelloExtensionRest<'a>> for ClientHelloExtensionRestInnerRef<'a> {
    fn ex_from(m: &'a ClientHelloExtensionRest<'a>) -> ClientHelloExtensionRestInnerRef<'a> {
        match m {
            ClientHelloExtensionRest::MaxFragmentLength(m) => Either::Left(m),
            ClientHelloExtensionRest::Heartbeat(m) => Either::Right(Either::Left(m)),
            ClientHelloExtensionRest::SignedCertificateTimeStamp(m) => Either::Right(Either::Right(Either::Left(m))),
            ClientHelloExtensionRest::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionRest::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionRest::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionRest::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionRest::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionRest::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionRest::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ClientHelloExtensionRest::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

impl<'a> From<ClientHelloExtensionRestInner<'a>> for ClientHelloExtensionRest<'a> {
    fn ex_from(m: ClientHelloExtensionRestInner<'a>) -> ClientHelloExtensionRest<'a> {
        match m {
            Either::Left(m) => ClientHelloExtensionRest::MaxFragmentLength(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionRest::Heartbeat(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionRest::SignedCertificateTimeStamp(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionRest::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionRest::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionRest::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionRest::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionRest::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionRest::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ClientHelloExtensionRest::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => ClientHelloExtensionRest::Unrecognized(m),
        }
    }
    
}


pub struct ClientHelloExtensionRestMapper;
impl View for ClientHelloExtensionRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionRestMapper {
    type Src = SpecClientHelloExtensionRestInner;
    type Dst = SpecClientHelloExtensionRest;
}
impl SpecIsoProof for ClientHelloExtensionRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientHelloExtensionRestMapper {
    type Src = ClientHelloExtensionRestInner<'a>;
    type Dst = ClientHelloExtensionRest<'a>;
    type RefSrc = ClientHelloExtensionRestInnerRef<'a>;
}

type SpecClientHelloExtensionRestCombinatorAlias1 = Choice<Cond<SpecSignatureSchemeListCombinator>, Cond<bytes::Variable>>;
type SpecClientHelloExtensionRestCombinatorAlias2 = Choice<Cond<SpecOidFilterExtensionCombinator>, SpecClientHelloExtensionRestCombinatorAlias1>;
type SpecClientHelloExtensionRestCombinatorAlias3 = Choice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, SpecClientHelloExtensionRestCombinatorAlias2>;
type SpecClientHelloExtensionRestCombinatorAlias4 = Choice<Cond<SpecCookieCombinator>, SpecClientHelloExtensionRestCombinatorAlias3>;
type SpecClientHelloExtensionRestCombinatorAlias5 = Choice<Cond<bytes::Variable>, SpecClientHelloExtensionRestCombinatorAlias4>;
type SpecClientHelloExtensionRestCombinatorAlias6 = Choice<Cond<SpecServerCertTypeClientExtensionCombinator>, SpecClientHelloExtensionRestCombinatorAlias5>;
type SpecClientHelloExtensionRestCombinatorAlias7 = Choice<Cond<SpecClientCertTypeClientExtensionCombinator>, SpecClientHelloExtensionRestCombinatorAlias6>;
type SpecClientHelloExtensionRestCombinatorAlias8 = Choice<Cond<SpecSignedCertificateTimestampListCombinator>, SpecClientHelloExtensionRestCombinatorAlias7>;
type SpecClientHelloExtensionRestCombinatorAlias9 = Choice<Cond<SpecHeartbeatModeCombinator>, SpecClientHelloExtensionRestCombinatorAlias8>;
type SpecClientHelloExtensionRestCombinatorAlias10 = Choice<Cond<SpecMaxFragmentLengthCombinator>, SpecClientHelloExtensionRestCombinatorAlias9>;
pub struct SpecClientHelloExtensionRestCombinator(SpecClientHelloExtensionRestCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionRestCombinator {
    type Type = SpecClientHelloExtensionRest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientHelloExtensionRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientHelloExtensionRestCombinatorAlias = Mapped<SpecClientHelloExtensionRestCombinatorAlias10, ClientHelloExtensionRestMapper>;
type ClientHelloExtensionRestCombinatorAlias1 = Choice<Cond<SignatureSchemeListCombinator>, Cond<bytes::Variable>>;
type ClientHelloExtensionRestCombinatorAlias2 = Choice<Cond<OidFilterExtensionCombinator>, ClientHelloExtensionRestCombinator1>;
type ClientHelloExtensionRestCombinatorAlias3 = Choice<Cond<CertificateAuthoritiesExtensionCombinator>, ClientHelloExtensionRestCombinator2>;
type ClientHelloExtensionRestCombinatorAlias4 = Choice<Cond<CookieCombinator>, ClientHelloExtensionRestCombinator3>;
type ClientHelloExtensionRestCombinatorAlias5 = Choice<Cond<bytes::Variable>, ClientHelloExtensionRestCombinator4>;
type ClientHelloExtensionRestCombinatorAlias6 = Choice<Cond<ServerCertTypeClientExtensionCombinator>, ClientHelloExtensionRestCombinator5>;
type ClientHelloExtensionRestCombinatorAlias7 = Choice<Cond<ClientCertTypeClientExtensionCombinator>, ClientHelloExtensionRestCombinator6>;
type ClientHelloExtensionRestCombinatorAlias8 = Choice<Cond<SignedCertificateTimestampListCombinator>, ClientHelloExtensionRestCombinator7>;
type ClientHelloExtensionRestCombinatorAlias9 = Choice<Cond<HeartbeatModeCombinator>, ClientHelloExtensionRestCombinator8>;
type ClientHelloExtensionRestCombinatorAlias10 = Choice<Cond<MaxFragmentLengthCombinator>, ClientHelloExtensionRestCombinator9>;
struct ClientHelloExtensionRestCombinator1(ClientHelloExtensionRestCombinatorAlias1);
impl View for ClientHelloExtensionRestCombinator1 {
    type V = SpecClientHelloExtensionRestCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator1, ClientHelloExtensionRestCombinatorAlias1);

struct ClientHelloExtensionRestCombinator2(ClientHelloExtensionRestCombinatorAlias2);
impl View for ClientHelloExtensionRestCombinator2 {
    type V = SpecClientHelloExtensionRestCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator2, ClientHelloExtensionRestCombinatorAlias2);

struct ClientHelloExtensionRestCombinator3(ClientHelloExtensionRestCombinatorAlias3);
impl View for ClientHelloExtensionRestCombinator3 {
    type V = SpecClientHelloExtensionRestCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator3, ClientHelloExtensionRestCombinatorAlias3);

struct ClientHelloExtensionRestCombinator4(ClientHelloExtensionRestCombinatorAlias4);
impl View for ClientHelloExtensionRestCombinator4 {
    type V = SpecClientHelloExtensionRestCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator4, ClientHelloExtensionRestCombinatorAlias4);

struct ClientHelloExtensionRestCombinator5(ClientHelloExtensionRestCombinatorAlias5);
impl View for ClientHelloExtensionRestCombinator5 {
    type V = SpecClientHelloExtensionRestCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator5, ClientHelloExtensionRestCombinatorAlias5);

struct ClientHelloExtensionRestCombinator6(ClientHelloExtensionRestCombinatorAlias6);
impl View for ClientHelloExtensionRestCombinator6 {
    type V = SpecClientHelloExtensionRestCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator6, ClientHelloExtensionRestCombinatorAlias6);

struct ClientHelloExtensionRestCombinator7(ClientHelloExtensionRestCombinatorAlias7);
impl View for ClientHelloExtensionRestCombinator7 {
    type V = SpecClientHelloExtensionRestCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator7, ClientHelloExtensionRestCombinatorAlias7);

struct ClientHelloExtensionRestCombinator8(ClientHelloExtensionRestCombinatorAlias8);
impl View for ClientHelloExtensionRestCombinator8 {
    type V = SpecClientHelloExtensionRestCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator8, ClientHelloExtensionRestCombinatorAlias8);

struct ClientHelloExtensionRestCombinator9(ClientHelloExtensionRestCombinatorAlias9);
impl View for ClientHelloExtensionRestCombinator9 {
    type V = SpecClientHelloExtensionRestCombinatorAlias9;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator9, ClientHelloExtensionRestCombinatorAlias9);

struct ClientHelloExtensionRestCombinator10(ClientHelloExtensionRestCombinatorAlias10);
impl View for ClientHelloExtensionRestCombinator10 {
    type V = SpecClientHelloExtensionRestCombinatorAlias10;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionRestCombinator10, ClientHelloExtensionRestCombinatorAlias10);

pub struct ClientHelloExtensionRestCombinator(ClientHelloExtensionRestCombinatorAlias);

impl View for ClientHelloExtensionRestCombinator {
    type V = SpecClientHelloExtensionRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientHelloExtensionRestCombinator {
    type Type = ClientHelloExtensionRest<'a>;
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
pub type ClientHelloExtensionRestCombinatorAlias = Mapped<ClientHelloExtensionRestCombinator10, ClientHelloExtensionRestMapper>;


pub closed spec fn spec_client_hello_extension_rest(ext_len: u16, extension_type: SpecExtensionType) -> SpecClientHelloExtensionRestCombinator {
    SpecClientHelloExtensionRestCombinator(Mapped { inner: Choice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, Choice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, Choice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, Choice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, Choice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, Choice(Cond { cond: extension_type == 21, inner: bytes::Variable(ext_len.spec_into()) }, Choice(Cond { cond: extension_type == 44, inner: spec_cookie() }, Choice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, Choice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, Choice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, Cond { cond: !(extension_type == 1 || extension_type == 15 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 44 || extension_type == 47 || extension_type == 48 || extension_type == 50), inner: bytes::Variable(ext_len.spec_into()) })))))))))), mapper: ClientHelloExtensionRestMapper })
}

pub fn client_hello_extension_rest<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: ClientHelloExtensionRestCombinator)
    ensures o@ == spec_client_hello_extension_rest(ext_len@, extension_type@),
{
    ClientHelloExtensionRestCombinator(Mapped { inner: ClientHelloExtensionRestCombinator10(Choice::new(Cond { cond: extension_type == 1, inner: max_fragment_length() }, ClientHelloExtensionRestCombinator9(Choice::new(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, ClientHelloExtensionRestCombinator8(Choice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, ClientHelloExtensionRestCombinator7(Choice::new(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, ClientHelloExtensionRestCombinator6(Choice::new(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, ClientHelloExtensionRestCombinator5(Choice::new(Cond { cond: extension_type == 21, inner: bytes::Variable(ext_len.ex_into()) }, ClientHelloExtensionRestCombinator4(Choice::new(Cond { cond: extension_type == 44, inner: cookie() }, ClientHelloExtensionRestCombinator3(Choice::new(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, ClientHelloExtensionRestCombinator2(Choice::new(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, ClientHelloExtensionRestCombinator1(Choice::new(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, Cond { cond: !(extension_type == 1 || extension_type == 15 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 44 || extension_type == 47 || extension_type == 48 || extension_type == 50), inner: bytes::Variable(ext_len.ex_into()) })))))))))))))))))))), mapper: ClientHelloExtensionRestMapper })
}


pub enum SpecClientHelloExtensionExtensionData {
    ServerName(SpecServerNameList),
    SignatureAlgorithms(SpecSignatureSchemeList),
    SupportedGroups(SpecNamedGroupList),
    StatusRequest(SpecCertificateStatusRequest),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SupportedVersions(SpecSupportedVersionsClient),
    KeyShare(SpecKeyShareClientHello),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    Unrecognized(SpecClientHelloExtensionRest),
}

pub type SpecClientHelloExtensionExtensionDataInner = Either<SpecServerNameList, Either<SpecSignatureSchemeList, Either<SpecNamedGroupList, Either<SpecCertificateStatusRequest, Either<SpecProtocolNameList, Either<SpecSupportedVersionsClient, Either<SpecKeyShareClientHello, Either<SpecPskKeyExchangeModes, Either<SpecPreSharedKeyClientExtension, SpecClientHelloExtensionRest>>>>>>>>>;

impl SpecFrom<SpecClientHelloExtensionExtensionData> for SpecClientHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionData) -> SpecClientHelloExtensionExtensionDataInner {
        match m {
            SpecClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Left(m)),
            SpecClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }

}

                
impl SpecFrom<SpecClientHelloExtensionExtensionDataInner> for SpecClientHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionDataInner) -> SpecClientHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => SpecClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClientHelloExtensionExtensionData<'a> {
    ServerName(ServerNameList<'a>),
    SignatureAlgorithms(SignatureSchemeList),
    SupportedGroups(NamedGroupList),
    StatusRequest(CertificateStatusRequest<'a>),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SupportedVersions(SupportedVersionsClient),
    KeyShare(KeyShareClientHello<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    Unrecognized(ClientHelloExtensionRest<'a>),
}

pub type ClientHelloExtensionExtensionDataInner<'a> = Either<ServerNameList<'a>, Either<SignatureSchemeList, Either<NamedGroupList, Either<CertificateStatusRequest<'a>, Either<ProtocolNameList<'a>, Either<SupportedVersionsClient, Either<KeyShareClientHello<'a>, Either<PskKeyExchangeModes, Either<PreSharedKeyClientExtension<'a>, ClientHelloExtensionRest<'a>>>>>>>>>>;

pub type ClientHelloExtensionExtensionDataInnerRef<'a> = Either<&'a ServerNameList<'a>, Either<&'a SignatureSchemeList, Either<&'a NamedGroupList, Either<&'a CertificateStatusRequest<'a>, Either<&'a ProtocolNameList<'a>, Either<&'a SupportedVersionsClient, Either<&'a KeyShareClientHello<'a>, Either<&'a PskKeyExchangeModes, Either<&'a PreSharedKeyClientExtension<'a>, &'a ClientHelloExtensionRest<'a>>>>>>>>>>;


impl<'a> View for ClientHelloExtensionExtensionData<'a> {
    type V = SpecClientHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionExtensionData::ServerName(m) => SpecClientHelloExtensionExtensionData::ServerName(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m@),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => SpecClientHelloExtensionExtensionData::SupportedGroups(m@),
            ClientHelloExtensionExtensionData::StatusRequest(m) => SpecClientHelloExtensionExtensionData::StatusRequest(m@),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => SpecClientHelloExtensionExtensionData::SupportedVersions(m@),
            ClientHelloExtensionExtensionData::KeyShare(m) => SpecClientHelloExtensionExtensionData::KeyShare(m@),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => SpecClientHelloExtensionExtensionData::PreSharedKey(m@),
            ClientHelloExtensionExtensionData::Unrecognized(m) => SpecClientHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a ClientHelloExtensionExtensionData<'a>> for ClientHelloExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a ClientHelloExtensionExtensionData<'a>) -> ClientHelloExtensionExtensionDataInnerRef<'a> {
        match m {
            ClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Left(m)),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Left(m))),
            ClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }

}

impl<'a> From<ClientHelloExtensionExtensionDataInner<'a>> for ClientHelloExtensionExtensionData<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionDataInner<'a>) -> ClientHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => ClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => ClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }
    
}


pub struct ClientHelloExtensionExtensionDataMapper;
impl View for ClientHelloExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionExtensionDataMapper {
    type Src = SpecClientHelloExtensionExtensionDataInner;
    type Dst = SpecClientHelloExtensionExtensionData;
}
impl SpecIsoProof for ClientHelloExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientHelloExtensionExtensionDataMapper {
    type Src = ClientHelloExtensionExtensionDataInner<'a>;
    type Dst = ClientHelloExtensionExtensionData<'a>;
    type RefSrc = ClientHelloExtensionExtensionDataInnerRef<'a>;
}

type SpecClientHelloExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecPreSharedKeyClientExtensionCombinator>, Cond<SpecClientHelloExtensionRestCombinator>>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecPskKeyExchangeModesCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias1>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SpecKeyShareClientHelloCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias2>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias4 = Choice<Cond<SpecSupportedVersionsClientCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias3>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias5 = Choice<Cond<SpecProtocolNameListCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias4>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias6 = Choice<Cond<SpecCertificateStatusRequestCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias5>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias7 = Choice<Cond<SpecNamedGroupListCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias6>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias8 = Choice<Cond<SpecSignatureSchemeListCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias7>;
type SpecClientHelloExtensionExtensionDataCombinatorAlias9 = Choice<Cond<SpecServerNameListCombinator>, SpecClientHelloExtensionExtensionDataCombinatorAlias8>;
pub struct SpecClientHelloExtensionExtensionDataCombinator(SpecClientHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    type Type = SpecClientHelloExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientHelloExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecClientHelloExtensionExtensionDataCombinatorAlias9, ClientHelloExtensionExtensionDataMapper>>;
type ClientHelloExtensionExtensionDataCombinatorAlias1 = Choice<Cond<PreSharedKeyClientExtensionCombinator>, Cond<ClientHelloExtensionRestCombinator>>;
type ClientHelloExtensionExtensionDataCombinatorAlias2 = Choice<Cond<PskKeyExchangeModesCombinator>, ClientHelloExtensionExtensionDataCombinator1>;
type ClientHelloExtensionExtensionDataCombinatorAlias3 = Choice<Cond<KeyShareClientHelloCombinator>, ClientHelloExtensionExtensionDataCombinator2>;
type ClientHelloExtensionExtensionDataCombinatorAlias4 = Choice<Cond<SupportedVersionsClientCombinator>, ClientHelloExtensionExtensionDataCombinator3>;
type ClientHelloExtensionExtensionDataCombinatorAlias5 = Choice<Cond<ProtocolNameListCombinator>, ClientHelloExtensionExtensionDataCombinator4>;
type ClientHelloExtensionExtensionDataCombinatorAlias6 = Choice<Cond<CertificateStatusRequestCombinator>, ClientHelloExtensionExtensionDataCombinator5>;
type ClientHelloExtensionExtensionDataCombinatorAlias7 = Choice<Cond<NamedGroupListCombinator>, ClientHelloExtensionExtensionDataCombinator6>;
type ClientHelloExtensionExtensionDataCombinatorAlias8 = Choice<Cond<SignatureSchemeListCombinator>, ClientHelloExtensionExtensionDataCombinator7>;
type ClientHelloExtensionExtensionDataCombinatorAlias9 = Choice<Cond<ServerNameListCombinator>, ClientHelloExtensionExtensionDataCombinator8>;
struct ClientHelloExtensionExtensionDataCombinator1(ClientHelloExtensionExtensionDataCombinatorAlias1);
impl View for ClientHelloExtensionExtensionDataCombinator1 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator1, ClientHelloExtensionExtensionDataCombinatorAlias1);

struct ClientHelloExtensionExtensionDataCombinator2(ClientHelloExtensionExtensionDataCombinatorAlias2);
impl View for ClientHelloExtensionExtensionDataCombinator2 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator2, ClientHelloExtensionExtensionDataCombinatorAlias2);

struct ClientHelloExtensionExtensionDataCombinator3(ClientHelloExtensionExtensionDataCombinatorAlias3);
impl View for ClientHelloExtensionExtensionDataCombinator3 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator3, ClientHelloExtensionExtensionDataCombinatorAlias3);

struct ClientHelloExtensionExtensionDataCombinator4(ClientHelloExtensionExtensionDataCombinatorAlias4);
impl View for ClientHelloExtensionExtensionDataCombinator4 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator4, ClientHelloExtensionExtensionDataCombinatorAlias4);

struct ClientHelloExtensionExtensionDataCombinator5(ClientHelloExtensionExtensionDataCombinatorAlias5);
impl View for ClientHelloExtensionExtensionDataCombinator5 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator5, ClientHelloExtensionExtensionDataCombinatorAlias5);

struct ClientHelloExtensionExtensionDataCombinator6(ClientHelloExtensionExtensionDataCombinatorAlias6);
impl View for ClientHelloExtensionExtensionDataCombinator6 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator6, ClientHelloExtensionExtensionDataCombinatorAlias6);

struct ClientHelloExtensionExtensionDataCombinator7(ClientHelloExtensionExtensionDataCombinatorAlias7);
impl View for ClientHelloExtensionExtensionDataCombinator7 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator7, ClientHelloExtensionExtensionDataCombinatorAlias7);

struct ClientHelloExtensionExtensionDataCombinator8(ClientHelloExtensionExtensionDataCombinatorAlias8);
impl View for ClientHelloExtensionExtensionDataCombinator8 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator8, ClientHelloExtensionExtensionDataCombinatorAlias8);

struct ClientHelloExtensionExtensionDataCombinator9(ClientHelloExtensionExtensionDataCombinatorAlias9);
impl View for ClientHelloExtensionExtensionDataCombinator9 {
    type V = SpecClientHelloExtensionExtensionDataCombinatorAlias9;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloExtensionExtensionDataCombinator9, ClientHelloExtensionExtensionDataCombinatorAlias9);

pub struct ClientHelloExtensionExtensionDataCombinator(ClientHelloExtensionExtensionDataCombinatorAlias);

impl View for ClientHelloExtensionExtensionDataCombinator {
    type V = SpecClientHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientHelloExtensionExtensionDataCombinator {
    type Type = ClientHelloExtensionExtensionData<'a>;
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
pub type ClientHelloExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<ClientHelloExtensionExtensionDataCombinator9, ClientHelloExtensionExtensionDataMapper>>;


pub closed spec fn spec_client_hello_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecClientHelloExtensionExtensionDataCombinator {
    SpecClientHelloExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 0, inner: spec_server_name_list() }, Choice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, Choice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, Choice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, Choice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, Choice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, Choice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, Choice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, Choice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, Cond { cond: !(extension_type == 0 || extension_type == 13 || extension_type == 10 || extension_type == 5 || extension_type == 16 || extension_type == 43 || extension_type == 51 || extension_type == 45 || extension_type == 41), inner: spec_client_hello_extension_rest(ext_len, extension_type) }))))))))), mapper: ClientHelloExtensionExtensionDataMapper }))
}

pub fn client_hello_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: ClientHelloExtensionExtensionDataCombinator)
    ensures o@ == spec_client_hello_extension_extension_data(extension_type@, ext_len@),
{
    ClientHelloExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: ClientHelloExtensionExtensionDataCombinator9(Choice::new(Cond { cond: extension_type == 0, inner: server_name_list() }, ClientHelloExtensionExtensionDataCombinator8(Choice::new(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, ClientHelloExtensionExtensionDataCombinator7(Choice::new(Cond { cond: extension_type == 10, inner: named_group_list() }, ClientHelloExtensionExtensionDataCombinator6(Choice::new(Cond { cond: extension_type == 5, inner: certificate_status_request() }, ClientHelloExtensionExtensionDataCombinator5(Choice::new(Cond { cond: extension_type == 16, inner: protocol_name_list() }, ClientHelloExtensionExtensionDataCombinator4(Choice::new(Cond { cond: extension_type == 43, inner: supported_versions_client() }, ClientHelloExtensionExtensionDataCombinator3(Choice::new(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, ClientHelloExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, ClientHelloExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, Cond { cond: !(extension_type == 0 || extension_type == 13 || extension_type == 10 || extension_type == 5 || extension_type == 16 || extension_type == 43 || extension_type == 51 || extension_type == 45 || extension_type == 41), inner: client_hello_extension_rest(ext_len, extension_type) })))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper }))
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

pub type ClientHelloExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a ClientHelloExtensionExtensionData<'a>);
impl<'a> From<&'a ClientHelloExtension<'a>> for ClientHelloExtensionInnerRef<'a> {
    fn ex_from(m: &'a ClientHelloExtension) -> ClientHelloExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<ClientHelloExtensionInner<'a>> for ClientHelloExtension<'a> {
    fn ex_from(m: ClientHelloExtensionInner) -> ClientHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        ClientHelloExtension { extension_type, ext_len, extension_data }
    }
}

pub struct ClientHelloExtensionMapper;
impl View for ClientHelloExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionMapper {
    type Src = SpecClientHelloExtensionInner;
    type Dst = SpecClientHelloExtension;
}
impl SpecIsoProof for ClientHelloExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientHelloExtensionMapper {
    type Src = ClientHelloExtensionInner<'a>;
    type Dst = ClientHelloExtension<'a>;
    type RefSrc = ClientHelloExtensionInnerRef<'a>;
}

pub struct SpecClientHelloExtensionCombinator(SpecClientHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionCombinator {
    type Type = SpecClientHelloExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientHelloExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecClientHelloExtensionExtensionDataCombinator>, ClientHelloExtensionMapper>;

pub struct ClientHelloExtensionCombinator(ClientHelloExtensionCombinatorAlias);

impl View for ClientHelloExtensionCombinator {
    type V = SpecClientHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientHelloExtensionCombinator {
    type Type = ClientHelloExtension<'a>;
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
pub type ClientHelloExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, ClientHelloExtensionCont1>, ClientHelloExtensionExtensionDataCombinator, ClientHelloExtensionCont0>, ClientHelloExtensionMapper>;


pub closed spec fn spec_client_hello_extension() -> SpecClientHelloExtensionCombinator {
    SpecClientHelloExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_client_hello_extension_cont1(deps)), |deps| spec_client_hello_extension_cont0(deps)),
        mapper: ClientHelloExtensionMapper,
    })
}

pub open spec fn spec_client_hello_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for ClientHelloExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_client_hello_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_client_hello_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecClientHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_client_hello_extension_extension_data(extension_type, ext_len)
}

impl View for ClientHelloExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecClientHelloExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_client_hello_extension_cont0(deps)
        }
    }
}

                
pub fn client_hello_extension() -> (o: ClientHelloExtensionCombinator)
    ensures o@ == spec_client_hello_extension(),
{
    ClientHelloExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), ClientHelloExtensionCont1), ClientHelloExtensionCont0),
        mapper: ClientHelloExtensionMapper,
    })
}

pub struct ClientHelloExtensionCont1;
type ClientHelloExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type ClientHelloExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type ClientHelloExtensionCont1Input<'a, 'b, 'x> = POrSType<ClientHelloExtensionCont1Type<'a, 'b>, ClientHelloExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ClientHelloExtensionCont1Input<'a, 'b, 'x>> for ClientHelloExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: ClientHelloExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ClientHelloExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont1(deps@)
    }

    fn apply(&self, deps: ClientHelloExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct ClientHelloExtensionCont0;
type ClientHelloExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type ClientHelloExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type ClientHelloExtensionCont0Input<'a, 'b, 'x> = POrSType<ClientHelloExtensionCont0Type<'a, 'b>, ClientHelloExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ClientHelloExtensionCont0Input<'a, 'b, 'x>> for ClientHelloExtensionCont0 {
    type Output = ClientHelloExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: ClientHelloExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ClientHelloExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont0(deps@)
    }

    fn apply(&self, deps: ClientHelloExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                client_hello_extension_extension_data(extension_type, ext_len)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                client_hello_extension_extension_data(extension_type, ext_len)
            }
        }
    }
}
                

pub struct SpecClientExtensions {
    pub l: u16,
    pub list: Seq<SpecClientHelloExtension>,
}

pub type SpecClientExtensionsInner = (u16, Seq<SpecClientHelloExtension>);


impl SpecFrom<SpecClientExtensions> for SpecClientExtensionsInner {
    open spec fn spec_from(m: SpecClientExtensions) -> SpecClientExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecClientExtensionsInner> for SpecClientExtensions {
    open spec fn spec_from(m: SpecClientExtensionsInner) -> SpecClientExtensions {
        let (l, list) = m;
        SpecClientExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ClientExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<ClientHelloExtension<'a>>,
}

impl View for ClientExtensions<'_> {
    type V = SpecClientExtensions;

    open spec fn view(&self) -> Self::V {
        SpecClientExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type ClientExtensionsInner<'a> = (u16, RepeatResult<ClientHelloExtension<'a>>);

pub type ClientExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<ClientHelloExtension<'a>>);
impl<'a> From<&'a ClientExtensions<'a>> for ClientExtensionsInnerRef<'a> {
    fn ex_from(m: &'a ClientExtensions) -> ClientExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<ClientExtensionsInner<'a>> for ClientExtensions<'a> {
    fn ex_from(m: ClientExtensionsInner) -> ClientExtensions {
        let (l, list) = m;
        ClientExtensions { l, list }
    }
}

pub struct ClientExtensionsMapper;
impl View for ClientExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientExtensionsMapper {
    type Src = SpecClientExtensionsInner;
    type Dst = SpecClientExtensions;
}
impl SpecIsoProof for ClientExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientExtensionsMapper {
    type Src = ClientExtensionsInner<'a>;
    type Dst = ClientExtensions<'a>;
    type RefSrc = ClientExtensionsInnerRef<'a>;
}

pub struct SpecClientExtensionsCombinator(SpecClientExtensionsCombinatorAlias);

impl SpecCombinator for SpecClientExtensionsCombinator {
    type Type = SpecClientExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientExtensionsCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate9952414989822543135>, AndThen<bytes::Variable, Repeat<SpecClientHelloExtensionCombinator>>>, ClientExtensionsMapper>;
pub struct Predicate9952414989822543135;
impl View for Predicate9952414989822543135 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate9952414989822543135 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate9952414989822543135 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 8 && i <= 65535)
    }
}

pub struct ClientExtensionsCombinator(ClientExtensionsCombinatorAlias);

impl View for ClientExtensionsCombinator {
    type V = SpecClientExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientExtensionsCombinator {
    type Type = ClientExtensions<'a>;
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
pub type ClientExtensionsCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate9952414989822543135>, AndThen<bytes::Variable, Repeat<ClientHelloExtensionCombinator>>, ClientExtensionsCont0>, ClientExtensionsMapper>;


pub closed spec fn spec_client_extensions() -> SpecClientExtensionsCombinator {
    SpecClientExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate9952414989822543135 }, |deps| spec_client_extensions_cont0(deps)),
        mapper: ClientExtensionsMapper,
    })
}

pub open spec fn spec_client_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecClientHelloExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_client_hello_extension()))
}

impl View for ClientExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecClientHelloExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_client_extensions_cont0(deps)
        }
    }
}

                
pub fn client_extensions() -> (o: ClientExtensionsCombinator)
    ensures o@ == spec_client_extensions(),
{
    ClientExtensionsCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate9952414989822543135 }, ClientExtensionsCont0),
        mapper: ClientExtensionsMapper,
    })
}

pub struct ClientExtensionsCont0;
type ClientExtensionsCont0Type<'a, 'b> = &'b u16;
type ClientExtensionsCont0SType<'a, 'x> = &'x u16;
type ClientExtensionsCont0Input<'a, 'b, 'x> = POrSType<ClientExtensionsCont0Type<'a, 'b>, ClientExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ClientExtensionsCont0Input<'a, 'b, 'x>> for ClientExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ClientHelloExtensionCombinator>>;

    open spec fn requires(&self, deps: ClientExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ClientExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_client_extensions_cont0(deps@)
    }

    fn apply(&self, deps: ClientExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(client_hello_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(client_hello_extension()))
            }
        }
    }
}
                

pub struct SpecCipherSuiteList {
    pub l: u16,
    pub list: Seq<SpecCipherSuite>,
}

pub type SpecCipherSuiteListInner = (u16, Seq<SpecCipherSuite>);


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
    pub l: u16,
    pub list: RepeatResult<CipherSuite>,
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
pub type CipherSuiteListInner = (u16, RepeatResult<CipherSuite>);

pub type CipherSuiteListInnerRef<'a> = (&'a u16, &'a RepeatResult<CipherSuite>);
impl<'a> From<&'a CipherSuiteList> for CipherSuiteListInnerRef<'a> {
    fn ex_from(m: &'a CipherSuiteList) -> CipherSuiteListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<CipherSuiteListInner> for CipherSuiteList {
    fn ex_from(m: CipherSuiteListInner) -> CipherSuiteList {
        let (l, list) = m;
        CipherSuiteList { l, list }
    }
}

pub struct CipherSuiteListMapper;
impl View for CipherSuiteListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CipherSuiteListMapper {
    type Src = SpecCipherSuiteListInner;
    type Dst = SpecCipherSuiteList;
}
impl SpecIsoProof for CipherSuiteListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CipherSuiteListMapper {
    type Src = CipherSuiteListInner;
    type Dst = CipherSuiteList;
    type RefSrc = CipherSuiteListInnerRef<'a>;
}

pub struct SpecCipherSuiteListCombinator(SpecCipherSuiteListCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteListCombinator {
    type Type = SpecCipherSuiteList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCipherSuiteListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteListCombinatorAlias::is_prefix_secure() }
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
pub type SpecCipherSuiteListCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate15206902916018849611>, AndThen<bytes::Variable, Repeat<SpecCipherSuiteCombinator>>>, CipherSuiteListMapper>;

pub struct CipherSuiteListCombinator(CipherSuiteListCombinatorAlias);

impl View for CipherSuiteListCombinator {
    type V = SpecCipherSuiteListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CipherSuiteListCombinator {
    type Type = CipherSuiteList;
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
pub type CipherSuiteListCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate15206902916018849611>, AndThen<bytes::Variable, Repeat<CipherSuiteCombinator>>, CipherSuiteListCont0>, CipherSuiteListMapper>;


pub closed spec fn spec_cipher_suite_list() -> SpecCipherSuiteListCombinator {
    SpecCipherSuiteListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate15206902916018849611 }, |deps| spec_cipher_suite_list_cont0(deps)),
        mapper: CipherSuiteListMapper,
    })
}

pub open spec fn spec_cipher_suite_list_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecCipherSuiteCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_cipher_suite()))
}

impl View for CipherSuiteListCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecCipherSuiteCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_cipher_suite_list_cont0(deps)
        }
    }
}

                
pub fn cipher_suite_list() -> (o: CipherSuiteListCombinator)
    ensures o@ == spec_cipher_suite_list(),
{
    CipherSuiteListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate15206902916018849611 }, CipherSuiteListCont0),
        mapper: CipherSuiteListMapper,
    })
}

pub struct CipherSuiteListCont0;
type CipherSuiteListCont0Type<'a, 'b> = &'b u16;
type CipherSuiteListCont0SType<'a, 'x> = &'x u16;
type CipherSuiteListCont0Input<'a, 'b, 'x> = POrSType<CipherSuiteListCont0Type<'a, 'b>, CipherSuiteListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CipherSuiteListCont0Input<'a, 'b, 'x>> for CipherSuiteListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CipherSuiteCombinator>>;

    open spec fn requires(&self, deps: CipherSuiteListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CipherSuiteListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_cipher_suite_list_cont0(deps@)
    }

    fn apply(&self, deps: CipherSuiteListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(cipher_suite()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(cipher_suite()))
            }
        }
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

pub type ClientHelloInnerRef<'a> = (&'a u16, (&'a &'a [u8], (&'a SessionId<'a>, (&'a CipherSuiteList, (&'a Opaque1Ff<'a>, &'a ClientExtensions<'a>)))));
impl<'a> From<&'a ClientHello<'a>> for ClientHelloInnerRef<'a> {
    fn ex_from(m: &'a ClientHello) -> ClientHelloInnerRef<'a> {
        (&m.legacy_version, (&m.random, (&m.legacy_session_id, (&m.cipher_suites, (&m.legacy_compression_methods, &m.extensions)))))
    }
}

impl<'a> From<ClientHelloInner<'a>> for ClientHello<'a> {
    fn ex_from(m: ClientHelloInner) -> ClientHello {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        ClientHello { legacy_version, random, legacy_session_id, cipher_suites, legacy_compression_methods, extensions }
    }
}

pub struct ClientHelloMapper;
impl View for ClientHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloMapper {
    type Src = SpecClientHelloInner;
    type Dst = SpecClientHello;
}
impl SpecIsoProof for ClientHelloMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientHelloMapper {
    type Src = ClientHelloInner<'a>;
    type Dst = ClientHello<'a>;
    type RefSrc = ClientHelloInnerRef<'a>;
}
pub const CLIENTHELLOLEGACY_VERSION_CONST: u16 = 771;
type SpecClientHelloCombinatorAlias1 = (SpecOpaque1FfCombinator, SpecClientExtensionsCombinator);
type SpecClientHelloCombinatorAlias2 = (SpecCipherSuiteListCombinator, SpecClientHelloCombinatorAlias1);
type SpecClientHelloCombinatorAlias3 = (SpecSessionIdCombinator, SpecClientHelloCombinatorAlias2);
type SpecClientHelloCombinatorAlias4 = (bytes::Fixed<32>, SpecClientHelloCombinatorAlias3);
type SpecClientHelloCombinatorAlias5 = (Refined<U16Be, TagPred<u16>>, SpecClientHelloCombinatorAlias4);
pub struct SpecClientHelloCombinator(SpecClientHelloCombinatorAlias);

impl SpecCombinator for SpecClientHelloCombinator {
    type Type = SpecClientHello;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientHelloCombinatorAlias = Mapped<SpecClientHelloCombinatorAlias5, ClientHelloMapper>;
type ClientHelloCombinatorAlias1 = (Opaque1FfCombinator, ClientExtensionsCombinator);
type ClientHelloCombinatorAlias2 = (CipherSuiteListCombinator, ClientHelloCombinator1);
type ClientHelloCombinatorAlias3 = (SessionIdCombinator, ClientHelloCombinator2);
type ClientHelloCombinatorAlias4 = (bytes::Fixed<32>, ClientHelloCombinator3);
type ClientHelloCombinatorAlias5 = (Refined<U16Be, TagPred<u16>>, ClientHelloCombinator4);
struct ClientHelloCombinator1(ClientHelloCombinatorAlias1);
impl View for ClientHelloCombinator1 {
    type V = SpecClientHelloCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloCombinator1, ClientHelloCombinatorAlias1);

struct ClientHelloCombinator2(ClientHelloCombinatorAlias2);
impl View for ClientHelloCombinator2 {
    type V = SpecClientHelloCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloCombinator2, ClientHelloCombinatorAlias2);

struct ClientHelloCombinator3(ClientHelloCombinatorAlias3);
impl View for ClientHelloCombinator3 {
    type V = SpecClientHelloCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloCombinator3, ClientHelloCombinatorAlias3);

struct ClientHelloCombinator4(ClientHelloCombinatorAlias4);
impl View for ClientHelloCombinator4 {
    type V = SpecClientHelloCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloCombinator4, ClientHelloCombinatorAlias4);

struct ClientHelloCombinator5(ClientHelloCombinatorAlias5);
impl View for ClientHelloCombinator5 {
    type V = SpecClientHelloCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ClientHelloCombinator5, ClientHelloCombinatorAlias5);

pub struct ClientHelloCombinator(ClientHelloCombinatorAlias);

impl View for ClientHelloCombinator {
    type V = SpecClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientHelloCombinator {
    type Type = ClientHello<'a>;
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
pub type ClientHelloCombinatorAlias = Mapped<ClientHelloCombinator5, ClientHelloMapper>;


pub closed spec fn spec_client_hello() -> SpecClientHelloCombinator {
    SpecClientHelloCombinator(
    Mapped {
        inner: (Refined { inner: U16Be, predicate: TagPred(CLIENTHELLOLEGACY_VERSION_CONST) }, (bytes::Fixed::<32>, (spec_session_id(), (spec_cipher_suite_list(), (spec_opaque_1_ff(), spec_client_extensions()))))),
        mapper: ClientHelloMapper,
    })
}

                
pub fn client_hello() -> (o: ClientHelloCombinator)
    ensures o@ == spec_client_hello(),
{
    ClientHelloCombinator(
    Mapped {
        inner: ClientHelloCombinator5((Refined { inner: U16Be, predicate: TagPred(CLIENTHELLOLEGACY_VERSION_CONST) }, ClientHelloCombinator4((bytes::Fixed::<32>, ClientHelloCombinator3((session_id(), ClientHelloCombinator2((cipher_suite_list(), ClientHelloCombinator1((opaque_1_ff(), client_extensions())))))))))),
        mapper: ClientHelloMapper,
    })
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

pub type ShOrHrrInnerRef<'a> = ((&'a u16, &'a &'a [u8]), &'a ShOrHrrPayload<'a>);
impl<'a> From<&'a ShOrHrr<'a>> for ShOrHrrInnerRef<'a> {
    fn ex_from(m: &'a ShOrHrr) -> ShOrHrrInnerRef<'a> {
        ((&m.legacy_version, &m.random), &m.payload)
    }
}

impl<'a> From<ShOrHrrInner<'a>> for ShOrHrr<'a> {
    fn ex_from(m: ShOrHrrInner) -> ShOrHrr {
        let ((legacy_version, random), payload) = m;
        ShOrHrr { legacy_version, random, payload }
    }
}

pub struct ShOrHrrMapper;
impl View for ShOrHrrMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ShOrHrrMapper {
    type Src = SpecShOrHrrInner;
    type Dst = SpecShOrHrr;
}
impl SpecIsoProof for ShOrHrrMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ShOrHrrMapper {
    type Src = ShOrHrrInner<'a>;
    type Dst = ShOrHrr<'a>;
    type RefSrc = ShOrHrrInnerRef<'a>;
}
pub const SHORHRRLEGACY_VERSION_CONST: u16 = 771;

pub struct SpecShOrHrrCombinator(SpecShOrHrrCombinatorAlias);

impl SpecCombinator for SpecShOrHrrCombinator {
    type Type = SpecShOrHrr;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecShOrHrrCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShOrHrrCombinatorAlias::is_prefix_secure() }
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
pub type SpecShOrHrrCombinatorAlias = Mapped<SpecPair<(Refined<U16Be, TagPred<u16>>, bytes::Fixed<32>), SpecShOrHrrPayloadCombinator>, ShOrHrrMapper>;

pub struct ShOrHrrCombinator(ShOrHrrCombinatorAlias);

impl View for ShOrHrrCombinator {
    type V = SpecShOrHrrCombinator;
    closed spec fn view(&self) -> Self::V { SpecShOrHrrCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ShOrHrrCombinator {
    type Type = ShOrHrr<'a>;
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
pub type ShOrHrrCombinatorAlias = Mapped<Pair<(Refined<U16Be, TagPred<u16>>, bytes::Fixed<32>), ShOrHrrPayloadCombinator, ShOrHrrCont0>, ShOrHrrMapper>;


pub closed spec fn spec_sh_or_hrr() -> SpecShOrHrrCombinator {
    SpecShOrHrrCombinator(
    Mapped {
        inner: Pair::spec_new((Refined { inner: U16Be, predicate: TagPred(SHORHRRLEGACY_VERSION_CONST) }, bytes::Fixed::<32>), |deps| spec_sh_or_hrr_cont0(deps)),
        mapper: ShOrHrrMapper,
    })
}

pub open spec fn spec_sh_or_hrr_cont0(deps: (u16, Seq<u8>)) -> SpecShOrHrrPayloadCombinator {
    let (_, random) = deps;
    spec_sh_or_hrr_payload(random)
}

impl View for ShOrHrrCont0 {
    type V = spec_fn((u16, Seq<u8>)) -> SpecShOrHrrPayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (u16, Seq<u8>)| {
            spec_sh_or_hrr_cont0(deps)
        }
    }
}

                
pub fn sh_or_hrr() -> (o: ShOrHrrCombinator)
    ensures o@ == spec_sh_or_hrr(),
{
    ShOrHrrCombinator(
    Mapped {
        inner: Pair::new((Refined { inner: U16Be, predicate: TagPred(SHORHRRLEGACY_VERSION_CONST) }, bytes::Fixed::<32>), ShOrHrrCont0),
        mapper: ShOrHrrMapper,
    })
}

pub struct ShOrHrrCont0;
type ShOrHrrCont0Type<'a, 'b> = &'b (u16, &'a [u8]);
type ShOrHrrCont0SType<'a, 'x> = (&'x u16, &'x &'a [u8]);
type ShOrHrrCont0Input<'a, 'b, 'x> = POrSType<ShOrHrrCont0Type<'a, 'b>, ShOrHrrCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ShOrHrrCont0Input<'a, 'b, 'x>> for ShOrHrrCont0 {
    type Output = ShOrHrrPayloadCombinator;

    open spec fn requires(&self, deps: ShOrHrrCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ShOrHrrCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_sh_or_hrr_cont0(deps@)
    }

    fn apply(&self, deps: ShOrHrrCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (_, random) = *deps;
                sh_or_hrr_payload(random)
            }
            POrSType::S(deps) => {
                let (_, random) = deps;
                let random = *random;
                sh_or_hrr_payload(random)
            }
        }
    }
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

pub type NewSessionTicketExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a NewSessionTicketExtensionExtensionData<'a>);
impl<'a> From<&'a NewSessionTicketExtension<'a>> for NewSessionTicketExtensionInnerRef<'a> {
    fn ex_from(m: &'a NewSessionTicketExtension) -> NewSessionTicketExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<NewSessionTicketExtensionInner<'a>> for NewSessionTicketExtension<'a> {
    fn ex_from(m: NewSessionTicketExtensionInner) -> NewSessionTicketExtension {
        let ((extension_type, ext_len), extension_data) = m;
        NewSessionTicketExtension { extension_type, ext_len, extension_data }
    }
}

pub struct NewSessionTicketExtensionMapper;
impl View for NewSessionTicketExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionMapper {
    type Src = SpecNewSessionTicketExtensionInner;
    type Dst = SpecNewSessionTicketExtension;
}
impl SpecIsoProof for NewSessionTicketExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NewSessionTicketExtensionMapper {
    type Src = NewSessionTicketExtensionInner<'a>;
    type Dst = NewSessionTicketExtension<'a>;
    type RefSrc = NewSessionTicketExtensionInnerRef<'a>;
}

pub struct SpecNewSessionTicketExtensionCombinator(SpecNewSessionTicketExtensionCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionCombinator {
    type Type = SpecNewSessionTicketExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecNewSessionTicketExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecNewSessionTicketExtensionExtensionDataCombinator>, NewSessionTicketExtensionMapper>;

pub struct NewSessionTicketExtensionCombinator(NewSessionTicketExtensionCombinatorAlias);

impl View for NewSessionTicketExtensionCombinator {
    type V = SpecNewSessionTicketExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NewSessionTicketExtensionCombinator {
    type Type = NewSessionTicketExtension<'a>;
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
pub type NewSessionTicketExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, NewSessionTicketExtensionCont1>, NewSessionTicketExtensionExtensionDataCombinator, NewSessionTicketExtensionCont0>, NewSessionTicketExtensionMapper>;


pub closed spec fn spec_new_session_ticket_extension() -> SpecNewSessionTicketExtensionCombinator {
    SpecNewSessionTicketExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_new_session_ticket_extension_cont1(deps)), |deps| spec_new_session_ticket_extension_cont0(deps)),
        mapper: NewSessionTicketExtensionMapper,
    })
}

pub open spec fn spec_new_session_ticket_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for NewSessionTicketExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_new_session_ticket_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_new_session_ticket_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecNewSessionTicketExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_new_session_ticket_extension_extension_data(ext_len, extension_type)
}

impl View for NewSessionTicketExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecNewSessionTicketExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_new_session_ticket_extension_cont0(deps)
        }
    }
}

                
pub fn new_session_ticket_extension() -> (o: NewSessionTicketExtensionCombinator)
    ensures o@ == spec_new_session_ticket_extension(),
{
    NewSessionTicketExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), NewSessionTicketExtensionCont1), NewSessionTicketExtensionCont0),
        mapper: NewSessionTicketExtensionMapper,
    })
}

pub struct NewSessionTicketExtensionCont1;
type NewSessionTicketExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type NewSessionTicketExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type NewSessionTicketExtensionCont1Input<'a, 'b, 'x> = POrSType<NewSessionTicketExtensionCont1Type<'a, 'b>, NewSessionTicketExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NewSessionTicketExtensionCont1Input<'a, 'b, 'x>> for NewSessionTicketExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: NewSessionTicketExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: NewSessionTicketExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extension_cont1(deps@)
    }

    fn apply(&self, deps: NewSessionTicketExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct NewSessionTicketExtensionCont0;
type NewSessionTicketExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type NewSessionTicketExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type NewSessionTicketExtensionCont0Input<'a, 'b, 'x> = POrSType<NewSessionTicketExtensionCont0Type<'a, 'b>, NewSessionTicketExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NewSessionTicketExtensionCont0Input<'a, 'b, 'x>> for NewSessionTicketExtensionCont0 {
    type Output = NewSessionTicketExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: NewSessionTicketExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: NewSessionTicketExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extension_cont0(deps@)
    }

    fn apply(&self, deps: NewSessionTicketExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                new_session_ticket_extension_extension_data(ext_len, extension_type)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                new_session_ticket_extension_extension_data(ext_len, extension_type)
            }
        }
    }
}
                

pub struct SpecNewSessionTicketExtensions {
    pub l: u16,
    pub list: Seq<SpecNewSessionTicketExtension>,
}

pub type SpecNewSessionTicketExtensionsInner = (u16, Seq<SpecNewSessionTicketExtension>);


impl SpecFrom<SpecNewSessionTicketExtensions> for SpecNewSessionTicketExtensionsInner {
    open spec fn spec_from(m: SpecNewSessionTicketExtensions) -> SpecNewSessionTicketExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecNewSessionTicketExtensionsInner> for SpecNewSessionTicketExtensions {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionsInner) -> SpecNewSessionTicketExtensions {
        let (l, list) = m;
        SpecNewSessionTicketExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NewSessionTicketExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<NewSessionTicketExtension<'a>>,
}

impl View for NewSessionTicketExtensions<'_> {
    type V = SpecNewSessionTicketExtensions;

    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type NewSessionTicketExtensionsInner<'a> = (u16, RepeatResult<NewSessionTicketExtension<'a>>);

pub type NewSessionTicketExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<NewSessionTicketExtension<'a>>);
impl<'a> From<&'a NewSessionTicketExtensions<'a>> for NewSessionTicketExtensionsInnerRef<'a> {
    fn ex_from(m: &'a NewSessionTicketExtensions) -> NewSessionTicketExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<NewSessionTicketExtensionsInner<'a>> for NewSessionTicketExtensions<'a> {
    fn ex_from(m: NewSessionTicketExtensionsInner) -> NewSessionTicketExtensions {
        let (l, list) = m;
        NewSessionTicketExtensions { l, list }
    }
}

pub struct NewSessionTicketExtensionsMapper;
impl View for NewSessionTicketExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionsMapper {
    type Src = SpecNewSessionTicketExtensionsInner;
    type Dst = SpecNewSessionTicketExtensions;
}
impl SpecIsoProof for NewSessionTicketExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NewSessionTicketExtensionsMapper {
    type Src = NewSessionTicketExtensionsInner<'a>;
    type Dst = NewSessionTicketExtensions<'a>;
    type RefSrc = NewSessionTicketExtensionsInnerRef<'a>;
}

pub struct SpecNewSessionTicketExtensionsCombinator(SpecNewSessionTicketExtensionsCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    type Type = SpecNewSessionTicketExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecNewSessionTicketExtensionsCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate14514213152276180162>, AndThen<bytes::Variable, Repeat<SpecNewSessionTicketExtensionCombinator>>>, NewSessionTicketExtensionsMapper>;
pub struct Predicate14514213152276180162;
impl View for Predicate14514213152276180162 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate14514213152276180162 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65534)
    }
}
impl SpecPred<u16> for Predicate14514213152276180162 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 0 && i <= 65534)
    }
}

pub struct NewSessionTicketExtensionsCombinator(NewSessionTicketExtensionsCombinatorAlias);

impl View for NewSessionTicketExtensionsCombinator {
    type V = SpecNewSessionTicketExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NewSessionTicketExtensionsCombinator {
    type Type = NewSessionTicketExtensions<'a>;
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
pub type NewSessionTicketExtensionsCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate14514213152276180162>, AndThen<bytes::Variable, Repeat<NewSessionTicketExtensionCombinator>>, NewSessionTicketExtensionsCont0>, NewSessionTicketExtensionsMapper>;


pub closed spec fn spec_new_session_ticket_extensions() -> SpecNewSessionTicketExtensionsCombinator {
    SpecNewSessionTicketExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate14514213152276180162 }, |deps| spec_new_session_ticket_extensions_cont0(deps)),
        mapper: NewSessionTicketExtensionsMapper,
    })
}

pub open spec fn spec_new_session_ticket_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecNewSessionTicketExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_new_session_ticket_extension()))
}

impl View for NewSessionTicketExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecNewSessionTicketExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_new_session_ticket_extensions_cont0(deps)
        }
    }
}

                
pub fn new_session_ticket_extensions() -> (o: NewSessionTicketExtensionsCombinator)
    ensures o@ == spec_new_session_ticket_extensions(),
{
    NewSessionTicketExtensionsCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate14514213152276180162 }, NewSessionTicketExtensionsCont0),
        mapper: NewSessionTicketExtensionsMapper,
    })
}

pub struct NewSessionTicketExtensionsCont0;
type NewSessionTicketExtensionsCont0Type<'a, 'b> = &'b u16;
type NewSessionTicketExtensionsCont0SType<'a, 'x> = &'x u16;
type NewSessionTicketExtensionsCont0Input<'a, 'b, 'x> = POrSType<NewSessionTicketExtensionsCont0Type<'a, 'b>, NewSessionTicketExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NewSessionTicketExtensionsCont0Input<'a, 'b, 'x>> for NewSessionTicketExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<NewSessionTicketExtensionCombinator>>;

    open spec fn requires(&self, deps: NewSessionTicketExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: NewSessionTicketExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extensions_cont0(deps@)
    }

    fn apply(&self, deps: NewSessionTicketExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(new_session_ticket_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(new_session_ticket_extension()))
            }
        }
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

pub type NewSessionTicketInnerRef<'a> = (&'a u32, (&'a u32, (&'a Opaque0Ff<'a>, (&'a Opaque1Ffff<'a>, &'a NewSessionTicketExtensions<'a>))));
impl<'a> From<&'a NewSessionTicket<'a>> for NewSessionTicketInnerRef<'a> {
    fn ex_from(m: &'a NewSessionTicket) -> NewSessionTicketInnerRef<'a> {
        (&m.ticket_lifetime, (&m.ticket_age_add, (&m.ticket_nonce, (&m.ticket, &m.extensions))))
    }
}

impl<'a> From<NewSessionTicketInner<'a>> for NewSessionTicket<'a> {
    fn ex_from(m: NewSessionTicketInner) -> NewSessionTicket {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        NewSessionTicket { ticket_lifetime, ticket_age_add, ticket_nonce, ticket, extensions }
    }
}

pub struct NewSessionTicketMapper;
impl View for NewSessionTicketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketMapper {
    type Src = SpecNewSessionTicketInner;
    type Dst = SpecNewSessionTicket;
}
impl SpecIsoProof for NewSessionTicketMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NewSessionTicketMapper {
    type Src = NewSessionTicketInner<'a>;
    type Dst = NewSessionTicket<'a>;
    type RefSrc = NewSessionTicketInnerRef<'a>;
}
type SpecNewSessionTicketCombinatorAlias1 = (SpecOpaque1FfffCombinator, SpecNewSessionTicketExtensionsCombinator);
type SpecNewSessionTicketCombinatorAlias2 = (SpecOpaque0FfCombinator, SpecNewSessionTicketCombinatorAlias1);
type SpecNewSessionTicketCombinatorAlias3 = (U32Be, SpecNewSessionTicketCombinatorAlias2);
type SpecNewSessionTicketCombinatorAlias4 = (U32Be, SpecNewSessionTicketCombinatorAlias3);
pub struct SpecNewSessionTicketCombinator(SpecNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketCombinator {
    type Type = SpecNewSessionTicket;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketCombinatorAlias::is_prefix_secure() }
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
pub type SpecNewSessionTicketCombinatorAlias = Mapped<SpecNewSessionTicketCombinatorAlias4, NewSessionTicketMapper>;
type NewSessionTicketCombinatorAlias1 = (Opaque1FfffCombinator, NewSessionTicketExtensionsCombinator);
type NewSessionTicketCombinatorAlias2 = (Opaque0FfCombinator, NewSessionTicketCombinator1);
type NewSessionTicketCombinatorAlias3 = (U32Be, NewSessionTicketCombinator2);
type NewSessionTicketCombinatorAlias4 = (U32Be, NewSessionTicketCombinator3);
struct NewSessionTicketCombinator1(NewSessionTicketCombinatorAlias1);
impl View for NewSessionTicketCombinator1 {
    type V = SpecNewSessionTicketCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NewSessionTicketCombinator1, NewSessionTicketCombinatorAlias1);

struct NewSessionTicketCombinator2(NewSessionTicketCombinatorAlias2);
impl View for NewSessionTicketCombinator2 {
    type V = SpecNewSessionTicketCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NewSessionTicketCombinator2, NewSessionTicketCombinatorAlias2);

struct NewSessionTicketCombinator3(NewSessionTicketCombinatorAlias3);
impl View for NewSessionTicketCombinator3 {
    type V = SpecNewSessionTicketCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NewSessionTicketCombinator3, NewSessionTicketCombinatorAlias3);

struct NewSessionTicketCombinator4(NewSessionTicketCombinatorAlias4);
impl View for NewSessionTicketCombinator4 {
    type V = SpecNewSessionTicketCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NewSessionTicketCombinator4, NewSessionTicketCombinatorAlias4);

pub struct NewSessionTicketCombinator(NewSessionTicketCombinatorAlias);

impl View for NewSessionTicketCombinator {
    type V = SpecNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NewSessionTicketCombinator {
    type Type = NewSessionTicket<'a>;
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
pub type NewSessionTicketCombinatorAlias = Mapped<NewSessionTicketCombinator4, NewSessionTicketMapper>;


pub closed spec fn spec_new_session_ticket() -> SpecNewSessionTicketCombinator {
    SpecNewSessionTicketCombinator(
    Mapped {
        inner: (U32Be, (U32Be, (spec_opaque_0_ff(), (spec_opaque_1_ffff(), spec_new_session_ticket_extensions())))),
        mapper: NewSessionTicketMapper,
    })
}

                
pub fn new_session_ticket() -> (o: NewSessionTicketCombinator)
    ensures o@ == spec_new_session_ticket(),
{
    NewSessionTicketCombinator(
    Mapped {
        inner: NewSessionTicketCombinator4((U32Be, NewSessionTicketCombinator3((U32Be, NewSessionTicketCombinator2((opaque_0_ff(), NewSessionTicketCombinator1((opaque_1_ffff(), new_session_ticket_extensions())))))))),
        mapper: NewSessionTicketMapper,
    })
}

                
pub type SpecEmpty = Seq<u8>;
pub type Empty<'a> = &'a [u8];
pub type EmptyRef<'a> = &'a &'a [u8];


pub struct SpecEmptyCombinator(SpecEmptyCombinatorAlias);

impl SpecCombinator for SpecEmptyCombinator {
    type Type = SpecEmpty;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEmptyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyCombinatorAlias::is_prefix_secure() }
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
pub type SpecEmptyCombinatorAlias = bytes::Fixed<0>;

pub struct EmptyCombinator(EmptyCombinatorAlias);

impl View for EmptyCombinator {
    type V = SpecEmptyCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EmptyCombinator {
    type Type = Empty<'a>;
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
pub type EmptyCombinatorAlias = bytes::Fixed<0>;


pub closed spec fn spec_empty() -> SpecEmptyCombinator {
    SpecEmptyCombinator(bytes::Fixed::<0>)
}

                
pub fn empty() -> (o: EmptyCombinator)
    ensures o@ == spec_empty(),
{
    EmptyCombinator(bytes::Fixed::<0>)
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

pub type EncryptedExtensionExtensionDataInnerRef<'a> = Either<&'a Empty<'a>, Either<&'a MaxFragmentLength, Either<&'a NamedGroupList, Either<&'a HeartbeatMode, Either<&'a ProtocolNameList<'a>, Either<&'a ClientCertTypeClientExtension, Either<&'a ServerCertTypeClientExtension, Either<&'a Empty<'a>, &'a &'a [u8]>>>>>>>>;


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


impl<'a> From<&'a EncryptedExtensionExtensionData<'a>> for EncryptedExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a EncryptedExtensionExtensionData<'a>) -> EncryptedExtensionExtensionDataInnerRef<'a> {
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


pub struct EncryptedExtensionExtensionDataMapper;
impl View for EncryptedExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionExtensionDataMapper {
    type Src = SpecEncryptedExtensionExtensionDataInner;
    type Dst = SpecEncryptedExtensionExtensionData;
}
impl SpecIsoProof for EncryptedExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EncryptedExtensionExtensionDataMapper {
    type Src = EncryptedExtensionExtensionDataInner<'a>;
    type Dst = EncryptedExtensionExtensionData<'a>;
    type RefSrc = EncryptedExtensionExtensionDataInnerRef<'a>;
}

type SpecEncryptedExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecEmptyCombinator>, Cond<bytes::Variable>>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecServerCertTypeClientExtensionCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias1>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SpecClientCertTypeClientExtensionCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias2>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias4 = Choice<Cond<SpecProtocolNameListCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias3>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias5 = Choice<Cond<SpecHeartbeatModeCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias4>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias6 = Choice<Cond<SpecNamedGroupListCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias5>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias7 = Choice<Cond<SpecMaxFragmentLengthCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias6>;
type SpecEncryptedExtensionExtensionDataCombinatorAlias8 = Choice<Cond<SpecEmptyCombinator>, SpecEncryptedExtensionExtensionDataCombinatorAlias7>;
pub struct SpecEncryptedExtensionExtensionDataCombinator(SpecEncryptedExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionExtensionDataCombinator {
    type Type = SpecEncryptedExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEncryptedExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecEncryptedExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecEncryptedExtensionExtensionDataCombinatorAlias8, EncryptedExtensionExtensionDataMapper>>;
type EncryptedExtensionExtensionDataCombinatorAlias1 = Choice<Cond<EmptyCombinator>, Cond<bytes::Variable>>;
type EncryptedExtensionExtensionDataCombinatorAlias2 = Choice<Cond<ServerCertTypeClientExtensionCombinator>, EncryptedExtensionExtensionDataCombinator1>;
type EncryptedExtensionExtensionDataCombinatorAlias3 = Choice<Cond<ClientCertTypeClientExtensionCombinator>, EncryptedExtensionExtensionDataCombinator2>;
type EncryptedExtensionExtensionDataCombinatorAlias4 = Choice<Cond<ProtocolNameListCombinator>, EncryptedExtensionExtensionDataCombinator3>;
type EncryptedExtensionExtensionDataCombinatorAlias5 = Choice<Cond<HeartbeatModeCombinator>, EncryptedExtensionExtensionDataCombinator4>;
type EncryptedExtensionExtensionDataCombinatorAlias6 = Choice<Cond<NamedGroupListCombinator>, EncryptedExtensionExtensionDataCombinator5>;
type EncryptedExtensionExtensionDataCombinatorAlias7 = Choice<Cond<MaxFragmentLengthCombinator>, EncryptedExtensionExtensionDataCombinator6>;
type EncryptedExtensionExtensionDataCombinatorAlias8 = Choice<Cond<EmptyCombinator>, EncryptedExtensionExtensionDataCombinator7>;
struct EncryptedExtensionExtensionDataCombinator1(EncryptedExtensionExtensionDataCombinatorAlias1);
impl View for EncryptedExtensionExtensionDataCombinator1 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator1, EncryptedExtensionExtensionDataCombinatorAlias1);

struct EncryptedExtensionExtensionDataCombinator2(EncryptedExtensionExtensionDataCombinatorAlias2);
impl View for EncryptedExtensionExtensionDataCombinator2 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator2, EncryptedExtensionExtensionDataCombinatorAlias2);

struct EncryptedExtensionExtensionDataCombinator3(EncryptedExtensionExtensionDataCombinatorAlias3);
impl View for EncryptedExtensionExtensionDataCombinator3 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator3, EncryptedExtensionExtensionDataCombinatorAlias3);

struct EncryptedExtensionExtensionDataCombinator4(EncryptedExtensionExtensionDataCombinatorAlias4);
impl View for EncryptedExtensionExtensionDataCombinator4 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator4, EncryptedExtensionExtensionDataCombinatorAlias4);

struct EncryptedExtensionExtensionDataCombinator5(EncryptedExtensionExtensionDataCombinatorAlias5);
impl View for EncryptedExtensionExtensionDataCombinator5 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator5, EncryptedExtensionExtensionDataCombinatorAlias5);

struct EncryptedExtensionExtensionDataCombinator6(EncryptedExtensionExtensionDataCombinatorAlias6);
impl View for EncryptedExtensionExtensionDataCombinator6 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator6, EncryptedExtensionExtensionDataCombinatorAlias6);

struct EncryptedExtensionExtensionDataCombinator7(EncryptedExtensionExtensionDataCombinatorAlias7);
impl View for EncryptedExtensionExtensionDataCombinator7 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator7, EncryptedExtensionExtensionDataCombinatorAlias7);

struct EncryptedExtensionExtensionDataCombinator8(EncryptedExtensionExtensionDataCombinatorAlias8);
impl View for EncryptedExtensionExtensionDataCombinator8 {
    type V = SpecEncryptedExtensionExtensionDataCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(EncryptedExtensionExtensionDataCombinator8, EncryptedExtensionExtensionDataCombinatorAlias8);

pub struct EncryptedExtensionExtensionDataCombinator(EncryptedExtensionExtensionDataCombinatorAlias);

impl View for EncryptedExtensionExtensionDataCombinator {
    type V = SpecEncryptedExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EncryptedExtensionExtensionDataCombinator {
    type Type = EncryptedExtensionExtensionData<'a>;
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
pub type EncryptedExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<EncryptedExtensionExtensionDataCombinator8, EncryptedExtensionExtensionDataMapper>>;


pub closed spec fn spec_encrypted_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecEncryptedExtensionExtensionDataCombinator {
    SpecEncryptedExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 0, inner: spec_empty() }, Choice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, Choice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, Choice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, Choice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, Choice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, Choice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, Choice(Cond { cond: extension_type == 42, inner: spec_empty() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 10 || extension_type == 15 || extension_type == 16 || extension_type == 19 || extension_type == 20 || extension_type == 42), inner: bytes::Variable(ext_len.spec_into()) })))))))), mapper: EncryptedExtensionExtensionDataMapper }))
}

pub fn encrypted_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: EncryptedExtensionExtensionDataCombinator)
    ensures o@ == spec_encrypted_extension_extension_data(extension_type@, ext_len@),
{
    EncryptedExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: EncryptedExtensionExtensionDataCombinator8(Choice::new(Cond { cond: extension_type == 0, inner: empty() }, EncryptedExtensionExtensionDataCombinator7(Choice::new(Cond { cond: extension_type == 1, inner: max_fragment_length() }, EncryptedExtensionExtensionDataCombinator6(Choice::new(Cond { cond: extension_type == 10, inner: named_group_list() }, EncryptedExtensionExtensionDataCombinator5(Choice::new(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, EncryptedExtensionExtensionDataCombinator4(Choice::new(Cond { cond: extension_type == 16, inner: protocol_name_list() }, EncryptedExtensionExtensionDataCombinator3(Choice::new(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, EncryptedExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, EncryptedExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 42, inner: empty() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 10 || extension_type == 15 || extension_type == 16 || extension_type == 19 || extension_type == 20 || extension_type == 42), inner: bytes::Variable(ext_len.ex_into()) })))))))))))))))), mapper: EncryptedExtensionExtensionDataMapper }))
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

pub type EncryptedExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a EncryptedExtensionExtensionData<'a>);
impl<'a> From<&'a EncryptedExtension<'a>> for EncryptedExtensionInnerRef<'a> {
    fn ex_from(m: &'a EncryptedExtension) -> EncryptedExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<EncryptedExtensionInner<'a>> for EncryptedExtension<'a> {
    fn ex_from(m: EncryptedExtensionInner) -> EncryptedExtension {
        let ((extension_type, ext_len), extension_data) = m;
        EncryptedExtension { extension_type, ext_len, extension_data }
    }
}

pub struct EncryptedExtensionMapper;
impl View for EncryptedExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionMapper {
    type Src = SpecEncryptedExtensionInner;
    type Dst = SpecEncryptedExtension;
}
impl SpecIsoProof for EncryptedExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EncryptedExtensionMapper {
    type Src = EncryptedExtensionInner<'a>;
    type Dst = EncryptedExtension<'a>;
    type RefSrc = EncryptedExtensionInnerRef<'a>;
}

pub struct SpecEncryptedExtensionCombinator(SpecEncryptedExtensionCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionCombinator {
    type Type = SpecEncryptedExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEncryptedExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecEncryptedExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecEncryptedExtensionExtensionDataCombinator>, EncryptedExtensionMapper>;

pub struct EncryptedExtensionCombinator(EncryptedExtensionCombinatorAlias);

impl View for EncryptedExtensionCombinator {
    type V = SpecEncryptedExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EncryptedExtensionCombinator {
    type Type = EncryptedExtension<'a>;
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
pub type EncryptedExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, EncryptedExtensionCont1>, EncryptedExtensionExtensionDataCombinator, EncryptedExtensionCont0>, EncryptedExtensionMapper>;


pub closed spec fn spec_encrypted_extension() -> SpecEncryptedExtensionCombinator {
    SpecEncryptedExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_encrypted_extension_cont1(deps)), |deps| spec_encrypted_extension_cont0(deps)),
        mapper: EncryptedExtensionMapper,
    })
}

pub open spec fn spec_encrypted_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for EncryptedExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_encrypted_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_encrypted_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecEncryptedExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_encrypted_extension_extension_data(extension_type, ext_len)
}

impl View for EncryptedExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecEncryptedExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_encrypted_extension_cont0(deps)
        }
    }
}

                
pub fn encrypted_extension() -> (o: EncryptedExtensionCombinator)
    ensures o@ == spec_encrypted_extension(),
{
    EncryptedExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), EncryptedExtensionCont1), EncryptedExtensionCont0),
        mapper: EncryptedExtensionMapper,
    })
}

pub struct EncryptedExtensionCont1;
type EncryptedExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type EncryptedExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type EncryptedExtensionCont1Input<'a, 'b, 'x> = POrSType<EncryptedExtensionCont1Type<'a, 'b>, EncryptedExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EncryptedExtensionCont1Input<'a, 'b, 'x>> for EncryptedExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: EncryptedExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: EncryptedExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_encrypted_extension_cont1(deps@)
    }

    fn apply(&self, deps: EncryptedExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct EncryptedExtensionCont0;
type EncryptedExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type EncryptedExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type EncryptedExtensionCont0Input<'a, 'b, 'x> = POrSType<EncryptedExtensionCont0Type<'a, 'b>, EncryptedExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EncryptedExtensionCont0Input<'a, 'b, 'x>> for EncryptedExtensionCont0 {
    type Output = EncryptedExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: EncryptedExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: EncryptedExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_encrypted_extension_cont0(deps@)
    }

    fn apply(&self, deps: EncryptedExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                encrypted_extension_extension_data(extension_type, ext_len)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                encrypted_extension_extension_data(extension_type, ext_len)
            }
        }
    }
}
                

pub struct SpecEncryptedExtensions {
    pub l: u16,
    pub list: Seq<SpecEncryptedExtension>,
}

pub type SpecEncryptedExtensionsInner = (u16, Seq<SpecEncryptedExtension>);


impl SpecFrom<SpecEncryptedExtensions> for SpecEncryptedExtensionsInner {
    open spec fn spec_from(m: SpecEncryptedExtensions) -> SpecEncryptedExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecEncryptedExtensionsInner> for SpecEncryptedExtensions {
    open spec fn spec_from(m: SpecEncryptedExtensionsInner) -> SpecEncryptedExtensions {
        let (l, list) = m;
        SpecEncryptedExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EncryptedExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<EncryptedExtension<'a>>,
}

impl View for EncryptedExtensions<'_> {
    type V = SpecEncryptedExtensions;

    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type EncryptedExtensionsInner<'a> = (u16, RepeatResult<EncryptedExtension<'a>>);

pub type EncryptedExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<EncryptedExtension<'a>>);
impl<'a> From<&'a EncryptedExtensions<'a>> for EncryptedExtensionsInnerRef<'a> {
    fn ex_from(m: &'a EncryptedExtensions) -> EncryptedExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<EncryptedExtensionsInner<'a>> for EncryptedExtensions<'a> {
    fn ex_from(m: EncryptedExtensionsInner) -> EncryptedExtensions {
        let (l, list) = m;
        EncryptedExtensions { l, list }
    }
}

pub struct EncryptedExtensionsMapper;
impl View for EncryptedExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionsMapper {
    type Src = SpecEncryptedExtensionsInner;
    type Dst = SpecEncryptedExtensions;
}
impl SpecIsoProof for EncryptedExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EncryptedExtensionsMapper {
    type Src = EncryptedExtensionsInner<'a>;
    type Dst = EncryptedExtensions<'a>;
    type RefSrc = EncryptedExtensionsInnerRef<'a>;
}

pub struct SpecEncryptedExtensionsCombinator(SpecEncryptedExtensionsCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionsCombinator {
    type Type = SpecEncryptedExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEncryptedExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecEncryptedExtensionsCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecEncryptedExtensionCombinator>>>, EncryptedExtensionsMapper>;

pub struct EncryptedExtensionsCombinator(EncryptedExtensionsCombinatorAlias);

impl View for EncryptedExtensionsCombinator {
    type V = SpecEncryptedExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EncryptedExtensionsCombinator {
    type Type = EncryptedExtensions<'a>;
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
pub type EncryptedExtensionsCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<EncryptedExtensionCombinator>>, EncryptedExtensionsCont0>, EncryptedExtensionsMapper>;


pub closed spec fn spec_encrypted_extensions() -> SpecEncryptedExtensionsCombinator {
    SpecEncryptedExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_encrypted_extensions_cont0(deps)),
        mapper: EncryptedExtensionsMapper,
    })
}

pub open spec fn spec_encrypted_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecEncryptedExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_encrypted_extension()))
}

impl View for EncryptedExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecEncryptedExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_encrypted_extensions_cont0(deps)
        }
    }
}

                
pub fn encrypted_extensions() -> (o: EncryptedExtensionsCombinator)
    ensures o@ == spec_encrypted_extensions(),
{
    EncryptedExtensionsCombinator(
    Mapped {
        inner: Pair::new(U16Be, EncryptedExtensionsCont0),
        mapper: EncryptedExtensionsMapper,
    })
}

pub struct EncryptedExtensionsCont0;
type EncryptedExtensionsCont0Type<'a, 'b> = &'b u16;
type EncryptedExtensionsCont0SType<'a, 'x> = &'x u16;
type EncryptedExtensionsCont0Input<'a, 'b, 'x> = POrSType<EncryptedExtensionsCont0Type<'a, 'b>, EncryptedExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EncryptedExtensionsCont0Input<'a, 'b, 'x>> for EncryptedExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<EncryptedExtensionCombinator>>;

    open spec fn requires(&self, deps: EncryptedExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: EncryptedExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_encrypted_extensions_cont0(deps@)
    }

    fn apply(&self, deps: EncryptedExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(encrypted_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(encrypted_extension()))
            }
        }
    }
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

pub type CertificateStatusInnerRef<'a> = (&'a u8, &'a OcspResponse<'a>);
impl<'a> From<&'a CertificateStatus<'a>> for CertificateStatusInnerRef<'a> {
    fn ex_from(m: &'a CertificateStatus) -> CertificateStatusInnerRef<'a> {
        (&m.status_type, &m.response)
    }
}

impl<'a> From<CertificateStatusInner<'a>> for CertificateStatus<'a> {
    fn ex_from(m: CertificateStatusInner) -> CertificateStatus {
        let (status_type, response) = m;
        CertificateStatus { status_type, response }
    }
}

pub struct CertificateStatusMapper;
impl View for CertificateStatusMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusMapper {
    type Src = SpecCertificateStatusInner;
    type Dst = SpecCertificateStatus;
}
impl SpecIsoProof for CertificateStatusMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateStatusMapper {
    type Src = CertificateStatusInner<'a>;
    type Dst = CertificateStatus<'a>;
    type RefSrc = CertificateStatusInnerRef<'a>;
}
pub const CERTIFICATESTATUSSTATUS_TYPE_CONST: u8 = 1;
type SpecCertificateStatusCombinatorAlias1 = (Refined<U8, TagPred<u8>>, SpecOcspResponseCombinator);
pub struct SpecCertificateStatusCombinator(SpecCertificateStatusCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusCombinator {
    type Type = SpecCertificateStatus;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateStatusCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateStatusCombinatorAlias = Mapped<SpecCertificateStatusCombinatorAlias1, CertificateStatusMapper>;
type CertificateStatusCombinatorAlias1 = (Refined<U8, TagPred<u8>>, OcspResponseCombinator);
struct CertificateStatusCombinator1(CertificateStatusCombinatorAlias1);
impl View for CertificateStatusCombinator1 {
    type V = SpecCertificateStatusCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateStatusCombinator1, CertificateStatusCombinatorAlias1);

pub struct CertificateStatusCombinator(CertificateStatusCombinatorAlias);

impl View for CertificateStatusCombinator {
    type V = SpecCertificateStatusCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateStatusCombinator {
    type Type = CertificateStatus<'a>;
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
pub type CertificateStatusCombinatorAlias = Mapped<CertificateStatusCombinator1, CertificateStatusMapper>;


pub closed spec fn spec_certificate_status() -> SpecCertificateStatusCombinator {
    SpecCertificateStatusCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSSTATUS_TYPE_CONST) }, spec_ocsp_response()),
        mapper: CertificateStatusMapper,
    })
}

                
pub fn certificate_status() -> (o: CertificateStatusCombinator)
    ensures o@ == spec_certificate_status(),
{
    CertificateStatusCombinator(
    Mapped {
        inner: CertificateStatusCombinator1((Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSSTATUS_TYPE_CONST) }, ocsp_response())),
        mapper: CertificateStatusMapper,
    })
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

pub type CertificateExtensionExtensionDataInnerRef<'a> = Either<&'a CertificateStatus<'a>, Either<&'a SignedCertificateTimestampList<'a>, &'a &'a [u8]>>;


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


impl<'a> From<&'a CertificateExtensionExtensionData<'a>> for CertificateExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a CertificateExtensionExtensionData<'a>) -> CertificateExtensionExtensionDataInnerRef<'a> {
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


pub struct CertificateExtensionExtensionDataMapper;
impl View for CertificateExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionExtensionDataMapper {
    type Src = SpecCertificateExtensionExtensionDataInner;
    type Dst = SpecCertificateExtensionExtensionData;
}
impl SpecIsoProof for CertificateExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateExtensionExtensionDataMapper {
    type Src = CertificateExtensionExtensionDataInner<'a>;
    type Dst = CertificateExtensionExtensionData<'a>;
    type RefSrc = CertificateExtensionExtensionDataInnerRef<'a>;
}

type SpecCertificateExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecSignedCertificateTimestampListCombinator>, Cond<bytes::Variable>>;
type SpecCertificateExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecCertificateStatusCombinator>, SpecCertificateExtensionExtensionDataCombinatorAlias1>;
pub struct SpecCertificateExtensionExtensionDataCombinator(SpecCertificateExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionExtensionDataCombinator {
    type Type = SpecCertificateExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecCertificateExtensionExtensionDataCombinatorAlias2, CertificateExtensionExtensionDataMapper>>;
type CertificateExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SignedCertificateTimestampListCombinator>, Cond<bytes::Variable>>;
type CertificateExtensionExtensionDataCombinatorAlias2 = Choice<Cond<CertificateStatusCombinator>, CertificateExtensionExtensionDataCombinator1>;
struct CertificateExtensionExtensionDataCombinator1(CertificateExtensionExtensionDataCombinatorAlias1);
impl View for CertificateExtensionExtensionDataCombinator1 {
    type V = SpecCertificateExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateExtensionExtensionDataCombinator1, CertificateExtensionExtensionDataCombinatorAlias1);

struct CertificateExtensionExtensionDataCombinator2(CertificateExtensionExtensionDataCombinatorAlias2);
impl View for CertificateExtensionExtensionDataCombinator2 {
    type V = SpecCertificateExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateExtensionExtensionDataCombinator2, CertificateExtensionExtensionDataCombinatorAlias2);

pub struct CertificateExtensionExtensionDataCombinator(CertificateExtensionExtensionDataCombinatorAlias);

impl View for CertificateExtensionExtensionDataCombinator {
    type V = SpecCertificateExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateExtensionExtensionDataCombinator {
    type Type = CertificateExtensionExtensionData<'a>;
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
pub type CertificateExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<CertificateExtensionExtensionDataCombinator2, CertificateExtensionExtensionDataMapper>>;


pub closed spec fn spec_certificate_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecCertificateExtensionExtensionDataCombinator {
    SpecCertificateExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 5, inner: spec_certificate_status() }, Choice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, Cond { cond: !(extension_type == 5 || extension_type == 18), inner: bytes::Variable(ext_len.spec_into()) })), mapper: CertificateExtensionExtensionDataMapper }))
}

pub fn certificate_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: CertificateExtensionExtensionDataCombinator)
    ensures o@ == spec_certificate_extension_extension_data(extension_type@, ext_len@),
{
    CertificateExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: CertificateExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 5, inner: certificate_status() }, CertificateExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, Cond { cond: !(extension_type == 5 || extension_type == 18), inner: bytes::Variable(ext_len.ex_into()) })))), mapper: CertificateExtensionExtensionDataMapper }))
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

pub type CertificateExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a CertificateExtensionExtensionData<'a>);
impl<'a> From<&'a CertificateExtension<'a>> for CertificateExtensionInnerRef<'a> {
    fn ex_from(m: &'a CertificateExtension) -> CertificateExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<CertificateExtensionInner<'a>> for CertificateExtension<'a> {
    fn ex_from(m: CertificateExtensionInner) -> CertificateExtension {
        let ((extension_type, ext_len), extension_data) = m;
        CertificateExtension { extension_type, ext_len, extension_data }
    }
}

pub struct CertificateExtensionMapper;
impl View for CertificateExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionMapper {
    type Src = SpecCertificateExtensionInner;
    type Dst = SpecCertificateExtension;
}
impl SpecIsoProof for CertificateExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateExtensionMapper {
    type Src = CertificateExtensionInner<'a>;
    type Dst = CertificateExtension<'a>;
    type RefSrc = CertificateExtensionInnerRef<'a>;
}

pub struct SpecCertificateExtensionCombinator(SpecCertificateExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionCombinator {
    type Type = SpecCertificateExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecCertificateExtensionExtensionDataCombinator>, CertificateExtensionMapper>;

pub struct CertificateExtensionCombinator(CertificateExtensionCombinatorAlias);

impl View for CertificateExtensionCombinator {
    type V = SpecCertificateExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateExtensionCombinator {
    type Type = CertificateExtension<'a>;
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
pub type CertificateExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, CertificateExtensionCont1>, CertificateExtensionExtensionDataCombinator, CertificateExtensionCont0>, CertificateExtensionMapper>;


pub closed spec fn spec_certificate_extension() -> SpecCertificateExtensionCombinator {
    SpecCertificateExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_certificate_extension_cont1(deps)), |deps| spec_certificate_extension_cont0(deps)),
        mapper: CertificateExtensionMapper,
    })
}

pub open spec fn spec_certificate_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for CertificateExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_certificate_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_certificate_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecCertificateExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_certificate_extension_extension_data(extension_type, ext_len)
}

impl View for CertificateExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecCertificateExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_certificate_extension_cont0(deps)
        }
    }
}

                
pub fn certificate_extension() -> (o: CertificateExtensionCombinator)
    ensures o@ == spec_certificate_extension(),
{
    CertificateExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), CertificateExtensionCont1), CertificateExtensionCont0),
        mapper: CertificateExtensionMapper,
    })
}

pub struct CertificateExtensionCont1;
type CertificateExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type CertificateExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type CertificateExtensionCont1Input<'a, 'b, 'x> = POrSType<CertificateExtensionCont1Type<'a, 'b>, CertificateExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateExtensionCont1Input<'a, 'b, 'x>> for CertificateExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: CertificateExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_extension_cont1(deps@)
    }

    fn apply(&self, deps: CertificateExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct CertificateExtensionCont0;
type CertificateExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type CertificateExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type CertificateExtensionCont0Input<'a, 'b, 'x> = POrSType<CertificateExtensionCont0Type<'a, 'b>, CertificateExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateExtensionCont0Input<'a, 'b, 'x>> for CertificateExtensionCont0 {
    type Output = CertificateExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: CertificateExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_extension_cont0(deps@)
    }

    fn apply(&self, deps: CertificateExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                certificate_extension_extension_data(extension_type, ext_len)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                certificate_extension_extension_data(extension_type, ext_len)
            }
        }
    }
}
                

pub struct SpecCertificateExtensions {
    pub l: u16,
    pub list: Seq<SpecCertificateExtension>,
}

pub type SpecCertificateExtensionsInner = (u16, Seq<SpecCertificateExtension>);


impl SpecFrom<SpecCertificateExtensions> for SpecCertificateExtensionsInner {
    open spec fn spec_from(m: SpecCertificateExtensions) -> SpecCertificateExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecCertificateExtensionsInner> for SpecCertificateExtensions {
    open spec fn spec_from(m: SpecCertificateExtensionsInner) -> SpecCertificateExtensions {
        let (l, list) = m;
        SpecCertificateExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<CertificateExtension<'a>>,
}

impl View for CertificateExtensions<'_> {
    type V = SpecCertificateExtensions;

    open spec fn view(&self) -> Self::V {
        SpecCertificateExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type CertificateExtensionsInner<'a> = (u16, RepeatResult<CertificateExtension<'a>>);

pub type CertificateExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<CertificateExtension<'a>>);
impl<'a> From<&'a CertificateExtensions<'a>> for CertificateExtensionsInnerRef<'a> {
    fn ex_from(m: &'a CertificateExtensions) -> CertificateExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<CertificateExtensionsInner<'a>> for CertificateExtensions<'a> {
    fn ex_from(m: CertificateExtensionsInner) -> CertificateExtensions {
        let (l, list) = m;
        CertificateExtensions { l, list }
    }
}

pub struct CertificateExtensionsMapper;
impl View for CertificateExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateExtensionsMapper {
    type Src = SpecCertificateExtensionsInner;
    type Dst = SpecCertificateExtensions;
}
impl SpecIsoProof for CertificateExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateExtensionsMapper {
    type Src = CertificateExtensionsInner<'a>;
    type Dst = CertificateExtensions<'a>;
    type RefSrc = CertificateExtensionsInnerRef<'a>;
}

pub struct SpecCertificateExtensionsCombinator(SpecCertificateExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionsCombinator {
    type Type = SpecCertificateExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateExtensionsCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecCertificateExtensionCombinator>>>, CertificateExtensionsMapper>;

pub struct CertificateExtensionsCombinator(CertificateExtensionsCombinatorAlias);

impl View for CertificateExtensionsCombinator {
    type V = SpecCertificateExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateExtensionsCombinator {
    type Type = CertificateExtensions<'a>;
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
pub type CertificateExtensionsCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<CertificateExtensionCombinator>>, CertificateExtensionsCont0>, CertificateExtensionsMapper>;


pub closed spec fn spec_certificate_extensions() -> SpecCertificateExtensionsCombinator {
    SpecCertificateExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_certificate_extensions_cont0(deps)),
        mapper: CertificateExtensionsMapper,
    })
}

pub open spec fn spec_certificate_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecCertificateExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_certificate_extension()))
}

impl View for CertificateExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecCertificateExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_certificate_extensions_cont0(deps)
        }
    }
}

                
pub fn certificate_extensions() -> (o: CertificateExtensionsCombinator)
    ensures o@ == spec_certificate_extensions(),
{
    CertificateExtensionsCombinator(
    Mapped {
        inner: Pair::new(U16Be, CertificateExtensionsCont0),
        mapper: CertificateExtensionsMapper,
    })
}

pub struct CertificateExtensionsCont0;
type CertificateExtensionsCont0Type<'a, 'b> = &'b u16;
type CertificateExtensionsCont0SType<'a, 'x> = &'x u16;
type CertificateExtensionsCont0Input<'a, 'b, 'x> = POrSType<CertificateExtensionsCont0Type<'a, 'b>, CertificateExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateExtensionsCont0Input<'a, 'b, 'x>> for CertificateExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CertificateExtensionCombinator>>;

    open spec fn requires(&self, deps: CertificateExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_extensions_cont0(deps@)
    }

    fn apply(&self, deps: CertificateExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_extension()))
            }
        }
    }
}
                

pub struct SpecCertificateEntryOpaque {
    pub cert_data: SpecOpaque1Ffffff,
    pub extensions: SpecCertificateExtensions,
}

pub type SpecCertificateEntryOpaqueInner = (SpecOpaque1Ffffff, SpecCertificateExtensions);


impl SpecFrom<SpecCertificateEntryOpaque> for SpecCertificateEntryOpaqueInner {
    open spec fn spec_from(m: SpecCertificateEntryOpaque) -> SpecCertificateEntryOpaqueInner {
        (m.cert_data, m.extensions)
    }
}

impl SpecFrom<SpecCertificateEntryOpaqueInner> for SpecCertificateEntryOpaque {
    open spec fn spec_from(m: SpecCertificateEntryOpaqueInner) -> SpecCertificateEntryOpaque {
        let (cert_data, extensions) = m;
        SpecCertificateEntryOpaque { cert_data, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateEntryOpaque<'a> {
    pub cert_data: Opaque1Ffffff<'a>,
    pub extensions: CertificateExtensions<'a>,
}

impl View for CertificateEntryOpaque<'_> {
    type V = SpecCertificateEntryOpaque;

    open spec fn view(&self) -> Self::V {
        SpecCertificateEntryOpaque {
            cert_data: self.cert_data@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateEntryOpaqueInner<'a> = (Opaque1Ffffff<'a>, CertificateExtensions<'a>);

pub type CertificateEntryOpaqueInnerRef<'a> = (&'a Opaque1Ffffff<'a>, &'a CertificateExtensions<'a>);
impl<'a> From<&'a CertificateEntryOpaque<'a>> for CertificateEntryOpaqueInnerRef<'a> {
    fn ex_from(m: &'a CertificateEntryOpaque) -> CertificateEntryOpaqueInnerRef<'a> {
        (&m.cert_data, &m.extensions)
    }
}

impl<'a> From<CertificateEntryOpaqueInner<'a>> for CertificateEntryOpaque<'a> {
    fn ex_from(m: CertificateEntryOpaqueInner) -> CertificateEntryOpaque {
        let (cert_data, extensions) = m;
        CertificateEntryOpaque { cert_data, extensions }
    }
}

pub struct CertificateEntryOpaqueMapper;
impl View for CertificateEntryOpaqueMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateEntryOpaqueMapper {
    type Src = SpecCertificateEntryOpaqueInner;
    type Dst = SpecCertificateEntryOpaque;
}
impl SpecIsoProof for CertificateEntryOpaqueMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateEntryOpaqueMapper {
    type Src = CertificateEntryOpaqueInner<'a>;
    type Dst = CertificateEntryOpaque<'a>;
    type RefSrc = CertificateEntryOpaqueInnerRef<'a>;
}
type SpecCertificateEntryOpaqueCombinatorAlias1 = (SpecOpaque1FfffffCombinator, SpecCertificateExtensionsCombinator);
pub struct SpecCertificateEntryOpaqueCombinator(SpecCertificateEntryOpaqueCombinatorAlias);

impl SpecCombinator for SpecCertificateEntryOpaqueCombinator {
    type Type = SpecCertificateEntryOpaque;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateEntryOpaqueCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateEntryOpaqueCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateEntryOpaqueCombinatorAlias = Mapped<SpecCertificateEntryOpaqueCombinatorAlias1, CertificateEntryOpaqueMapper>;
type CertificateEntryOpaqueCombinatorAlias1 = (Opaque1FfffffCombinator, CertificateExtensionsCombinator);
struct CertificateEntryOpaqueCombinator1(CertificateEntryOpaqueCombinatorAlias1);
impl View for CertificateEntryOpaqueCombinator1 {
    type V = SpecCertificateEntryOpaqueCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateEntryOpaqueCombinator1, CertificateEntryOpaqueCombinatorAlias1);

pub struct CertificateEntryOpaqueCombinator(CertificateEntryOpaqueCombinatorAlias);

impl View for CertificateEntryOpaqueCombinator {
    type V = SpecCertificateEntryOpaqueCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateEntryOpaqueCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateEntryOpaqueCombinator {
    type Type = CertificateEntryOpaque<'a>;
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
pub type CertificateEntryOpaqueCombinatorAlias = Mapped<CertificateEntryOpaqueCombinator1, CertificateEntryOpaqueMapper>;


pub closed spec fn spec_certificate_entry_opaque() -> SpecCertificateEntryOpaqueCombinator {
    SpecCertificateEntryOpaqueCombinator(
    Mapped {
        inner: (spec_opaque_1_ffffff(), spec_certificate_extensions()),
        mapper: CertificateEntryOpaqueMapper,
    })
}

                
pub fn certificate_entry_opaque() -> (o: CertificateEntryOpaqueCombinator)
    ensures o@ == spec_certificate_entry_opaque(),
{
    CertificateEntryOpaqueCombinator(
    Mapped {
        inner: CertificateEntryOpaqueCombinator1((opaque_1_ffffff(), certificate_extensions())),
        mapper: CertificateEntryOpaqueMapper,
    })
}

                

pub struct SpecCertificateList {
    pub l: u24,
    pub list: Seq<SpecCertificateEntryOpaque>,
}

pub type SpecCertificateListInner = (u24, Seq<SpecCertificateEntryOpaque>);


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
    pub list: RepeatResult<CertificateEntryOpaque<'a>>,
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
pub type CertificateListInner<'a> = (u24, RepeatResult<CertificateEntryOpaque<'a>>);

pub type CertificateListInnerRef<'a> = (&'a u24, &'a RepeatResult<CertificateEntryOpaque<'a>>);
impl<'a> From<&'a CertificateList<'a>> for CertificateListInnerRef<'a> {
    fn ex_from(m: &'a CertificateList) -> CertificateListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<CertificateListInner<'a>> for CertificateList<'a> {
    fn ex_from(m: CertificateListInner) -> CertificateList {
        let (l, list) = m;
        CertificateList { l, list }
    }
}

pub struct CertificateListMapper;
impl View for CertificateListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateListMapper {
    type Src = SpecCertificateListInner;
    type Dst = SpecCertificateList;
}
impl SpecIsoProof for CertificateListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateListMapper {
    type Src = CertificateListInner<'a>;
    type Dst = CertificateList<'a>;
    type RefSrc = CertificateListInnerRef<'a>;
}

pub struct SpecCertificateListCombinator(SpecCertificateListCombinatorAlias);

impl SpecCombinator for SpecCertificateListCombinator {
    type Type = SpecCertificateList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateListCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateListCombinatorAlias = Mapped<SpecPair<U24Be, AndThen<bytes::Variable, Repeat<SpecCertificateEntryOpaqueCombinator>>>, CertificateListMapper>;

pub struct CertificateListCombinator(CertificateListCombinatorAlias);

impl View for CertificateListCombinator {
    type V = SpecCertificateListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateListCombinator {
    type Type = CertificateList<'a>;
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
pub type CertificateListCombinatorAlias = Mapped<Pair<U24Be, AndThen<bytes::Variable, Repeat<CertificateEntryOpaqueCombinator>>, CertificateListCont0>, CertificateListMapper>;


pub closed spec fn spec_certificate_list() -> SpecCertificateListCombinator {
    SpecCertificateListCombinator(
    Mapped {
        inner: Pair::spec_new(U24Be, |deps| spec_certificate_list_cont0(deps)),
        mapper: CertificateListMapper,
    })
}

pub open spec fn spec_certificate_list_cont0(deps: u24) -> AndThen<bytes::Variable, Repeat<SpecCertificateEntryOpaqueCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_certificate_entry_opaque()))
}

impl View for CertificateListCont0 {
    type V = spec_fn(u24) -> AndThen<bytes::Variable, Repeat<SpecCertificateEntryOpaqueCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u24| {
            spec_certificate_list_cont0(deps)
        }
    }
}

                
pub fn certificate_list() -> (o: CertificateListCombinator)
    ensures o@ == spec_certificate_list(),
{
    CertificateListCombinator(
    Mapped {
        inner: Pair::new(U24Be, CertificateListCont0),
        mapper: CertificateListMapper,
    })
}

pub struct CertificateListCont0;
type CertificateListCont0Type<'a, 'b> = &'b u24;
type CertificateListCont0SType<'a, 'x> = &'x u24;
type CertificateListCont0Input<'a, 'b, 'x> = POrSType<CertificateListCont0Type<'a, 'b>, CertificateListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateListCont0Input<'a, 'b, 'x>> for CertificateListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CertificateEntryOpaqueCombinator>>;

    open spec fn requires(&self, deps: CertificateListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_list_cont0(deps@)
    }

    fn apply(&self, deps: CertificateListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_entry_opaque()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_entry_opaque()))
            }
        }
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

pub type CertificateInnerRef<'a> = (&'a Opaque0Ff<'a>, &'a CertificateList<'a>);
impl<'a> From<&'a Certificate<'a>> for CertificateInnerRef<'a> {
    fn ex_from(m: &'a Certificate) -> CertificateInnerRef<'a> {
        (&m.certificate_request_context, &m.certificate_list)
    }
}

impl<'a> From<CertificateInner<'a>> for Certificate<'a> {
    fn ex_from(m: CertificateInner) -> Certificate {
        let (certificate_request_context, certificate_list) = m;
        Certificate { certificate_request_context, certificate_list }
    }
}

pub struct CertificateMapper;
impl View for CertificateMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateMapper {
    type Src = SpecCertificateInner;
    type Dst = SpecCertificate;
}
impl SpecIsoProof for CertificateMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateMapper {
    type Src = CertificateInner<'a>;
    type Dst = Certificate<'a>;
    type RefSrc = CertificateInnerRef<'a>;
}
type SpecCertificateCombinatorAlias1 = (SpecOpaque0FfCombinator, SpecCertificateListCombinator);
pub struct SpecCertificateCombinator(SpecCertificateCombinatorAlias);

impl SpecCombinator for SpecCertificateCombinator {
    type Type = SpecCertificate;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateCombinatorAlias = Mapped<SpecCertificateCombinatorAlias1, CertificateMapper>;
type CertificateCombinatorAlias1 = (Opaque0FfCombinator, CertificateListCombinator);
struct CertificateCombinator1(CertificateCombinatorAlias1);
impl View for CertificateCombinator1 {
    type V = SpecCertificateCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateCombinator1, CertificateCombinatorAlias1);

pub struct CertificateCombinator(CertificateCombinatorAlias);

impl View for CertificateCombinator {
    type V = SpecCertificateCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateCombinator {
    type Type = Certificate<'a>;
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
pub type CertificateCombinatorAlias = Mapped<CertificateCombinator1, CertificateMapper>;


pub closed spec fn spec_certificate() -> SpecCertificateCombinator {
    SpecCertificateCombinator(
    Mapped {
        inner: (spec_opaque_0_ff(), spec_certificate_list()),
        mapper: CertificateMapper,
    })
}

                
pub fn certificate() -> (o: CertificateCombinator)
    ensures o@ == spec_certificate(),
{
    CertificateCombinator(
    Mapped {
        inner: CertificateCombinator1((opaque_0_ff(), certificate_list())),
        mapper: CertificateMapper,
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

pub type CertificateRequestExtensionExtensionDataInnerRef<'a> = Either<&'a SignatureSchemeList, Either<&'a CertificateAuthoritiesExtension<'a>, Either<&'a SignatureSchemeList, Either<&'a CertificateStatusRequest<'a>, Either<&'a SignedCertificateTimestampList<'a>, Either<&'a OidFilterExtension<'a>, &'a &'a [u8]>>>>>>;


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


impl<'a> From<&'a CertificateRequestExtensionExtensionData<'a>> for CertificateRequestExtensionExtensionDataInnerRef<'a> {
    fn ex_from(m: &'a CertificateRequestExtensionExtensionData<'a>) -> CertificateRequestExtensionExtensionDataInnerRef<'a> {
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


pub struct CertificateRequestExtensionExtensionDataMapper;
impl View for CertificateRequestExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionExtensionDataMapper {
    type Src = SpecCertificateRequestExtensionExtensionDataInner;
    type Dst = SpecCertificateRequestExtensionExtensionData;
}
impl SpecIsoProof for CertificateRequestExtensionExtensionDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateRequestExtensionExtensionDataMapper {
    type Src = CertificateRequestExtensionExtensionDataInner<'a>;
    type Dst = CertificateRequestExtensionExtensionData<'a>;
    type RefSrc = CertificateRequestExtensionExtensionDataInnerRef<'a>;
}

type SpecCertificateRequestExtensionExtensionDataCombinatorAlias1 = Choice<Cond<SpecOidFilterExtensionCombinator>, Cond<bytes::Variable>>;
type SpecCertificateRequestExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SpecSignedCertificateTimestampListCombinator>, SpecCertificateRequestExtensionExtensionDataCombinatorAlias1>;
type SpecCertificateRequestExtensionExtensionDataCombinatorAlias3 = Choice<Cond<SpecCertificateStatusRequestCombinator>, SpecCertificateRequestExtensionExtensionDataCombinatorAlias2>;
type SpecCertificateRequestExtensionExtensionDataCombinatorAlias4 = Choice<Cond<SpecSignatureSchemeListCombinator>, SpecCertificateRequestExtensionExtensionDataCombinatorAlias3>;
type SpecCertificateRequestExtensionExtensionDataCombinatorAlias5 = Choice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, SpecCertificateRequestExtensionExtensionDataCombinatorAlias4>;
type SpecCertificateRequestExtensionExtensionDataCombinatorAlias6 = Choice<Cond<SpecSignatureSchemeListCombinator>, SpecCertificateRequestExtensionExtensionDataCombinatorAlias5>;
pub struct SpecCertificateRequestExtensionExtensionDataCombinator(SpecCertificateRequestExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionExtensionDataCombinator {
    type Type = SpecCertificateRequestExtensionExtensionData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateRequestExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateRequestExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecCertificateRequestExtensionExtensionDataCombinatorAlias6, CertificateRequestExtensionExtensionDataMapper>>;
type CertificateRequestExtensionExtensionDataCombinatorAlias1 = Choice<Cond<OidFilterExtensionCombinator>, Cond<bytes::Variable>>;
type CertificateRequestExtensionExtensionDataCombinatorAlias2 = Choice<Cond<SignedCertificateTimestampListCombinator>, CertificateRequestExtensionExtensionDataCombinator1>;
type CertificateRequestExtensionExtensionDataCombinatorAlias3 = Choice<Cond<CertificateStatusRequestCombinator>, CertificateRequestExtensionExtensionDataCombinator2>;
type CertificateRequestExtensionExtensionDataCombinatorAlias4 = Choice<Cond<SignatureSchemeListCombinator>, CertificateRequestExtensionExtensionDataCombinator3>;
type CertificateRequestExtensionExtensionDataCombinatorAlias5 = Choice<Cond<CertificateAuthoritiesExtensionCombinator>, CertificateRequestExtensionExtensionDataCombinator4>;
type CertificateRequestExtensionExtensionDataCombinatorAlias6 = Choice<Cond<SignatureSchemeListCombinator>, CertificateRequestExtensionExtensionDataCombinator5>;
struct CertificateRequestExtensionExtensionDataCombinator1(CertificateRequestExtensionExtensionDataCombinatorAlias1);
impl View for CertificateRequestExtensionExtensionDataCombinator1 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator1, CertificateRequestExtensionExtensionDataCombinatorAlias1);

struct CertificateRequestExtensionExtensionDataCombinator2(CertificateRequestExtensionExtensionDataCombinatorAlias2);
impl View for CertificateRequestExtensionExtensionDataCombinator2 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator2, CertificateRequestExtensionExtensionDataCombinatorAlias2);

struct CertificateRequestExtensionExtensionDataCombinator3(CertificateRequestExtensionExtensionDataCombinatorAlias3);
impl View for CertificateRequestExtensionExtensionDataCombinator3 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator3, CertificateRequestExtensionExtensionDataCombinatorAlias3);

struct CertificateRequestExtensionExtensionDataCombinator4(CertificateRequestExtensionExtensionDataCombinatorAlias4);
impl View for CertificateRequestExtensionExtensionDataCombinator4 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator4, CertificateRequestExtensionExtensionDataCombinatorAlias4);

struct CertificateRequestExtensionExtensionDataCombinator5(CertificateRequestExtensionExtensionDataCombinatorAlias5);
impl View for CertificateRequestExtensionExtensionDataCombinator5 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator5, CertificateRequestExtensionExtensionDataCombinatorAlias5);

struct CertificateRequestExtensionExtensionDataCombinator6(CertificateRequestExtensionExtensionDataCombinatorAlias6);
impl View for CertificateRequestExtensionExtensionDataCombinator6 {
    type V = SpecCertificateRequestExtensionExtensionDataCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestExtensionExtensionDataCombinator6, CertificateRequestExtensionExtensionDataCombinatorAlias6);

pub struct CertificateRequestExtensionExtensionDataCombinator(CertificateRequestExtensionExtensionDataCombinatorAlias);

impl View for CertificateRequestExtensionExtensionDataCombinator {
    type V = SpecCertificateRequestExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionExtensionDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateRequestExtensionExtensionDataCombinator {
    type Type = CertificateRequestExtensionExtensionData<'a>;
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
pub type CertificateRequestExtensionExtensionDataCombinatorAlias = AndThen<bytes::Variable, Mapped<CertificateRequestExtensionExtensionDataCombinator6, CertificateRequestExtensionExtensionDataMapper>>;


pub closed spec fn spec_certificate_request_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecCertificateRequestExtensionExtensionDataCombinator {
    SpecCertificateRequestExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.spec_into()), Mapped { inner: Choice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, Choice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, Choice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, Choice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, Choice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, Choice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, Cond { cond: !(extension_type == 13 || extension_type == 47 || extension_type == 50 || extension_type == 5 || extension_type == 18 || extension_type == 48), inner: bytes::Variable(ext_len.spec_into()) })))))), mapper: CertificateRequestExtensionExtensionDataMapper }))
}

pub fn certificate_request_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: CertificateRequestExtensionExtensionDataCombinator)
    ensures o@ == spec_certificate_request_extension_extension_data(extension_type@, ext_len@),
{
    CertificateRequestExtensionExtensionDataCombinator(AndThen(bytes::Variable(ext_len.ex_into()), Mapped { inner: CertificateRequestExtensionExtensionDataCombinator6(Choice::new(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, CertificateRequestExtensionExtensionDataCombinator5(Choice::new(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, CertificateRequestExtensionExtensionDataCombinator4(Choice::new(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, CertificateRequestExtensionExtensionDataCombinator3(Choice::new(Cond { cond: extension_type == 5, inner: certificate_status_request() }, CertificateRequestExtensionExtensionDataCombinator2(Choice::new(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, CertificateRequestExtensionExtensionDataCombinator1(Choice::new(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, Cond { cond: !(extension_type == 13 || extension_type == 47 || extension_type == 50 || extension_type == 5 || extension_type == 18 || extension_type == 48), inner: bytes::Variable(ext_len.ex_into()) })))))))))))), mapper: CertificateRequestExtensionExtensionDataMapper }))
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

pub type CertificateRequestExtensionInnerRef<'a> = ((&'a ExtensionType, &'a u16), &'a CertificateRequestExtensionExtensionData<'a>);
impl<'a> From<&'a CertificateRequestExtension<'a>> for CertificateRequestExtensionInnerRef<'a> {
    fn ex_from(m: &'a CertificateRequestExtension) -> CertificateRequestExtensionInnerRef<'a> {
        ((&m.extension_type, &m.ext_len), &m.extension_data)
    }
}

impl<'a> From<CertificateRequestExtensionInner<'a>> for CertificateRequestExtension<'a> {
    fn ex_from(m: CertificateRequestExtensionInner) -> CertificateRequestExtension {
        let ((extension_type, ext_len), extension_data) = m;
        CertificateRequestExtension { extension_type, ext_len, extension_data }
    }
}

pub struct CertificateRequestExtensionMapper;
impl View for CertificateRequestExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionMapper {
    type Src = SpecCertificateRequestExtensionInner;
    type Dst = SpecCertificateRequestExtension;
}
impl SpecIsoProof for CertificateRequestExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateRequestExtensionMapper {
    type Src = CertificateRequestExtensionInner<'a>;
    type Dst = CertificateRequestExtension<'a>;
    type RefSrc = CertificateRequestExtensionInnerRef<'a>;
}

pub struct SpecCertificateRequestExtensionCombinator(SpecCertificateRequestExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionCombinator {
    type Type = SpecCertificateRequestExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateRequestExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateRequestExtensionCombinatorAlias = Mapped<SpecPair<SpecPair<SpecExtensionTypeCombinator, U16Be>, SpecCertificateRequestExtensionExtensionDataCombinator>, CertificateRequestExtensionMapper>;

pub struct CertificateRequestExtensionCombinator(CertificateRequestExtensionCombinatorAlias);

impl View for CertificateRequestExtensionCombinator {
    type V = SpecCertificateRequestExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateRequestExtensionCombinator {
    type Type = CertificateRequestExtension<'a>;
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
pub type CertificateRequestExtensionCombinatorAlias = Mapped<Pair<Pair<ExtensionTypeCombinator, U16Be, CertificateRequestExtensionCont1>, CertificateRequestExtensionExtensionDataCombinator, CertificateRequestExtensionCont0>, CertificateRequestExtensionMapper>;


pub closed spec fn spec_certificate_request_extension() -> SpecCertificateRequestExtensionCombinator {
    SpecCertificateRequestExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_extension_type(), |deps| spec_certificate_request_extension_cont1(deps)), |deps| spec_certificate_request_extension_cont0(deps)),
        mapper: CertificateRequestExtensionMapper,
    })
}

pub open spec fn spec_certificate_request_extension_cont1(deps: SpecExtensionType) -> U16Be {
    let extension_type = deps;
    U16Be
}

impl View for CertificateRequestExtensionCont1 {
    type V = spec_fn(SpecExtensionType) -> U16Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecExtensionType| {
            spec_certificate_request_extension_cont1(deps)
        }
    }
}

pub open spec fn spec_certificate_request_extension_cont0(deps: (SpecExtensionType, u16)) -> SpecCertificateRequestExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_certificate_request_extension_extension_data(extension_type, ext_len)
}

impl View for CertificateRequestExtensionCont0 {
    type V = spec_fn((SpecExtensionType, u16)) -> SpecCertificateRequestExtensionExtensionDataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecExtensionType, u16)| {
            spec_certificate_request_extension_cont0(deps)
        }
    }
}

                
pub fn certificate_request_extension() -> (o: CertificateRequestExtensionCombinator)
    ensures o@ == spec_certificate_request_extension(),
{
    CertificateRequestExtensionCombinator(
    Mapped {
        inner: Pair::new(Pair::new(extension_type(), CertificateRequestExtensionCont1), CertificateRequestExtensionCont0),
        mapper: CertificateRequestExtensionMapper,
    })
}

pub struct CertificateRequestExtensionCont1;
type CertificateRequestExtensionCont1Type<'a, 'b> = &'b ExtensionType;
type CertificateRequestExtensionCont1SType<'a, 'x> = &'x ExtensionType;
type CertificateRequestExtensionCont1Input<'a, 'b, 'x> = POrSType<CertificateRequestExtensionCont1Type<'a, 'b>, CertificateRequestExtensionCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateRequestExtensionCont1Input<'a, 'b, 'x>> for CertificateRequestExtensionCont1 {
    type Output = U16Be;

    open spec fn requires(&self, deps: CertificateRequestExtensionCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateRequestExtensionCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extension_cont1(deps@)
    }

    fn apply(&self, deps: CertificateRequestExtensionCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let extension_type = *deps;
                U16Be
            }
            POrSType::S(deps) => {
                let extension_type = deps;
                let extension_type = *extension_type;
                U16Be
            }
        }
    }
}
pub struct CertificateRequestExtensionCont0;
type CertificateRequestExtensionCont0Type<'a, 'b> = &'b (ExtensionType, u16);
type CertificateRequestExtensionCont0SType<'a, 'x> = (&'x ExtensionType, &'x u16);
type CertificateRequestExtensionCont0Input<'a, 'b, 'x> = POrSType<CertificateRequestExtensionCont0Type<'a, 'b>, CertificateRequestExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateRequestExtensionCont0Input<'a, 'b, 'x>> for CertificateRequestExtensionCont0 {
    type Output = CertificateRequestExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: CertificateRequestExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateRequestExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extension_cont0(deps@)
    }

    fn apply(&self, deps: CertificateRequestExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (extension_type, ext_len) = *deps;
                certificate_request_extension_extension_data(extension_type, ext_len)
            }
            POrSType::S(deps) => {
                let (extension_type, ext_len) = deps;
                let (extension_type, ext_len) = (*extension_type, *ext_len);
                certificate_request_extension_extension_data(extension_type, ext_len)
            }
        }
    }
}
                

pub struct SpecCertificateRequestExtensions {
    pub l: u16,
    pub list: Seq<SpecCertificateRequestExtension>,
}

pub type SpecCertificateRequestExtensionsInner = (u16, Seq<SpecCertificateRequestExtension>);


impl SpecFrom<SpecCertificateRequestExtensions> for SpecCertificateRequestExtensionsInner {
    open spec fn spec_from(m: SpecCertificateRequestExtensions) -> SpecCertificateRequestExtensionsInner {
        (m.l, m.list)
    }
}

impl SpecFrom<SpecCertificateRequestExtensionsInner> for SpecCertificateRequestExtensions {
    open spec fn spec_from(m: SpecCertificateRequestExtensionsInner) -> SpecCertificateRequestExtensions {
        let (l, list) = m;
        SpecCertificateRequestExtensions { l, list }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateRequestExtensions<'a> {
    pub l: u16,
    pub list: RepeatResult<CertificateRequestExtension<'a>>,
}

impl View for CertificateRequestExtensions<'_> {
    type V = SpecCertificateRequestExtensions;

    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtensions {
            l: self.l@,
            list: self.list@,
        }
    }
}
pub type CertificateRequestExtensionsInner<'a> = (u16, RepeatResult<CertificateRequestExtension<'a>>);

pub type CertificateRequestExtensionsInnerRef<'a> = (&'a u16, &'a RepeatResult<CertificateRequestExtension<'a>>);
impl<'a> From<&'a CertificateRequestExtensions<'a>> for CertificateRequestExtensionsInnerRef<'a> {
    fn ex_from(m: &'a CertificateRequestExtensions) -> CertificateRequestExtensionsInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl<'a> From<CertificateRequestExtensionsInner<'a>> for CertificateRequestExtensions<'a> {
    fn ex_from(m: CertificateRequestExtensionsInner) -> CertificateRequestExtensions {
        let (l, list) = m;
        CertificateRequestExtensions { l, list }
    }
}

pub struct CertificateRequestExtensionsMapper;
impl View for CertificateRequestExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionsMapper {
    type Src = SpecCertificateRequestExtensionsInner;
    type Dst = SpecCertificateRequestExtensions;
}
impl SpecIsoProof for CertificateRequestExtensionsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateRequestExtensionsMapper {
    type Src = CertificateRequestExtensionsInner<'a>;
    type Dst = CertificateRequestExtensions<'a>;
    type RefSrc = CertificateRequestExtensionsInnerRef<'a>;
}

pub struct SpecCertificateRequestExtensionsCombinator(SpecCertificateRequestExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionsCombinator {
    type Type = SpecCertificateRequestExtensions;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateRequestExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionsCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateRequestExtensionsCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<SpecCertificateRequestExtensionCombinator>>>, CertificateRequestExtensionsMapper>;

pub struct CertificateRequestExtensionsCombinator(CertificateRequestExtensionsCombinatorAlias);

impl View for CertificateRequestExtensionsCombinator {
    type V = SpecCertificateRequestExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateRequestExtensionsCombinator {
    type Type = CertificateRequestExtensions<'a>;
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
pub type CertificateRequestExtensionsCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate8195707947578446211>, AndThen<bytes::Variable, Repeat<CertificateRequestExtensionCombinator>>, CertificateRequestExtensionsCont0>, CertificateRequestExtensionsMapper>;


pub closed spec fn spec_certificate_request_extensions() -> SpecCertificateRequestExtensionsCombinator {
    SpecCertificateRequestExtensionsCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, |deps| spec_certificate_request_extensions_cont0(deps)),
        mapper: CertificateRequestExtensionsMapper,
    })
}

pub open spec fn spec_certificate_request_extensions_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecCertificateRequestExtensionCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_certificate_request_extension()))
}

impl View for CertificateRequestExtensionsCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecCertificateRequestExtensionCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_certificate_request_extensions_cont0(deps)
        }
    }
}

                
pub fn certificate_request_extensions() -> (o: CertificateRequestExtensionsCombinator)
    ensures o@ == spec_certificate_request_extensions(),
{
    CertificateRequestExtensionsCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate8195707947578446211 }, CertificateRequestExtensionsCont0),
        mapper: CertificateRequestExtensionsMapper,
    })
}

pub struct CertificateRequestExtensionsCont0;
type CertificateRequestExtensionsCont0Type<'a, 'b> = &'b u16;
type CertificateRequestExtensionsCont0SType<'a, 'x> = &'x u16;
type CertificateRequestExtensionsCont0Input<'a, 'b, 'x> = POrSType<CertificateRequestExtensionsCont0Type<'a, 'b>, CertificateRequestExtensionsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CertificateRequestExtensionsCont0Input<'a, 'b, 'x>> for CertificateRequestExtensionsCont0 {
    type Output = AndThen<bytes::Variable, Repeat<CertificateRequestExtensionCombinator>>;

    open spec fn requires(&self, deps: CertificateRequestExtensionsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CertificateRequestExtensionsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extensions_cont0(deps@)
    }

    fn apply(&self, deps: CertificateRequestExtensionsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_request_extension()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(certificate_request_extension()))
            }
        }
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

pub type CertificateRequestInnerRef<'a> = (&'a Opaque0Ff<'a>, &'a CertificateRequestExtensions<'a>);
impl<'a> From<&'a CertificateRequest<'a>> for CertificateRequestInnerRef<'a> {
    fn ex_from(m: &'a CertificateRequest) -> CertificateRequestInnerRef<'a> {
        (&m.certificate_request_context, &m.extensions)
    }
}

impl<'a> From<CertificateRequestInner<'a>> for CertificateRequest<'a> {
    fn ex_from(m: CertificateRequestInner) -> CertificateRequest {
        let (certificate_request_context, extensions) = m;
        CertificateRequest { certificate_request_context, extensions }
    }
}

pub struct CertificateRequestMapper;
impl View for CertificateRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestMapper {
    type Src = SpecCertificateRequestInner;
    type Dst = SpecCertificateRequest;
}
impl SpecIsoProof for CertificateRequestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateRequestMapper {
    type Src = CertificateRequestInner<'a>;
    type Dst = CertificateRequest<'a>;
    type RefSrc = CertificateRequestInnerRef<'a>;
}
type SpecCertificateRequestCombinatorAlias1 = (SpecOpaque0FfCombinator, SpecCertificateRequestExtensionsCombinator);
pub struct SpecCertificateRequestCombinator(SpecCertificateRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestCombinator {
    type Type = SpecCertificateRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateRequestCombinatorAlias = Mapped<SpecCertificateRequestCombinatorAlias1, CertificateRequestMapper>;
type CertificateRequestCombinatorAlias1 = (Opaque0FfCombinator, CertificateRequestExtensionsCombinator);
struct CertificateRequestCombinator1(CertificateRequestCombinatorAlias1);
impl View for CertificateRequestCombinator1 {
    type V = SpecCertificateRequestCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateRequestCombinator1, CertificateRequestCombinatorAlias1);

pub struct CertificateRequestCombinator(CertificateRequestCombinatorAlias);

impl View for CertificateRequestCombinator {
    type V = SpecCertificateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateRequestCombinator {
    type Type = CertificateRequest<'a>;
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
pub type CertificateRequestCombinatorAlias = Mapped<CertificateRequestCombinator1, CertificateRequestMapper>;


pub closed spec fn spec_certificate_request() -> SpecCertificateRequestCombinator {
    SpecCertificateRequestCombinator(
    Mapped {
        inner: (spec_opaque_0_ff(), spec_certificate_request_extensions()),
        mapper: CertificateRequestMapper,
    })
}

                
pub fn certificate_request() -> (o: CertificateRequestCombinator)
    ensures o@ == spec_certificate_request(),
{
    CertificateRequestCombinator(
    Mapped {
        inner: CertificateRequestCombinator1((opaque_0_ff(), certificate_request_extensions())),
        mapper: CertificateRequestMapper,
    })
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

pub type CertificateVerifyInnerRef<'a> = (&'a SignatureScheme, &'a Opaque0Ffff<'a>);
impl<'a> From<&'a CertificateVerify<'a>> for CertificateVerifyInnerRef<'a> {
    fn ex_from(m: &'a CertificateVerify) -> CertificateVerifyInnerRef<'a> {
        (&m.algorithm, &m.signature)
    }
}

impl<'a> From<CertificateVerifyInner<'a>> for CertificateVerify<'a> {
    fn ex_from(m: CertificateVerifyInner) -> CertificateVerify {
        let (algorithm, signature) = m;
        CertificateVerify { algorithm, signature }
    }
}

pub struct CertificateVerifyMapper;
impl View for CertificateVerifyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateVerifyMapper {
    type Src = SpecCertificateVerifyInner;
    type Dst = SpecCertificateVerify;
}
impl SpecIsoProof for CertificateVerifyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateVerifyMapper {
    type Src = CertificateVerifyInner<'a>;
    type Dst = CertificateVerify<'a>;
    type RefSrc = CertificateVerifyInnerRef<'a>;
}
type SpecCertificateVerifyCombinatorAlias1 = (SpecSignatureSchemeCombinator, SpecOpaque0FfffCombinator);
pub struct SpecCertificateVerifyCombinator(SpecCertificateVerifyCombinatorAlias);

impl SpecCombinator for SpecCertificateVerifyCombinator {
    type Type = SpecCertificateVerify;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateVerifyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateVerifyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateVerifyCombinatorAlias = Mapped<SpecCertificateVerifyCombinatorAlias1, CertificateVerifyMapper>;
type CertificateVerifyCombinatorAlias1 = (SignatureSchemeCombinator, Opaque0FfffCombinator);
struct CertificateVerifyCombinator1(CertificateVerifyCombinatorAlias1);
impl View for CertificateVerifyCombinator1 {
    type V = SpecCertificateVerifyCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateVerifyCombinator1, CertificateVerifyCombinatorAlias1);

pub struct CertificateVerifyCombinator(CertificateVerifyCombinatorAlias);

impl View for CertificateVerifyCombinator {
    type V = SpecCertificateVerifyCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateVerifyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateVerifyCombinator {
    type Type = CertificateVerify<'a>;
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
pub type CertificateVerifyCombinatorAlias = Mapped<CertificateVerifyCombinator1, CertificateVerifyMapper>;


pub closed spec fn spec_certificate_verify() -> SpecCertificateVerifyCombinator {
    SpecCertificateVerifyCombinator(
    Mapped {
        inner: (spec_signature_scheme(), spec_opaque_0_ffff()),
        mapper: CertificateVerifyMapper,
    })
}

                
pub fn certificate_verify() -> (o: CertificateVerifyCombinator)
    ensures o@ == spec_certificate_verify(),
{
    CertificateVerifyCombinator(
    Mapped {
        inner: CertificateVerifyCombinator1((signature_scheme(), opaque_0_ffff())),
        mapper: CertificateVerifyMapper,
    })
}

                

pub enum SpecFinished {
    Hash12(Seq<u8>),
    Hash20(Seq<u8>),
    Sha256(Seq<u8>),
    Sha384(Seq<u8>),
    Sha512(Seq<u8>),
    Unrecognized(Seq<u8>),
}

pub type SpecFinishedInner = Either<Seq<u8>, Either<Seq<u8>, Either<Seq<u8>, Either<Seq<u8>, Either<Seq<u8>, Seq<u8>>>>>>;

impl SpecFrom<SpecFinished> for SpecFinishedInner {
    open spec fn spec_from(m: SpecFinished) -> SpecFinishedInner {
        match m {
            SpecFinished::Hash12(m) => Either::Left(m),
            SpecFinished::Hash20(m) => Either::Right(Either::Left(m)),
            SpecFinished::Sha256(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecFinished::Sha384(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecFinished::Sha512(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecFinished::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

                
impl SpecFrom<SpecFinishedInner> for SpecFinished {
    open spec fn spec_from(m: SpecFinishedInner) -> SpecFinished {
        match m {
            Either::Left(m) => SpecFinished::Hash12(m),
            Either::Right(Either::Left(m)) => SpecFinished::Hash20(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecFinished::Sha256(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecFinished::Sha384(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecFinished::Sha512(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => SpecFinished::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Finished<'a> {
    Hash12(&'a [u8]),
    Hash20(&'a [u8]),
    Sha256(&'a [u8]),
    Sha384(&'a [u8]),
    Sha512(&'a [u8]),
    Unrecognized(&'a [u8]),
}

pub type FinishedInner<'a> = Either<&'a [u8], Either<&'a [u8], Either<&'a [u8], Either<&'a [u8], Either<&'a [u8], &'a [u8]>>>>>;

pub type FinishedInnerRef<'a> = Either<&'a &'a [u8], Either<&'a &'a [u8], Either<&'a &'a [u8], Either<&'a &'a [u8], Either<&'a &'a [u8], &'a &'a [u8]>>>>>;


impl<'a> View for Finished<'a> {
    type V = SpecFinished;
    open spec fn view(&self) -> Self::V {
        match self {
            Finished::Hash12(m) => SpecFinished::Hash12(m@),
            Finished::Hash20(m) => SpecFinished::Hash20(m@),
            Finished::Sha256(m) => SpecFinished::Sha256(m@),
            Finished::Sha384(m) => SpecFinished::Sha384(m@),
            Finished::Sha512(m) => SpecFinished::Sha512(m@),
            Finished::Unrecognized(m) => SpecFinished::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a Finished<'a>> for FinishedInnerRef<'a> {
    fn ex_from(m: &'a Finished<'a>) -> FinishedInnerRef<'a> {
        match m {
            Finished::Hash12(m) => Either::Left(m),
            Finished::Hash20(m) => Either::Right(Either::Left(m)),
            Finished::Sha256(m) => Either::Right(Either::Right(Either::Left(m))),
            Finished::Sha384(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            Finished::Sha512(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            Finished::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

impl<'a> From<FinishedInner<'a>> for Finished<'a> {
    fn ex_from(m: FinishedInner<'a>) -> Finished<'a> {
        match m {
            Either::Left(m) => Finished::Hash12(m),
            Either::Right(Either::Left(m)) => Finished::Hash20(m),
            Either::Right(Either::Right(Either::Left(m))) => Finished::Sha256(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => Finished::Sha384(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => Finished::Sha512(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => Finished::Unrecognized(m),
        }
    }
    
}


pub struct FinishedMapper;
impl View for FinishedMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FinishedMapper {
    type Src = SpecFinishedInner;
    type Dst = SpecFinished;
}
impl SpecIsoProof for FinishedMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FinishedMapper {
    type Src = FinishedInner<'a>;
    type Dst = Finished<'a>;
    type RefSrc = FinishedInnerRef<'a>;
}

type SpecFinishedCombinatorAlias1 = Choice<Cond<bytes::Fixed<64>>, Cond<bytes::Variable>>;
type SpecFinishedCombinatorAlias2 = Choice<Cond<bytes::Fixed<48>>, SpecFinishedCombinatorAlias1>;
type SpecFinishedCombinatorAlias3 = Choice<Cond<bytes::Fixed<32>>, SpecFinishedCombinatorAlias2>;
type SpecFinishedCombinatorAlias4 = Choice<Cond<bytes::Fixed<20>>, SpecFinishedCombinatorAlias3>;
type SpecFinishedCombinatorAlias5 = Choice<Cond<bytes::Fixed<12>>, SpecFinishedCombinatorAlias4>;
pub struct SpecFinishedCombinator(SpecFinishedCombinatorAlias);

impl SpecCombinator for SpecFinishedCombinator {
    type Type = SpecFinished;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFinishedCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFinishedCombinatorAlias::is_prefix_secure() }
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
pub type SpecFinishedCombinatorAlias = Mapped<SpecFinishedCombinatorAlias5, FinishedMapper>;
type FinishedCombinatorAlias1 = Choice<Cond<bytes::Fixed<64>>, Cond<bytes::Variable>>;
type FinishedCombinatorAlias2 = Choice<Cond<bytes::Fixed<48>>, FinishedCombinator1>;
type FinishedCombinatorAlias3 = Choice<Cond<bytes::Fixed<32>>, FinishedCombinator2>;
type FinishedCombinatorAlias4 = Choice<Cond<bytes::Fixed<20>>, FinishedCombinator3>;
type FinishedCombinatorAlias5 = Choice<Cond<bytes::Fixed<12>>, FinishedCombinator4>;
struct FinishedCombinator1(FinishedCombinatorAlias1);
impl View for FinishedCombinator1 {
    type V = SpecFinishedCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FinishedCombinator1, FinishedCombinatorAlias1);

struct FinishedCombinator2(FinishedCombinatorAlias2);
impl View for FinishedCombinator2 {
    type V = SpecFinishedCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FinishedCombinator2, FinishedCombinatorAlias2);

struct FinishedCombinator3(FinishedCombinatorAlias3);
impl View for FinishedCombinator3 {
    type V = SpecFinishedCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FinishedCombinator3, FinishedCombinatorAlias3);

struct FinishedCombinator4(FinishedCombinatorAlias4);
impl View for FinishedCombinator4 {
    type V = SpecFinishedCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FinishedCombinator4, FinishedCombinatorAlias4);

struct FinishedCombinator5(FinishedCombinatorAlias5);
impl View for FinishedCombinator5 {
    type V = SpecFinishedCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(FinishedCombinator5, FinishedCombinatorAlias5);

pub struct FinishedCombinator(FinishedCombinatorAlias);

impl View for FinishedCombinator {
    type V = SpecFinishedCombinator;
    closed spec fn view(&self) -> Self::V { SpecFinishedCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FinishedCombinator {
    type Type = Finished<'a>;
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
pub type FinishedCombinatorAlias = Mapped<FinishedCombinator5, FinishedMapper>;


pub closed spec fn spec_finished(size: SpecDigestSize) -> SpecFinishedCombinator {
    SpecFinishedCombinator(Mapped { inner: Choice(Cond { cond: size.spec_as_u32() == 12, inner: bytes::Fixed::<12> }, Choice(Cond { cond: size.spec_as_u32() == 20, inner: bytes::Fixed::<20> }, Choice(Cond { cond: size.spec_as_u32() == 32, inner: bytes::Fixed::<32> }, Choice(Cond { cond: size.spec_as_u32() == 48, inner: bytes::Fixed::<48> }, Choice(Cond { cond: size.spec_as_u32() == 64, inner: bytes::Fixed::<64> }, Cond { cond: !(size.spec_as_u32() == 12 || size.spec_as_u32() == 20 || size.spec_as_u32() == 32 || size.spec_as_u32() == 48 || size.spec_as_u32() == 64), inner: bytes::Variable(size.spec_into()) }))))), mapper: FinishedMapper })
}

pub fn finished<'a>(size: DigestSize) -> (o: FinishedCombinator)
    ensures o@ == spec_finished(size@),
{
    FinishedCombinator(Mapped { inner: FinishedCombinator5(Choice::new(Cond { cond: size.as_u32() == 12, inner: bytes::Fixed::<12> }, FinishedCombinator4(Choice::new(Cond { cond: size.as_u32() == 20, inner: bytes::Fixed::<20> }, FinishedCombinator3(Choice::new(Cond { cond: size.as_u32() == 32, inner: bytes::Fixed::<32> }, FinishedCombinator2(Choice::new(Cond { cond: size.as_u32() == 48, inner: bytes::Fixed::<48> }, FinishedCombinator1(Choice::new(Cond { cond: size.as_u32() == 64, inner: bytes::Fixed::<64> }, Cond { cond: !(size.as_u32() == 12 || size.as_u32() == 20 || size.as_u32() == 32 || size.as_u32() == 48 || size.as_u32() == 64), inner: bytes::Variable(size.ex_into()) })))))))))), mapper: FinishedMapper })
}


pub spec const SPEC_KeyUpdateRequest_UpdateNotRequested: u8 = 0;
pub spec const SPEC_KeyUpdateRequest_UpdateRequested: u8 = 1;
pub exec static EXEC_KeyUpdateRequest_UpdateNotRequested: u8 ensures EXEC_KeyUpdateRequest_UpdateNotRequested == SPEC_KeyUpdateRequest_UpdateNotRequested { 0 }
pub exec static EXEC_KeyUpdateRequest_UpdateRequested: u8 ensures EXEC_KeyUpdateRequest_UpdateRequested == SPEC_KeyUpdateRequest_UpdateRequested { 1 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum KeyUpdateRequest {
    UpdateNotRequested = 0,
UpdateRequested = 1
}
pub type SpecKeyUpdateRequest = KeyUpdateRequest;

pub type KeyUpdateRequestInner = u8;

pub type KeyUpdateRequestInnerRef<'a> = &'a u8;

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
            KeyUpdateRequest::UpdateNotRequested => Ok(SPEC_KeyUpdateRequest_UpdateNotRequested),
            KeyUpdateRequest::UpdateRequested => Ok(SPEC_KeyUpdateRequest_UpdateRequested),
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

impl<'a> TryFrom<&'a KeyUpdateRequest> for KeyUpdateRequestInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a KeyUpdateRequest) -> Result<KeyUpdateRequestInnerRef<'a>, ()> {
        match v {
            KeyUpdateRequest::UpdateNotRequested => Ok(&EXEC_KeyUpdateRequest_UpdateNotRequested),
            KeyUpdateRequest::UpdateRequested => Ok(&EXEC_KeyUpdateRequest_UpdateRequested),
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

impl SpecPartialIso for KeyUpdateRequestMapper {
    type Src = KeyUpdateRequestInner;
    type Dst = KeyUpdateRequest;
}

impl SpecPartialIsoProof for KeyUpdateRequestMapper {
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

impl<'a> PartialIso<'a> for KeyUpdateRequestMapper {
    type Src = KeyUpdateRequestInner;
    type Dst = KeyUpdateRequest;
    type RefSrc = KeyUpdateRequestInnerRef<'a>;
}


pub struct SpecKeyUpdateRequestCombinator(SpecKeyUpdateRequestCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateRequestCombinator {
    type Type = SpecKeyUpdateRequest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecKeyUpdateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateRequestCombinatorAlias::is_prefix_secure() }
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
pub type SpecKeyUpdateRequestCombinatorAlias = TryMap<U8, KeyUpdateRequestMapper>;

pub struct KeyUpdateRequestCombinator(KeyUpdateRequestCombinatorAlias);

impl View for KeyUpdateRequestCombinator {
    type V = SpecKeyUpdateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateRequestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for KeyUpdateRequestCombinator {
    type Type = KeyUpdateRequest;
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

pub type KeyUpdateInnerRef<'a> = &'a KeyUpdateRequest;
impl<'a> From<&'a KeyUpdate> for KeyUpdateInnerRef<'a> {
    fn ex_from(m: &'a KeyUpdate) -> KeyUpdateInnerRef<'a> {
        &m.request_update
    }
}

impl From<KeyUpdateInner> for KeyUpdate {
    fn ex_from(m: KeyUpdateInner) -> KeyUpdate {
        let request_update = m;
        KeyUpdate { request_update }
    }
}

pub struct KeyUpdateMapper;
impl View for KeyUpdateMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyUpdateMapper {
    type Src = SpecKeyUpdateInner;
    type Dst = SpecKeyUpdate;
}
impl SpecIsoProof for KeyUpdateMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for KeyUpdateMapper {
    type Src = KeyUpdateInner;
    type Dst = KeyUpdate;
    type RefSrc = KeyUpdateInnerRef<'a>;
}

pub struct SpecKeyUpdateCombinator(SpecKeyUpdateCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateCombinator {
    type Type = SpecKeyUpdate;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecKeyUpdateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateCombinatorAlias::is_prefix_secure() }
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
pub type SpecKeyUpdateCombinatorAlias = Mapped<SpecKeyUpdateRequestCombinator, KeyUpdateMapper>;

pub struct KeyUpdateCombinator(KeyUpdateCombinatorAlias);

impl View for KeyUpdateCombinator {
    type V = SpecKeyUpdateCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for KeyUpdateCombinator {
    type Type = KeyUpdate;
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
pub type KeyUpdateCombinatorAlias = Mapped<KeyUpdateRequestCombinator, KeyUpdateMapper>;


pub closed spec fn spec_key_update() -> SpecKeyUpdateCombinator {
    SpecKeyUpdateCombinator(
    Mapped {
        inner: spec_key_update_request(),
        mapper: KeyUpdateMapper,
    })
}

                
pub fn key_update() -> (o: KeyUpdateCombinator)
    ensures o@ == spec_key_update(),
{
    KeyUpdateCombinator(
    Mapped {
        inner: key_update_request(),
        mapper: KeyUpdateMapper,
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

pub type HandshakeMsgInnerRef<'a> = Either<&'a ClientHello<'a>, Either<&'a ShOrHrr<'a>, Either<&'a NewSessionTicket<'a>, Either<&'a Empty<'a>, Either<&'a EncryptedExtensions<'a>, Either<&'a Certificate<'a>, Either<&'a CertificateRequest<'a>, Either<&'a CertificateVerify<'a>, Either<&'a Finished<'a>, &'a KeyUpdate>>>>>>>>>;


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


impl<'a> From<&'a HandshakeMsg<'a>> for HandshakeMsgInnerRef<'a> {
    fn ex_from(m: &'a HandshakeMsg<'a>) -> HandshakeMsgInnerRef<'a> {
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


pub struct HandshakeMsgMapper;
impl View for HandshakeMsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMsgMapper {
    type Src = SpecHandshakeMsgInner;
    type Dst = SpecHandshakeMsg;
}
impl SpecIsoProof for HandshakeMsgMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HandshakeMsgMapper {
    type Src = HandshakeMsgInner<'a>;
    type Dst = HandshakeMsg<'a>;
    type RefSrc = HandshakeMsgInnerRef<'a>;
}

type SpecHandshakeMsgCombinatorAlias1 = Choice<Cond<SpecFinishedCombinator>, Cond<SpecKeyUpdateCombinator>>;
type SpecHandshakeMsgCombinatorAlias2 = Choice<Cond<SpecCertificateVerifyCombinator>, SpecHandshakeMsgCombinatorAlias1>;
type SpecHandshakeMsgCombinatorAlias3 = Choice<Cond<SpecCertificateRequestCombinator>, SpecHandshakeMsgCombinatorAlias2>;
type SpecHandshakeMsgCombinatorAlias4 = Choice<Cond<SpecCertificateCombinator>, SpecHandshakeMsgCombinatorAlias3>;
type SpecHandshakeMsgCombinatorAlias5 = Choice<Cond<SpecEncryptedExtensionsCombinator>, SpecHandshakeMsgCombinatorAlias4>;
type SpecHandshakeMsgCombinatorAlias6 = Choice<Cond<SpecEmptyCombinator>, SpecHandshakeMsgCombinatorAlias5>;
type SpecHandshakeMsgCombinatorAlias7 = Choice<Cond<SpecNewSessionTicketCombinator>, SpecHandshakeMsgCombinatorAlias6>;
type SpecHandshakeMsgCombinatorAlias8 = Choice<Cond<SpecShOrHrrCombinator>, SpecHandshakeMsgCombinatorAlias7>;
type SpecHandshakeMsgCombinatorAlias9 = Choice<Cond<SpecClientHelloCombinator>, SpecHandshakeMsgCombinatorAlias8>;
pub struct SpecHandshakeMsgCombinator(SpecHandshakeMsgCombinatorAlias);

impl SpecCombinator for SpecHandshakeMsgCombinator {
    type Type = SpecHandshakeMsg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHandshakeMsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeMsgCombinatorAlias::is_prefix_secure() }
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
pub type SpecHandshakeMsgCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecHandshakeMsgCombinatorAlias9, HandshakeMsgMapper>>;
type HandshakeMsgCombinatorAlias1 = Choice<Cond<FinishedCombinator>, Cond<KeyUpdateCombinator>>;
type HandshakeMsgCombinatorAlias2 = Choice<Cond<CertificateVerifyCombinator>, HandshakeMsgCombinator1>;
type HandshakeMsgCombinatorAlias3 = Choice<Cond<CertificateRequestCombinator>, HandshakeMsgCombinator2>;
type HandshakeMsgCombinatorAlias4 = Choice<Cond<CertificateCombinator>, HandshakeMsgCombinator3>;
type HandshakeMsgCombinatorAlias5 = Choice<Cond<EncryptedExtensionsCombinator>, HandshakeMsgCombinator4>;
type HandshakeMsgCombinatorAlias6 = Choice<Cond<EmptyCombinator>, HandshakeMsgCombinator5>;
type HandshakeMsgCombinatorAlias7 = Choice<Cond<NewSessionTicketCombinator>, HandshakeMsgCombinator6>;
type HandshakeMsgCombinatorAlias8 = Choice<Cond<ShOrHrrCombinator>, HandshakeMsgCombinator7>;
type HandshakeMsgCombinatorAlias9 = Choice<Cond<ClientHelloCombinator>, HandshakeMsgCombinator8>;
struct HandshakeMsgCombinator1(HandshakeMsgCombinatorAlias1);
impl View for HandshakeMsgCombinator1 {
    type V = SpecHandshakeMsgCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator1, HandshakeMsgCombinatorAlias1);

struct HandshakeMsgCombinator2(HandshakeMsgCombinatorAlias2);
impl View for HandshakeMsgCombinator2 {
    type V = SpecHandshakeMsgCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator2, HandshakeMsgCombinatorAlias2);

struct HandshakeMsgCombinator3(HandshakeMsgCombinatorAlias3);
impl View for HandshakeMsgCombinator3 {
    type V = SpecHandshakeMsgCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator3, HandshakeMsgCombinatorAlias3);

struct HandshakeMsgCombinator4(HandshakeMsgCombinatorAlias4);
impl View for HandshakeMsgCombinator4 {
    type V = SpecHandshakeMsgCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator4, HandshakeMsgCombinatorAlias4);

struct HandshakeMsgCombinator5(HandshakeMsgCombinatorAlias5);
impl View for HandshakeMsgCombinator5 {
    type V = SpecHandshakeMsgCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator5, HandshakeMsgCombinatorAlias5);

struct HandshakeMsgCombinator6(HandshakeMsgCombinatorAlias6);
impl View for HandshakeMsgCombinator6 {
    type V = SpecHandshakeMsgCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator6, HandshakeMsgCombinatorAlias6);

struct HandshakeMsgCombinator7(HandshakeMsgCombinatorAlias7);
impl View for HandshakeMsgCombinator7 {
    type V = SpecHandshakeMsgCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator7, HandshakeMsgCombinatorAlias7);

struct HandshakeMsgCombinator8(HandshakeMsgCombinatorAlias8);
impl View for HandshakeMsgCombinator8 {
    type V = SpecHandshakeMsgCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator8, HandshakeMsgCombinatorAlias8);

struct HandshakeMsgCombinator9(HandshakeMsgCombinatorAlias9);
impl View for HandshakeMsgCombinator9 {
    type V = SpecHandshakeMsgCombinatorAlias9;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(HandshakeMsgCombinator9, HandshakeMsgCombinatorAlias9);

pub struct HandshakeMsgCombinator(HandshakeMsgCombinatorAlias);

impl View for HandshakeMsgCombinator {
    type V = SpecHandshakeMsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeMsgCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HandshakeMsgCombinator {
    type Type = HandshakeMsg<'a>;
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
pub type HandshakeMsgCombinatorAlias = AndThen<bytes::Variable, Mapped<HandshakeMsgCombinator9, HandshakeMsgMapper>>;


pub closed spec fn spec_handshake_msg(length: u24, msg_type: SpecHandshakeType) -> SpecHandshakeMsgCombinator {
    SpecHandshakeMsgCombinator(AndThen(bytes::Variable(length.spec_into()), Mapped { inner: Choice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: spec_client_hello() }, Choice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: spec_sh_or_hrr() }, Choice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: spec_new_session_ticket() }, Choice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: spec_empty() }, Choice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: spec_encrypted_extensions() }, Choice(Cond { cond: msg_type == HandshakeType::Certificate, inner: spec_certificate() }, Choice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: spec_certificate_request() }, Choice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: spec_certificate_verify() }, Choice(Cond { cond: msg_type == HandshakeType::Finished, inner: spec_finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: spec_key_update() }))))))))), mapper: HandshakeMsgMapper }))
}

pub fn handshake_msg<'a>(length: u24, msg_type: HandshakeType) -> (o: HandshakeMsgCombinator)
    ensures o@ == spec_handshake_msg(length@, msg_type@),
{
    HandshakeMsgCombinator(AndThen(bytes::Variable(length.ex_into()), Mapped { inner: HandshakeMsgCombinator9(Choice::new(Cond { cond: msg_type == HandshakeType::ClientHello, inner: client_hello() }, HandshakeMsgCombinator8(Choice::new(Cond { cond: msg_type == HandshakeType::ServerHello, inner: sh_or_hrr() }, HandshakeMsgCombinator7(Choice::new(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: new_session_ticket() }, HandshakeMsgCombinator6(Choice::new(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: empty() }, HandshakeMsgCombinator5(Choice::new(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: encrypted_extensions() }, HandshakeMsgCombinator4(Choice::new(Cond { cond: msg_type == HandshakeType::Certificate, inner: certificate() }, HandshakeMsgCombinator3(Choice::new(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: certificate_request() }, HandshakeMsgCombinator2(Choice::new(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: certificate_verify() }, HandshakeMsgCombinator1(Choice::new(Cond { cond: msg_type == HandshakeType::Finished, inner: finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: key_update() })))))))))))))))))), mapper: HandshakeMsgMapper }))
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

pub type ServerCertTypeServerExtensionInnerRef<'a> = &'a CertificateType;
impl<'a> From<&'a ServerCertTypeServerExtension> for ServerCertTypeServerExtensionInnerRef<'a> {
    fn ex_from(m: &'a ServerCertTypeServerExtension) -> ServerCertTypeServerExtensionInnerRef<'a> {
        &m.server_certificate_type
    }
}

impl From<ServerCertTypeServerExtensionInner> for ServerCertTypeServerExtension {
    fn ex_from(m: ServerCertTypeServerExtensionInner) -> ServerCertTypeServerExtension {
        let server_certificate_type = m;
        ServerCertTypeServerExtension { server_certificate_type }
    }
}

pub struct ServerCertTypeServerExtensionMapper;
impl View for ServerCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeServerExtensionMapper {
    type Src = SpecServerCertTypeServerExtensionInner;
    type Dst = SpecServerCertTypeServerExtension;
}
impl SpecIsoProof for ServerCertTypeServerExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ServerCertTypeServerExtensionMapper {
    type Src = ServerCertTypeServerExtensionInner;
    type Dst = ServerCertTypeServerExtension;
    type RefSrc = ServerCertTypeServerExtensionInnerRef<'a>;
}

pub struct SpecServerCertTypeServerExtensionCombinator(SpecServerCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    type Type = SpecServerCertTypeServerExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecServerCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;

pub struct ServerCertTypeServerExtensionCombinator(ServerCertTypeServerExtensionCombinatorAlias);

impl View for ServerCertTypeServerExtensionCombinator {
    type V = SpecServerCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ServerCertTypeServerExtensionCombinator {
    type Type = ServerCertTypeServerExtension;
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
pub type ServerCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;


pub closed spec fn spec_server_cert_type_server_extension() -> SpecServerCertTypeServerExtensionCombinator {
    SpecServerCertTypeServerExtensionCombinator(
    Mapped {
        inner: spec_certificate_type(),
        mapper: ServerCertTypeServerExtensionMapper,
    })
}

                
pub fn server_cert_type_server_extension() -> (o: ServerCertTypeServerExtensionCombinator)
    ensures o@ == spec_server_cert_type_server_extension(),
{
    ServerCertTypeServerExtensionCombinator(
    Mapped {
        inner: certificate_type(),
        mapper: ServerCertTypeServerExtensionMapper,
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

pub type Opaque0FfffffInnerRef<'a> = (&'a u24, &'a &'a [u8]);
impl<'a> From<&'a Opaque0Ffffff<'a>> for Opaque0FfffffInnerRef<'a> {
    fn ex_from(m: &'a Opaque0Ffffff) -> Opaque0FfffffInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque0FfffffInner<'a>> for Opaque0Ffffff<'a> {
    fn ex_from(m: Opaque0FfffffInner) -> Opaque0Ffffff {
        let (l, data) = m;
        Opaque0Ffffff { l, data }
    }
}

pub struct Opaque0FfffffMapper;
impl View for Opaque0FfffffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffffMapper {
    type Src = SpecOpaque0FfffffInner;
    type Dst = SpecOpaque0Ffffff;
}
impl SpecIsoProof for Opaque0FfffffMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque0FfffffMapper {
    type Src = Opaque0FfffffInner<'a>;
    type Dst = Opaque0Ffffff<'a>;
    type RefSrc = Opaque0FfffffInnerRef<'a>;
}

pub struct SpecOpaque0FfffffCombinator(SpecOpaque0FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffffCombinator {
    type Type = SpecOpaque0Ffffff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque0FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffffCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque0FfffffCombinatorAlias = Mapped<SpecPair<U24Be, bytes::Variable>, Opaque0FfffffMapper>;

pub struct Opaque0FfffffCombinator(Opaque0FfffffCombinatorAlias);

impl View for Opaque0FfffffCombinator {
    type V = SpecOpaque0FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffffCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque0FfffffCombinator {
    type Type = Opaque0Ffffff<'a>;
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
pub type Opaque0FfffffCombinatorAlias = Mapped<Pair<U24Be, bytes::Variable, Opaque0FfffffCont0>, Opaque0FfffffMapper>;


pub closed spec fn spec_opaque_0_ffffff() -> SpecOpaque0FfffffCombinator {
    SpecOpaque0FfffffCombinator(
    Mapped {
        inner: Pair::spec_new(U24Be, |deps| spec_opaque0_ffffff_cont0(deps)),
        mapper: Opaque0FfffffMapper,
    })
}

pub open spec fn spec_opaque0_ffffff_cont0(deps: u24) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque0FfffffCont0 {
    type V = spec_fn(u24) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u24| {
            spec_opaque0_ffffff_cont0(deps)
        }
    }
}

                
pub fn opaque_0_ffffff() -> (o: Opaque0FfffffCombinator)
    ensures o@ == spec_opaque_0_ffffff(),
{
    Opaque0FfffffCombinator(
    Mapped {
        inner: Pair::new(U24Be, Opaque0FfffffCont0),
        mapper: Opaque0FfffffMapper,
    })
}

pub struct Opaque0FfffffCont0;
type Opaque0FfffffCont0Type<'a, 'b> = &'b u24;
type Opaque0FfffffCont0SType<'a, 'x> = &'x u24;
type Opaque0FfffffCont0Input<'a, 'b, 'x> = POrSType<Opaque0FfffffCont0Type<'a, 'b>, Opaque0FfffffCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque0FfffffCont0Input<'a, 'b, 'x>> for Opaque0FfffffCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque0FfffffCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque0FfffffCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffffff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque0FfffffCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub enum SpecCertificateEntryData {
    X509(SpecOpaque1Ffffff),
    RawPublicKey(SpecOpaque1Ffffff),
}

pub type SpecCertificateEntryDataInner = Either<SpecOpaque1Ffffff, SpecOpaque1Ffffff>;

impl SpecFrom<SpecCertificateEntryData> for SpecCertificateEntryDataInner {
    open spec fn spec_from(m: SpecCertificateEntryData) -> SpecCertificateEntryDataInner {
        match m {
            SpecCertificateEntryData::X509(m) => Either::Left(m),
            SpecCertificateEntryData::RawPublicKey(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCertificateEntryDataInner> for SpecCertificateEntryData {
    open spec fn spec_from(m: SpecCertificateEntryDataInner) -> SpecCertificateEntryData {
        match m {
            Either::Left(m) => SpecCertificateEntryData::X509(m),
            Either::Right(m) => SpecCertificateEntryData::RawPublicKey(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateEntryData<'a> {
    X509(Opaque1Ffffff<'a>),
    RawPublicKey(Opaque1Ffffff<'a>),
}

pub type CertificateEntryDataInner<'a> = Either<Opaque1Ffffff<'a>, Opaque1Ffffff<'a>>;

pub type CertificateEntryDataInnerRef<'a> = Either<&'a Opaque1Ffffff<'a>, &'a Opaque1Ffffff<'a>>;


impl<'a> View for CertificateEntryData<'a> {
    type V = SpecCertificateEntryData;
    open spec fn view(&self) -> Self::V {
        match self {
            CertificateEntryData::X509(m) => SpecCertificateEntryData::X509(m@),
            CertificateEntryData::RawPublicKey(m) => SpecCertificateEntryData::RawPublicKey(m@),
        }
    }
}


impl<'a> From<&'a CertificateEntryData<'a>> for CertificateEntryDataInnerRef<'a> {
    fn ex_from(m: &'a CertificateEntryData<'a>) -> CertificateEntryDataInnerRef<'a> {
        match m {
            CertificateEntryData::X509(m) => Either::Left(m),
            CertificateEntryData::RawPublicKey(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CertificateEntryDataInner<'a>> for CertificateEntryData<'a> {
    fn ex_from(m: CertificateEntryDataInner<'a>) -> CertificateEntryData<'a> {
        match m {
            Either::Left(m) => CertificateEntryData::X509(m),
            Either::Right(m) => CertificateEntryData::RawPublicKey(m),
        }
    }
    
}


pub struct CertificateEntryDataMapper;
impl View for CertificateEntryDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateEntryDataMapper {
    type Src = SpecCertificateEntryDataInner;
    type Dst = SpecCertificateEntryData;
}
impl SpecIsoProof for CertificateEntryDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateEntryDataMapper {
    type Src = CertificateEntryDataInner<'a>;
    type Dst = CertificateEntryData<'a>;
    type RefSrc = CertificateEntryDataInnerRef<'a>;
}

type SpecCertificateEntryDataCombinatorAlias1 = Choice<Cond<SpecOpaque1FfffffCombinator>, Cond<SpecOpaque1FfffffCombinator>>;
pub struct SpecCertificateEntryDataCombinator(SpecCertificateEntryDataCombinatorAlias);

impl SpecCombinator for SpecCertificateEntryDataCombinator {
    type Type = SpecCertificateEntryData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateEntryDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateEntryDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateEntryDataCombinatorAlias = Mapped<SpecCertificateEntryDataCombinatorAlias1, CertificateEntryDataMapper>;
type CertificateEntryDataCombinatorAlias1 = Choice<Cond<Opaque1FfffffCombinator>, Cond<Opaque1FfffffCombinator>>;
struct CertificateEntryDataCombinator1(CertificateEntryDataCombinatorAlias1);
impl View for CertificateEntryDataCombinator1 {
    type V = SpecCertificateEntryDataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateEntryDataCombinator1, CertificateEntryDataCombinatorAlias1);

pub struct CertificateEntryDataCombinator(CertificateEntryDataCombinatorAlias);

impl View for CertificateEntryDataCombinator {
    type V = SpecCertificateEntryDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateEntryDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateEntryDataCombinator {
    type Type = CertificateEntryData<'a>;
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
pub type CertificateEntryDataCombinatorAlias = Mapped<CertificateEntryDataCombinator1, CertificateEntryDataMapper>;


pub closed spec fn spec_certificate_entry_data(cert_type: SpecCertificateType) -> SpecCertificateEntryDataCombinator {
    SpecCertificateEntryDataCombinator(Mapped { inner: Choice(Cond { cond: cert_type == 0, inner: spec_opaque_1_ffffff() }, Cond { cond: cert_type == 2, inner: spec_opaque_1_ffffff() }), mapper: CertificateEntryDataMapper })
}

pub fn certificate_entry_data<'a>(cert_type: CertificateType) -> (o: CertificateEntryDataCombinator)
    ensures o@ == spec_certificate_entry_data(cert_type@),
{
    CertificateEntryDataCombinator(Mapped { inner: CertificateEntryDataCombinator1(Choice::new(Cond { cond: cert_type == 0, inner: opaque_1_ffffff() }, Cond { cond: cert_type == 2, inner: opaque_1_ffffff() })), mapper: CertificateEntryDataMapper })
}


pub struct SpecCertificateEntry {
    pub data: SpecCertificateEntryData,
    pub extensions: SpecCertificateExtensions,
}

pub type SpecCertificateEntryInner = (SpecCertificateEntryData, SpecCertificateExtensions);


impl SpecFrom<SpecCertificateEntry> for SpecCertificateEntryInner {
    open spec fn spec_from(m: SpecCertificateEntry) -> SpecCertificateEntryInner {
        (m.data, m.extensions)
    }
}

impl SpecFrom<SpecCertificateEntryInner> for SpecCertificateEntry {
    open spec fn spec_from(m: SpecCertificateEntryInner) -> SpecCertificateEntry {
        let (data, extensions) = m;
        SpecCertificateEntry { data, extensions }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CertificateEntry<'a> {
    pub data: CertificateEntryData<'a>,
    pub extensions: CertificateExtensions<'a>,
}

impl View for CertificateEntry<'_> {
    type V = SpecCertificateEntry;

    open spec fn view(&self) -> Self::V {
        SpecCertificateEntry {
            data: self.data@,
            extensions: self.extensions@,
        }
    }
}
pub type CertificateEntryInner<'a> = (CertificateEntryData<'a>, CertificateExtensions<'a>);

pub type CertificateEntryInnerRef<'a> = (&'a CertificateEntryData<'a>, &'a CertificateExtensions<'a>);
impl<'a> From<&'a CertificateEntry<'a>> for CertificateEntryInnerRef<'a> {
    fn ex_from(m: &'a CertificateEntry) -> CertificateEntryInnerRef<'a> {
        (&m.data, &m.extensions)
    }
}

impl<'a> From<CertificateEntryInner<'a>> for CertificateEntry<'a> {
    fn ex_from(m: CertificateEntryInner) -> CertificateEntry {
        let (data, extensions) = m;
        CertificateEntry { data, extensions }
    }
}

pub struct CertificateEntryMapper;
impl View for CertificateEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateEntryMapper {
    type Src = SpecCertificateEntryInner;
    type Dst = SpecCertificateEntry;
}
impl SpecIsoProof for CertificateEntryMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CertificateEntryMapper {
    type Src = CertificateEntryInner<'a>;
    type Dst = CertificateEntry<'a>;
    type RefSrc = CertificateEntryInnerRef<'a>;
}
type SpecCertificateEntryCombinatorAlias1 = (SpecCertificateEntryDataCombinator, SpecCertificateExtensionsCombinator);
pub struct SpecCertificateEntryCombinator(SpecCertificateEntryCombinatorAlias);

impl SpecCombinator for SpecCertificateEntryCombinator {
    type Type = SpecCertificateEntry;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCertificateEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateEntryCombinatorAlias::is_prefix_secure() }
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
pub type SpecCertificateEntryCombinatorAlias = Mapped<SpecCertificateEntryCombinatorAlias1, CertificateEntryMapper>;
type CertificateEntryCombinatorAlias1 = (CertificateEntryDataCombinator, CertificateExtensionsCombinator);
struct CertificateEntryCombinator1(CertificateEntryCombinatorAlias1);
impl View for CertificateEntryCombinator1 {
    type V = SpecCertificateEntryCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CertificateEntryCombinator1, CertificateEntryCombinatorAlias1);

pub struct CertificateEntryCombinator(CertificateEntryCombinatorAlias);

impl View for CertificateEntryCombinator {
    type V = SpecCertificateEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateEntryCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CertificateEntryCombinator {
    type Type = CertificateEntry<'a>;
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
pub type CertificateEntryCombinatorAlias = Mapped<CertificateEntryCombinator1, CertificateEntryMapper>;


pub closed spec fn spec_certificate_entry(cert_type: SpecCertificateType) -> SpecCertificateEntryCombinator {
    SpecCertificateEntryCombinator(
    Mapped {
        inner: (spec_certificate_entry_data(cert_type), spec_certificate_extensions()),
        mapper: CertificateEntryMapper,
    })
}

pub fn certificate_entry<'a>(cert_type: CertificateType) -> (o: CertificateEntryCombinator)
    ensures o@ == spec_certificate_entry(cert_type@),
{
    CertificateEntryCombinator(
    Mapped {
        inner: CertificateEntryCombinator1((certificate_entry_data(cert_type), certificate_extensions())),
        mapper: CertificateEntryMapper,
    })
}

pub type SpecUnknownExtension = SpecOpaque0Ffff;
pub type UnknownExtension<'a> = Opaque0Ffff<'a>;
pub type UnknownExtensionRef<'a> = &'a Opaque0Ffff<'a>;


pub struct SpecUnknownExtensionCombinator(SpecUnknownExtensionCombinatorAlias);

impl SpecCombinator for SpecUnknownExtensionCombinator {
    type Type = SpecUnknownExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecUnknownExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecUnknownExtensionCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct UnknownExtensionCombinator(UnknownExtensionCombinatorAlias);

impl View for UnknownExtensionCombinator {
    type V = SpecUnknownExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for UnknownExtensionCombinator {
    type Type = UnknownExtension<'a>;
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
pub type UnknownExtensionCombinatorAlias = Opaque0FfffCombinator;


pub closed spec fn spec_unknown_extension() -> SpecUnknownExtensionCombinator {
    SpecUnknownExtensionCombinator(spec_opaque_0_ffff())
}

                
pub fn unknown_extension() -> (o: UnknownExtensionCombinator)
    ensures o@ == spec_unknown_extension(),
{
    UnknownExtensionCombinator(opaque_0_ffff())
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

pub type ClientCertTypeServerExtensionInnerRef<'a> = &'a CertificateType;
impl<'a> From<&'a ClientCertTypeServerExtension> for ClientCertTypeServerExtensionInnerRef<'a> {
    fn ex_from(m: &'a ClientCertTypeServerExtension) -> ClientCertTypeServerExtensionInnerRef<'a> {
        &m.client_certificate_type
    }
}

impl From<ClientCertTypeServerExtensionInner> for ClientCertTypeServerExtension {
    fn ex_from(m: ClientCertTypeServerExtensionInner) -> ClientCertTypeServerExtension {
        let client_certificate_type = m;
        ClientCertTypeServerExtension { client_certificate_type }
    }
}

pub struct ClientCertTypeServerExtensionMapper;
impl View for ClientCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeServerExtensionMapper {
    type Src = SpecClientCertTypeServerExtensionInner;
    type Dst = SpecClientCertTypeServerExtension;
}
impl SpecIsoProof for ClientCertTypeServerExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ClientCertTypeServerExtensionMapper {
    type Src = ClientCertTypeServerExtensionInner;
    type Dst = ClientCertTypeServerExtension;
    type RefSrc = ClientCertTypeServerExtensionInnerRef<'a>;
}

pub struct SpecClientCertTypeServerExtensionCombinator(SpecClientCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    type Type = SpecClientCertTypeServerExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecClientCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;

pub struct ClientCertTypeServerExtensionCombinator(ClientCertTypeServerExtensionCombinatorAlias);

impl View for ClientCertTypeServerExtensionCombinator {
    type V = SpecClientCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeServerExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ClientCertTypeServerExtensionCombinator {
    type Type = ClientCertTypeServerExtension;
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
pub type ClientCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;


pub closed spec fn spec_client_cert_type_server_extension() -> SpecClientCertTypeServerExtensionCombinator {
    SpecClientCertTypeServerExtensionCombinator(
    Mapped {
        inner: spec_certificate_type(),
        mapper: ClientCertTypeServerExtensionMapper,
    })
}

                
pub fn client_cert_type_server_extension() -> (o: ClientCertTypeServerExtensionCombinator)
    ensures o@ == spec_client_cert_type_server_extension(),
{
    ClientCertTypeServerExtensionCombinator(
    Mapped {
        inner: certificate_type(),
        mapper: ClientCertTypeServerExtensionMapper,
    })
}

                

pub struct SpecOpaque2Ffff {
    pub l: u16,
    pub data: Seq<u8>,
}

pub type SpecOpaque2FfffInner = (u16, Seq<u8>);


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
    pub l: u16,
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
pub type Opaque2FfffInner<'a> = (u16, &'a [u8]);

pub type Opaque2FfffInnerRef<'a> = (&'a u16, &'a &'a [u8]);
impl<'a> From<&'a Opaque2Ffff<'a>> for Opaque2FfffInnerRef<'a> {
    fn ex_from(m: &'a Opaque2Ffff) -> Opaque2FfffInnerRef<'a> {
        (&m.l, &m.data)
    }
}

impl<'a> From<Opaque2FfffInner<'a>> for Opaque2Ffff<'a> {
    fn ex_from(m: Opaque2FfffInner) -> Opaque2Ffff {
        let (l, data) = m;
        Opaque2Ffff { l, data }
    }
}

pub struct Opaque2FfffMapper;
impl View for Opaque2FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque2FfffMapper {
    type Src = SpecOpaque2FfffInner;
    type Dst = SpecOpaque2Ffff;
}
impl SpecIsoProof for Opaque2FfffMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Opaque2FfffMapper {
    type Src = Opaque2FfffInner<'a>;
    type Dst = Opaque2Ffff<'a>;
    type RefSrc = Opaque2FfffInnerRef<'a>;
}

pub struct SpecOpaque2FfffCombinator(SpecOpaque2FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque2FfffCombinator {
    type Type = SpecOpaque2Ffff;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecOpaque2FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque2FfffCombinatorAlias::is_prefix_secure() }
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
pub type SpecOpaque2FfffCombinatorAlias = Mapped<SpecPair<Refined<U16Be, Predicate3016150102856496288>, bytes::Variable>, Opaque2FfffMapper>;
pub struct Predicate3016150102856496288;
impl View for Predicate3016150102856496288 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u16> for Predicate3016150102856496288 {
    fn apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}
impl SpecPred<u16> for Predicate3016150102856496288 {
    open spec fn spec_apply(&self, i: &u16) -> bool {
        let i = (*i);
        (i >= 2 && i <= 65535)
    }
}

pub struct Opaque2FfffCombinator(Opaque2FfffCombinatorAlias);

impl View for Opaque2FfffCombinator {
    type V = SpecOpaque2FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque2FfffCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Opaque2FfffCombinator {
    type Type = Opaque2Ffff<'a>;
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
pub type Opaque2FfffCombinatorAlias = Mapped<Pair<Refined<U16Be, Predicate3016150102856496288>, bytes::Variable, Opaque2FfffCont0>, Opaque2FfffMapper>;


pub closed spec fn spec_opaque_2_ffff() -> SpecOpaque2FfffCombinator {
    SpecOpaque2FfffCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U16Be, predicate: Predicate3016150102856496288 }, |deps| spec_opaque2_ffff_cont0(deps)),
        mapper: Opaque2FfffMapper,
    })
}

pub open spec fn spec_opaque2_ffff_cont0(deps: u16) -> bytes::Variable {
    let l = deps;
    bytes::Variable(l.spec_into())
}

impl View for Opaque2FfffCont0 {
    type V = spec_fn(u16) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_opaque2_ffff_cont0(deps)
        }
    }
}

                
pub fn opaque_2_ffff() -> (o: Opaque2FfffCombinator)
    ensures o@ == spec_opaque_2_ffff(),
{
    Opaque2FfffCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U16Be, predicate: Predicate3016150102856496288 }, Opaque2FfffCont0),
        mapper: Opaque2FfffMapper,
    })
}

pub struct Opaque2FfffCont0;
type Opaque2FfffCont0Type<'a, 'b> = &'b u16;
type Opaque2FfffCont0SType<'a, 'x> = &'x u16;
type Opaque2FfffCont0Input<'a, 'b, 'x> = POrSType<Opaque2FfffCont0Type<'a, 'b>, Opaque2FfffCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<Opaque2FfffCont0Input<'a, 'b, 'x>> for Opaque2FfffCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: Opaque2FfffCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: Opaque2FfffCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_opaque2_ffff_cont0(deps@)
    }

    fn apply(&self, deps: Opaque2FfffCont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub spec const SPEC_HandshakeType_ClientHello: u8 = 1;
pub spec const SPEC_HandshakeType_ServerHello: u8 = 2;
pub spec const SPEC_HandshakeType_NewSessionTicket: u8 = 4;
pub spec const SPEC_HandshakeType_EndOfEarlyData: u8 = 5;
pub spec const SPEC_HandshakeType_EncryptedExtensions: u8 = 8;
pub spec const SPEC_HandshakeType_Certificate: u8 = 11;
pub spec const SPEC_HandshakeType_CertificateRequest: u8 = 13;
pub spec const SPEC_HandshakeType_CertificateVerify: u8 = 15;
pub spec const SPEC_HandshakeType_Finished: u8 = 20;
pub spec const SPEC_HandshakeType_KeyUpdate: u8 = 24;
pub exec static EXEC_HandshakeType_ClientHello: u8 ensures EXEC_HandshakeType_ClientHello == SPEC_HandshakeType_ClientHello { 1 }
pub exec static EXEC_HandshakeType_ServerHello: u8 ensures EXEC_HandshakeType_ServerHello == SPEC_HandshakeType_ServerHello { 2 }
pub exec static EXEC_HandshakeType_NewSessionTicket: u8 ensures EXEC_HandshakeType_NewSessionTicket == SPEC_HandshakeType_NewSessionTicket { 4 }
pub exec static EXEC_HandshakeType_EndOfEarlyData: u8 ensures EXEC_HandshakeType_EndOfEarlyData == SPEC_HandshakeType_EndOfEarlyData { 5 }
pub exec static EXEC_HandshakeType_EncryptedExtensions: u8 ensures EXEC_HandshakeType_EncryptedExtensions == SPEC_HandshakeType_EncryptedExtensions { 8 }
pub exec static EXEC_HandshakeType_Certificate: u8 ensures EXEC_HandshakeType_Certificate == SPEC_HandshakeType_Certificate { 11 }
pub exec static EXEC_HandshakeType_CertificateRequest: u8 ensures EXEC_HandshakeType_CertificateRequest == SPEC_HandshakeType_CertificateRequest { 13 }
pub exec static EXEC_HandshakeType_CertificateVerify: u8 ensures EXEC_HandshakeType_CertificateVerify == SPEC_HandshakeType_CertificateVerify { 15 }
pub exec static EXEC_HandshakeType_Finished: u8 ensures EXEC_HandshakeType_Finished == SPEC_HandshakeType_Finished { 20 }
pub exec static EXEC_HandshakeType_KeyUpdate: u8 ensures EXEC_HandshakeType_KeyUpdate == SPEC_HandshakeType_KeyUpdate { 24 }

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

pub type HandshakeTypeInnerRef<'a> = &'a u8;

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
            HandshakeType::ClientHello => Ok(SPEC_HandshakeType_ClientHello),
            HandshakeType::ServerHello => Ok(SPEC_HandshakeType_ServerHello),
            HandshakeType::NewSessionTicket => Ok(SPEC_HandshakeType_NewSessionTicket),
            HandshakeType::EndOfEarlyData => Ok(SPEC_HandshakeType_EndOfEarlyData),
            HandshakeType::EncryptedExtensions => Ok(SPEC_HandshakeType_EncryptedExtensions),
            HandshakeType::Certificate => Ok(SPEC_HandshakeType_Certificate),
            HandshakeType::CertificateRequest => Ok(SPEC_HandshakeType_CertificateRequest),
            HandshakeType::CertificateVerify => Ok(SPEC_HandshakeType_CertificateVerify),
            HandshakeType::Finished => Ok(SPEC_HandshakeType_Finished),
            HandshakeType::KeyUpdate => Ok(SPEC_HandshakeType_KeyUpdate),
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

impl<'a> TryFrom<&'a HandshakeType> for HandshakeTypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a HandshakeType) -> Result<HandshakeTypeInnerRef<'a>, ()> {
        match v {
            HandshakeType::ClientHello => Ok(&EXEC_HandshakeType_ClientHello),
            HandshakeType::ServerHello => Ok(&EXEC_HandshakeType_ServerHello),
            HandshakeType::NewSessionTicket => Ok(&EXEC_HandshakeType_NewSessionTicket),
            HandshakeType::EndOfEarlyData => Ok(&EXEC_HandshakeType_EndOfEarlyData),
            HandshakeType::EncryptedExtensions => Ok(&EXEC_HandshakeType_EncryptedExtensions),
            HandshakeType::Certificate => Ok(&EXEC_HandshakeType_Certificate),
            HandshakeType::CertificateRequest => Ok(&EXEC_HandshakeType_CertificateRequest),
            HandshakeType::CertificateVerify => Ok(&EXEC_HandshakeType_CertificateVerify),
            HandshakeType::Finished => Ok(&EXEC_HandshakeType_Finished),
            HandshakeType::KeyUpdate => Ok(&EXEC_HandshakeType_KeyUpdate),
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

impl SpecPartialIso for HandshakeTypeMapper {
    type Src = HandshakeTypeInner;
    type Dst = HandshakeType;
}

impl SpecPartialIsoProof for HandshakeTypeMapper {
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

impl<'a> PartialIso<'a> for HandshakeTypeMapper {
    type Src = HandshakeTypeInner;
    type Dst = HandshakeType;
    type RefSrc = HandshakeTypeInnerRef<'a>;
}


pub struct SpecHandshakeTypeCombinator(SpecHandshakeTypeCombinatorAlias);

impl SpecCombinator for SpecHandshakeTypeCombinator {
    type Type = SpecHandshakeType;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHandshakeTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeTypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecHandshakeTypeCombinatorAlias = TryMap<U8, HandshakeTypeMapper>;

pub struct HandshakeTypeCombinator(HandshakeTypeCombinatorAlias);

impl View for HandshakeTypeCombinator {
    type V = SpecHandshakeTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeTypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HandshakeTypeCombinator {
    type Type = HandshakeType;
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

pub type HandshakeInnerRef<'a> = ((&'a HandshakeType, &'a u24), &'a HandshakeMsg<'a>);
impl<'a> From<&'a Handshake<'a>> for HandshakeInnerRef<'a> {
    fn ex_from(m: &'a Handshake) -> HandshakeInnerRef<'a> {
        ((&m.msg_type, &m.length), &m.msg)
    }
}

impl<'a> From<HandshakeInner<'a>> for Handshake<'a> {
    fn ex_from(m: HandshakeInner) -> Handshake {
        let ((msg_type, length), msg) = m;
        Handshake { msg_type, length, msg }
    }
}

pub struct HandshakeMapper;
impl View for HandshakeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMapper {
    type Src = SpecHandshakeInner;
    type Dst = SpecHandshake;
}
impl SpecIsoProof for HandshakeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for HandshakeMapper {
    type Src = HandshakeInner<'a>;
    type Dst = Handshake<'a>;
    type RefSrc = HandshakeInnerRef<'a>;
}

pub struct SpecHandshakeCombinator(SpecHandshakeCombinatorAlias);

impl SpecCombinator for SpecHandshakeCombinator {
    type Type = SpecHandshake;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecHandshakeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeCombinatorAlias::is_prefix_secure() }
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
pub type SpecHandshakeCombinatorAlias = Mapped<SpecPair<SpecPair<SpecHandshakeTypeCombinator, U24Be>, SpecHandshakeMsgCombinator>, HandshakeMapper>;

pub struct HandshakeCombinator(HandshakeCombinatorAlias);

impl View for HandshakeCombinator {
    type V = SpecHandshakeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for HandshakeCombinator {
    type Type = Handshake<'a>;
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
pub type HandshakeCombinatorAlias = Mapped<Pair<Pair<HandshakeTypeCombinator, U24Be, HandshakeCont1>, HandshakeMsgCombinator, HandshakeCont0>, HandshakeMapper>;


pub closed spec fn spec_handshake() -> SpecHandshakeCombinator {
    SpecHandshakeCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(spec_handshake_type(), |deps| spec_handshake_cont1(deps)), |deps| spec_handshake_cont0(deps)),
        mapper: HandshakeMapper,
    })
}

pub open spec fn spec_handshake_cont1(deps: SpecHandshakeType) -> U24Be {
    let msg_type = deps;
    U24Be
}

impl View for HandshakeCont1 {
    type V = spec_fn(SpecHandshakeType) -> U24Be;

    open spec fn view(&self) -> Self::V {
        |deps: SpecHandshakeType| {
            spec_handshake_cont1(deps)
        }
    }
}

pub open spec fn spec_handshake_cont0(deps: (SpecHandshakeType, u24)) -> SpecHandshakeMsgCombinator {
    let (msg_type, length) = deps;
    spec_handshake_msg(length, msg_type)
}

impl View for HandshakeCont0 {
    type V = spec_fn((SpecHandshakeType, u24)) -> SpecHandshakeMsgCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: (SpecHandshakeType, u24)| {
            spec_handshake_cont0(deps)
        }
    }
}

                
pub fn handshake() -> (o: HandshakeCombinator)
    ensures o@ == spec_handshake(),
{
    HandshakeCombinator(
    Mapped {
        inner: Pair::new(Pair::new(handshake_type(), HandshakeCont1), HandshakeCont0),
        mapper: HandshakeMapper,
    })
}

pub struct HandshakeCont1;
type HandshakeCont1Type<'a, 'b> = &'b HandshakeType;
type HandshakeCont1SType<'a, 'x> = &'x HandshakeType;
type HandshakeCont1Input<'a, 'b, 'x> = POrSType<HandshakeCont1Type<'a, 'b>, HandshakeCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HandshakeCont1Input<'a, 'b, 'x>> for HandshakeCont1 {
    type Output = U24Be;

    open spec fn requires(&self, deps: HandshakeCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: HandshakeCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_handshake_cont1(deps@)
    }

    fn apply(&self, deps: HandshakeCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let msg_type = *deps;
                U24Be
            }
            POrSType::S(deps) => {
                let msg_type = deps;
                let msg_type = *msg_type;
                U24Be
            }
        }
    }
}
pub struct HandshakeCont0;
type HandshakeCont0Type<'a, 'b> = &'b (HandshakeType, u24);
type HandshakeCont0SType<'a, 'x> = (&'x HandshakeType, &'x u24);
type HandshakeCont0Input<'a, 'b, 'x> = POrSType<HandshakeCont0Type<'a, 'b>, HandshakeCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<HandshakeCont0Input<'a, 'b, 'x>> for HandshakeCont0 {
    type Output = HandshakeMsgCombinator;

    open spec fn requires(&self, deps: HandshakeCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: HandshakeCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_handshake_cont0(deps@)
    }

    fn apply(&self, deps: HandshakeCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (msg_type, length) = *deps;
                handshake_msg(length, msg_type)
            }
            POrSType::S(deps) => {
                let (msg_type, length) = deps;
                let (msg_type, length) = (*msg_type, *length);
                handshake_msg(length, msg_type)
            }
        }
    }
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

pub type TlsPlaintextInnerRef<'a> = (&'a ContentType, (&'a ProtocolVersion, &'a Opaque0Ffff<'a>));
impl<'a> From<&'a TlsPlaintext<'a>> for TlsPlaintextInnerRef<'a> {
    fn ex_from(m: &'a TlsPlaintext) -> TlsPlaintextInnerRef<'a> {
        (&m.content_type, (&m.legacy_record_version, &m.fragment))
    }
}

impl<'a> From<TlsPlaintextInner<'a>> for TlsPlaintext<'a> {
    fn ex_from(m: TlsPlaintextInner) -> TlsPlaintext {
        let (content_type, (legacy_record_version, fragment)) = m;
        TlsPlaintext { content_type, legacy_record_version, fragment }
    }
}

pub struct TlsPlaintextMapper;
impl View for TlsPlaintextMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsPlaintextMapper {
    type Src = SpecTlsPlaintextInner;
    type Dst = SpecTlsPlaintext;
}
impl SpecIsoProof for TlsPlaintextMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TlsPlaintextMapper {
    type Src = TlsPlaintextInner<'a>;
    type Dst = TlsPlaintext<'a>;
    type RefSrc = TlsPlaintextInnerRef<'a>;
}
type SpecTlsPlaintextCombinatorAlias1 = (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator);
type SpecTlsPlaintextCombinatorAlias2 = (SpecContentTypeCombinator, SpecTlsPlaintextCombinatorAlias1);
pub struct SpecTlsPlaintextCombinator(SpecTlsPlaintextCombinatorAlias);

impl SpecCombinator for SpecTlsPlaintextCombinator {
    type Type = SpecTlsPlaintext;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTlsPlaintextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsPlaintextCombinatorAlias::is_prefix_secure() }
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
pub type SpecTlsPlaintextCombinatorAlias = Mapped<SpecTlsPlaintextCombinatorAlias2, TlsPlaintextMapper>;
type TlsPlaintextCombinatorAlias1 = (ProtocolVersionCombinator, Opaque0FfffCombinator);
type TlsPlaintextCombinatorAlias2 = (ContentTypeCombinator, TlsPlaintextCombinator1);
struct TlsPlaintextCombinator1(TlsPlaintextCombinatorAlias1);
impl View for TlsPlaintextCombinator1 {
    type V = SpecTlsPlaintextCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TlsPlaintextCombinator1, TlsPlaintextCombinatorAlias1);

struct TlsPlaintextCombinator2(TlsPlaintextCombinatorAlias2);
impl View for TlsPlaintextCombinator2 {
    type V = SpecTlsPlaintextCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TlsPlaintextCombinator2, TlsPlaintextCombinatorAlias2);

pub struct TlsPlaintextCombinator(TlsPlaintextCombinatorAlias);

impl View for TlsPlaintextCombinator {
    type V = SpecTlsPlaintextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsPlaintextCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TlsPlaintextCombinator {
    type Type = TlsPlaintext<'a>;
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
pub type TlsPlaintextCombinatorAlias = Mapped<TlsPlaintextCombinator2, TlsPlaintextMapper>;


pub closed spec fn spec_tls_plaintext() -> SpecTlsPlaintextCombinator {
    SpecTlsPlaintextCombinator(
    Mapped {
        inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())),
        mapper: TlsPlaintextMapper,
    })
}

                
pub fn tls_plaintext() -> (o: TlsPlaintextCombinator)
    ensures o@ == spec_tls_plaintext(),
{
    TlsPlaintextCombinator(
    Mapped {
        inner: TlsPlaintextCombinator2((content_type(), TlsPlaintextCombinator1((protocol_version(), opaque_0_ffff())))),
        mapper: TlsPlaintextMapper,
    })
}

                

pub struct SpecEcPointFormatList {
    pub l: u8,
    pub list: Seq<SpecEcPointFormat>,
}

pub type SpecEcPointFormatListInner = (u8, Seq<SpecEcPointFormat>);


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
    pub l: u8,
    pub list: RepeatResult<EcPointFormat>,
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
pub type EcPointFormatListInner = (u8, RepeatResult<EcPointFormat>);

pub type EcPointFormatListInnerRef<'a> = (&'a u8, &'a RepeatResult<EcPointFormat>);
impl<'a> From<&'a EcPointFormatList> for EcPointFormatListInnerRef<'a> {
    fn ex_from(m: &'a EcPointFormatList) -> EcPointFormatListInnerRef<'a> {
        (&m.l, &m.list)
    }
}

impl From<EcPointFormatListInner> for EcPointFormatList {
    fn ex_from(m: EcPointFormatListInner) -> EcPointFormatList {
        let (l, list) = m;
        EcPointFormatList { l, list }
    }
}

pub struct EcPointFormatListMapper;
impl View for EcPointFormatListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EcPointFormatListMapper {
    type Src = SpecEcPointFormatListInner;
    type Dst = SpecEcPointFormatList;
}
impl SpecIsoProof for EcPointFormatListMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EcPointFormatListMapper {
    type Src = EcPointFormatListInner;
    type Dst = EcPointFormatList;
    type RefSrc = EcPointFormatListInnerRef<'a>;
}

pub struct SpecEcPointFormatListCombinator(SpecEcPointFormatListCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatListCombinator {
    type Type = SpecEcPointFormatList;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEcPointFormatListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatListCombinatorAlias::is_prefix_secure() }
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
pub type SpecEcPointFormatListCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<SpecEcPointFormatCombinator>>>, EcPointFormatListMapper>;

pub struct EcPointFormatListCombinator(EcPointFormatListCombinatorAlias);

impl View for EcPointFormatListCombinator {
    type V = SpecEcPointFormatListCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatListCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EcPointFormatListCombinator {
    type Type = EcPointFormatList;
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
pub type EcPointFormatListCombinatorAlias = Mapped<Pair<Refined<U8, Predicate13984338198318635021>, AndThen<bytes::Variable, Repeat<EcPointFormatCombinator>>, EcPointFormatListCont0>, EcPointFormatListMapper>;


pub closed spec fn spec_ec_point_format_list() -> SpecEcPointFormatListCombinator {
    SpecEcPointFormatListCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, |deps| spec_ec_point_format_list_cont0(deps)),
        mapper: EcPointFormatListMapper,
    })
}

pub open spec fn spec_ec_point_format_list_cont0(deps: u8) -> AndThen<bytes::Variable, Repeat<SpecEcPointFormatCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_ec_point_format()))
}

impl View for EcPointFormatListCont0 {
    type V = spec_fn(u8) -> AndThen<bytes::Variable, Repeat<SpecEcPointFormatCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_ec_point_format_list_cont0(deps)
        }
    }
}

                
pub fn ec_point_format_list() -> (o: EcPointFormatListCombinator)
    ensures o@ == spec_ec_point_format_list(),
{
    EcPointFormatListCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate13984338198318635021 }, EcPointFormatListCont0),
        mapper: EcPointFormatListMapper,
    })
}

pub struct EcPointFormatListCont0;
type EcPointFormatListCont0Type<'a, 'b> = &'b u8;
type EcPointFormatListCont0SType<'a, 'x> = &'x u8;
type EcPointFormatListCont0Input<'a, 'b, 'x> = POrSType<EcPointFormatListCont0Type<'a, 'b>, EcPointFormatListCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<EcPointFormatListCont0Input<'a, 'b, 'x>> for EcPointFormatListCont0 {
    type Output = AndThen<bytes::Variable, Repeat<EcPointFormatCombinator>>;

    open spec fn requires(&self, deps: EcPointFormatListCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: EcPointFormatListCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_ec_point_format_list_cont0(deps@)
    }

    fn apply(&self, deps: EcPointFormatListCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(ec_point_format()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(ec_point_format()))
            }
        }
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

pub type ExtensionInnerRef<'a> = (&'a ExtensionType, &'a Opaque0Ffff<'a>);
impl<'a> From<&'a Extension<'a>> for ExtensionInnerRef<'a> {
    fn ex_from(m: &'a Extension) -> ExtensionInnerRef<'a> {
        (&m.extension_type, &m.extension_data)
    }
}

impl<'a> From<ExtensionInner<'a>> for Extension<'a> {
    fn ex_from(m: ExtensionInner) -> Extension {
        let (extension_type, extension_data) = m;
        Extension { extension_type, extension_data }
    }
}

pub struct ExtensionMapper;
impl View for ExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExtensionMapper {
    type Src = SpecExtensionInner;
    type Dst = SpecExtension;
}
impl SpecIsoProof for ExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExtensionMapper {
    type Src = ExtensionInner<'a>;
    type Dst = Extension<'a>;
    type RefSrc = ExtensionInnerRef<'a>;
}
type SpecExtensionCombinatorAlias1 = (SpecExtensionTypeCombinator, SpecOpaque0FfffCombinator);
pub struct SpecExtensionCombinator(SpecExtensionCombinatorAlias);

impl SpecCombinator for SpecExtensionCombinator {
    type Type = SpecExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecExtensionCombinatorAlias = Mapped<SpecExtensionCombinatorAlias1, ExtensionMapper>;
type ExtensionCombinatorAlias1 = (ExtensionTypeCombinator, Opaque0FfffCombinator);
struct ExtensionCombinator1(ExtensionCombinatorAlias1);
impl View for ExtensionCombinator1 {
    type V = SpecExtensionCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ExtensionCombinator1, ExtensionCombinatorAlias1);

pub struct ExtensionCombinator(ExtensionCombinatorAlias);

impl View for ExtensionCombinator {
    type V = SpecExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExtensionCombinator {
    type Type = Extension<'a>;
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
pub type ExtensionCombinatorAlias = Mapped<ExtensionCombinator1, ExtensionMapper>;


pub closed spec fn spec_extension() -> SpecExtensionCombinator {
    SpecExtensionCombinator(
    Mapped {
        inner: (spec_extension_type(), spec_opaque_0_ffff()),
        mapper: ExtensionMapper,
    })
}

                
pub fn extension() -> (o: ExtensionCombinator)
    ensures o@ == spec_extension(),
{
    ExtensionCombinator(
    Mapped {
        inner: ExtensionCombinator1((extension_type(), opaque_0_ffff())),
        mapper: ExtensionMapper,
    })
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

pub type ZeroByteInnerRef<'a> = &'a u8;
impl<'a> From<&'a ZeroByte> for ZeroByteInnerRef<'a> {
    fn ex_from(m: &'a ZeroByte) -> ZeroByteInnerRef<'a> {
        &m.zero
    }
}

impl From<ZeroByteInner> for ZeroByte {
    fn ex_from(m: ZeroByteInner) -> ZeroByte {
        let zero = m;
        ZeroByte { zero }
    }
}

pub struct ZeroByteMapper;
impl View for ZeroByteMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ZeroByteMapper {
    type Src = SpecZeroByteInner;
    type Dst = SpecZeroByte;
}
impl SpecIsoProof for ZeroByteMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ZeroByteMapper {
    type Src = ZeroByteInner;
    type Dst = ZeroByte;
    type RefSrc = ZeroByteInnerRef<'a>;
}
pub const ZEROBYTEZERO_CONST: u8 = 0;

pub struct SpecZeroByteCombinator(SpecZeroByteCombinatorAlias);

impl SpecCombinator for SpecZeroByteCombinator {
    type Type = SpecZeroByte;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecZeroByteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecZeroByteCombinatorAlias::is_prefix_secure() }
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
pub type SpecZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;

pub struct ZeroByteCombinator(ZeroByteCombinatorAlias);

impl View for ZeroByteCombinator {
    type V = SpecZeroByteCombinator;
    closed spec fn view(&self) -> Self::V { SpecZeroByteCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ZeroByteCombinator {
    type Type = ZeroByte;
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
pub type ZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;


pub closed spec fn spec_zero_byte() -> SpecZeroByteCombinator {
    SpecZeroByteCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(ZEROBYTEZERO_CONST) },
        mapper: ZeroByteMapper,
    })
}

                
pub fn zero_byte() -> (o: ZeroByteCombinator)
    ensures o@ == spec_zero_byte(),
{
    ZeroByteCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(ZEROBYTEZERO_CONST) },
        mapper: ZeroByteMapper,
    })
}

                

pub struct SpecPaddingExtension {
    pub l: u16,
    pub padding: Seq<SpecZeroByte>,
}

pub type SpecPaddingExtensionInner = (u16, Seq<SpecZeroByte>);


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
    pub l: u16,
    pub padding: RepeatResult<ZeroByte>,
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
pub type PaddingExtensionInner = (u16, RepeatResult<ZeroByte>);

pub type PaddingExtensionInnerRef<'a> = (&'a u16, &'a RepeatResult<ZeroByte>);
impl<'a> From<&'a PaddingExtension> for PaddingExtensionInnerRef<'a> {
    fn ex_from(m: &'a PaddingExtension) -> PaddingExtensionInnerRef<'a> {
        (&m.l, &m.padding)
    }
}

impl From<PaddingExtensionInner> for PaddingExtension {
    fn ex_from(m: PaddingExtensionInner) -> PaddingExtension {
        let (l, padding) = m;
        PaddingExtension { l, padding }
    }
}

pub struct PaddingExtensionMapper;
impl View for PaddingExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PaddingExtensionMapper {
    type Src = SpecPaddingExtensionInner;
    type Dst = SpecPaddingExtension;
}
impl SpecIsoProof for PaddingExtensionMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PaddingExtensionMapper {
    type Src = PaddingExtensionInner;
    type Dst = PaddingExtension;
    type RefSrc = PaddingExtensionInnerRef<'a>;
}

pub struct SpecPaddingExtensionCombinator(SpecPaddingExtensionCombinatorAlias);

impl SpecCombinator for SpecPaddingExtensionCombinator {
    type Type = SpecPaddingExtension;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPaddingExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPaddingExtensionCombinatorAlias::is_prefix_secure() }
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
pub type SpecPaddingExtensionCombinatorAlias = Mapped<SpecPair<U16Be, AndThen<bytes::Variable, Repeat<SpecZeroByteCombinator>>>, PaddingExtensionMapper>;

pub struct PaddingExtensionCombinator(PaddingExtensionCombinatorAlias);

impl View for PaddingExtensionCombinator {
    type V = SpecPaddingExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPaddingExtensionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PaddingExtensionCombinator {
    type Type = PaddingExtension;
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
pub type PaddingExtensionCombinatorAlias = Mapped<Pair<U16Be, AndThen<bytes::Variable, Repeat<ZeroByteCombinator>>, PaddingExtensionCont0>, PaddingExtensionMapper>;


pub closed spec fn spec_padding_extension(ext_len: u16) -> SpecPaddingExtensionCombinator {
    SpecPaddingExtensionCombinator(
    Mapped {
        inner: Pair::spec_new(U16Be, |deps| spec_padding_extension_cont0(deps)),
        mapper: PaddingExtensionMapper,
    })
}

pub open spec fn spec_padding_extension_cont0(deps: u16) -> AndThen<bytes::Variable, Repeat<SpecZeroByteCombinator>> {
    let l = deps;
    AndThen(bytes::Variable(l.spec_into()), Repeat(spec_zero_byte()))
}

impl View for PaddingExtensionCont0 {
    type V = spec_fn(u16) -> AndThen<bytes::Variable, Repeat<SpecZeroByteCombinator>>;

    open spec fn view(&self) -> Self::V {
        |deps: u16| {
            spec_padding_extension_cont0(deps)
        }
    }
}

pub fn padding_extension<'a>(ext_len: u16) -> (o: PaddingExtensionCombinator)
    ensures o@ == spec_padding_extension(ext_len@),
{
    PaddingExtensionCombinator(
    Mapped {
        inner: Pair::new(U16Be, PaddingExtensionCont0),
        mapper: PaddingExtensionMapper,
    })
}

pub struct PaddingExtensionCont0;
type PaddingExtensionCont0Type<'a, 'b> = &'b u16;
type PaddingExtensionCont0SType<'a, 'x> = &'x u16;
type PaddingExtensionCont0Input<'a, 'b, 'x> = POrSType<PaddingExtensionCont0Type<'a, 'b>, PaddingExtensionCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<PaddingExtensionCont0Input<'a, 'b, 'x>> for PaddingExtensionCont0 {
    type Output = AndThen<bytes::Variable, Repeat<ZeroByteCombinator>>;

    open spec fn requires(&self, deps: PaddingExtensionCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: PaddingExtensionCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_padding_extension_cont0(deps@)
    }

    fn apply(&self, deps: PaddingExtensionCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(zero_byte()))
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                AndThen(bytes::Variable(l.ex_into()), Repeat::new(zero_byte()))
            }
        }
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

pub type TlsCiphertextInnerRef<'a> = (&'a ContentType, (&'a ProtocolVersion, &'a Opaque0Ffff<'a>));
impl<'a> From<&'a TlsCiphertext<'a>> for TlsCiphertextInnerRef<'a> {
    fn ex_from(m: &'a TlsCiphertext) -> TlsCiphertextInnerRef<'a> {
        (&m.opaque_type, (&m.version, &m.encrypted_record))
    }
}

impl<'a> From<TlsCiphertextInner<'a>> for TlsCiphertext<'a> {
    fn ex_from(m: TlsCiphertextInner) -> TlsCiphertext {
        let (opaque_type, (version, encrypted_record)) = m;
        TlsCiphertext { opaque_type, version, encrypted_record }
    }
}

pub struct TlsCiphertextMapper;
impl View for TlsCiphertextMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsCiphertextMapper {
    type Src = SpecTlsCiphertextInner;
    type Dst = SpecTlsCiphertext;
}
impl SpecIsoProof for TlsCiphertextMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TlsCiphertextMapper {
    type Src = TlsCiphertextInner<'a>;
    type Dst = TlsCiphertext<'a>;
    type RefSrc = TlsCiphertextInnerRef<'a>;
}
type SpecTlsCiphertextCombinatorAlias1 = (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator);
type SpecTlsCiphertextCombinatorAlias2 = (SpecContentTypeCombinator, SpecTlsCiphertextCombinatorAlias1);
pub struct SpecTlsCiphertextCombinator(SpecTlsCiphertextCombinatorAlias);

impl SpecCombinator for SpecTlsCiphertextCombinator {
    type Type = SpecTlsCiphertext;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTlsCiphertextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsCiphertextCombinatorAlias::is_prefix_secure() }
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
pub type SpecTlsCiphertextCombinatorAlias = Mapped<SpecTlsCiphertextCombinatorAlias2, TlsCiphertextMapper>;
type TlsCiphertextCombinatorAlias1 = (ProtocolVersionCombinator, Opaque0FfffCombinator);
type TlsCiphertextCombinatorAlias2 = (ContentTypeCombinator, TlsCiphertextCombinator1);
struct TlsCiphertextCombinator1(TlsCiphertextCombinatorAlias1);
impl View for TlsCiphertextCombinator1 {
    type V = SpecTlsCiphertextCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TlsCiphertextCombinator1, TlsCiphertextCombinatorAlias1);

struct TlsCiphertextCombinator2(TlsCiphertextCombinatorAlias2);
impl View for TlsCiphertextCombinator2 {
    type V = SpecTlsCiphertextCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TlsCiphertextCombinator2, TlsCiphertextCombinatorAlias2);

pub struct TlsCiphertextCombinator(TlsCiphertextCombinatorAlias);

impl View for TlsCiphertextCombinator {
    type V = SpecTlsCiphertextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsCiphertextCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TlsCiphertextCombinator {
    type Type = TlsCiphertext<'a>;
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
pub type TlsCiphertextCombinatorAlias = Mapped<TlsCiphertextCombinator2, TlsCiphertextMapper>;


pub closed spec fn spec_tls_ciphertext() -> SpecTlsCiphertextCombinator {
    SpecTlsCiphertextCombinator(
    Mapped {
        inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())),
        mapper: TlsCiphertextMapper,
    })
}

                
pub fn tls_ciphertext() -> (o: TlsCiphertextCombinator)
    ensures o@ == spec_tls_ciphertext(),
{
    TlsCiphertextCombinator(
    Mapped {
        inner: TlsCiphertextCombinator2((content_type(), TlsCiphertextCombinator1((protocol_version(), opaque_0_ffff())))),
        mapper: TlsCiphertextMapper,
    })
}

                
pub type SpecFinishedOpaque = Seq<u8>;
pub type FinishedOpaque<'a> = &'a [u8];
pub type FinishedOpaqueRef<'a> = &'a &'a [u8];


pub struct SpecFinishedOpaqueCombinator(SpecFinishedOpaqueCombinatorAlias);

impl SpecCombinator for SpecFinishedOpaqueCombinator {
    type Type = SpecFinishedOpaque;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFinishedOpaqueCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFinishedOpaqueCombinatorAlias::is_prefix_secure() }
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
pub type SpecFinishedOpaqueCombinatorAlias = bytes::Variable;

pub struct FinishedOpaqueCombinator(FinishedOpaqueCombinatorAlias);

impl View for FinishedOpaqueCombinator {
    type V = SpecFinishedOpaqueCombinator;
    closed spec fn view(&self) -> Self::V { SpecFinishedOpaqueCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FinishedOpaqueCombinator {
    type Type = FinishedOpaque<'a>;
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
pub type FinishedOpaqueCombinatorAlias = bytes::Variable;


pub closed spec fn spec_finished_opaque(digest_size: u24) -> SpecFinishedOpaqueCombinator {
    SpecFinishedOpaqueCombinator(bytes::Variable(digest_size.spec_into()))
}

pub fn finished_opaque<'a>(digest_size: u24) -> (o: FinishedOpaqueCombinator)
    ensures o@ == spec_finished_opaque(digest_size@),
{
    FinishedOpaqueCombinator(bytes::Variable(digest_size.ex_into()))
}


}
