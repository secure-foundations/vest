
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
        } // verus!
    };
}
verus!{

pub enum SpecCaptureParamAndLocalXAPayload {
    C(Seq<u8>),
    D(Seq<u8>),
}

pub type SpecCaptureParamAndLocalXAPayloadInner = Either<Seq<u8>, Seq<u8>>;

impl SpecFrom<SpecCaptureParamAndLocalXAPayload> for SpecCaptureParamAndLocalXAPayloadInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXAPayload) -> SpecCaptureParamAndLocalXAPayloadInner {
        match m {
            SpecCaptureParamAndLocalXAPayload::C(m) => Either::Left(m),
            SpecCaptureParamAndLocalXAPayload::D(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalXAPayloadInner> for SpecCaptureParamAndLocalXAPayload {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXAPayloadInner) -> SpecCaptureParamAndLocalXAPayload {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalXAPayload::C(m),
            Either::Right(m) => SpecCaptureParamAndLocalXAPayload::D(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalXAPayload<'a> {
    C(&'a [u8]),
    D(&'a [u8]),
}

pub type CaptureParamAndLocalXAPayloadInner<'a> = Either<&'a [u8], &'a [u8]>;

pub type CaptureParamAndLocalXAPayloadInnerRef<'a> = Either<&'a &'a [u8], &'a &'a [u8]>;


impl<'a> View for CaptureParamAndLocalXAPayload<'a> {
    type V = SpecCaptureParamAndLocalXAPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalXAPayload::C(m) => SpecCaptureParamAndLocalXAPayload::C(m@),
            CaptureParamAndLocalXAPayload::D(m) => SpecCaptureParamAndLocalXAPayload::D(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalXAPayload<'a>> for CaptureParamAndLocalXAPayloadInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalXAPayload<'a>) -> CaptureParamAndLocalXAPayloadInnerRef<'a> {
        match m {
            CaptureParamAndLocalXAPayload::C(m) => Either::Left(m),
            CaptureParamAndLocalXAPayload::D(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureParamAndLocalXAPayloadInner<'a>> for CaptureParamAndLocalXAPayload<'a> {
    fn ex_from(m: CaptureParamAndLocalXAPayloadInner<'a>) -> CaptureParamAndLocalXAPayload<'a> {
        match m {
            Either::Left(m) => CaptureParamAndLocalXAPayload::C(m),
            Either::Right(m) => CaptureParamAndLocalXAPayload::D(m),
        }
    }
    
}


pub struct CaptureParamAndLocalXAPayloadMapper;
impl View for CaptureParamAndLocalXAPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalXAPayloadMapper {
    type Src = SpecCaptureParamAndLocalXAPayloadInner;
    type Dst = SpecCaptureParamAndLocalXAPayload;
}
impl SpecIsoProof for CaptureParamAndLocalXAPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalXAPayloadMapper {
    type Src = CaptureParamAndLocalXAPayloadInner<'a>;
    type Dst = CaptureParamAndLocalXAPayload<'a>;
    type RefSrc = CaptureParamAndLocalXAPayloadInnerRef<'a>;
}

type SpecCaptureParamAndLocalXAPayloadCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<bytes::Variable>>;
pub struct SpecCaptureParamAndLocalXAPayloadCombinator(pub SpecCaptureParamAndLocalXAPayloadCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalXAPayloadCombinator {
    type Type = SpecCaptureParamAndLocalXAPayload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalXAPayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalXAPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalXAPayloadCombinatorAlias = Mapped<SpecCaptureParamAndLocalXAPayloadCombinatorAlias1, CaptureParamAndLocalXAPayloadMapper>;
type CaptureParamAndLocalXAPayloadCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<bytes::Variable>>;
pub struct CaptureParamAndLocalXAPayloadCombinator1(pub CaptureParamAndLocalXAPayloadCombinatorAlias1);
impl View for CaptureParamAndLocalXAPayloadCombinator1 {
    type V = SpecCaptureParamAndLocalXAPayloadCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalXAPayloadCombinator1, CaptureParamAndLocalXAPayloadCombinatorAlias1);

pub struct CaptureParamAndLocalXAPayloadCombinator(pub CaptureParamAndLocalXAPayloadCombinatorAlias);

impl View for CaptureParamAndLocalXAPayloadCombinator {
    type V = SpecCaptureParamAndLocalXAPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalXAPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalXAPayloadCombinator {
    type Type = CaptureParamAndLocalXAPayload<'a>;
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
pub type CaptureParamAndLocalXAPayloadCombinatorAlias = Mapped<CaptureParamAndLocalXAPayloadCombinator1, CaptureParamAndLocalXAPayloadMapper>;


pub open spec fn spec_capture_param_and_local_x_a_payload(choice2: SpecCOrD, len: u8) -> SpecCaptureParamAndLocalXAPayloadCombinator {
    SpecCaptureParamAndLocalXAPayloadCombinator(Mapped { inner: Choice(Cond { cond: choice2 == COrD::C, inner: bytes::Variable((usize::spec_from(len)) as usize) }, Cond { cond: choice2 == COrD::D, inner: bytes::Variable((usize::spec_from(len)) as usize) }), mapper: CaptureParamAndLocalXAPayloadMapper })
}

pub fn capture_param_and_local_x_a_payload<'a>(choice2: COrD, len: u8) -> (o: CaptureParamAndLocalXAPayloadCombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_x_a_payload(choice2@, len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalXAPayloadCombinator(Mapped { inner: CaptureParamAndLocalXAPayloadCombinator1(Choice::new(Cond { cond: choice2 == COrD::C, inner: bytes::Variable((usize::ex_from(len)) as usize) }, Cond { cond: choice2 == COrD::D, inner: bytes::Variable((usize::ex_from(len)) as usize) })), mapper: CaptureParamAndLocalXAPayloadMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_x_a_payload(choice2@, len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_x_a_payload<'a>(input: &'a [u8], choice2: COrD, len: u8) -> (res: PResult<<CaptureParamAndLocalXAPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_parse(input@) is None,
        spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_x_a_payload( choice2, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_x_a_payload<'a>(v: <CaptureParamAndLocalXAPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD, len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_a_payload(choice2@, len@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_x_a_payload( choice2, len );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_param_and_local_x_a_payload_infallible<'a>(v: <CaptureParamAndLocalXAPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD, len: u8) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_a_payload(choice2@, len@).wf(v@),
        spec_c_or_d().wf(choice2@),
        spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@)),
{
    let combinator = capture_param_and_local_x_a_payload( choice2, len );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_x_a_payload_len<'a>(v: <CaptureParamAndLocalXAPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD, len: u8) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_x_a_payload(choice2@, len@).wf(v@),
        spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_x_a_payload(choice2@, len@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_x_a_payload( choice2, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureParamAndLocalXA {
    pub len: u8,
    pub payload: SpecCaptureParamAndLocalXAPayload,
}

pub type SpecCaptureParamAndLocalXAInner = (u8, SpecCaptureParamAndLocalXAPayload);


impl SpecFrom<SpecCaptureParamAndLocalXA> for SpecCaptureParamAndLocalXAInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXA) -> SpecCaptureParamAndLocalXAInner {
        (m.len, m.payload)
    }
}

impl SpecFrom<SpecCaptureParamAndLocalXAInner> for SpecCaptureParamAndLocalXA {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXAInner) -> SpecCaptureParamAndLocalXA {
        let (len, payload) = m;
        SpecCaptureParamAndLocalXA { len, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureParamAndLocalXA<'a> {
    pub len: u8,
    pub payload: CaptureParamAndLocalXAPayload<'a>,
}

impl View for CaptureParamAndLocalXA<'_> {
    type V = SpecCaptureParamAndLocalXA;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocalXA {
            len: self.len@,
            payload: self.payload@,
        }
    }
}
pub type CaptureParamAndLocalXAInner<'a> = (u8, CaptureParamAndLocalXAPayload<'a>);

pub type CaptureParamAndLocalXAInnerRef<'a> = (&'a u8, &'a CaptureParamAndLocalXAPayload<'a>);
impl<'a> From<&'a CaptureParamAndLocalXA<'a>> for CaptureParamAndLocalXAInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalXA) -> CaptureParamAndLocalXAInnerRef<'a> {
        (&m.len, &m.payload)
    }
}

impl<'a> From<CaptureParamAndLocalXAInner<'a>> for CaptureParamAndLocalXA<'a> {
    fn ex_from(m: CaptureParamAndLocalXAInner) -> CaptureParamAndLocalXA {
        let (len, payload) = m;
        CaptureParamAndLocalXA { len, payload }
    }
}

pub struct CaptureParamAndLocalXAMapper;
impl View for CaptureParamAndLocalXAMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalXAMapper {
    type Src = SpecCaptureParamAndLocalXAInner;
    type Dst = SpecCaptureParamAndLocalXA;
}
impl SpecIsoProof for CaptureParamAndLocalXAMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalXAMapper {
    type Src = CaptureParamAndLocalXAInner<'a>;
    type Dst = CaptureParamAndLocalXA<'a>;
    type RefSrc = CaptureParamAndLocalXAInnerRef<'a>;
}

pub struct SpecCaptureParamAndLocalXACombinator(pub SpecCaptureParamAndLocalXACombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalXACombinator {
    type Type = SpecCaptureParamAndLocalXA;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalXACombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalXACombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalXACombinatorAlias = Mapped<SpecPair<U8, SpecCaptureParamAndLocalXAPayloadCombinator>, CaptureParamAndLocalXAMapper>;

pub struct CaptureParamAndLocalXACombinator(pub CaptureParamAndLocalXACombinatorAlias);

impl View for CaptureParamAndLocalXACombinator {
    type V = SpecCaptureParamAndLocalXACombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalXACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalXACombinator {
    type Type = CaptureParamAndLocalXA<'a>;
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
pub type CaptureParamAndLocalXACombinatorAlias = Mapped<Pair<U8, CaptureParamAndLocalXAPayloadCombinator, CaptureParamAndLocalXACont0>, CaptureParamAndLocalXAMapper>;


pub open spec fn spec_capture_param_and_local_x_a(choice2: SpecCOrD) -> SpecCaptureParamAndLocalXACombinator {
    SpecCaptureParamAndLocalXACombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_param_and_local_x_a_cont0(choice2, deps)),
        mapper: CaptureParamAndLocalXAMapper,
    })
}

pub open spec fn spec_capture_param_and_local_x_a_cont0(choice2: SpecCOrD, deps: u8) -> SpecCaptureParamAndLocalXAPayloadCombinator {
    let len = deps;
    spec_capture_param_and_local_x_a_payload(choice2, len)
}

impl View for CaptureParamAndLocalXACont0 {
    type V = spec_fn(u8) -> SpecCaptureParamAndLocalXAPayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_param_and_local_x_a_cont0(self.choice2@, deps)
        }
    }
}

pub fn capture_param_and_local_x_a<'a>(choice2: COrD) -> (o: CaptureParamAndLocalXACombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_x_a(choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalXACombinator(
    Mapped {
        inner: Pair::new(U8, CaptureParamAndLocalXACont0 { choice2 }),
        mapper: CaptureParamAndLocalXAMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_x_a(choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_x_a<'a>(input: &'a [u8], choice2: COrD) -> (res: PResult<<CaptureParamAndLocalXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_x_a(choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_x_a(choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_x_a(choice2@).spec_parse(input@) is None,
        spec_capture_param_and_local_x_a(choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_x_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_x_a<'a>(v: <CaptureParamAndLocalXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_x_a( choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_param_and_local_x_a_infallible<'a>(v: <CaptureParamAndLocalXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),
        spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@)),
{
    let combinator = capture_param_and_local_x_a( choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_x_a_len<'a>(v: <CaptureParamAndLocalXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_x_a(choice2@).wf(v@),
        spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_x_a(choice2@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_x_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureParamAndLocalXACont0 {
    pub choice2: COrD,
}
type CaptureParamAndLocalXACont0Type<'a, 'b> = &'b u8;
type CaptureParamAndLocalXACont0SType<'a, 'x> = &'x u8;
type CaptureParamAndLocalXACont0Input<'a, 'b, 'x> = POrSType<CaptureParamAndLocalXACont0Type<'a, 'b>, CaptureParamAndLocalXACont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureParamAndLocalXACont0Input<'a, 'b, 'x>> for CaptureParamAndLocalXACont0 {
    type Output = CaptureParamAndLocalXAPayloadCombinator;

    open spec fn requires(&self, deps: CaptureParamAndLocalXACont0Input<'a, 'b, 'x>) -> bool {        let choice2 = self.choice2@;

        &&& spec_c_or_d().wf(self.choice2@)
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureParamAndLocalXACont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_param_and_local_x_a_cont0(self.choice2@, deps@)
    }

    fn apply(&self, deps: CaptureParamAndLocalXACont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = deps;
                let choice2 = self.choice2;
                let len = *len;
                capture_param_and_local_x_a_payload(choice2, len)
            }
            POrSType::S(deps) => {
                let len = deps;
                let choice2 = self.choice2;
                let len = *len;
                capture_param_and_local_x_a_payload(choice2, len)
            }
        }
    }
}

pub enum SpecCaptureParamAndLocalXBY {
    Variant0(u8),
    Variant1(u16),
}

pub type SpecCaptureParamAndLocalXBYInner = Either<u8, u16>;

impl SpecFrom<SpecCaptureParamAndLocalXBY> for SpecCaptureParamAndLocalXBYInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXBY) -> SpecCaptureParamAndLocalXBYInner {
        match m {
            SpecCaptureParamAndLocalXBY::Variant0(m) => Either::Left(m),
            SpecCaptureParamAndLocalXBY::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalXBYInner> for SpecCaptureParamAndLocalXBY {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXBYInner) -> SpecCaptureParamAndLocalXBY {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalXBY::Variant0(m),
            Either::Right(m) => SpecCaptureParamAndLocalXBY::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalXBY {
    Variant0(u8),
    Variant1(u16),
}

pub type CaptureParamAndLocalXBYInner = Either<u8, u16>;

pub type CaptureParamAndLocalXBYInnerRef<'a> = Either<&'a u8, &'a u16>;


impl View for CaptureParamAndLocalXBY {
    type V = SpecCaptureParamAndLocalXBY;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalXBY::Variant0(m) => SpecCaptureParamAndLocalXBY::Variant0(m@),
            CaptureParamAndLocalXBY::Variant1(m) => SpecCaptureParamAndLocalXBY::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalXBY> for CaptureParamAndLocalXBYInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalXBY) -> CaptureParamAndLocalXBYInnerRef<'a> {
        match m {
            CaptureParamAndLocalXBY::Variant0(m) => Either::Left(m),
            CaptureParamAndLocalXBY::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<CaptureParamAndLocalXBYInner> for CaptureParamAndLocalXBY {
    fn ex_from(m: CaptureParamAndLocalXBYInner) -> CaptureParamAndLocalXBY {
        match m {
            Either::Left(m) => CaptureParamAndLocalXBY::Variant0(m),
            Either::Right(m) => CaptureParamAndLocalXBY::Variant1(m),
        }
    }
    
}


pub struct CaptureParamAndLocalXBYMapper;
impl View for CaptureParamAndLocalXBYMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalXBYMapper {
    type Src = SpecCaptureParamAndLocalXBYInner;
    type Dst = SpecCaptureParamAndLocalXBY;
}
impl SpecIsoProof for CaptureParamAndLocalXBYMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalXBYMapper {
    type Src = CaptureParamAndLocalXBYInner;
    type Dst = CaptureParamAndLocalXBY;
    type RefSrc = CaptureParamAndLocalXBYInnerRef<'a>;
}

type SpecCaptureParamAndLocalXBYCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct SpecCaptureParamAndLocalXBYCombinator(pub SpecCaptureParamAndLocalXBYCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalXBYCombinator {
    type Type = SpecCaptureParamAndLocalXBY;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalXBYCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalXBYCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalXBYCombinatorAlias = Mapped<SpecCaptureParamAndLocalXBYCombinatorAlias1, CaptureParamAndLocalXBYMapper>;
type CaptureParamAndLocalXBYCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct CaptureParamAndLocalXBYCombinator1(pub CaptureParamAndLocalXBYCombinatorAlias1);
impl View for CaptureParamAndLocalXBYCombinator1 {
    type V = SpecCaptureParamAndLocalXBYCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalXBYCombinator1, CaptureParamAndLocalXBYCombinatorAlias1);

pub struct CaptureParamAndLocalXBYCombinator(pub CaptureParamAndLocalXBYCombinatorAlias);

impl View for CaptureParamAndLocalXBYCombinator {
    type V = SpecCaptureParamAndLocalXBYCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalXBYCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalXBYCombinator {
    type Type = CaptureParamAndLocalXBY;
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
pub type CaptureParamAndLocalXBYCombinatorAlias = Mapped<CaptureParamAndLocalXBYCombinator1, CaptureParamAndLocalXBYMapper>;


pub open spec fn spec_capture_param_and_local_x_b_y(tag: u8) -> SpecCaptureParamAndLocalXBYCombinator {
    SpecCaptureParamAndLocalXBYCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: U8 }, Cond { cond: !(tag == 0), inner: U16Le }), mapper: CaptureParamAndLocalXBYMapper })
}

pub fn capture_param_and_local_x_b_y<'a>(tag: u8) -> (o: CaptureParamAndLocalXBYCombinator)

    ensures o@ == spec_capture_param_and_local_x_b_y(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalXBYCombinator(Mapped { inner: CaptureParamAndLocalXBYCombinator1(Choice::new(Cond { cond: tag == 0, inner: U8 }, Cond { cond: !(tag == 0), inner: U16Le })), mapper: CaptureParamAndLocalXBYMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_x_b_y(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_x_b_y<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<CaptureParamAndLocalXBYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_x_b_y(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_x_b_y(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_x_b_y(tag@).spec_parse(input@) is None,
        spec_capture_param_and_local_x_b_y(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_x_b_y( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_x_b_y<'a>(v: <CaptureParamAndLocalXBYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_b_y(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_x_b_y( tag );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_param_and_local_x_b_y_infallible<'a>(v: <CaptureParamAndLocalXBYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_b_y(tag@).wf(v@),
        spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@)),
{
    let combinator = capture_param_and_local_x_b_y( tag );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_x_b_y_len<'a>(v: <CaptureParamAndLocalXBYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_x_b_y(tag@).wf(v@),
        spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_capture_param_and_local_x_b_y(tag@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_x_b_y( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureParamAndLocalXB {
    pub tag: u8,
    pub y: SpecCaptureParamAndLocalXBY,
}

pub type SpecCaptureParamAndLocalXBInner = (u8, SpecCaptureParamAndLocalXBY);


impl SpecFrom<SpecCaptureParamAndLocalXB> for SpecCaptureParamAndLocalXBInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXB) -> SpecCaptureParamAndLocalXBInner {
        (m.tag, m.y)
    }
}

impl SpecFrom<SpecCaptureParamAndLocalXBInner> for SpecCaptureParamAndLocalXB {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXBInner) -> SpecCaptureParamAndLocalXB {
        let (tag, y) = m;
        SpecCaptureParamAndLocalXB { tag, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureParamAndLocalXB {
    pub tag: u8,
    pub y: CaptureParamAndLocalXBY,
}

impl View for CaptureParamAndLocalXB {
    type V = SpecCaptureParamAndLocalXB;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocalXB {
            tag: self.tag@,
            y: self.y@,
        }
    }
}
pub type CaptureParamAndLocalXBInner = (u8, CaptureParamAndLocalXBY);

pub type CaptureParamAndLocalXBInnerRef<'a> = (&'a u8, &'a CaptureParamAndLocalXBY);
impl<'a> From<&'a CaptureParamAndLocalXB> for CaptureParamAndLocalXBInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalXB) -> CaptureParamAndLocalXBInnerRef<'a> {
        (&m.tag, &m.y)
    }
}

impl From<CaptureParamAndLocalXBInner> for CaptureParamAndLocalXB {
    fn ex_from(m: CaptureParamAndLocalXBInner) -> CaptureParamAndLocalXB {
        let (tag, y) = m;
        CaptureParamAndLocalXB { tag, y }
    }
}

pub struct CaptureParamAndLocalXBMapper;
impl View for CaptureParamAndLocalXBMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalXBMapper {
    type Src = SpecCaptureParamAndLocalXBInner;
    type Dst = SpecCaptureParamAndLocalXB;
}
impl SpecIsoProof for CaptureParamAndLocalXBMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalXBMapper {
    type Src = CaptureParamAndLocalXBInner;
    type Dst = CaptureParamAndLocalXB;
    type RefSrc = CaptureParamAndLocalXBInnerRef<'a>;
}

pub struct SpecCaptureParamAndLocalXBCombinator(pub SpecCaptureParamAndLocalXBCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalXBCombinator {
    type Type = SpecCaptureParamAndLocalXB;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalXBCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalXBCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalXBCombinatorAlias = Mapped<SpecPair<U8, SpecCaptureParamAndLocalXBYCombinator>, CaptureParamAndLocalXBMapper>;

pub struct CaptureParamAndLocalXBCombinator(pub CaptureParamAndLocalXBCombinatorAlias);

impl View for CaptureParamAndLocalXBCombinator {
    type V = SpecCaptureParamAndLocalXBCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalXBCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalXBCombinator {
    type Type = CaptureParamAndLocalXB;
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
pub type CaptureParamAndLocalXBCombinatorAlias = Mapped<Pair<U8, CaptureParamAndLocalXBYCombinator, CaptureParamAndLocalXBCont0>, CaptureParamAndLocalXBMapper>;


pub open spec fn spec_capture_param_and_local_x_b() -> SpecCaptureParamAndLocalXBCombinator {
    SpecCaptureParamAndLocalXBCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_param_and_local_x_b_cont0(deps)),
        mapper: CaptureParamAndLocalXBMapper,
    })
}

pub open spec fn spec_capture_param_and_local_x_b_cont0(deps: u8) -> SpecCaptureParamAndLocalXBYCombinator {
    let tag = deps;
    spec_capture_param_and_local_x_b_y(tag)
}

impl View for CaptureParamAndLocalXBCont0 {
    type V = spec_fn(u8) -> SpecCaptureParamAndLocalXBYCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_param_and_local_x_b_cont0(deps)
        }
    }
}

                
pub fn capture_param_and_local_x_b<'a>() -> (o: CaptureParamAndLocalXBCombinator)
    ensures o@ == spec_capture_param_and_local_x_b(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalXBCombinator(
    Mapped {
        inner: Pair::new(U8, CaptureParamAndLocalXBCont0),
        mapper: CaptureParamAndLocalXBMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_x_b()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_x_b<'a>(input: &'a [u8]) -> (res: PResult<<CaptureParamAndLocalXBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_x_b().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_x_b().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_x_b().spec_parse(input@) is None,
        spec_capture_param_and_local_x_b().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_x_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_x_b<'a>(v: <CaptureParamAndLocalXBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_b().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_x_b().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_b().spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_x_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_param_and_local_x_b_infallible<'a>(v: <CaptureParamAndLocalXBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x_b().wf(v@),
        spec_capture_param_and_local_x_b().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local_x_b().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local_x_b().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x_b().spec_serialize(v@)),
{
    let combinator = capture_param_and_local_x_b();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_x_b_len<'a>(v: <CaptureParamAndLocalXBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_x_b().wf(v@),
        spec_capture_param_and_local_x_b().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_param_and_local_x_b().spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_x_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureParamAndLocalXBCont0;
type CaptureParamAndLocalXBCont0Type<'a, 'b> = &'b u8;
type CaptureParamAndLocalXBCont0SType<'a, 'x> = &'x u8;
type CaptureParamAndLocalXBCont0Input<'a, 'b, 'x> = POrSType<CaptureParamAndLocalXBCont0Type<'a, 'b>, CaptureParamAndLocalXBCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureParamAndLocalXBCont0Input<'a, 'b, 'x>> for CaptureParamAndLocalXBCont0 {
    type Output = CaptureParamAndLocalXBYCombinator;

    open spec fn requires(&self, deps: CaptureParamAndLocalXBCont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureParamAndLocalXBCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_param_and_local_x_b_cont0(deps@)
    }

    fn apply(&self, deps: CaptureParamAndLocalXBCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_param_and_local_x_b_y(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_param_and_local_x_b_y(tag)
            }
        }
    }
}
                

pub enum SpecCaptureParamAndLocalX {
    A(SpecCaptureParamAndLocalXA),
    B(SpecCaptureParamAndLocalXB),
}

pub type SpecCaptureParamAndLocalXInner = Either<SpecCaptureParamAndLocalXA, SpecCaptureParamAndLocalXB>;

impl SpecFrom<SpecCaptureParamAndLocalX> for SpecCaptureParamAndLocalXInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalX) -> SpecCaptureParamAndLocalXInner {
        match m {
            SpecCaptureParamAndLocalX::A(m) => Either::Left(m),
            SpecCaptureParamAndLocalX::B(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalXInner> for SpecCaptureParamAndLocalX {
    open spec fn spec_from(m: SpecCaptureParamAndLocalXInner) -> SpecCaptureParamAndLocalX {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalX::A(m),
            Either::Right(m) => SpecCaptureParamAndLocalX::B(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalX<'a> {
    A(CaptureParamAndLocalXA<'a>),
    B(CaptureParamAndLocalXB),
}

pub type CaptureParamAndLocalXInner<'a> = Either<CaptureParamAndLocalXA<'a>, CaptureParamAndLocalXB>;

pub type CaptureParamAndLocalXInnerRef<'a> = Either<&'a CaptureParamAndLocalXA<'a>, &'a CaptureParamAndLocalXB>;


impl<'a> View for CaptureParamAndLocalX<'a> {
    type V = SpecCaptureParamAndLocalX;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalX::A(m) => SpecCaptureParamAndLocalX::A(m@),
            CaptureParamAndLocalX::B(m) => SpecCaptureParamAndLocalX::B(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalX<'a>> for CaptureParamAndLocalXInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalX<'a>) -> CaptureParamAndLocalXInnerRef<'a> {
        match m {
            CaptureParamAndLocalX::A(m) => Either::Left(m),
            CaptureParamAndLocalX::B(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureParamAndLocalXInner<'a>> for CaptureParamAndLocalX<'a> {
    fn ex_from(m: CaptureParamAndLocalXInner<'a>) -> CaptureParamAndLocalX<'a> {
        match m {
            Either::Left(m) => CaptureParamAndLocalX::A(m),
            Either::Right(m) => CaptureParamAndLocalX::B(m),
        }
    }
    
}


pub struct CaptureParamAndLocalXMapper;
impl View for CaptureParamAndLocalXMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalXMapper {
    type Src = SpecCaptureParamAndLocalXInner;
    type Dst = SpecCaptureParamAndLocalX;
}
impl SpecIsoProof for CaptureParamAndLocalXMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalXMapper {
    type Src = CaptureParamAndLocalXInner<'a>;
    type Dst = CaptureParamAndLocalX<'a>;
    type RefSrc = CaptureParamAndLocalXInnerRef<'a>;
}

type SpecCaptureParamAndLocalXCombinatorAlias1 = Choice<Cond<SpecCaptureParamAndLocalXACombinator>, Cond<SpecCaptureParamAndLocalXBCombinator>>;
pub struct SpecCaptureParamAndLocalXCombinator(pub SpecCaptureParamAndLocalXCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalXCombinator {
    type Type = SpecCaptureParamAndLocalX;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalXCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalXCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalXCombinatorAlias = Mapped<SpecCaptureParamAndLocalXCombinatorAlias1, CaptureParamAndLocalXMapper>;
type CaptureParamAndLocalXCombinatorAlias1 = Choice<Cond<CaptureParamAndLocalXACombinator>, Cond<CaptureParamAndLocalXBCombinator>>;
pub struct CaptureParamAndLocalXCombinator1(pub CaptureParamAndLocalXCombinatorAlias1);
impl View for CaptureParamAndLocalXCombinator1 {
    type V = SpecCaptureParamAndLocalXCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalXCombinator1, CaptureParamAndLocalXCombinatorAlias1);

pub struct CaptureParamAndLocalXCombinator(pub CaptureParamAndLocalXCombinatorAlias);

impl View for CaptureParamAndLocalXCombinator {
    type V = SpecCaptureParamAndLocalXCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalXCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalXCombinator {
    type Type = CaptureParamAndLocalX<'a>;
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
pub type CaptureParamAndLocalXCombinatorAlias = Mapped<CaptureParamAndLocalXCombinator1, CaptureParamAndLocalXMapper>;


pub open spec fn spec_capture_param_and_local_x(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecCaptureParamAndLocalXCombinator {
    SpecCaptureParamAndLocalXCombinator(Mapped { inner: Choice(Cond { cond: choice1 == AOrB::A, inner: spec_capture_param_and_local_x_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: spec_capture_param_and_local_x_b() }), mapper: CaptureParamAndLocalXMapper })
}

pub fn capture_param_and_local_x<'a>(choice1: AOrB, choice2: COrD) -> (o: CaptureParamAndLocalXCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_x(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalXCombinator(Mapped { inner: CaptureParamAndLocalXCombinator1(Choice::new(Cond { cond: choice1 == AOrB::A, inner: capture_param_and_local_x_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: capture_param_and_local_x_b() })), mapper: CaptureParamAndLocalXMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_x(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_x<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<CaptureParamAndLocalXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_x(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_x(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_x(choice1@, choice2@).spec_parse(input@) is None,
        spec_capture_param_and_local_x(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_x<'a>(v: <CaptureParamAndLocalXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_x( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_param_and_local_x_infallible<'a>(v: <CaptureParamAndLocalXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),
        spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@)),
{
    let combinator = capture_param_and_local_x( choice1, choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_x_len<'a>(v: <CaptureParamAndLocalXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_x(choice1@, choice2@).wf(v@),
        spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_x(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecNestedInnerChoiceXA {
    C(u8),
    D(u16),
}

pub type SpecNestedInnerChoiceXAInner = Either<u8, u16>;

impl SpecFrom<SpecNestedInnerChoiceXA> for SpecNestedInnerChoiceXAInner {
    open spec fn spec_from(m: SpecNestedInnerChoiceXA) -> SpecNestedInnerChoiceXAInner {
        match m {
            SpecNestedInnerChoiceXA::C(m) => Either::Left(m),
            SpecNestedInnerChoiceXA::D(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecNestedInnerChoiceXAInner> for SpecNestedInnerChoiceXA {
    open spec fn spec_from(m: SpecNestedInnerChoiceXAInner) -> SpecNestedInnerChoiceXA {
        match m {
            Either::Left(m) => SpecNestedInnerChoiceXA::C(m),
            Either::Right(m) => SpecNestedInnerChoiceXA::D(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NestedInnerChoiceXA {
    C(u8),
    D(u16),
}

pub type NestedInnerChoiceXAInner = Either<u8, u16>;

pub type NestedInnerChoiceXAInnerRef<'a> = Either<&'a u8, &'a u16>;


impl View for NestedInnerChoiceXA {
    type V = SpecNestedInnerChoiceXA;
    open spec fn view(&self) -> Self::V {
        match self {
            NestedInnerChoiceXA::C(m) => SpecNestedInnerChoiceXA::C(m@),
            NestedInnerChoiceXA::D(m) => SpecNestedInnerChoiceXA::D(m@),
        }
    }
}


impl<'a> From<&'a NestedInnerChoiceXA> for NestedInnerChoiceXAInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerChoiceXA) -> NestedInnerChoiceXAInnerRef<'a> {
        match m {
            NestedInnerChoiceXA::C(m) => Either::Left(m),
            NestedInnerChoiceXA::D(m) => Either::Right(m),
        }
    }

}

impl From<NestedInnerChoiceXAInner> for NestedInnerChoiceXA {
    fn ex_from(m: NestedInnerChoiceXAInner) -> NestedInnerChoiceXA {
        match m {
            Either::Left(m) => NestedInnerChoiceXA::C(m),
            Either::Right(m) => NestedInnerChoiceXA::D(m),
        }
    }
    
}


pub struct NestedInnerChoiceXAMapper;
impl View for NestedInnerChoiceXAMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerChoiceXAMapper {
    type Src = SpecNestedInnerChoiceXAInner;
    type Dst = SpecNestedInnerChoiceXA;
}
impl SpecIsoProof for NestedInnerChoiceXAMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerChoiceXAMapper {
    type Src = NestedInnerChoiceXAInner;
    type Dst = NestedInnerChoiceXA;
    type RefSrc = NestedInnerChoiceXAInnerRef<'a>;
}

type SpecNestedInnerChoiceXACombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct SpecNestedInnerChoiceXACombinator(pub SpecNestedInnerChoiceXACombinatorAlias);

impl SpecCombinator for SpecNestedInnerChoiceXACombinator {
    type Type = SpecNestedInnerChoiceXA;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerChoiceXACombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerChoiceXACombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerChoiceXACombinatorAlias = Mapped<SpecNestedInnerChoiceXACombinatorAlias1, NestedInnerChoiceXAMapper>;
type NestedInnerChoiceXACombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct NestedInnerChoiceXACombinator1(pub NestedInnerChoiceXACombinatorAlias1);
impl View for NestedInnerChoiceXACombinator1 {
    type V = SpecNestedInnerChoiceXACombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerChoiceXACombinator1, NestedInnerChoiceXACombinatorAlias1);

pub struct NestedInnerChoiceXACombinator(pub NestedInnerChoiceXACombinatorAlias);

impl View for NestedInnerChoiceXACombinator {
    type V = SpecNestedInnerChoiceXACombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerChoiceXACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerChoiceXACombinator {
    type Type = NestedInnerChoiceXA;
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
pub type NestedInnerChoiceXACombinatorAlias = Mapped<NestedInnerChoiceXACombinator1, NestedInnerChoiceXAMapper>;


pub open spec fn spec_nested_inner_choice_x_a(choice2: SpecCOrD) -> SpecNestedInnerChoiceXACombinator {
    SpecNestedInnerChoiceXACombinator(Mapped { inner: Choice(Cond { cond: choice2 == COrD::C, inner: U8 }, Cond { cond: choice2 == COrD::D, inner: U16Le }), mapper: NestedInnerChoiceXAMapper })
}

pub fn nested_inner_choice_x_a<'a>(choice2: COrD) -> (o: NestedInnerChoiceXACombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_nested_inner_choice_x_a(choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerChoiceXACombinator(Mapped { inner: NestedInnerChoiceXACombinator1(Choice::new(Cond { cond: choice2 == COrD::C, inner: U8 }, Cond { cond: choice2 == COrD::D, inner: U16Le })), mapper: NestedInnerChoiceXAMapper });
    // assert({
    //     &&& combinator@ == spec_nested_inner_choice_x_a(choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_choice_x_a<'a>(input: &'a [u8], choice2: COrD) -> (res: PResult<<NestedInnerChoiceXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_choice_x_a(choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_choice_x_a(choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_choice_x_a(choice2@).spec_parse(input@) is None,
        spec_nested_inner_choice_x_a(choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_choice_x_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_choice_x_a<'a>(v: <NestedInnerChoiceXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_x_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_choice_x_a( choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_nested_inner_choice_x_a_infallible<'a>(v: <NestedInnerChoiceXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_x_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),
        spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@)),
{
    let combinator = nested_inner_choice_x_a( choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn nested_inner_choice_x_a_len<'a>(v: <NestedInnerChoiceXACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_nested_inner_choice_x_a(choice2@).wf(v@),
        spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_nested_inner_choice_x_a(choice2@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_choice_x_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1 {
    pub count: u8,
    pub items: Seq<u8>,
}

pub type SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner = (u8, Seq<u8>);


impl SpecFrom<SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1> for SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner {
        (m.count, m.items)
    }
}

impl SpecFrom<SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner> for SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1 {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1 {
        let (count, items) = m;
        SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1 { count, items }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a> {
    pub count: u8,
    pub items: &'a [u8],
}

impl View for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'_> {
    type V = SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1;

    open spec fn view(&self) -> Self::V {
        SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1 {
            count: self.count@,
            items: self.items@,
        }
    }
}
pub type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner<'a> = (u8, &'a [u8]);

pub type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1InnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>> for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1InnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalPayloadAnonInnerBodyChoice1) -> CaptureOuterAndLocalPayloadAnonInnerBodyChoice1InnerRef<'a> {
        (&m.count, &m.items)
    }
}

impl<'a> From<CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner<'a>> for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a> {
    fn ex_from(m: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner) -> CaptureOuterAndLocalPayloadAnonInnerBodyChoice1 {
        let (count, items) = m;
        CaptureOuterAndLocalPayloadAnonInnerBodyChoice1 { count, items }
    }
}

pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper;
impl View for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper {
    type Src = SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner;
    type Dst = SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1;
}
impl SpecIsoProof for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper {
    type Src = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Inner<'a>;
    type Dst = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>;
    type RefSrc = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1InnerRef<'a>;
}

pub struct SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator(pub SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1CombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator {
    type Type = SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1CombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1CombinatorAlias = Mapped<SpecPair<U8, bytes::Variable>, CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper>;

pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator(pub CaptureOuterAndLocalPayloadAnonInnerBodyChoice1CombinatorAlias);

impl View for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator {
    type V = SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator {
    type Type = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>;
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
pub type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1CombinatorAlias = Mapped<Pair<U8, bytes::Variable, CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0>, CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper>;


pub open spec fn spec_capture_outer_and_local_payload_anon_inner_body_choice1() -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator {
    SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_outer_and_local_payload_anon_inner_body_choice1_cont0(deps)),
        mapper: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper,
    })
}

pub open spec fn spec_capture_outer_and_local_payload_anon_inner_body_choice1_cont0(deps: u8) -> bytes::Variable {
    let count = deps;
    bytes::Variable((usize::spec_from(count)) as usize)
}

impl View for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_outer_and_local_payload_anon_inner_body_choice1_cont0(deps)
        }
    }
}

                
pub fn capture_outer_and_local_payload_anon_inner_body_choice1<'a>() -> (o: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator)
    ensures o@ == spec_capture_outer_and_local_payload_anon_inner_body_choice1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator(
    Mapped {
        inner: Pair::new(U8, CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0),
        mapper: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_payload_anon_inner_body_choice1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_payload_anon_inner_body_choice1<'a>(input: &'a [u8]) -> (res: PResult<<CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_parse(input@) is None,
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_payload_anon_inner_body_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_payload_anon_inner_body_choice1<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_payload_anon_inner_body_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_outer_and_local_payload_anon_inner_body_choice1_infallible<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().wf(v@),
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@)),
{
    let combinator = capture_outer_and_local_payload_anon_inner_body_choice1();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_outer_and_local_payload_anon_inner_body_choice1_len<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().wf(v@),
        spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_outer_and_local_payload_anon_inner_body_choice1().spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_payload_anon_inner_body_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0;
type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Type<'a, 'b> = &'b u8;
type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0SType<'a, 'x> = &'x u8;
type CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Input<'a, 'b, 'x> = POrSType<CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Type<'a, 'b>, CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Input<'a, 'b, 'x>> for CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_outer_and_local_payload_anon_inner_body_choice1_cont0(deps@)
    }

    fn apply(&self, deps: CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let count = deps;
                let count = *count;
                bytes::Variable((usize::ex_from(count)) as usize)
            }
            POrSType::S(deps) => {
                let count = deps;
                let count = *count;
                bytes::Variable((usize::ex_from(count)) as usize)
            }
        }
    }
}
                

pub enum SpecCaptureOuterAndLocalPayloadAnonInnerBody {
    Variant0(Seq<u8>),
    Variant1(SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1),
}

pub type SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner = Either<Seq<u8>, SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1>;

impl SpecFrom<SpecCaptureOuterAndLocalPayloadAnonInnerBody> for SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayloadAnonInnerBody) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner {
        match m {
            SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m) => Either::Left(m),
            SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner> for SpecCaptureOuterAndLocalPayloadAnonInnerBody {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner) -> SpecCaptureOuterAndLocalPayloadAnonInnerBody {
        match m {
            Either::Left(m) => SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m),
            Either::Right(m) => SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureOuterAndLocalPayloadAnonInnerBody<'a> {
    Variant0(&'a [u8]),
    Variant1(CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>),
}

pub type CaptureOuterAndLocalPayloadAnonInnerBodyInner<'a> = Either<&'a [u8], CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>>;

pub type CaptureOuterAndLocalPayloadAnonInnerBodyInnerRef<'a> = Either<&'a &'a [u8], &'a CaptureOuterAndLocalPayloadAnonInnerBodyChoice1<'a>>;


impl<'a> View for CaptureOuterAndLocalPayloadAnonInnerBody<'a> {
    type V = SpecCaptureOuterAndLocalPayloadAnonInnerBody;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m) => SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m@),
            CaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m) => SpecCaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureOuterAndLocalPayloadAnonInnerBody<'a>> for CaptureOuterAndLocalPayloadAnonInnerBodyInnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalPayloadAnonInnerBody<'a>) -> CaptureOuterAndLocalPayloadAnonInnerBodyInnerRef<'a> {
        match m {
            CaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m) => Either::Left(m),
            CaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureOuterAndLocalPayloadAnonInnerBodyInner<'a>> for CaptureOuterAndLocalPayloadAnonInnerBody<'a> {
    fn ex_from(m: CaptureOuterAndLocalPayloadAnonInnerBodyInner<'a>) -> CaptureOuterAndLocalPayloadAnonInnerBody<'a> {
        match m {
            Either::Left(m) => CaptureOuterAndLocalPayloadAnonInnerBody::Variant0(m),
            Either::Right(m) => CaptureOuterAndLocalPayloadAnonInnerBody::Variant1(m),
        }
    }
    
}


pub struct CaptureOuterAndLocalPayloadAnonInnerBodyMapper;
impl View for CaptureOuterAndLocalPayloadAnonInnerBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalPayloadAnonInnerBodyMapper {
    type Src = SpecCaptureOuterAndLocalPayloadAnonInnerBodyInner;
    type Dst = SpecCaptureOuterAndLocalPayloadAnonInnerBody;
}
impl SpecIsoProof for CaptureOuterAndLocalPayloadAnonInnerBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalPayloadAnonInnerBodyMapper {
    type Src = CaptureOuterAndLocalPayloadAnonInnerBodyInner<'a>;
    type Dst = CaptureOuterAndLocalPayloadAnonInnerBody<'a>;
    type RefSrc = CaptureOuterAndLocalPayloadAnonInnerBodyInnerRef<'a>;
}

type SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<SpecCaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator>>;
pub struct SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator(pub SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    type Type = SpecCaptureOuterAndLocalPayloadAnonInnerBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias = Mapped<SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1, CaptureOuterAndLocalPayloadAnonInnerBodyMapper>;
type CaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<CaptureOuterAndLocalPayloadAnonInnerBodyChoice1Combinator>>;
pub struct CaptureOuterAndLocalPayloadAnonInnerBodyCombinator1(pub CaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1);
impl View for CaptureOuterAndLocalPayloadAnonInnerBodyCombinator1 {
    type V = SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureOuterAndLocalPayloadAnonInnerBodyCombinator1, CaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias1);

pub struct CaptureOuterAndLocalPayloadAnonInnerBodyCombinator(pub CaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias);

impl View for CaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    type V = SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    type Type = CaptureOuterAndLocalPayloadAnonInnerBody<'a>;
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
pub type CaptureOuterAndLocalPayloadAnonInnerBodyCombinatorAlias = Mapped<CaptureOuterAndLocalPayloadAnonInnerBodyCombinator1, CaptureOuterAndLocalPayloadAnonInnerBodyMapper>;


pub open spec fn spec_capture_outer_and_local_payload_anon_inner_body(frame_len: u8, tag: u8) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: bytes::Variable(((usize::spec_from(frame_len) - 1)) as usize) }, Cond { cond: !(tag == 0), inner: spec_capture_outer_and_local_payload_anon_inner_body_choice1() }), mapper: CaptureOuterAndLocalPayloadAnonInnerBodyMapper })
}

pub fn capture_outer_and_local_payload_anon_inner_body<'a>(frame_len: u8, tag: u8) -> (o: CaptureOuterAndLocalPayloadAnonInnerBodyCombinator)
    requires
        ((frame_len) >= 1),

    ensures o@ == spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalPayloadAnonInnerBodyCombinator(Mapped { inner: CaptureOuterAndLocalPayloadAnonInnerBodyCombinator1(Choice::new(Cond { cond: tag == 0, inner: bytes::Variable(((usize::ex_from(frame_len) - 1)) as usize) }, Cond { cond: !(tag == 0), inner: capture_outer_and_local_payload_anon_inner_body_choice1() })), mapper: CaptureOuterAndLocalPayloadAnonInnerBodyMapper });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_payload_anon_inner_body<'a>(input: &'a [u8], frame_len: u8, tag: u8) -> (res: PResult<<CaptureOuterAndLocalPayloadAnonInnerBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_parse(input@) is None,
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_payload_anon_inner_body( frame_len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_payload_anon_inner_body<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).wf(v@),
        ((frame_len) >= 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_payload_anon_inner_body( frame_len, tag );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_outer_and_local_payload_anon_inner_body_infallible<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8, tag: u8) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).wf(v@),
        ((frame_len) >= 1),
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@)),
{
    let combinator = capture_outer_and_local_payload_anon_inner_body( frame_len, tag );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_outer_and_local_payload_anon_inner_body_len<'a>(v: <CaptureOuterAndLocalPayloadAnonInnerBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, frame_len: u8, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).wf(v@),
        spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        serialize_len == spec_capture_outer_and_local_payload_anon_inner_body(frame_len@, tag@).spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_payload_anon_inner_body( frame_len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureOuterAndLocalPayload {
    pub tag: u8,
    pub body: SpecCaptureOuterAndLocalPayloadAnonInnerBody,
}

pub type SpecCaptureOuterAndLocalPayloadInner = (u8, SpecCaptureOuterAndLocalPayloadAnonInnerBody);


impl SpecFrom<SpecCaptureOuterAndLocalPayload> for SpecCaptureOuterAndLocalPayloadInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayload) -> SpecCaptureOuterAndLocalPayloadInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecCaptureOuterAndLocalPayloadInner> for SpecCaptureOuterAndLocalPayload {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalPayloadInner) -> SpecCaptureOuterAndLocalPayload {
        let (tag, body) = m;
        SpecCaptureOuterAndLocalPayload { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureOuterAndLocalPayload<'a> {
    pub tag: u8,
    pub body: CaptureOuterAndLocalPayloadAnonInnerBody<'a>,
}

impl View for CaptureOuterAndLocalPayload<'_> {
    type V = SpecCaptureOuterAndLocalPayload;

    open spec fn view(&self) -> Self::V {
        SpecCaptureOuterAndLocalPayload {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type CaptureOuterAndLocalPayloadInner<'a> = (u8, CaptureOuterAndLocalPayloadAnonInnerBody<'a>);

pub type CaptureOuterAndLocalPayloadInnerRef<'a> = (&'a u8, &'a CaptureOuterAndLocalPayloadAnonInnerBody<'a>);
impl<'a> From<&'a CaptureOuterAndLocalPayload<'a>> for CaptureOuterAndLocalPayloadInnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalPayload) -> CaptureOuterAndLocalPayloadInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl<'a> From<CaptureOuterAndLocalPayloadInner<'a>> for CaptureOuterAndLocalPayload<'a> {
    fn ex_from(m: CaptureOuterAndLocalPayloadInner) -> CaptureOuterAndLocalPayload {
        let (tag, body) = m;
        CaptureOuterAndLocalPayload { tag, body }
    }
}

pub struct CaptureOuterAndLocalPayloadMapper;
impl View for CaptureOuterAndLocalPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalPayloadMapper {
    type Src = SpecCaptureOuterAndLocalPayloadInner;
    type Dst = SpecCaptureOuterAndLocalPayload;
}
impl SpecIsoProof for CaptureOuterAndLocalPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalPayloadMapper {
    type Src = CaptureOuterAndLocalPayloadInner<'a>;
    type Dst = CaptureOuterAndLocalPayload<'a>;
    type RefSrc = CaptureOuterAndLocalPayloadInnerRef<'a>;
}

pub struct SpecCaptureOuterAndLocalPayloadCombinator(pub SpecCaptureOuterAndLocalPayloadCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalPayloadCombinator {
    type Type = SpecCaptureOuterAndLocalPayload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalPayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalPayloadCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecPair<U8, SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator>, CaptureOuterAndLocalPayloadMapper>>;

pub struct CaptureOuterAndLocalPayloadCombinator(pub CaptureOuterAndLocalPayloadCombinatorAlias);

impl View for CaptureOuterAndLocalPayloadCombinator {
    type V = SpecCaptureOuterAndLocalPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalPayloadCombinator {
    type Type = CaptureOuterAndLocalPayload<'a>;
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
pub type CaptureOuterAndLocalPayloadCombinatorAlias = AndThen<bytes::Variable, Mapped<Pair<U8, CaptureOuterAndLocalPayloadAnonInnerBodyCombinator, CaptureOuterAndLocalPayloadCont0>, CaptureOuterAndLocalPayloadMapper>>;


pub open spec fn spec_capture_outer_and_local_payload(frame_len: u8) -> SpecCaptureOuterAndLocalPayloadCombinator {
    SpecCaptureOuterAndLocalPayloadCombinator(AndThen(bytes::Variable((usize::spec_from(frame_len)) as usize), 
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_outer_and_local_payload_cont0(frame_len, deps)),
        mapper: CaptureOuterAndLocalPayloadMapper,
    }))
}

pub open spec fn spec_capture_outer_and_local_payload_cont0(frame_len: u8, deps: u8) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator {
    let tag = deps;
    spec_capture_outer_and_local_payload_anon_inner_body(frame_len, tag)
}

impl View for CaptureOuterAndLocalPayloadCont0 {
    type V = spec_fn(u8) -> SpecCaptureOuterAndLocalPayloadAnonInnerBodyCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_outer_and_local_payload_cont0(self.frame_len@, deps)
        }
    }
}

pub fn capture_outer_and_local_payload<'a>(frame_len: u8) -> (o: CaptureOuterAndLocalPayloadCombinator)
    requires
        ((frame_len) >= 1),

    ensures o@ == spec_capture_outer_and_local_payload(frame_len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalPayloadCombinator(AndThen(bytes::Variable((usize::ex_from(frame_len)) as usize), 
    Mapped {
        inner: Pair::new(U8, CaptureOuterAndLocalPayloadCont0 { frame_len }),
        mapper: CaptureOuterAndLocalPayloadMapper,
    }));
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_payload(frame_len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_payload<'a>(input: &'a [u8], frame_len: u8) -> (res: PResult<<CaptureOuterAndLocalPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_payload(frame_len@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_payload(frame_len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_payload(frame_len@).spec_parse(input@) is None,
        spec_capture_outer_and_local_payload(frame_len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_payload( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_payload<'a>(v: <CaptureOuterAndLocalPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload(frame_len@).wf(v@),
        ((frame_len) >= 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_payload( frame_len );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_outer_and_local_payload_infallible<'a>(v: <CaptureOuterAndLocalPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_payload(frame_len@).wf(v@),
        ((frame_len) >= 1),
        spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@)),
{
    let combinator = capture_outer_and_local_payload( frame_len );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_outer_and_local_payload_len<'a>(v: <CaptureOuterAndLocalPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, frame_len: u8) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_payload(frame_len@).wf(v@),
        spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        serialize_len == spec_capture_outer_and_local_payload(frame_len@).spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_payload( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureOuterAndLocalPayloadCont0 {
    pub frame_len: u8,
}
type CaptureOuterAndLocalPayloadCont0Type<'a, 'b> = &'b u8;
type CaptureOuterAndLocalPayloadCont0SType<'a, 'x> = &'x u8;
type CaptureOuterAndLocalPayloadCont0Input<'a, 'b, 'x> = POrSType<CaptureOuterAndLocalPayloadCont0Type<'a, 'b>, CaptureOuterAndLocalPayloadCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureOuterAndLocalPayloadCont0Input<'a, 'b, 'x>> for CaptureOuterAndLocalPayloadCont0 {
    type Output = CaptureOuterAndLocalPayloadAnonInnerBodyCombinator;

    open spec fn requires(&self, deps: CaptureOuterAndLocalPayloadCont0Input<'a, 'b, 'x>) -> bool {        let frame_len = self.frame_len@;

        &&& ((self.frame_len@) >= 1)
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureOuterAndLocalPayloadCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_outer_and_local_payload_cont0(self.frame_len@, deps@)
    }

    fn apply(&self, deps: CaptureOuterAndLocalPayloadCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let frame_len = self.frame_len;
                let tag = *tag;
                capture_outer_and_local_payload_anon_inner_body(frame_len, tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let frame_len = self.frame_len;
                let tag = *tag;
                capture_outer_and_local_payload_anon_inner_body(frame_len, tag)
            }
        }
    }
}

pub struct SpecCaptureOuterAndLocal {
    pub frame_len: u8,
    pub payload: SpecCaptureOuterAndLocalPayload,
}

pub type SpecCaptureOuterAndLocalInner = (u8, SpecCaptureOuterAndLocalPayload);


impl SpecFrom<SpecCaptureOuterAndLocal> for SpecCaptureOuterAndLocalInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocal) -> SpecCaptureOuterAndLocalInner {
        (m.frame_len, m.payload)
    }
}

impl SpecFrom<SpecCaptureOuterAndLocalInner> for SpecCaptureOuterAndLocal {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalInner) -> SpecCaptureOuterAndLocal {
        let (frame_len, payload) = m;
        SpecCaptureOuterAndLocal { frame_len, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureOuterAndLocal<'a> {
    pub frame_len: u8,
    pub payload: CaptureOuterAndLocalPayload<'a>,
}

impl View for CaptureOuterAndLocal<'_> {
    type V = SpecCaptureOuterAndLocal;

    open spec fn view(&self) -> Self::V {
        SpecCaptureOuterAndLocal {
            frame_len: self.frame_len@,
            payload: self.payload@,
        }
    }
}
pub type CaptureOuterAndLocalInner<'a> = (u8, CaptureOuterAndLocalPayload<'a>);

pub type CaptureOuterAndLocalInnerRef<'a> = (&'a u8, &'a CaptureOuterAndLocalPayload<'a>);
impl<'a> From<&'a CaptureOuterAndLocal<'a>> for CaptureOuterAndLocalInnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocal) -> CaptureOuterAndLocalInnerRef<'a> {
        (&m.frame_len, &m.payload)
    }
}

impl<'a> From<CaptureOuterAndLocalInner<'a>> for CaptureOuterAndLocal<'a> {
    fn ex_from(m: CaptureOuterAndLocalInner) -> CaptureOuterAndLocal {
        let (frame_len, payload) = m;
        CaptureOuterAndLocal { frame_len, payload }
    }
}

pub struct CaptureOuterAndLocalMapper;
impl View for CaptureOuterAndLocalMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalMapper {
    type Src = SpecCaptureOuterAndLocalInner;
    type Dst = SpecCaptureOuterAndLocal;
}
impl SpecIsoProof for CaptureOuterAndLocalMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalMapper {
    type Src = CaptureOuterAndLocalInner<'a>;
    type Dst = CaptureOuterAndLocal<'a>;
    type RefSrc = CaptureOuterAndLocalInnerRef<'a>;
}

pub struct SpecCaptureOuterAndLocalCombinator(pub SpecCaptureOuterAndLocalCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalCombinator {
    type Type = SpecCaptureOuterAndLocal;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate2172399096230090262>, SpecCaptureOuterAndLocalPayloadCombinator>, CaptureOuterAndLocalMapper>;
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

pub struct CaptureOuterAndLocalCombinator(pub CaptureOuterAndLocalCombinatorAlias);

impl View for CaptureOuterAndLocalCombinator {
    type V = SpecCaptureOuterAndLocalCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalCombinator {
    type Type = CaptureOuterAndLocal<'a>;
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
pub type CaptureOuterAndLocalCombinatorAlias = Mapped<Pair<Refined<U8, Predicate2172399096230090262>, CaptureOuterAndLocalPayloadCombinator, CaptureOuterAndLocalCont0>, CaptureOuterAndLocalMapper>;


pub open spec fn spec_capture_outer_and_local() -> SpecCaptureOuterAndLocalCombinator {
    SpecCaptureOuterAndLocalCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate2172399096230090262 }, |deps| spec_capture_outer_and_local_cont0(deps)),
        mapper: CaptureOuterAndLocalMapper,
    })
}

pub open spec fn spec_capture_outer_and_local_cont0(deps: u8) -> SpecCaptureOuterAndLocalPayloadCombinator {
    let frame_len = deps;
    spec_capture_outer_and_local_payload(frame_len)
}

impl View for CaptureOuterAndLocalCont0 {
    type V = spec_fn(u8) -> SpecCaptureOuterAndLocalPayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_outer_and_local_cont0(deps)
        }
    }
}

                
pub fn capture_outer_and_local<'a>() -> (o: CaptureOuterAndLocalCombinator)
    ensures o@ == spec_capture_outer_and_local(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalCombinator(
    Mapped {
        inner: Pair::new(Refined { inner: U8, predicate: Predicate2172399096230090262 }, CaptureOuterAndLocalCont0),
        mapper: CaptureOuterAndLocalMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local<'a>(input: &'a [u8]) -> (res: PResult<<CaptureOuterAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local().spec_parse(input@) is None,
        spec_capture_outer_and_local().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local<'a>(v: <CaptureOuterAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local().spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_outer_and_local_infallible<'a>(v: <CaptureOuterAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local().wf(v@),
        spec_capture_outer_and_local().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_outer_and_local().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_outer_and_local().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local().spec_serialize(v@)),
{
    let combinator = capture_outer_and_local();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_outer_and_local_len<'a>(v: <CaptureOuterAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local().wf(v@),
        spec_capture_outer_and_local().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_outer_and_local().spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureOuterAndLocalCont0;
type CaptureOuterAndLocalCont0Type<'a, 'b> = &'b u8;
type CaptureOuterAndLocalCont0SType<'a, 'x> = &'x u8;
type CaptureOuterAndLocalCont0Input<'a, 'b, 'x> = POrSType<CaptureOuterAndLocalCont0Type<'a, 'b>, CaptureOuterAndLocalCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureOuterAndLocalCont0Input<'a, 'b, 'x>> for CaptureOuterAndLocalCont0 {
    type Output = CaptureOuterAndLocalPayloadCombinator;

    open spec fn requires(&self, deps: CaptureOuterAndLocalCont0Input<'a, 'b, 'x>) -> bool {
        &&& (Refined { inner: U8, predicate: Predicate2172399096230090262 }).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureOuterAndLocalCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_outer_and_local_cont0(deps@)
    }

    fn apply(&self, deps: CaptureOuterAndLocalCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let frame_len = deps;
                let frame_len = *frame_len;
                capture_outer_and_local_payload(frame_len)
            }
            POrSType::S(deps) => {
                let frame_len = deps;
                let frame_len = *frame_len;
                capture_outer_and_local_payload(frame_len)
            }
        }
    }
}
                

pub struct SpecNestedInnerStructAnonInner {
    pub x: u8,
    pub y: Seq<u8>,
}

pub type SpecNestedInnerStructAnonInnerInner = (u8, Seq<u8>);


impl SpecFrom<SpecNestedInnerStructAnonInner> for SpecNestedInnerStructAnonInnerInner {
    open spec fn spec_from(m: SpecNestedInnerStructAnonInner) -> SpecNestedInnerStructAnonInnerInner {
        (m.x, m.y)
    }
}

impl SpecFrom<SpecNestedInnerStructAnonInnerInner> for SpecNestedInnerStructAnonInner {
    open spec fn spec_from(m: SpecNestedInnerStructAnonInnerInner) -> SpecNestedInnerStructAnonInner {
        let (x, y) = m;
        SpecNestedInnerStructAnonInner { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NestedInnerStructAnonInner<'a> {
    pub x: u8,
    pub y: &'a [u8],
}

impl View for NestedInnerStructAnonInner<'_> {
    type V = SpecNestedInnerStructAnonInner;

    open spec fn view(&self) -> Self::V {
        SpecNestedInnerStructAnonInner {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type NestedInnerStructAnonInnerInner<'a> = (u8, &'a [u8]);

pub type NestedInnerStructAnonInnerInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a NestedInnerStructAnonInner<'a>> for NestedInnerStructAnonInnerInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerStructAnonInner) -> NestedInnerStructAnonInnerInnerRef<'a> {
        (&m.x, &m.y)
    }
}

impl<'a> From<NestedInnerStructAnonInnerInner<'a>> for NestedInnerStructAnonInner<'a> {
    fn ex_from(m: NestedInnerStructAnonInnerInner) -> NestedInnerStructAnonInner {
        let (x, y) = m;
        NestedInnerStructAnonInner { x, y }
    }
}

pub struct NestedInnerStructAnonInnerMapper;
impl View for NestedInnerStructAnonInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerStructAnonInnerMapper {
    type Src = SpecNestedInnerStructAnonInnerInner;
    type Dst = SpecNestedInnerStructAnonInner;
}
impl SpecIsoProof for NestedInnerStructAnonInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerStructAnonInnerMapper {
    type Src = NestedInnerStructAnonInnerInner<'a>;
    type Dst = NestedInnerStructAnonInner<'a>;
    type RefSrc = NestedInnerStructAnonInnerInnerRef<'a>;
}
type SpecNestedInnerStructAnonInnerCombinatorAlias1 = (U8, bytes::Tail);
pub struct SpecNestedInnerStructAnonInnerCombinator(pub SpecNestedInnerStructAnonInnerCombinatorAlias);

impl SpecCombinator for SpecNestedInnerStructAnonInnerCombinator {
    type Type = SpecNestedInnerStructAnonInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerStructAnonInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerStructAnonInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerStructAnonInnerCombinatorAlias = AndThen<bytes::Variable, Mapped<SpecNestedInnerStructAnonInnerCombinatorAlias1, NestedInnerStructAnonInnerMapper>>;
type NestedInnerStructAnonInnerCombinatorAlias1 = (U8, bytes::Tail);
pub struct NestedInnerStructAnonInnerCombinator1(pub NestedInnerStructAnonInnerCombinatorAlias1);
impl View for NestedInnerStructAnonInnerCombinator1 {
    type V = SpecNestedInnerStructAnonInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerStructAnonInnerCombinator1, NestedInnerStructAnonInnerCombinatorAlias1);

pub struct NestedInnerStructAnonInnerCombinator(pub NestedInnerStructAnonInnerCombinatorAlias);

impl View for NestedInnerStructAnonInnerCombinator {
    type V = SpecNestedInnerStructAnonInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerStructAnonInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerStructAnonInnerCombinator {
    type Type = NestedInnerStructAnonInner<'a>;
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
pub type NestedInnerStructAnonInnerCombinatorAlias = AndThen<bytes::Variable, Mapped<NestedInnerStructAnonInnerCombinator1, NestedInnerStructAnonInnerMapper>>;


pub open spec fn spec_nested_inner_struct_anon_inner(len: u32) -> SpecNestedInnerStructAnonInnerCombinator {
    SpecNestedInnerStructAnonInnerCombinator(AndThen(bytes::Variable((usize::spec_from(len)) as usize), 
    Mapped {
        inner: (U8, bytes::Tail),
        mapper: NestedInnerStructAnonInnerMapper,
    }))
}

pub fn nested_inner_struct_anon_inner<'a>(len: u32) -> (o: NestedInnerStructAnonInnerCombinator)

    ensures o@ == spec_nested_inner_struct_anon_inner(len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerStructAnonInnerCombinator(AndThen(bytes::Variable((usize::ex_from(len)) as usize), 
    Mapped {
        inner: NestedInnerStructAnonInnerCombinator1((U8, bytes::Tail)),
        mapper: NestedInnerStructAnonInnerMapper,
    }));
    // assert({
    //     &&& combinator@ == spec_nested_inner_struct_anon_inner(len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_struct_anon_inner<'a>(input: &'a [u8], len: u32) -> (res: PResult<<NestedInnerStructAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_struct_anon_inner(len@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_struct_anon_inner(len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_struct_anon_inner(len@).spec_parse(input@) is None,
        spec_nested_inner_struct_anon_inner(len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_struct_anon_inner( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_struct_anon_inner<'a>(v: <NestedInnerStructAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, len: u32) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_struct_anon_inner(len@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_struct_anon_inner( len );
    combinator.serialize(v, data, pos)
}

pub fn serialize_nested_inner_struct_anon_inner_infallible<'a>(v: <NestedInnerStructAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, len: u32) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_struct_anon_inner(len@).wf(v@),
        spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@)),
{
    let combinator = nested_inner_struct_anon_inner( len );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn nested_inner_struct_anon_inner_len<'a>(v: <NestedInnerStructAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, len: u32) -> (serialize_len: usize)
    requires
        spec_nested_inner_struct_anon_inner(len@).wf(v@),
        spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_nested_inner_struct_anon_inner(len@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_struct_anon_inner( len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureLocalInAnonStructWrapperValueChoice0 {
    pub len: u8,
    pub bytes: Seq<u8>,
}

pub type SpecCaptureLocalInAnonStructWrapperValueChoice0Inner = (u8, Seq<u8>);


impl SpecFrom<SpecCaptureLocalInAnonStructWrapperValueChoice0> for SpecCaptureLocalInAnonStructWrapperValueChoice0Inner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapperValueChoice0) -> SpecCaptureLocalInAnonStructWrapperValueChoice0Inner {
        (m.len, m.bytes)
    }
}

impl SpecFrom<SpecCaptureLocalInAnonStructWrapperValueChoice0Inner> for SpecCaptureLocalInAnonStructWrapperValueChoice0 {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapperValueChoice0Inner) -> SpecCaptureLocalInAnonStructWrapperValueChoice0 {
        let (len, bytes) = m;
        SpecCaptureLocalInAnonStructWrapperValueChoice0 { len, bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureLocalInAnonStructWrapperValueChoice0<'a> {
    pub len: u8,
    pub bytes: &'a [u8],
}

impl View for CaptureLocalInAnonStructWrapperValueChoice0<'_> {
    type V = SpecCaptureLocalInAnonStructWrapperValueChoice0;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStructWrapperValueChoice0 {
            len: self.len@,
            bytes: self.bytes@,
        }
    }
}
pub type CaptureLocalInAnonStructWrapperValueChoice0Inner<'a> = (u8, &'a [u8]);

pub type CaptureLocalInAnonStructWrapperValueChoice0InnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CaptureLocalInAnonStructWrapperValueChoice0<'a>> for CaptureLocalInAnonStructWrapperValueChoice0InnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructWrapperValueChoice0) -> CaptureLocalInAnonStructWrapperValueChoice0InnerRef<'a> {
        (&m.len, &m.bytes)
    }
}

impl<'a> From<CaptureLocalInAnonStructWrapperValueChoice0Inner<'a>> for CaptureLocalInAnonStructWrapperValueChoice0<'a> {
    fn ex_from(m: CaptureLocalInAnonStructWrapperValueChoice0Inner) -> CaptureLocalInAnonStructWrapperValueChoice0 {
        let (len, bytes) = m;
        CaptureLocalInAnonStructWrapperValueChoice0 { len, bytes }
    }
}

pub struct CaptureLocalInAnonStructWrapperValueChoice0Mapper;
impl View for CaptureLocalInAnonStructWrapperValueChoice0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructWrapperValueChoice0Mapper {
    type Src = SpecCaptureLocalInAnonStructWrapperValueChoice0Inner;
    type Dst = SpecCaptureLocalInAnonStructWrapperValueChoice0;
}
impl SpecIsoProof for CaptureLocalInAnonStructWrapperValueChoice0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructWrapperValueChoice0Mapper {
    type Src = CaptureLocalInAnonStructWrapperValueChoice0Inner<'a>;
    type Dst = CaptureLocalInAnonStructWrapperValueChoice0<'a>;
    type RefSrc = CaptureLocalInAnonStructWrapperValueChoice0InnerRef<'a>;
}

pub struct SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator(pub SpecCaptureLocalInAnonStructWrapperValueChoice0CombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator {
    type Type = SpecCaptureLocalInAnonStructWrapperValueChoice0;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructWrapperValueChoice0CombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructWrapperValueChoice0CombinatorAlias = Mapped<SpecPair<U8, bytes::Variable>, CaptureLocalInAnonStructWrapperValueChoice0Mapper>;

pub struct CaptureLocalInAnonStructWrapperValueChoice0Combinator(pub CaptureLocalInAnonStructWrapperValueChoice0CombinatorAlias);

impl View for CaptureLocalInAnonStructWrapperValueChoice0Combinator {
    type V = SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructWrapperValueChoice0Combinator {
    type Type = CaptureLocalInAnonStructWrapperValueChoice0<'a>;
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
pub type CaptureLocalInAnonStructWrapperValueChoice0CombinatorAlias = Mapped<Pair<U8, bytes::Variable, CaptureLocalInAnonStructWrapperValueChoice0Cont0>, CaptureLocalInAnonStructWrapperValueChoice0Mapper>;


pub open spec fn spec_capture_local_in_anon_struct_wrapper_value_choice0() -> SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator {
    SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_local_in_anon_struct_wrapper_value_choice0_cont0(deps)),
        mapper: CaptureLocalInAnonStructWrapperValueChoice0Mapper,
    })
}

pub open spec fn spec_capture_local_in_anon_struct_wrapper_value_choice0_cont0(deps: u8) -> bytes::Variable {
    let len = deps;
    bytes::Variable((usize::spec_from(len)) as usize)
}

impl View for CaptureLocalInAnonStructWrapperValueChoice0Cont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_local_in_anon_struct_wrapper_value_choice0_cont0(deps)
        }
    }
}

                
pub fn capture_local_in_anon_struct_wrapper_value_choice0<'a>() -> (o: CaptureLocalInAnonStructWrapperValueChoice0Combinator)
    ensures o@ == spec_capture_local_in_anon_struct_wrapper_value_choice0(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructWrapperValueChoice0Combinator(
    Mapped {
        inner: Pair::new(U8, CaptureLocalInAnonStructWrapperValueChoice0Cont0),
        mapper: CaptureLocalInAnonStructWrapperValueChoice0Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_wrapper_value_choice0()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_wrapper_value_choice0<'a>(input: &'a [u8]) -> (res: PResult<<CaptureLocalInAnonStructWrapperValueChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_wrapper_value_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_wrapper_value_choice0<'a>(v: <CaptureLocalInAnonStructWrapperValueChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper_value_choice0().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_wrapper_value_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_local_in_anon_struct_wrapper_value_choice0_infallible<'a>(v: <CaptureLocalInAnonStructWrapperValueChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper_value_choice0().wf(v@),
        spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@)),
{
    let combinator = capture_local_in_anon_struct_wrapper_value_choice0();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_wrapper_value_choice0_len<'a>(v: <CaptureLocalInAnonStructWrapperValueChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_wrapper_value_choice0().wf(v@),
        spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_local_in_anon_struct_wrapper_value_choice0().spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_wrapper_value_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureLocalInAnonStructWrapperValueChoice0Cont0;
type CaptureLocalInAnonStructWrapperValueChoice0Cont0Type<'a, 'b> = &'b u8;
type CaptureLocalInAnonStructWrapperValueChoice0Cont0SType<'a, 'x> = &'x u8;
type CaptureLocalInAnonStructWrapperValueChoice0Cont0Input<'a, 'b, 'x> = POrSType<CaptureLocalInAnonStructWrapperValueChoice0Cont0Type<'a, 'b>, CaptureLocalInAnonStructWrapperValueChoice0Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureLocalInAnonStructWrapperValueChoice0Cont0Input<'a, 'b, 'x>> for CaptureLocalInAnonStructWrapperValueChoice0Cont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CaptureLocalInAnonStructWrapperValueChoice0Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureLocalInAnonStructWrapperValueChoice0Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_local_in_anon_struct_wrapper_value_choice0_cont0(deps@)
    }

    fn apply(&self, deps: CaptureLocalInAnonStructWrapperValueChoice0Cont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = deps;
                let len = *len;
                bytes::Variable((usize::ex_from(len)) as usize)
            }
            POrSType::S(deps) => {
                let len = deps;
                let len = *len;
                bytes::Variable((usize::ex_from(len)) as usize)
            }
        }
    }
}
                

pub enum SpecCaptureLocalInAnonStructWrapperValue {
    Variant0(SpecCaptureLocalInAnonStructWrapperValueChoice0),
    Variant1(u16),
}

pub type SpecCaptureLocalInAnonStructWrapperValueInner = Either<SpecCaptureLocalInAnonStructWrapperValueChoice0, u16>;

impl SpecFrom<SpecCaptureLocalInAnonStructWrapperValue> for SpecCaptureLocalInAnonStructWrapperValueInner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapperValue) -> SpecCaptureLocalInAnonStructWrapperValueInner {
        match m {
            SpecCaptureLocalInAnonStructWrapperValue::Variant0(m) => Either::Left(m),
            SpecCaptureLocalInAnonStructWrapperValue::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureLocalInAnonStructWrapperValueInner> for SpecCaptureLocalInAnonStructWrapperValue {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapperValueInner) -> SpecCaptureLocalInAnonStructWrapperValue {
        match m {
            Either::Left(m) => SpecCaptureLocalInAnonStructWrapperValue::Variant0(m),
            Either::Right(m) => SpecCaptureLocalInAnonStructWrapperValue::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureLocalInAnonStructWrapperValue<'a> {
    Variant0(CaptureLocalInAnonStructWrapperValueChoice0<'a>),
    Variant1(u16),
}

pub type CaptureLocalInAnonStructWrapperValueInner<'a> = Either<CaptureLocalInAnonStructWrapperValueChoice0<'a>, u16>;

pub type CaptureLocalInAnonStructWrapperValueInnerRef<'a> = Either<&'a CaptureLocalInAnonStructWrapperValueChoice0<'a>, &'a u16>;


impl<'a> View for CaptureLocalInAnonStructWrapperValue<'a> {
    type V = SpecCaptureLocalInAnonStructWrapperValue;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureLocalInAnonStructWrapperValue::Variant0(m) => SpecCaptureLocalInAnonStructWrapperValue::Variant0(m@),
            CaptureLocalInAnonStructWrapperValue::Variant1(m) => SpecCaptureLocalInAnonStructWrapperValue::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureLocalInAnonStructWrapperValue<'a>> for CaptureLocalInAnonStructWrapperValueInnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructWrapperValue<'a>) -> CaptureLocalInAnonStructWrapperValueInnerRef<'a> {
        match m {
            CaptureLocalInAnonStructWrapperValue::Variant0(m) => Either::Left(m),
            CaptureLocalInAnonStructWrapperValue::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureLocalInAnonStructWrapperValueInner<'a>> for CaptureLocalInAnonStructWrapperValue<'a> {
    fn ex_from(m: CaptureLocalInAnonStructWrapperValueInner<'a>) -> CaptureLocalInAnonStructWrapperValue<'a> {
        match m {
            Either::Left(m) => CaptureLocalInAnonStructWrapperValue::Variant0(m),
            Either::Right(m) => CaptureLocalInAnonStructWrapperValue::Variant1(m),
        }
    }
    
}


pub struct CaptureLocalInAnonStructWrapperValueMapper;
impl View for CaptureLocalInAnonStructWrapperValueMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructWrapperValueMapper {
    type Src = SpecCaptureLocalInAnonStructWrapperValueInner;
    type Dst = SpecCaptureLocalInAnonStructWrapperValue;
}
impl SpecIsoProof for CaptureLocalInAnonStructWrapperValueMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructWrapperValueMapper {
    type Src = CaptureLocalInAnonStructWrapperValueInner<'a>;
    type Dst = CaptureLocalInAnonStructWrapperValue<'a>;
    type RefSrc = CaptureLocalInAnonStructWrapperValueInnerRef<'a>;
}

type SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias1 = Choice<Cond<SpecCaptureLocalInAnonStructWrapperValueChoice0Combinator>, Cond<U16Le>>;
pub struct SpecCaptureLocalInAnonStructWrapperValueCombinator(pub SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructWrapperValueCombinator {
    type Type = SpecCaptureLocalInAnonStructWrapperValue;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructWrapperValueCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias = Mapped<SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias1, CaptureLocalInAnonStructWrapperValueMapper>;
type CaptureLocalInAnonStructWrapperValueCombinatorAlias1 = Choice<Cond<CaptureLocalInAnonStructWrapperValueChoice0Combinator>, Cond<U16Le>>;
pub struct CaptureLocalInAnonStructWrapperValueCombinator1(pub CaptureLocalInAnonStructWrapperValueCombinatorAlias1);
impl View for CaptureLocalInAnonStructWrapperValueCombinator1 {
    type V = SpecCaptureLocalInAnonStructWrapperValueCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureLocalInAnonStructWrapperValueCombinator1, CaptureLocalInAnonStructWrapperValueCombinatorAlias1);

pub struct CaptureLocalInAnonStructWrapperValueCombinator(pub CaptureLocalInAnonStructWrapperValueCombinatorAlias);

impl View for CaptureLocalInAnonStructWrapperValueCombinator {
    type V = SpecCaptureLocalInAnonStructWrapperValueCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructWrapperValueCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructWrapperValueCombinator {
    type Type = CaptureLocalInAnonStructWrapperValue<'a>;
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
pub type CaptureLocalInAnonStructWrapperValueCombinatorAlias = Mapped<CaptureLocalInAnonStructWrapperValueCombinator1, CaptureLocalInAnonStructWrapperValueMapper>;


pub open spec fn spec_capture_local_in_anon_struct_wrapper_value(tag: u8) -> SpecCaptureLocalInAnonStructWrapperValueCombinator {
    SpecCaptureLocalInAnonStructWrapperValueCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: spec_capture_local_in_anon_struct_wrapper_value_choice0() }, Cond { cond: !(tag == 0), inner: U16Le }), mapper: CaptureLocalInAnonStructWrapperValueMapper })
}

pub fn capture_local_in_anon_struct_wrapper_value<'a>(tag: u8) -> (o: CaptureLocalInAnonStructWrapperValueCombinator)

    ensures o@ == spec_capture_local_in_anon_struct_wrapper_value(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructWrapperValueCombinator(Mapped { inner: CaptureLocalInAnonStructWrapperValueCombinator1(Choice::new(Cond { cond: tag == 0, inner: capture_local_in_anon_struct_wrapper_value_choice0() }, Cond { cond: !(tag == 0), inner: U16Le })), mapper: CaptureLocalInAnonStructWrapperValueMapper });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_wrapper_value(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_wrapper_value<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<CaptureLocalInAnonStructWrapperValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_wrapper_value( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_wrapper_value<'a>(v: <CaptureLocalInAnonStructWrapperValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper_value(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_wrapper_value( tag );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_local_in_anon_struct_wrapper_value_infallible<'a>(v: <CaptureLocalInAnonStructWrapperValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper_value(tag@).wf(v@),
        spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@)),
{
    let combinator = capture_local_in_anon_struct_wrapper_value( tag );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_wrapper_value_len<'a>(v: <CaptureLocalInAnonStructWrapperValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_wrapper_value(tag@).wf(v@),
        spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_capture_local_in_anon_struct_wrapper_value(tag@).spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_wrapper_value( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecNestedInnerChoiceX {
    A(SpecNestedInnerChoiceXA),
    B(u32),
}

pub type SpecNestedInnerChoiceXInner = Either<SpecNestedInnerChoiceXA, u32>;

impl SpecFrom<SpecNestedInnerChoiceX> for SpecNestedInnerChoiceXInner {
    open spec fn spec_from(m: SpecNestedInnerChoiceX) -> SpecNestedInnerChoiceXInner {
        match m {
            SpecNestedInnerChoiceX::A(m) => Either::Left(m),
            SpecNestedInnerChoiceX::B(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecNestedInnerChoiceXInner> for SpecNestedInnerChoiceX {
    open spec fn spec_from(m: SpecNestedInnerChoiceXInner) -> SpecNestedInnerChoiceX {
        match m {
            Either::Left(m) => SpecNestedInnerChoiceX::A(m),
            Either::Right(m) => SpecNestedInnerChoiceX::B(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NestedInnerChoiceX {
    A(NestedInnerChoiceXA),
    B(u32),
}

pub type NestedInnerChoiceXInner = Either<NestedInnerChoiceXA, u32>;

pub type NestedInnerChoiceXInnerRef<'a> = Either<&'a NestedInnerChoiceXA, &'a u32>;


impl View for NestedInnerChoiceX {
    type V = SpecNestedInnerChoiceX;
    open spec fn view(&self) -> Self::V {
        match self {
            NestedInnerChoiceX::A(m) => SpecNestedInnerChoiceX::A(m@),
            NestedInnerChoiceX::B(m) => SpecNestedInnerChoiceX::B(m@),
        }
    }
}


impl<'a> From<&'a NestedInnerChoiceX> for NestedInnerChoiceXInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerChoiceX) -> NestedInnerChoiceXInnerRef<'a> {
        match m {
            NestedInnerChoiceX::A(m) => Either::Left(m),
            NestedInnerChoiceX::B(m) => Either::Right(m),
        }
    }

}

impl From<NestedInnerChoiceXInner> for NestedInnerChoiceX {
    fn ex_from(m: NestedInnerChoiceXInner) -> NestedInnerChoiceX {
        match m {
            Either::Left(m) => NestedInnerChoiceX::A(m),
            Either::Right(m) => NestedInnerChoiceX::B(m),
        }
    }
    
}


pub struct NestedInnerChoiceXMapper;
impl View for NestedInnerChoiceXMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerChoiceXMapper {
    type Src = SpecNestedInnerChoiceXInner;
    type Dst = SpecNestedInnerChoiceX;
}
impl SpecIsoProof for NestedInnerChoiceXMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerChoiceXMapper {
    type Src = NestedInnerChoiceXInner;
    type Dst = NestedInnerChoiceX;
    type RefSrc = NestedInnerChoiceXInnerRef<'a>;
}

type SpecNestedInnerChoiceXCombinatorAlias1 = Choice<Cond<SpecNestedInnerChoiceXACombinator>, Cond<U32Le>>;
pub struct SpecNestedInnerChoiceXCombinator(pub SpecNestedInnerChoiceXCombinatorAlias);

impl SpecCombinator for SpecNestedInnerChoiceXCombinator {
    type Type = SpecNestedInnerChoiceX;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerChoiceXCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerChoiceXCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerChoiceXCombinatorAlias = Mapped<SpecNestedInnerChoiceXCombinatorAlias1, NestedInnerChoiceXMapper>;
type NestedInnerChoiceXCombinatorAlias1 = Choice<Cond<NestedInnerChoiceXACombinator>, Cond<U32Le>>;
pub struct NestedInnerChoiceXCombinator1(pub NestedInnerChoiceXCombinatorAlias1);
impl View for NestedInnerChoiceXCombinator1 {
    type V = SpecNestedInnerChoiceXCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerChoiceXCombinator1, NestedInnerChoiceXCombinatorAlias1);

pub struct NestedInnerChoiceXCombinator(pub NestedInnerChoiceXCombinatorAlias);

impl View for NestedInnerChoiceXCombinator {
    type V = SpecNestedInnerChoiceXCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerChoiceXCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerChoiceXCombinator {
    type Type = NestedInnerChoiceX;
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
pub type NestedInnerChoiceXCombinatorAlias = Mapped<NestedInnerChoiceXCombinator1, NestedInnerChoiceXMapper>;


pub open spec fn spec_nested_inner_choice_x(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecNestedInnerChoiceXCombinator {
    SpecNestedInnerChoiceXCombinator(Mapped { inner: Choice(Cond { cond: choice1 == AOrB::A, inner: spec_nested_inner_choice_x_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: U32Le }), mapper: NestedInnerChoiceXMapper })
}

pub fn nested_inner_choice_x<'a>(choice1: AOrB, choice2: COrD) -> (o: NestedInnerChoiceXCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_nested_inner_choice_x(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerChoiceXCombinator(Mapped { inner: NestedInnerChoiceXCombinator1(Choice::new(Cond { cond: choice1 == AOrB::A, inner: nested_inner_choice_x_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: U32Le })), mapper: NestedInnerChoiceXMapper });
    // assert({
    //     &&& combinator@ == spec_nested_inner_choice_x(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_choice_x<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<NestedInnerChoiceXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_choice_x(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_choice_x(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_choice_x(choice1@, choice2@).spec_parse(input@) is None,
        spec_nested_inner_choice_x(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_choice_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_choice_x<'a>(v: <NestedInnerChoiceXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_choice_x( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_nested_inner_choice_x_infallible<'a>(v: <NestedInnerChoiceXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),
        spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@)),
{
    let combinator = nested_inner_choice_x( choice1, choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn nested_inner_choice_x_len<'a>(v: <NestedInnerChoiceXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_nested_inner_choice_x(choice1@, choice2@).wf(v@),
        spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_nested_inner_choice_x(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_choice_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecNestedInnerChoice {
    pub x: SpecNestedInnerChoiceX,
}

pub type SpecNestedInnerChoiceInner = SpecNestedInnerChoiceX;


impl SpecFrom<SpecNestedInnerChoice> for SpecNestedInnerChoiceInner {
    open spec fn spec_from(m: SpecNestedInnerChoice) -> SpecNestedInnerChoiceInner {
        m.x
    }
}

impl SpecFrom<SpecNestedInnerChoiceInner> for SpecNestedInnerChoice {
    open spec fn spec_from(m: SpecNestedInnerChoiceInner) -> SpecNestedInnerChoice {
        let x = m;
        SpecNestedInnerChoice { x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NestedInnerChoice {
    pub x: NestedInnerChoiceX,
}

impl View for NestedInnerChoice {
    type V = SpecNestedInnerChoice;

    open spec fn view(&self) -> Self::V {
        SpecNestedInnerChoice {
            x: self.x@,
        }
    }
}
pub type NestedInnerChoiceInner = NestedInnerChoiceX;

pub type NestedInnerChoiceInnerRef<'a> = &'a NestedInnerChoiceX;
impl<'a> From<&'a NestedInnerChoice> for NestedInnerChoiceInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerChoice) -> NestedInnerChoiceInnerRef<'a> {
        &m.x
    }
}

impl From<NestedInnerChoiceInner> for NestedInnerChoice {
    fn ex_from(m: NestedInnerChoiceInner) -> NestedInnerChoice {
        let x = m;
        NestedInnerChoice { x }
    }
}

pub struct NestedInnerChoiceMapper;
impl View for NestedInnerChoiceMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerChoiceMapper {
    type Src = SpecNestedInnerChoiceInner;
    type Dst = SpecNestedInnerChoice;
}
impl SpecIsoProof for NestedInnerChoiceMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerChoiceMapper {
    type Src = NestedInnerChoiceInner;
    type Dst = NestedInnerChoice;
    type RefSrc = NestedInnerChoiceInnerRef<'a>;
}

pub struct SpecNestedInnerChoiceCombinator(pub SpecNestedInnerChoiceCombinatorAlias);

impl SpecCombinator for SpecNestedInnerChoiceCombinator {
    type Type = SpecNestedInnerChoice;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerChoiceCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerChoiceCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerChoiceCombinatorAlias = Mapped<SpecNestedInnerChoiceXCombinator, NestedInnerChoiceMapper>;

pub struct NestedInnerChoiceCombinator(pub NestedInnerChoiceCombinatorAlias);

impl View for NestedInnerChoiceCombinator {
    type V = SpecNestedInnerChoiceCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerChoiceCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerChoiceCombinator {
    type Type = NestedInnerChoice;
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
pub type NestedInnerChoiceCombinatorAlias = Mapped<NestedInnerChoiceXCombinator, NestedInnerChoiceMapper>;


pub open spec fn spec_nested_inner_choice(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecNestedInnerChoiceCombinator {
    SpecNestedInnerChoiceCombinator(
    Mapped {
        inner: spec_nested_inner_choice_x(choice1, choice2),
        mapper: NestedInnerChoiceMapper,
    })
}

pub fn nested_inner_choice<'a>(choice1: AOrB, choice2: COrD) -> (o: NestedInnerChoiceCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_nested_inner_choice(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerChoiceCombinator(
    Mapped {
        inner: nested_inner_choice_x(choice1, choice2),
        mapper: NestedInnerChoiceMapper,
    });
    // assert({
    //     &&& combinator@ == spec_nested_inner_choice(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_choice<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<NestedInnerChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_choice(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_choice(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_choice(choice1@, choice2@).spec_parse(input@) is None,
        spec_nested_inner_choice(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_choice( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_choice<'a>(v: <NestedInnerChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_choice( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_nested_inner_choice_infallible<'a>(v: <NestedInnerChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),
        spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@)),
{
    let combinator = nested_inner_choice( choice1, choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn nested_inner_choice_len<'a>(v: <NestedInnerChoiceCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_nested_inner_choice(choice1@, choice2@).wf(v@),
        spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_nested_inner_choice(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_choice( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureParamAndLocal {
    pub x: SpecCaptureParamAndLocalX,
}

pub type SpecCaptureParamAndLocalInner = SpecCaptureParamAndLocalX;


impl SpecFrom<SpecCaptureParamAndLocal> for SpecCaptureParamAndLocalInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocal) -> SpecCaptureParamAndLocalInner {
        m.x
    }
}

impl SpecFrom<SpecCaptureParamAndLocalInner> for SpecCaptureParamAndLocal {
    open spec fn spec_from(m: SpecCaptureParamAndLocalInner) -> SpecCaptureParamAndLocal {
        let x = m;
        SpecCaptureParamAndLocal { x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureParamAndLocal<'a> {
    pub x: CaptureParamAndLocalX<'a>,
}

impl View for CaptureParamAndLocal<'_> {
    type V = SpecCaptureParamAndLocal;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocal {
            x: self.x@,
        }
    }
}
pub type CaptureParamAndLocalInner<'a> = CaptureParamAndLocalX<'a>;

pub type CaptureParamAndLocalInnerRef<'a> = &'a CaptureParamAndLocalX<'a>;
impl<'a> From<&'a CaptureParamAndLocal<'a>> for CaptureParamAndLocalInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocal) -> CaptureParamAndLocalInnerRef<'a> {
        &m.x
    }
}

impl<'a> From<CaptureParamAndLocalInner<'a>> for CaptureParamAndLocal<'a> {
    fn ex_from(m: CaptureParamAndLocalInner) -> CaptureParamAndLocal {
        let x = m;
        CaptureParamAndLocal { x }
    }
}

pub struct CaptureParamAndLocalMapper;
impl View for CaptureParamAndLocalMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalMapper {
    type Src = SpecCaptureParamAndLocalInner;
    type Dst = SpecCaptureParamAndLocal;
}
impl SpecIsoProof for CaptureParamAndLocalMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalMapper {
    type Src = CaptureParamAndLocalInner<'a>;
    type Dst = CaptureParamAndLocal<'a>;
    type RefSrc = CaptureParamAndLocalInnerRef<'a>;
}

pub struct SpecCaptureParamAndLocalCombinator(pub SpecCaptureParamAndLocalCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalCombinator {
    type Type = SpecCaptureParamAndLocal;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalCombinatorAlias = Mapped<SpecCaptureParamAndLocalXCombinator, CaptureParamAndLocalMapper>;

pub struct CaptureParamAndLocalCombinator(pub CaptureParamAndLocalCombinatorAlias);

impl View for CaptureParamAndLocalCombinator {
    type V = SpecCaptureParamAndLocalCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalCombinator {
    type Type = CaptureParamAndLocal<'a>;
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
pub type CaptureParamAndLocalCombinatorAlias = Mapped<CaptureParamAndLocalXCombinator, CaptureParamAndLocalMapper>;


pub open spec fn spec_capture_param_and_local(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecCaptureParamAndLocalCombinator {
    SpecCaptureParamAndLocalCombinator(
    Mapped {
        inner: spec_capture_param_and_local_x(choice1, choice2),
        mapper: CaptureParamAndLocalMapper,
    })
}

pub fn capture_param_and_local<'a>(choice1: AOrB, choice2: COrD) -> (o: CaptureParamAndLocalCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalCombinator(
    Mapped {
        inner: capture_param_and_local_x(choice1, choice2),
        mapper: CaptureParamAndLocalMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<CaptureParamAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local(choice1@, choice2@).spec_parse(input@) is None,
        spec_capture_param_and_local(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local<'a>(v: <CaptureParamAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn serialize_capture_param_and_local_infallible<'a>(v: <CaptureParamAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),
        spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@)),
{
    let combinator = capture_param_and_local( choice1, choice2 );
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_param_and_local_len<'a>(v: <CaptureParamAndLocalCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local(choice1@, choice2@).wf(v@),
        spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecNestedInnerStruct {
    pub len: u32,
    pub inner: SpecNestedInnerStructAnonInner,
}

pub type SpecNestedInnerStructInner = (u32, SpecNestedInnerStructAnonInner);


impl SpecFrom<SpecNestedInnerStruct> for SpecNestedInnerStructInner {
    open spec fn spec_from(m: SpecNestedInnerStruct) -> SpecNestedInnerStructInner {
        (m.len, m.inner)
    }
}

impl SpecFrom<SpecNestedInnerStructInner> for SpecNestedInnerStruct {
    open spec fn spec_from(m: SpecNestedInnerStructInner) -> SpecNestedInnerStruct {
        let (len, inner) = m;
        SpecNestedInnerStruct { len, inner }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NestedInnerStruct<'a> {
    pub len: u32,
    pub inner: NestedInnerStructAnonInner<'a>,
}

impl View for NestedInnerStruct<'_> {
    type V = SpecNestedInnerStruct;

    open spec fn view(&self) -> Self::V {
        SpecNestedInnerStruct {
            len: self.len@,
            inner: self.inner@,
        }
    }
}
pub type NestedInnerStructInner<'a> = (u32, NestedInnerStructAnonInner<'a>);

pub type NestedInnerStructInnerRef<'a> = (&'a u32, &'a NestedInnerStructAnonInner<'a>);
impl<'a> From<&'a NestedInnerStruct<'a>> for NestedInnerStructInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerStruct) -> NestedInnerStructInnerRef<'a> {
        (&m.len, &m.inner)
    }
}

impl<'a> From<NestedInnerStructInner<'a>> for NestedInnerStruct<'a> {
    fn ex_from(m: NestedInnerStructInner) -> NestedInnerStruct {
        let (len, inner) = m;
        NestedInnerStruct { len, inner }
    }
}

pub struct NestedInnerStructMapper;
impl View for NestedInnerStructMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerStructMapper {
    type Src = SpecNestedInnerStructInner;
    type Dst = SpecNestedInnerStruct;
}
impl SpecIsoProof for NestedInnerStructMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerStructMapper {
    type Src = NestedInnerStructInner<'a>;
    type Dst = NestedInnerStruct<'a>;
    type RefSrc = NestedInnerStructInnerRef<'a>;
}

pub struct SpecNestedInnerStructCombinator(pub SpecNestedInnerStructCombinatorAlias);

impl SpecCombinator for SpecNestedInnerStructCombinator {
    type Type = SpecNestedInnerStruct;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerStructCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerStructCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerStructCombinatorAlias = Mapped<SpecPair<U32Le, SpecNestedInnerStructAnonInnerCombinator>, NestedInnerStructMapper>;

pub struct NestedInnerStructCombinator(pub NestedInnerStructCombinatorAlias);

impl View for NestedInnerStructCombinator {
    type V = SpecNestedInnerStructCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerStructCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerStructCombinator {
    type Type = NestedInnerStruct<'a>;
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
pub type NestedInnerStructCombinatorAlias = Mapped<Pair<U32Le, NestedInnerStructAnonInnerCombinator, NestedInnerStructCont0>, NestedInnerStructMapper>;


pub open spec fn spec_nested_inner_struct() -> SpecNestedInnerStructCombinator {
    SpecNestedInnerStructCombinator(
    Mapped {
        inner: Pair::spec_new(U32Le, |deps| spec_nested_inner_struct_cont0(deps)),
        mapper: NestedInnerStructMapper,
    })
}

pub open spec fn spec_nested_inner_struct_cont0(deps: u32) -> SpecNestedInnerStructAnonInnerCombinator {
    let len = deps;
    spec_nested_inner_struct_anon_inner(len)
}

impl View for NestedInnerStructCont0 {
    type V = spec_fn(u32) -> SpecNestedInnerStructAnonInnerCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u32| {
            spec_nested_inner_struct_cont0(deps)
        }
    }
}

                
pub fn nested_inner_struct<'a>() -> (o: NestedInnerStructCombinator)
    ensures o@ == spec_nested_inner_struct(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerStructCombinator(
    Mapped {
        inner: Pair::new(U32Le, NestedInnerStructCont0),
        mapper: NestedInnerStructMapper,
    });
    // assert({
    //     &&& combinator@ == spec_nested_inner_struct()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_struct<'a>(input: &'a [u8]) -> (res: PResult<<NestedInnerStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_struct().spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_struct().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_struct().spec_parse(input@) is None,
        spec_nested_inner_struct().spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_struct<'a>(v: <NestedInnerStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_struct().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_struct().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_struct().spec_serialize(v@))
        },
{
    let combinator = nested_inner_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_nested_inner_struct_infallible<'a>(v: <NestedInnerStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_struct().wf(v@),
        spec_nested_inner_struct().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_nested_inner_struct().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_nested_inner_struct().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_nested_inner_struct().spec_serialize(v@)),
{
    let combinator = nested_inner_struct();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn nested_inner_struct_len<'a>(v: <NestedInnerStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_nested_inner_struct().wf(v@),
        spec_nested_inner_struct().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_nested_inner_struct().spec_serialize(v@).len(),
{
    let combinator = nested_inner_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct NestedInnerStructCont0;
type NestedInnerStructCont0Type<'a, 'b> = &'b u32;
type NestedInnerStructCont0SType<'a, 'x> = &'x u32;
type NestedInnerStructCont0Input<'a, 'b, 'x> = POrSType<NestedInnerStructCont0Type<'a, 'b>, NestedInnerStructCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<NestedInnerStructCont0Input<'a, 'b, 'x>> for NestedInnerStructCont0 {
    type Output = NestedInnerStructAnonInnerCombinator;

    open spec fn requires(&self, deps: NestedInnerStructCont0Input<'a, 'b, 'x>) -> bool {
        &&& (U32Le).wf(deps@)
        }

    open spec fn ensures(&self, deps: NestedInnerStructCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_nested_inner_struct_cont0(deps@)
    }

    fn apply(&self, deps: NestedInnerStructCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = deps;
                let len = *len;
                nested_inner_struct_anon_inner(len)
            }
            POrSType::S(deps) => {
                let len = deps;
                let len = *len;
                nested_inner_struct_anon_inner(len)
            }
        }
    }
}
                

pub spec const SPEC_COrD_C: u8 = 1;
pub spec const SPEC_COrD_D: u8 = 2;
pub exec static EXEC_COrD_C: u8 ensures EXEC_COrD_C == SPEC_COrD_C { 1 }
pub exec static EXEC_COrD_D: u8 ensures EXEC_COrD_D == SPEC_COrD_D { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum COrD {
    C = 1,
D = 2
}
pub type SpecCOrD = COrD;

pub type COrDInner = u8;

pub type COrDInnerRef<'a> = &'a u8;

impl View for COrD {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<COrDInner> for COrD {
    type Error = ();

    open spec fn spec_try_from(v: COrDInner) -> Result<COrD, ()> {
        match v {
            1u8 => Ok(COrD::C),
            2u8 => Ok(COrD::D),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<COrD> for COrDInner {
    type Error = ();

    open spec fn spec_try_from(v: COrD) -> Result<COrDInner, ()> {
        match v {
            COrD::C => Ok(SPEC_COrD_C),
            COrD::D => Ok(SPEC_COrD_D),
        }
    }
}

impl TryFrom<COrDInner> for COrD {
    type Error = ();

    fn ex_try_from(v: COrDInner) -> Result<COrD, ()> {
        match v {
            1u8 => Ok(COrD::C),
            2u8 => Ok(COrD::D),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a COrD> for COrDInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a COrD) -> Result<COrDInnerRef<'a>, ()> {
        match v {
            COrD::C => Ok(&EXEC_COrD_C),
            COrD::D => Ok(&EXEC_COrD_D),
        }
    }
}

pub struct COrDMapper;

impl View for COrDMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for COrDMapper {
    type Src = COrDInner;
    type Dst = COrD;
}

impl SpecPartialIsoProof for COrDMapper {
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

impl<'a> PartialIso<'a> for COrDMapper {
    type Src = COrDInner;
    type Dst = COrD;
    type RefSrc = COrDInnerRef<'a>;
}


pub struct SpecCOrDCombinator(pub SpecCOrDCombinatorAlias);

impl SpecCombinator for SpecCOrDCombinator {
    type Type = SpecCOrD;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCOrDCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCOrDCombinatorAlias::is_prefix_secure() }
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
pub type SpecCOrDCombinatorAlias = TryMap<U8, COrDMapper>;

pub struct COrDCombinator(pub COrDCombinatorAlias);

impl View for COrDCombinator {
    type V = SpecCOrDCombinator;
    open spec fn view(&self) -> Self::V { SpecCOrDCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for COrDCombinator {
    type Type = COrD;
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
pub type COrDCombinatorAlias = TryMap<U8, COrDMapper>;


pub open spec fn spec_c_or_d() -> SpecCOrDCombinator {
    SpecCOrDCombinator(TryMap { inner: U8, mapper: COrDMapper })
}

                
pub fn c_or_d<'a>() -> (o: COrDCombinator)
    ensures o@ == spec_c_or_d(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = COrDCombinator(TryMap { inner: U8, mapper: COrDMapper });
    // assert({
    //     &&& combinator@ == spec_c_or_d()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_c_or_d<'a>(input: &'a [u8]) -> (res: PResult<<COrDCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_c_or_d().spec_parse(input@) == Some((n as int, v@)),
        spec_c_or_d().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_c_or_d().spec_parse(input@) is None,
        spec_c_or_d().spec_parse(input@) is None ==> res is Err,
{
    let combinator = c_or_d();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_c_or_d<'a>(v: <COrDCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_c_or_d().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_c_or_d().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_c_or_d().spec_serialize(v@))
        },
{
    let combinator = c_or_d();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_c_or_d_infallible<'a>(v: <COrDCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_c_or_d().wf(v@),
        spec_c_or_d().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_c_or_d().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_c_or_d().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_c_or_d().spec_serialize(v@)),
{
    let combinator = c_or_d();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn c_or_d_len<'a>(v: <COrDCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_c_or_d().wf(v@),
        spec_c_or_d().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_c_or_d().spec_serialize(v@).len(),
{
    let combinator = c_or_d();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecCaptureLocalInAnonStructWrapper {
    pub tag: u8,
    pub value: SpecCaptureLocalInAnonStructWrapperValue,
}

pub type SpecCaptureLocalInAnonStructWrapperInner = (u8, SpecCaptureLocalInAnonStructWrapperValue);


impl SpecFrom<SpecCaptureLocalInAnonStructWrapper> for SpecCaptureLocalInAnonStructWrapperInner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapper) -> SpecCaptureLocalInAnonStructWrapperInner {
        (m.tag, m.value)
    }
}

impl SpecFrom<SpecCaptureLocalInAnonStructWrapperInner> for SpecCaptureLocalInAnonStructWrapper {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructWrapperInner) -> SpecCaptureLocalInAnonStructWrapper {
        let (tag, value) = m;
        SpecCaptureLocalInAnonStructWrapper { tag, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureLocalInAnonStructWrapper<'a> {
    pub tag: u8,
    pub value: CaptureLocalInAnonStructWrapperValue<'a>,
}

impl View for CaptureLocalInAnonStructWrapper<'_> {
    type V = SpecCaptureLocalInAnonStructWrapper;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStructWrapper {
            tag: self.tag@,
            value: self.value@,
        }
    }
}
pub type CaptureLocalInAnonStructWrapperInner<'a> = (u8, CaptureLocalInAnonStructWrapperValue<'a>);

pub type CaptureLocalInAnonStructWrapperInnerRef<'a> = (&'a u8, &'a CaptureLocalInAnonStructWrapperValue<'a>);
impl<'a> From<&'a CaptureLocalInAnonStructWrapper<'a>> for CaptureLocalInAnonStructWrapperInnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructWrapper) -> CaptureLocalInAnonStructWrapperInnerRef<'a> {
        (&m.tag, &m.value)
    }
}

impl<'a> From<CaptureLocalInAnonStructWrapperInner<'a>> for CaptureLocalInAnonStructWrapper<'a> {
    fn ex_from(m: CaptureLocalInAnonStructWrapperInner) -> CaptureLocalInAnonStructWrapper {
        let (tag, value) = m;
        CaptureLocalInAnonStructWrapper { tag, value }
    }
}

pub struct CaptureLocalInAnonStructWrapperMapper;
impl View for CaptureLocalInAnonStructWrapperMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructWrapperMapper {
    type Src = SpecCaptureLocalInAnonStructWrapperInner;
    type Dst = SpecCaptureLocalInAnonStructWrapper;
}
impl SpecIsoProof for CaptureLocalInAnonStructWrapperMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructWrapperMapper {
    type Src = CaptureLocalInAnonStructWrapperInner<'a>;
    type Dst = CaptureLocalInAnonStructWrapper<'a>;
    type RefSrc = CaptureLocalInAnonStructWrapperInnerRef<'a>;
}

pub struct SpecCaptureLocalInAnonStructWrapperCombinator(pub SpecCaptureLocalInAnonStructWrapperCombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructWrapperCombinator {
    type Type = SpecCaptureLocalInAnonStructWrapper;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructWrapperCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructWrapperCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructWrapperCombinatorAlias = Mapped<SpecPair<U8, SpecCaptureLocalInAnonStructWrapperValueCombinator>, CaptureLocalInAnonStructWrapperMapper>;

pub struct CaptureLocalInAnonStructWrapperCombinator(pub CaptureLocalInAnonStructWrapperCombinatorAlias);

impl View for CaptureLocalInAnonStructWrapperCombinator {
    type V = SpecCaptureLocalInAnonStructWrapperCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructWrapperCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructWrapperCombinator {
    type Type = CaptureLocalInAnonStructWrapper<'a>;
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
pub type CaptureLocalInAnonStructWrapperCombinatorAlias = Mapped<Pair<U8, CaptureLocalInAnonStructWrapperValueCombinator, CaptureLocalInAnonStructWrapperCont0>, CaptureLocalInAnonStructWrapperMapper>;


pub open spec fn spec_capture_local_in_anon_struct_wrapper() -> SpecCaptureLocalInAnonStructWrapperCombinator {
    SpecCaptureLocalInAnonStructWrapperCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_local_in_anon_struct_wrapper_cont0(deps)),
        mapper: CaptureLocalInAnonStructWrapperMapper,
    })
}

pub open spec fn spec_capture_local_in_anon_struct_wrapper_cont0(deps: u8) -> SpecCaptureLocalInAnonStructWrapperValueCombinator {
    let tag = deps;
    spec_capture_local_in_anon_struct_wrapper_value(tag)
}

impl View for CaptureLocalInAnonStructWrapperCont0 {
    type V = spec_fn(u8) -> SpecCaptureLocalInAnonStructWrapperValueCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_local_in_anon_struct_wrapper_cont0(deps)
        }
    }
}

                
pub fn capture_local_in_anon_struct_wrapper<'a>() -> (o: CaptureLocalInAnonStructWrapperCombinator)
    ensures o@ == spec_capture_local_in_anon_struct_wrapper(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructWrapperCombinator(
    Mapped {
        inner: Pair::new(U8, CaptureLocalInAnonStructWrapperCont0),
        mapper: CaptureLocalInAnonStructWrapperMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_wrapper()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_wrapper<'a>(input: &'a [u8]) -> (res: PResult<<CaptureLocalInAnonStructWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_wrapper().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_wrapper().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_wrapper().spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_wrapper().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_wrapper<'a>(v: <CaptureLocalInAnonStructWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_local_in_anon_struct_wrapper_infallible<'a>(v: <CaptureLocalInAnonStructWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_wrapper().wf(v@),
        spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@)),
{
    let combinator = capture_local_in_anon_struct_wrapper();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_wrapper_len<'a>(v: <CaptureLocalInAnonStructWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_wrapper().wf(v@),
        spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_local_in_anon_struct_wrapper().spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureLocalInAnonStructWrapperCont0;
type CaptureLocalInAnonStructWrapperCont0Type<'a, 'b> = &'b u8;
type CaptureLocalInAnonStructWrapperCont0SType<'a, 'x> = &'x u8;
type CaptureLocalInAnonStructWrapperCont0Input<'a, 'b, 'x> = POrSType<CaptureLocalInAnonStructWrapperCont0Type<'a, 'b>, CaptureLocalInAnonStructWrapperCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureLocalInAnonStructWrapperCont0Input<'a, 'b, 'x>> for CaptureLocalInAnonStructWrapperCont0 {
    type Output = CaptureLocalInAnonStructWrapperValueCombinator;

    open spec fn requires(&self, deps: CaptureLocalInAnonStructWrapperCont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureLocalInAnonStructWrapperCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_local_in_anon_struct_wrapper_cont0(deps@)
    }

    fn apply(&self, deps: CaptureLocalInAnonStructWrapperCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_local_in_anon_struct_wrapper_value(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_local_in_anon_struct_wrapper_value(tag)
            }
        }
    }
}
                

pub struct SpecCaptureLocalInAnonStruct {
    pub wrapper: SpecCaptureLocalInAnonStructWrapper,
}

pub type SpecCaptureLocalInAnonStructInner = SpecCaptureLocalInAnonStructWrapper;


impl SpecFrom<SpecCaptureLocalInAnonStruct> for SpecCaptureLocalInAnonStructInner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStruct) -> SpecCaptureLocalInAnonStructInner {
        m.wrapper
    }
}

impl SpecFrom<SpecCaptureLocalInAnonStructInner> for SpecCaptureLocalInAnonStruct {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructInner) -> SpecCaptureLocalInAnonStruct {
        let wrapper = m;
        SpecCaptureLocalInAnonStruct { wrapper }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureLocalInAnonStruct<'a> {
    pub wrapper: CaptureLocalInAnonStructWrapper<'a>,
}

impl View for CaptureLocalInAnonStruct<'_> {
    type V = SpecCaptureLocalInAnonStruct;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStruct {
            wrapper: self.wrapper@,
        }
    }
}
pub type CaptureLocalInAnonStructInner<'a> = CaptureLocalInAnonStructWrapper<'a>;

pub type CaptureLocalInAnonStructInnerRef<'a> = &'a CaptureLocalInAnonStructWrapper<'a>;
impl<'a> From<&'a CaptureLocalInAnonStruct<'a>> for CaptureLocalInAnonStructInnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStruct) -> CaptureLocalInAnonStructInnerRef<'a> {
        &m.wrapper
    }
}

impl<'a> From<CaptureLocalInAnonStructInner<'a>> for CaptureLocalInAnonStruct<'a> {
    fn ex_from(m: CaptureLocalInAnonStructInner) -> CaptureLocalInAnonStruct {
        let wrapper = m;
        CaptureLocalInAnonStruct { wrapper }
    }
}

pub struct CaptureLocalInAnonStructMapper;
impl View for CaptureLocalInAnonStructMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructMapper {
    type Src = SpecCaptureLocalInAnonStructInner;
    type Dst = SpecCaptureLocalInAnonStruct;
}
impl SpecIsoProof for CaptureLocalInAnonStructMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructMapper {
    type Src = CaptureLocalInAnonStructInner<'a>;
    type Dst = CaptureLocalInAnonStruct<'a>;
    type RefSrc = CaptureLocalInAnonStructInnerRef<'a>;
}

pub struct SpecCaptureLocalInAnonStructCombinator(pub SpecCaptureLocalInAnonStructCombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructCombinator {
    type Type = SpecCaptureLocalInAnonStruct;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructCombinatorAlias = Mapped<SpecCaptureLocalInAnonStructWrapperCombinator, CaptureLocalInAnonStructMapper>;

pub struct CaptureLocalInAnonStructCombinator(pub CaptureLocalInAnonStructCombinatorAlias);

impl View for CaptureLocalInAnonStructCombinator {
    type V = SpecCaptureLocalInAnonStructCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructCombinator {
    type Type = CaptureLocalInAnonStruct<'a>;
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
pub type CaptureLocalInAnonStructCombinatorAlias = Mapped<CaptureLocalInAnonStructWrapperCombinator, CaptureLocalInAnonStructMapper>;


pub open spec fn spec_capture_local_in_anon_struct() -> SpecCaptureLocalInAnonStructCombinator {
    SpecCaptureLocalInAnonStructCombinator(
    Mapped {
        inner: spec_capture_local_in_anon_struct_wrapper(),
        mapper: CaptureLocalInAnonStructMapper,
    })
}

                
pub fn capture_local_in_anon_struct<'a>() -> (o: CaptureLocalInAnonStructCombinator)
    ensures o@ == spec_capture_local_in_anon_struct(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructCombinator(
    Mapped {
        inner: capture_local_in_anon_struct_wrapper(),
        mapper: CaptureLocalInAnonStructMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct<'a>(input: &'a [u8]) -> (res: PResult<<CaptureLocalInAnonStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct().spec_parse(input@) is None,
        spec_capture_local_in_anon_struct().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct<'a>(v: <CaptureLocalInAnonStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct().spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_capture_local_in_anon_struct_infallible<'a>(v: <CaptureLocalInAnonStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct().wf(v@),
        spec_capture_local_in_anon_struct().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_capture_local_in_anon_struct().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_capture_local_in_anon_struct().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct().spec_serialize(v@)),
{
    let combinator = capture_local_in_anon_struct();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_len<'a>(v: <CaptureLocalInAnonStructCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct().wf(v@),
        spec_capture_local_in_anon_struct().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_local_in_anon_struct().spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub spec const SPEC_AOrB_A: u8 = 1;
pub spec const SPEC_AOrB_B: u8 = 2;
pub exec static EXEC_AOrB_A: u8 ensures EXEC_AOrB_A == SPEC_AOrB_A { 1 }
pub exec static EXEC_AOrB_B: u8 ensures EXEC_AOrB_B == SPEC_AOrB_B { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AOrB {
    A = 1,
B = 2
}
pub type SpecAOrB = AOrB;

pub type AOrBInner = u8;

pub type AOrBInnerRef<'a> = &'a u8;

impl View for AOrB {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AOrBInner> for AOrB {
    type Error = ();

    open spec fn spec_try_from(v: AOrBInner) -> Result<AOrB, ()> {
        match v {
            1u8 => Ok(AOrB::A),
            2u8 => Ok(AOrB::B),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AOrB> for AOrBInner {
    type Error = ();

    open spec fn spec_try_from(v: AOrB) -> Result<AOrBInner, ()> {
        match v {
            AOrB::A => Ok(SPEC_AOrB_A),
            AOrB::B => Ok(SPEC_AOrB_B),
        }
    }
}

impl TryFrom<AOrBInner> for AOrB {
    type Error = ();

    fn ex_try_from(v: AOrBInner) -> Result<AOrB, ()> {
        match v {
            1u8 => Ok(AOrB::A),
            2u8 => Ok(AOrB::B),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a AOrB> for AOrBInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AOrB) -> Result<AOrBInnerRef<'a>, ()> {
        match v {
            AOrB::A => Ok(&EXEC_AOrB_A),
            AOrB::B => Ok(&EXEC_AOrB_B),
        }
    }
}

pub struct AOrBMapper;

impl View for AOrBMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for AOrBMapper {
    type Src = AOrBInner;
    type Dst = AOrB;
}

impl SpecPartialIsoProof for AOrBMapper {
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

impl<'a> PartialIso<'a> for AOrBMapper {
    type Src = AOrBInner;
    type Dst = AOrB;
    type RefSrc = AOrBInnerRef<'a>;
}


pub struct SpecAOrBCombinator(pub SpecAOrBCombinatorAlias);

impl SpecCombinator for SpecAOrBCombinator {
    type Type = SpecAOrB;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAOrBCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecAOrBCombinatorAlias::is_prefix_secure() }
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
pub type SpecAOrBCombinatorAlias = TryMap<U8, AOrBMapper>;

pub struct AOrBCombinator(pub AOrBCombinatorAlias);

impl View for AOrBCombinator {
    type V = SpecAOrBCombinator;
    open spec fn view(&self) -> Self::V { SpecAOrBCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AOrBCombinator {
    type Type = AOrB;
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
pub type AOrBCombinatorAlias = TryMap<U8, AOrBMapper>;


pub open spec fn spec_a_or_b() -> SpecAOrBCombinator {
    SpecAOrBCombinator(TryMap { inner: U8, mapper: AOrBMapper })
}

                
pub fn a_or_b<'a>() -> (o: AOrBCombinator)
    ensures o@ == spec_a_or_b(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = AOrBCombinator(TryMap { inner: U8, mapper: AOrBMapper });
    // assert({
    //     &&& combinator@ == spec_a_or_b()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_a_or_b<'a>(input: &'a [u8]) -> (res: PResult<<AOrBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_a_or_b().spec_parse(input@) == Some((n as int, v@)),
        spec_a_or_b().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_a_or_b().spec_parse(input@) is None,
        spec_a_or_b().spec_parse(input@) is None ==> res is Err,
{
    let combinator = a_or_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_a_or_b<'a>(v: <AOrBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_or_b().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_a_or_b().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_a_or_b().spec_serialize(v@))
        },
{
    let combinator = a_or_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn serialize_a_or_b_infallible<'a>(v: <AOrBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (n: usize)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_a_or_b().wf(v@),
        spec_a_or_b().spec_serialize(v@).len() <= usize::MAX,
        pos + spec_a_or_b().spec_serialize(v@).len() <= old(data)@.len(),
    ensures
        data@.len() == old(data)@.len(),
        pos <= usize::MAX - n && pos + n <= data@.len(),
        n == spec_a_or_b().spec_serialize(v@).len(),
        data@ == seq_splice(old(data)@, pos, spec_a_or_b().spec_serialize(v@)),
{
    let combinator = a_or_b();
    serialize_infallible(&combinator, v, data, pos)
}

pub fn a_or_b_len<'a>(v: <AOrBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_a_or_b().wf(v@),
        spec_a_or_b().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_a_or_b().spec_serialize(v@).len(),
{
    let combinator = a_or_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
