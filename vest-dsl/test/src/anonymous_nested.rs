
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

pub struct SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 {
    pub count: u8,
    pub items: Seq<u8>,
}

pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner = (u8, Seq<u8>);


impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1> for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner {
        (m.count, m.items)
    }
}

impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner> for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 {
        let (count, items) = m;
        SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 { count, items }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a> {
    pub count: u8,
    pub items: &'a [u8],
}

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'_> {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1;

    open spec fn view(&self) -> Self::V {
        SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 {
            count: self.count@,
            items: self.items@,
        }
    }
}
pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner<'a> = (u8, &'a [u8]);

pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1InnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1InnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1) -> CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1InnerRef<'a> {
        (&m.count, &m.items)
    }
}

impl<'a> From<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner<'a>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a> {
    fn ex_from(m: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner) -> CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 {
        let (count, items) = m;
        CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1 { count, items }
    }
}

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper;
impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper {
    type Src = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner;
    type Dst = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1;
}
impl SpecIsoProof for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper {
    type Src = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Inner<'a>;
    type Dst = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>;
    type RefSrc = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1InnerRef<'a>;
}

pub struct SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator(pub SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1CombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator {
    type Type = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1CombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1CombinatorAlias = Mapped<SpecPair<U8, bytes::Variable>, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper>;

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator(pub CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1CombinatorAlias);

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator {
    type Type = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>;
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
pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1CombinatorAlias = Mapped<Pair<U8, bytes::Variable, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0>, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper>;


pub open spec fn spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1() -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator {
    SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1_cont0(deps)),
        mapper: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper,
    })
}

pub open spec fn spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1_cont0(deps: u8) -> bytes::Variable {
    let count = deps;
    bytes::Variable((usize::spec_from(count)) as usize)
}

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1_cont0(deps)
        }
    }
}

                
pub fn capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1<'a>() -> (o: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator)
    ensures o@ == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator(
    Mapped {
        inner: Pair::new(U8, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0),
        mapper: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1<'a>(input: &'a [u8]) -> (res: PResult<<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_parse(input@) is None,
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1_len<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().wf(v@),
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1().spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0;
type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Type<'a, 'b> = &'b u8;
type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0SType<'a, 'x> = &'x u8;
type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Input<'a, 'b, 'x> = POrSType<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Type<'a, 'b>, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Input<'a, 'b, 'x>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1_cont0(deps@)
    }

    fn apply(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Cont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub enum SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody {
    Variant0(Seq<u8>),
    Variant1(SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1),
}

pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner = Either<Seq<u8>, SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1>;

impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody> for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner {
        match m {
            SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m) => Either::Left(m),
            SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner> for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody {
        match m {
            Either::Left(m) => SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m),
            Either::Right(m) => SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a> {
    Variant0(&'a [u8]),
    Variant1(CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>),
}

pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner<'a> = Either<&'a [u8], CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>>;

pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInnerRef<'a> = Either<&'a &'a [u8], &'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1<'a>>;


impl<'a> View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a> {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m) => SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m@),
            CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m) => SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>) -> CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInnerRef<'a> {
        match m {
            CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m) => Either::Left(m),
            CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner<'a>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a> {
    fn ex_from(m: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner<'a>) -> CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a> {
        match m {
            Either::Left(m) => CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant0(m),
            Either::Right(m) => CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody::Variant1(m),
        }
    }
    
}


pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper;
impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper {
    type Src = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner;
    type Dst = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody;
}
impl SpecIsoProof for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper {
    type Src = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInner<'a>;
    type Dst = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>;
    type RefSrc = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyInnerRef<'a>;
}

type SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator>>;
pub struct SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator(pub SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    type Type = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias = Mapped<SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper>;
type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyAnonChoice1Combinator>>;
pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator1(pub CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1);
impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator1 {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator1, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias1);

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator(pub CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias);

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    type Type = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>;
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
pub type CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinatorAlias = Mapped<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator1, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper>;


pub open spec fn spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len: u8, tag: u8) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: bytes::Variable(((usize::spec_from(frame_len) - 1)) as usize) }, Cond { cond: !(tag == 0), inner: spec_capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1() }), mapper: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper })
}

pub fn capture_outer_and_local_anon_payload_anon_inner_anon_body<'a>(frame_len: u8, tag: u8) -> (o: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator)
    requires
        ((frame_len) >= 1),

    ensures o@ == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator(Mapped { inner: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator1(Choice::new(Cond { cond: tag == 0, inner: bytes::Variable(((usize::ex_from(frame_len) - 1)) as usize) }, Cond { cond: !(tag == 0), inner: capture_outer_and_local_anon_payload_anon_inner_anon_body_anon_choice1() })), mapper: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyMapper });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_anon_payload_anon_inner_anon_body<'a>(input: &'a [u8], frame_len: u8, tag: u8) -> (res: PResult<<CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_parse(input@) is None,
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body( frame_len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_anon_payload_anon_inner_anon_body<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).wf(v@),
        ((frame_len) >= 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body( frame_len, tag );
    combinator.serialize(v, data, pos)
}

pub fn capture_outer_and_local_anon_payload_anon_inner_anon_body_len<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, frame_len: u8, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).wf(v@),
        spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_serialize(v@).len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        serialize_len == spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len@, tag@).spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner_anon_body( frame_len, tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecCaptureParamAndLocalAnonXAnonBAnonY {
    Variant0(u8),
    Variant1(u16),
}

pub type SpecCaptureParamAndLocalAnonXAnonBAnonYInner = Either<u8, u16>;

impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonBAnonY> for SpecCaptureParamAndLocalAnonXAnonBAnonYInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonBAnonY) -> SpecCaptureParamAndLocalAnonXAnonBAnonYInner {
        match m {
            SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant0(m) => Either::Left(m),
            SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonBAnonYInner> for SpecCaptureParamAndLocalAnonXAnonBAnonY {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonBAnonYInner) -> SpecCaptureParamAndLocalAnonXAnonBAnonY {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant0(m),
            Either::Right(m) => SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalAnonXAnonBAnonY {
    Variant0(u8),
    Variant1(u16),
}

pub type CaptureParamAndLocalAnonXAnonBAnonYInner = Either<u8, u16>;

pub type CaptureParamAndLocalAnonXAnonBAnonYInnerRef<'a> = Either<&'a u8, &'a u16>;


impl View for CaptureParamAndLocalAnonXAnonBAnonY {
    type V = SpecCaptureParamAndLocalAnonXAnonBAnonY;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalAnonXAnonBAnonY::Variant0(m) => SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant0(m@),
            CaptureParamAndLocalAnonXAnonBAnonY::Variant1(m) => SpecCaptureParamAndLocalAnonXAnonBAnonY::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalAnonXAnonBAnonY> for CaptureParamAndLocalAnonXAnonBAnonYInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalAnonXAnonBAnonY) -> CaptureParamAndLocalAnonXAnonBAnonYInnerRef<'a> {
        match m {
            CaptureParamAndLocalAnonXAnonBAnonY::Variant0(m) => Either::Left(m),
            CaptureParamAndLocalAnonXAnonBAnonY::Variant1(m) => Either::Right(m),
        }
    }

}

impl From<CaptureParamAndLocalAnonXAnonBAnonYInner> for CaptureParamAndLocalAnonXAnonBAnonY {
    fn ex_from(m: CaptureParamAndLocalAnonXAnonBAnonYInner) -> CaptureParamAndLocalAnonXAnonBAnonY {
        match m {
            Either::Left(m) => CaptureParamAndLocalAnonXAnonBAnonY::Variant0(m),
            Either::Right(m) => CaptureParamAndLocalAnonXAnonBAnonY::Variant1(m),
        }
    }
    
}


pub struct CaptureParamAndLocalAnonXAnonBAnonYMapper;
impl View for CaptureParamAndLocalAnonXAnonBAnonYMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalAnonXAnonBAnonYMapper {
    type Src = SpecCaptureParamAndLocalAnonXAnonBAnonYInner;
    type Dst = SpecCaptureParamAndLocalAnonXAnonBAnonY;
}
impl SpecIsoProof for CaptureParamAndLocalAnonXAnonBAnonYMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalAnonXAnonBAnonYMapper {
    type Src = CaptureParamAndLocalAnonXAnonBAnonYInner;
    type Dst = CaptureParamAndLocalAnonXAnonBAnonY;
    type RefSrc = CaptureParamAndLocalAnonXAnonBAnonYInnerRef<'a>;
}

type SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator(pub SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator {
    type Type = SpecCaptureParamAndLocalAnonXAnonBAnonY;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias = Mapped<SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1, CaptureParamAndLocalAnonXAnonBAnonYMapper>;
type CaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct CaptureParamAndLocalAnonXAnonBAnonYCombinator1(pub CaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1);
impl View for CaptureParamAndLocalAnonXAnonBAnonYCombinator1 {
    type V = SpecCaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalAnonXAnonBAnonYCombinator1, CaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias1);

pub struct CaptureParamAndLocalAnonXAnonBAnonYCombinator(pub CaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias);

impl View for CaptureParamAndLocalAnonXAnonBAnonYCombinator {
    type V = SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalAnonXAnonBAnonYCombinator {
    type Type = CaptureParamAndLocalAnonXAnonBAnonY;
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
pub type CaptureParamAndLocalAnonXAnonBAnonYCombinatorAlias = Mapped<CaptureParamAndLocalAnonXAnonBAnonYCombinator1, CaptureParamAndLocalAnonXAnonBAnonYMapper>;


pub open spec fn spec_capture_param_and_local_anon_x_anon_b_anon_y(tag: u8) -> SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator {
    SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: U8 }, Cond { cond: !(tag == 0), inner: U16Le }), mapper: CaptureParamAndLocalAnonXAnonBAnonYMapper })
}

pub fn capture_param_and_local_anon_x_anon_b_anon_y<'a>(tag: u8) -> (o: CaptureParamAndLocalAnonXAnonBAnonYCombinator)

    ensures o@ == spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalAnonXAnonBAnonYCombinator(Mapped { inner: CaptureParamAndLocalAnonXAnonBAnonYCombinator1(Choice::new(Cond { cond: tag == 0, inner: U8 }, Cond { cond: !(tag == 0), inner: U16Le })), mapper: CaptureParamAndLocalAnonXAnonBAnonYMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_anon_x_anon_b_anon_y<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<CaptureParamAndLocalAnonXAnonBAnonYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_parse(input@) is None,
        spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_anon_x_anon_b_anon_y( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_anon_x_anon_b_anon_y<'a>(v: <CaptureParamAndLocalAnonXAnonBAnonYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_anon_x_anon_b_anon_y( tag );
    combinator.serialize(v, data, pos)
}

pub fn capture_param_and_local_anon_x_anon_b_anon_y_len<'a>(v: <CaptureParamAndLocalAnonXAnonBAnonYCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).wf(v@),
        spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_capture_param_and_local_anon_x_anon_b_anon_y(tag@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_anon_x_anon_b_anon_y( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureParamAndLocalAnonXAnonB {
    pub tag: u8,
    pub y: SpecCaptureParamAndLocalAnonXAnonBAnonY,
}

pub type SpecCaptureParamAndLocalAnonXAnonBInner = (u8, SpecCaptureParamAndLocalAnonXAnonBAnonY);


impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonB> for SpecCaptureParamAndLocalAnonXAnonBInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonB) -> SpecCaptureParamAndLocalAnonXAnonBInner {
        (m.tag, m.y)
    }
}

impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonBInner> for SpecCaptureParamAndLocalAnonXAnonB {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonBInner) -> SpecCaptureParamAndLocalAnonXAnonB {
        let (tag, y) = m;
        SpecCaptureParamAndLocalAnonXAnonB { tag, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureParamAndLocalAnonXAnonB {
    pub tag: u8,
    pub y: CaptureParamAndLocalAnonXAnonBAnonY,
}

impl View for CaptureParamAndLocalAnonXAnonB {
    type V = SpecCaptureParamAndLocalAnonXAnonB;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocalAnonXAnonB {
            tag: self.tag@,
            y: self.y@,
        }
    }
}
pub type CaptureParamAndLocalAnonXAnonBInner = (u8, CaptureParamAndLocalAnonXAnonBAnonY);

pub type CaptureParamAndLocalAnonXAnonBInnerRef<'a> = (&'a u8, &'a CaptureParamAndLocalAnonXAnonBAnonY);
impl<'a> From<&'a CaptureParamAndLocalAnonXAnonB> for CaptureParamAndLocalAnonXAnonBInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalAnonXAnonB) -> CaptureParamAndLocalAnonXAnonBInnerRef<'a> {
        (&m.tag, &m.y)
    }
}

impl From<CaptureParamAndLocalAnonXAnonBInner> for CaptureParamAndLocalAnonXAnonB {
    fn ex_from(m: CaptureParamAndLocalAnonXAnonBInner) -> CaptureParamAndLocalAnonXAnonB {
        let (tag, y) = m;
        CaptureParamAndLocalAnonXAnonB { tag, y }
    }
}

pub struct CaptureParamAndLocalAnonXAnonBMapper;
impl View for CaptureParamAndLocalAnonXAnonBMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalAnonXAnonBMapper {
    type Src = SpecCaptureParamAndLocalAnonXAnonBInner;
    type Dst = SpecCaptureParamAndLocalAnonXAnonB;
}
impl SpecIsoProof for CaptureParamAndLocalAnonXAnonBMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalAnonXAnonBMapper {
    type Src = CaptureParamAndLocalAnonXAnonBInner;
    type Dst = CaptureParamAndLocalAnonXAnonB;
    type RefSrc = CaptureParamAndLocalAnonXAnonBInnerRef<'a>;
}

pub struct SpecCaptureParamAndLocalAnonXAnonBCombinator(pub SpecCaptureParamAndLocalAnonXAnonBCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalAnonXAnonBCombinator {
    type Type = SpecCaptureParamAndLocalAnonXAnonB;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalAnonXAnonBCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalAnonXAnonBCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalAnonXAnonBCombinatorAlias = Mapped<SpecPair<U8, SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator>, CaptureParamAndLocalAnonXAnonBMapper>;

pub struct CaptureParamAndLocalAnonXAnonBCombinator(pub CaptureParamAndLocalAnonXAnonBCombinatorAlias);

impl View for CaptureParamAndLocalAnonXAnonBCombinator {
    type V = SpecCaptureParamAndLocalAnonXAnonBCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalAnonXAnonBCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalAnonXAnonBCombinator {
    type Type = CaptureParamAndLocalAnonXAnonB;
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
pub type CaptureParamAndLocalAnonXAnonBCombinatorAlias = Mapped<Pair<U8, CaptureParamAndLocalAnonXAnonBAnonYCombinator, CaptureParamAndLocalAnonXAnonBCont0>, CaptureParamAndLocalAnonXAnonBMapper>;


pub open spec fn spec_capture_param_and_local_anon_x_anon_b() -> SpecCaptureParamAndLocalAnonXAnonBCombinator {
    SpecCaptureParamAndLocalAnonXAnonBCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_param_and_local_anon_x_anon_b_cont0(deps)),
        mapper: CaptureParamAndLocalAnonXAnonBMapper,
    })
}

pub open spec fn spec_capture_param_and_local_anon_x_anon_b_cont0(deps: u8) -> SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator {
    let tag = deps;
    spec_capture_param_and_local_anon_x_anon_b_anon_y(tag)
}

impl View for CaptureParamAndLocalAnonXAnonBCont0 {
    type V = spec_fn(u8) -> SpecCaptureParamAndLocalAnonXAnonBAnonYCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_param_and_local_anon_x_anon_b_cont0(deps)
        }
    }
}

                
pub fn capture_param_and_local_anon_x_anon_b<'a>() -> (o: CaptureParamAndLocalAnonXAnonBCombinator)
    ensures o@ == spec_capture_param_and_local_anon_x_anon_b(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalAnonXAnonBCombinator(
    Mapped {
        inner: Pair::new(U8, CaptureParamAndLocalAnonXAnonBCont0),
        mapper: CaptureParamAndLocalAnonXAnonBMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_anon_x_anon_b()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_anon_x_anon_b<'a>(input: &'a [u8]) -> (res: PResult<<CaptureParamAndLocalAnonXAnonBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_anon_x_anon_b().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_anon_x_anon_b().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_anon_x_anon_b().spec_parse(input@) is None,
        spec_capture_param_and_local_anon_x_anon_b().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_anon_x_anon_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_anon_x_anon_b<'a>(v: <CaptureParamAndLocalAnonXAnonBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_anon_x_anon_b().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_anon_x_anon_b().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_anon_x_anon_b().spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_anon_x_anon_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn capture_param_and_local_anon_x_anon_b_len<'a>(v: <CaptureParamAndLocalAnonXAnonBCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_anon_x_anon_b().wf(v@),
        spec_capture_param_and_local_anon_x_anon_b().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_param_and_local_anon_x_anon_b().spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_anon_x_anon_b();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureParamAndLocalAnonXAnonBCont0;
type CaptureParamAndLocalAnonXAnonBCont0Type<'a, 'b> = &'b u8;
type CaptureParamAndLocalAnonXAnonBCont0SType<'a, 'x> = &'x u8;
type CaptureParamAndLocalAnonXAnonBCont0Input<'a, 'b, 'x> = POrSType<CaptureParamAndLocalAnonXAnonBCont0Type<'a, 'b>, CaptureParamAndLocalAnonXAnonBCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureParamAndLocalAnonXAnonBCont0Input<'a, 'b, 'x>> for CaptureParamAndLocalAnonXAnonBCont0 {
    type Output = CaptureParamAndLocalAnonXAnonBAnonYCombinator;

    open spec fn requires(&self, deps: CaptureParamAndLocalAnonXAnonBCont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureParamAndLocalAnonXAnonBCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_param_and_local_anon_x_anon_b_cont0(deps@)
    }

    fn apply(&self, deps: CaptureParamAndLocalAnonXAnonBCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_param_and_local_anon_x_anon_b_anon_y(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_param_and_local_anon_x_anon_b_anon_y(tag)
            }
        }
    }
}
                

pub struct SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 {
    pub len: u8,
    pub bytes: Seq<u8>,
}

pub type SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner = (u8, Seq<u8>);


impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0> for SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner {
        (m.len, m.bytes)
    }
}

impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner> for SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 {
        let (len, bytes) = m;
        SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 { len, bytes }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a> {
    pub len: u8,
    pub bytes: &'a [u8],
}

impl View for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'_> {
    type V = SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 {
            len: self.len@,
            bytes: self.bytes@,
        }
    }
}
pub type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner<'a> = (u8, &'a [u8]);

pub type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0InnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>> for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0InnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0) -> CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0InnerRef<'a> {
        (&m.len, &m.bytes)
    }
}

impl<'a> From<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner<'a>> for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a> {
    fn ex_from(m: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner) -> CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 {
        let (len, bytes) = m;
        CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0 { len, bytes }
    }
}

pub struct CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper;
impl View for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper {
    type Src = SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner;
    type Dst = SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0;
}
impl SpecIsoProof for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper {
    type Src = CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Inner<'a>;
    type Dst = CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>;
    type RefSrc = CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0InnerRef<'a>;
}

pub struct SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator(pub SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0CombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator {
    type Type = SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0CombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0CombinatorAlias = Mapped<SpecPair<U8, bytes::Variable>, CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper>;

pub struct CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator(pub CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0CombinatorAlias);

impl View for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator {
    type V = SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator {
    type Type = CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>;
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
pub type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0CombinatorAlias = Mapped<Pair<U8, bytes::Variable, CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0>, CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper>;


pub open spec fn spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0() -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator {
    SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0_cont0(deps)),
        mapper: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper,
    })
}

pub open spec fn spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0_cont0(deps: u8) -> bytes::Variable {
    let len = deps;
    bytes::Variable((usize::spec_from(len)) as usize)
}

impl View for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0 {
    type V = spec_fn(u8) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0_cont0(deps)
        }
    }
}

                
pub fn capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0<'a>() -> (o: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator)
    ensures o@ == spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator(
    Mapped {
        inner: Pair::new(U8, CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0),
        mapper: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0<'a>(input: &'a [u8]) -> (res: PResult<<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0<'a>(v: <CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0_len<'a>(v: <CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().wf(v@),
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0().spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0;
type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Type<'a, 'b> = &'b u8;
type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0SType<'a, 'x> = &'x u8;
type CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Input<'a, 'b, 'x> = POrSType<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Type<'a, 'b>, CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Input<'a, 'b, 'x>> for CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0_cont0(deps@)
    }

    fn apply(&self, deps: CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Cont0Input<'a, 'b, 'x>) -> Self::Output {
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
                

pub enum SpecCaptureLocalInAnonStructAnonWrapperAnonValue {
    Variant0(SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0),
    Variant1(u16),
}

pub type SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner = Either<SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0, u16>;

impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapperAnonValue> for SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapperAnonValue) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner {
        match m {
            SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m) => Either::Left(m),
            SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner> for SpecCaptureLocalInAnonStructAnonWrapperAnonValue {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValue {
        match m {
            Either::Left(m) => SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m),
            Either::Right(m) => SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureLocalInAnonStructAnonWrapperAnonValue<'a> {
    Variant0(CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>),
    Variant1(u16),
}

pub type CaptureLocalInAnonStructAnonWrapperAnonValueInner<'a> = Either<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>, u16>;

pub type CaptureLocalInAnonStructAnonWrapperAnonValueInnerRef<'a> = Either<&'a CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0<'a>, &'a u16>;


impl<'a> View for CaptureLocalInAnonStructAnonWrapperAnonValue<'a> {
    type V = SpecCaptureLocalInAnonStructAnonWrapperAnonValue;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m) => SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m@),
            CaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m) => SpecCaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m@),
        }
    }
}


impl<'a> From<&'a CaptureLocalInAnonStructAnonWrapperAnonValue<'a>> for CaptureLocalInAnonStructAnonWrapperAnonValueInnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructAnonWrapperAnonValue<'a>) -> CaptureLocalInAnonStructAnonWrapperAnonValueInnerRef<'a> {
        match m {
            CaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m) => Either::Left(m),
            CaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureLocalInAnonStructAnonWrapperAnonValueInner<'a>> for CaptureLocalInAnonStructAnonWrapperAnonValue<'a> {
    fn ex_from(m: CaptureLocalInAnonStructAnonWrapperAnonValueInner<'a>) -> CaptureLocalInAnonStructAnonWrapperAnonValue<'a> {
        match m {
            Either::Left(m) => CaptureLocalInAnonStructAnonWrapperAnonValue::Variant0(m),
            Either::Right(m) => CaptureLocalInAnonStructAnonWrapperAnonValue::Variant1(m),
        }
    }
    
}


pub struct CaptureLocalInAnonStructAnonWrapperAnonValueMapper;
impl View for CaptureLocalInAnonStructAnonWrapperAnonValueMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructAnonWrapperAnonValueMapper {
    type Src = SpecCaptureLocalInAnonStructAnonWrapperAnonValueInner;
    type Dst = SpecCaptureLocalInAnonStructAnonWrapperAnonValue;
}
impl SpecIsoProof for CaptureLocalInAnonStructAnonWrapperAnonValueMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructAnonWrapperAnonValueMapper {
    type Src = CaptureLocalInAnonStructAnonWrapperAnonValueInner<'a>;
    type Dst = CaptureLocalInAnonStructAnonWrapperAnonValue<'a>;
    type RefSrc = CaptureLocalInAnonStructAnonWrapperAnonValueInnerRef<'a>;
}

type SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1 = Choice<Cond<SpecCaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator>, Cond<U16Le>>;
pub struct SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator(pub SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    type Type = SpecCaptureLocalInAnonStructAnonWrapperAnonValue;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias = Mapped<SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1, CaptureLocalInAnonStructAnonWrapperAnonValueMapper>;
type CaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1 = Choice<Cond<CaptureLocalInAnonStructAnonWrapperAnonValueAnonChoice0Combinator>, Cond<U16Le>>;
pub struct CaptureLocalInAnonStructAnonWrapperAnonValueCombinator1(pub CaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1);
impl View for CaptureLocalInAnonStructAnonWrapperAnonValueCombinator1 {
    type V = SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureLocalInAnonStructAnonWrapperAnonValueCombinator1, CaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias1);

pub struct CaptureLocalInAnonStructAnonWrapperAnonValueCombinator(pub CaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias);

impl View for CaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    type V = SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    type Type = CaptureLocalInAnonStructAnonWrapperAnonValue<'a>;
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
pub type CaptureLocalInAnonStructAnonWrapperAnonValueCombinatorAlias = Mapped<CaptureLocalInAnonStructAnonWrapperAnonValueCombinator1, CaptureLocalInAnonStructAnonWrapperAnonValueMapper>;


pub open spec fn spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag: u8) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: spec_capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0() }, Cond { cond: !(tag == 0), inner: U16Le }), mapper: CaptureLocalInAnonStructAnonWrapperAnonValueMapper })
}

pub fn capture_local_in_anon_struct_anon_wrapper_anon_value<'a>(tag: u8) -> (o: CaptureLocalInAnonStructAnonWrapperAnonValueCombinator)

    ensures o@ == spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructAnonWrapperAnonValueCombinator(Mapped { inner: CaptureLocalInAnonStructAnonWrapperAnonValueCombinator1(Choice::new(Cond { cond: tag == 0, inner: capture_local_in_anon_struct_anon_wrapper_anon_value_anon_choice0() }, Cond { cond: !(tag == 0), inner: U16Le })), mapper: CaptureLocalInAnonStructAnonWrapperAnonValueMapper });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_anon_wrapper_anon_value<'a>(input: &'a [u8], tag: u8) -> (res: PResult<<CaptureLocalInAnonStructAnonWrapperAnonValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,

    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_anon_wrapper_anon_value<'a>(v: <CaptureLocalInAnonStructAnonWrapperAnonValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, tag: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).wf(v@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value( tag );
    combinator.serialize(v, data, pos)
}

pub fn capture_local_in_anon_struct_anon_wrapper_anon_value_len<'a>(v: <CaptureLocalInAnonStructAnonWrapperAnonValueCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, tag: u8) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).wf(v@),
        spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_serialize(v@).len() <= usize::MAX,

    ensures
        serialize_len == spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag@).spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_anon_wrapper_anon_value( tag );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureLocalInAnonStructAnonWrapper {
    pub tag: u8,
    pub value: SpecCaptureLocalInAnonStructAnonWrapperAnonValue,
}

pub type SpecCaptureLocalInAnonStructAnonWrapperInner = (u8, SpecCaptureLocalInAnonStructAnonWrapperAnonValue);


impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapper> for SpecCaptureLocalInAnonStructAnonWrapperInner {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapper) -> SpecCaptureLocalInAnonStructAnonWrapperInner {
        (m.tag, m.value)
    }
}

impl SpecFrom<SpecCaptureLocalInAnonStructAnonWrapperInner> for SpecCaptureLocalInAnonStructAnonWrapper {
    open spec fn spec_from(m: SpecCaptureLocalInAnonStructAnonWrapperInner) -> SpecCaptureLocalInAnonStructAnonWrapper {
        let (tag, value) = m;
        SpecCaptureLocalInAnonStructAnonWrapper { tag, value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureLocalInAnonStructAnonWrapper<'a> {
    pub tag: u8,
    pub value: CaptureLocalInAnonStructAnonWrapperAnonValue<'a>,
}

impl View for CaptureLocalInAnonStructAnonWrapper<'_> {
    type V = SpecCaptureLocalInAnonStructAnonWrapper;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStructAnonWrapper {
            tag: self.tag@,
            value: self.value@,
        }
    }
}
pub type CaptureLocalInAnonStructAnonWrapperInner<'a> = (u8, CaptureLocalInAnonStructAnonWrapperAnonValue<'a>);

pub type CaptureLocalInAnonStructAnonWrapperInnerRef<'a> = (&'a u8, &'a CaptureLocalInAnonStructAnonWrapperAnonValue<'a>);
impl<'a> From<&'a CaptureLocalInAnonStructAnonWrapper<'a>> for CaptureLocalInAnonStructAnonWrapperInnerRef<'a> {
    fn ex_from(m: &'a CaptureLocalInAnonStructAnonWrapper) -> CaptureLocalInAnonStructAnonWrapperInnerRef<'a> {
        (&m.tag, &m.value)
    }
}

impl<'a> From<CaptureLocalInAnonStructAnonWrapperInner<'a>> for CaptureLocalInAnonStructAnonWrapper<'a> {
    fn ex_from(m: CaptureLocalInAnonStructAnonWrapperInner) -> CaptureLocalInAnonStructAnonWrapper {
        let (tag, value) = m;
        CaptureLocalInAnonStructAnonWrapper { tag, value }
    }
}

pub struct CaptureLocalInAnonStructAnonWrapperMapper;
impl View for CaptureLocalInAnonStructAnonWrapperMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureLocalInAnonStructAnonWrapperMapper {
    type Src = SpecCaptureLocalInAnonStructAnonWrapperInner;
    type Dst = SpecCaptureLocalInAnonStructAnonWrapper;
}
impl SpecIsoProof for CaptureLocalInAnonStructAnonWrapperMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureLocalInAnonStructAnonWrapperMapper {
    type Src = CaptureLocalInAnonStructAnonWrapperInner<'a>;
    type Dst = CaptureLocalInAnonStructAnonWrapper<'a>;
    type RefSrc = CaptureLocalInAnonStructAnonWrapperInnerRef<'a>;
}

pub struct SpecCaptureLocalInAnonStructAnonWrapperCombinator(pub SpecCaptureLocalInAnonStructAnonWrapperCombinatorAlias);

impl SpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperCombinator {
    type Type = SpecCaptureLocalInAnonStructAnonWrapper;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureLocalInAnonStructAnonWrapperCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureLocalInAnonStructAnonWrapperCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureLocalInAnonStructAnonWrapperCombinatorAlias = Mapped<SpecPair<U8, SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator>, CaptureLocalInAnonStructAnonWrapperMapper>;

pub struct CaptureLocalInAnonStructAnonWrapperCombinator(pub CaptureLocalInAnonStructAnonWrapperCombinatorAlias);

impl View for CaptureLocalInAnonStructAnonWrapperCombinator {
    type V = SpecCaptureLocalInAnonStructAnonWrapperCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureLocalInAnonStructAnonWrapperCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureLocalInAnonStructAnonWrapperCombinator {
    type Type = CaptureLocalInAnonStructAnonWrapper<'a>;
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
pub type CaptureLocalInAnonStructAnonWrapperCombinatorAlias = Mapped<Pair<U8, CaptureLocalInAnonStructAnonWrapperAnonValueCombinator, CaptureLocalInAnonStructAnonWrapperCont0>, CaptureLocalInAnonStructAnonWrapperMapper>;


pub open spec fn spec_capture_local_in_anon_struct_anon_wrapper() -> SpecCaptureLocalInAnonStructAnonWrapperCombinator {
    SpecCaptureLocalInAnonStructAnonWrapperCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_local_in_anon_struct_anon_wrapper_cont0(deps)),
        mapper: CaptureLocalInAnonStructAnonWrapperMapper,
    })
}

pub open spec fn spec_capture_local_in_anon_struct_anon_wrapper_cont0(deps: u8) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator {
    let tag = deps;
    spec_capture_local_in_anon_struct_anon_wrapper_anon_value(tag)
}

impl View for CaptureLocalInAnonStructAnonWrapperCont0 {
    type V = spec_fn(u8) -> SpecCaptureLocalInAnonStructAnonWrapperAnonValueCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_local_in_anon_struct_anon_wrapper_cont0(deps)
        }
    }
}

                
pub fn capture_local_in_anon_struct_anon_wrapper<'a>() -> (o: CaptureLocalInAnonStructAnonWrapperCombinator)
    ensures o@ == spec_capture_local_in_anon_struct_anon_wrapper(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureLocalInAnonStructAnonWrapperCombinator(
    Mapped {
        inner: Pair::new(U8, CaptureLocalInAnonStructAnonWrapperCont0),
        mapper: CaptureLocalInAnonStructAnonWrapperMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_local_in_anon_struct_anon_wrapper()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_local_in_anon_struct_anon_wrapper<'a>(input: &'a [u8]) -> (res: PResult<<CaptureLocalInAnonStructAnonWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_capture_local_in_anon_struct_anon_wrapper().spec_parse(input@) == Some((n as int, v@)),
        spec_capture_local_in_anon_struct_anon_wrapper().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_local_in_anon_struct_anon_wrapper().spec_parse(input@) is None,
        spec_capture_local_in_anon_struct_anon_wrapper().spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_local_in_anon_struct_anon_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_local_in_anon_struct_anon_wrapper<'a>(v: <CaptureLocalInAnonStructAnonWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_local_in_anon_struct_anon_wrapper().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_local_in_anon_struct_anon_wrapper().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_local_in_anon_struct_anon_wrapper().spec_serialize(v@))
        },
{
    let combinator = capture_local_in_anon_struct_anon_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn capture_local_in_anon_struct_anon_wrapper_len<'a>(v: <CaptureLocalInAnonStructAnonWrapperCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_capture_local_in_anon_struct_anon_wrapper().wf(v@),
        spec_capture_local_in_anon_struct_anon_wrapper().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_capture_local_in_anon_struct_anon_wrapper().spec_serialize(v@).len(),
{
    let combinator = capture_local_in_anon_struct_anon_wrapper();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureLocalInAnonStructAnonWrapperCont0;
type CaptureLocalInAnonStructAnonWrapperCont0Type<'a, 'b> = &'b u8;
type CaptureLocalInAnonStructAnonWrapperCont0SType<'a, 'x> = &'x u8;
type CaptureLocalInAnonStructAnonWrapperCont0Input<'a, 'b, 'x> = POrSType<CaptureLocalInAnonStructAnonWrapperCont0Type<'a, 'b>, CaptureLocalInAnonStructAnonWrapperCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureLocalInAnonStructAnonWrapperCont0Input<'a, 'b, 'x>> for CaptureLocalInAnonStructAnonWrapperCont0 {
    type Output = CaptureLocalInAnonStructAnonWrapperAnonValueCombinator;

    open spec fn requires(&self, deps: CaptureLocalInAnonStructAnonWrapperCont0Input<'a, 'b, 'x>) -> bool {
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureLocalInAnonStructAnonWrapperCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_local_in_anon_struct_anon_wrapper_cont0(deps@)
    }

    fn apply(&self, deps: CaptureLocalInAnonStructAnonWrapperCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_local_in_anon_struct_anon_wrapper_anon_value(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                capture_local_in_anon_struct_anon_wrapper_anon_value(tag)
            }
        }
    }
}
                

pub enum SpecNestedInnerChoiceAnonXAnonA {
    C(u8),
    D(u16),
}

pub type SpecNestedInnerChoiceAnonXAnonAInner = Either<u8, u16>;

impl SpecFrom<SpecNestedInnerChoiceAnonXAnonA> for SpecNestedInnerChoiceAnonXAnonAInner {
    open spec fn spec_from(m: SpecNestedInnerChoiceAnonXAnonA) -> SpecNestedInnerChoiceAnonXAnonAInner {
        match m {
            SpecNestedInnerChoiceAnonXAnonA::C(m) => Either::Left(m),
            SpecNestedInnerChoiceAnonXAnonA::D(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecNestedInnerChoiceAnonXAnonAInner> for SpecNestedInnerChoiceAnonXAnonA {
    open spec fn spec_from(m: SpecNestedInnerChoiceAnonXAnonAInner) -> SpecNestedInnerChoiceAnonXAnonA {
        match m {
            Either::Left(m) => SpecNestedInnerChoiceAnonXAnonA::C(m),
            Either::Right(m) => SpecNestedInnerChoiceAnonXAnonA::D(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NestedInnerChoiceAnonXAnonA {
    C(u8),
    D(u16),
}

pub type NestedInnerChoiceAnonXAnonAInner = Either<u8, u16>;

pub type NestedInnerChoiceAnonXAnonAInnerRef<'a> = Either<&'a u8, &'a u16>;


impl View for NestedInnerChoiceAnonXAnonA {
    type V = SpecNestedInnerChoiceAnonXAnonA;
    open spec fn view(&self) -> Self::V {
        match self {
            NestedInnerChoiceAnonXAnonA::C(m) => SpecNestedInnerChoiceAnonXAnonA::C(m@),
            NestedInnerChoiceAnonXAnonA::D(m) => SpecNestedInnerChoiceAnonXAnonA::D(m@),
        }
    }
}


impl<'a> From<&'a NestedInnerChoiceAnonXAnonA> for NestedInnerChoiceAnonXAnonAInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerChoiceAnonXAnonA) -> NestedInnerChoiceAnonXAnonAInnerRef<'a> {
        match m {
            NestedInnerChoiceAnonXAnonA::C(m) => Either::Left(m),
            NestedInnerChoiceAnonXAnonA::D(m) => Either::Right(m),
        }
    }

}

impl From<NestedInnerChoiceAnonXAnonAInner> for NestedInnerChoiceAnonXAnonA {
    fn ex_from(m: NestedInnerChoiceAnonXAnonAInner) -> NestedInnerChoiceAnonXAnonA {
        match m {
            Either::Left(m) => NestedInnerChoiceAnonXAnonA::C(m),
            Either::Right(m) => NestedInnerChoiceAnonXAnonA::D(m),
        }
    }
    
}


pub struct NestedInnerChoiceAnonXAnonAMapper;
impl View for NestedInnerChoiceAnonXAnonAMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerChoiceAnonXAnonAMapper {
    type Src = SpecNestedInnerChoiceAnonXAnonAInner;
    type Dst = SpecNestedInnerChoiceAnonXAnonA;
}
impl SpecIsoProof for NestedInnerChoiceAnonXAnonAMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerChoiceAnonXAnonAMapper {
    type Src = NestedInnerChoiceAnonXAnonAInner;
    type Dst = NestedInnerChoiceAnonXAnonA;
    type RefSrc = NestedInnerChoiceAnonXAnonAInnerRef<'a>;
}

type SpecNestedInnerChoiceAnonXAnonACombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct SpecNestedInnerChoiceAnonXAnonACombinator(pub SpecNestedInnerChoiceAnonXAnonACombinatorAlias);

impl SpecCombinator for SpecNestedInnerChoiceAnonXAnonACombinator {
    type Type = SpecNestedInnerChoiceAnonXAnonA;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerChoiceAnonXAnonACombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerChoiceAnonXAnonACombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerChoiceAnonXAnonACombinatorAlias = Mapped<SpecNestedInnerChoiceAnonXAnonACombinatorAlias1, NestedInnerChoiceAnonXAnonAMapper>;
type NestedInnerChoiceAnonXAnonACombinatorAlias1 = Choice<Cond<U8>, Cond<U16Le>>;
pub struct NestedInnerChoiceAnonXAnonACombinator1(pub NestedInnerChoiceAnonXAnonACombinatorAlias1);
impl View for NestedInnerChoiceAnonXAnonACombinator1 {
    type V = SpecNestedInnerChoiceAnonXAnonACombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerChoiceAnonXAnonACombinator1, NestedInnerChoiceAnonXAnonACombinatorAlias1);

pub struct NestedInnerChoiceAnonXAnonACombinator(pub NestedInnerChoiceAnonXAnonACombinatorAlias);

impl View for NestedInnerChoiceAnonXAnonACombinator {
    type V = SpecNestedInnerChoiceAnonXAnonACombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerChoiceAnonXAnonACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerChoiceAnonXAnonACombinator {
    type Type = NestedInnerChoiceAnonXAnonA;
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
pub type NestedInnerChoiceAnonXAnonACombinatorAlias = Mapped<NestedInnerChoiceAnonXAnonACombinator1, NestedInnerChoiceAnonXAnonAMapper>;


pub open spec fn spec_nested_inner_choice_anon_x_anon_a(choice2: SpecCOrD) -> SpecNestedInnerChoiceAnonXAnonACombinator {
    SpecNestedInnerChoiceAnonXAnonACombinator(Mapped { inner: Choice(Cond { cond: choice2 == COrD::C, inner: U8 }, Cond { cond: choice2 == COrD::D, inner: U16Le }), mapper: NestedInnerChoiceAnonXAnonAMapper })
}

pub fn nested_inner_choice_anon_x_anon_a<'a>(choice2: COrD) -> (o: NestedInnerChoiceAnonXAnonACombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_nested_inner_choice_anon_x_anon_a(choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerChoiceAnonXAnonACombinator(Mapped { inner: NestedInnerChoiceAnonXAnonACombinator1(Choice::new(Cond { cond: choice2 == COrD::C, inner: U8 }, Cond { cond: choice2 == COrD::D, inner: U16Le })), mapper: NestedInnerChoiceAnonXAnonAMapper });
    // assert({
    //     &&& combinator@ == spec_nested_inner_choice_anon_x_anon_a(choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_choice_anon_x_anon_a<'a>(input: &'a [u8], choice2: COrD) -> (res: PResult<<NestedInnerChoiceAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_parse(input@) is None,
        spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_choice_anon_x_anon_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_choice_anon_x_anon_a<'a>(v: <NestedInnerChoiceAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_anon_x_anon_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_choice_anon_x_anon_a( choice2 );
    combinator.serialize(v, data, pos)
}

pub fn nested_inner_choice_anon_x_anon_a_len<'a>(v: <NestedInnerChoiceAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_nested_inner_choice_anon_x_anon_a(choice2@).wf(v@),
        spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_nested_inner_choice_anon_x_anon_a(choice2@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_choice_anon_x_anon_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureOuterAndLocalAnonPayloadAnonInner {
    pub tag: u8,
    pub body: SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody,
}

pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner = (u8, SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBody);


impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInner> for SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInner) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner> for SpecCaptureOuterAndLocalAnonPayloadAnonInner {
    open spec fn spec_from(m: SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner) -> SpecCaptureOuterAndLocalAnonPayloadAnonInner {
        let (tag, body) = m;
        SpecCaptureOuterAndLocalAnonPayloadAnonInner { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureOuterAndLocalAnonPayloadAnonInner<'a> {
    pub tag: u8,
    pub body: CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>,
}

impl View for CaptureOuterAndLocalAnonPayloadAnonInner<'_> {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInner;

    open spec fn view(&self) -> Self::V {
        SpecCaptureOuterAndLocalAnonPayloadAnonInner {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type CaptureOuterAndLocalAnonPayloadAnonInnerInner<'a> = (u8, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>);

pub type CaptureOuterAndLocalAnonPayloadAnonInnerInnerRef<'a> = (&'a u8, &'a CaptureOuterAndLocalAnonPayloadAnonInnerAnonBody<'a>);
impl<'a> From<&'a CaptureOuterAndLocalAnonPayloadAnonInner<'a>> for CaptureOuterAndLocalAnonPayloadAnonInnerInnerRef<'a> {
    fn ex_from(m: &'a CaptureOuterAndLocalAnonPayloadAnonInner) -> CaptureOuterAndLocalAnonPayloadAnonInnerInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl<'a> From<CaptureOuterAndLocalAnonPayloadAnonInnerInner<'a>> for CaptureOuterAndLocalAnonPayloadAnonInner<'a> {
    fn ex_from(m: CaptureOuterAndLocalAnonPayloadAnonInnerInner) -> CaptureOuterAndLocalAnonPayloadAnonInner {
        let (tag, body) = m;
        CaptureOuterAndLocalAnonPayloadAnonInner { tag, body }
    }
}

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerMapper;
impl View for CaptureOuterAndLocalAnonPayloadAnonInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureOuterAndLocalAnonPayloadAnonInnerMapper {
    type Src = SpecCaptureOuterAndLocalAnonPayloadAnonInnerInner;
    type Dst = SpecCaptureOuterAndLocalAnonPayloadAnonInner;
}
impl SpecIsoProof for CaptureOuterAndLocalAnonPayloadAnonInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureOuterAndLocalAnonPayloadAnonInnerMapper {
    type Src = CaptureOuterAndLocalAnonPayloadAnonInnerInner<'a>;
    type Dst = CaptureOuterAndLocalAnonPayloadAnonInner<'a>;
    type RefSrc = CaptureOuterAndLocalAnonPayloadAnonInnerInnerRef<'a>;
}

pub struct SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator(pub SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator {
    type Type = SpecCaptureOuterAndLocalAnonPayloadAnonInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinatorAlias = Mapped<SpecPair<U8, SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator>, CaptureOuterAndLocalAnonPayloadAnonInnerMapper>;

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerCombinator(pub CaptureOuterAndLocalAnonPayloadAnonInnerCombinatorAlias);

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerCombinator {
    type V = SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalAnonPayloadAnonInnerCombinator {
    type Type = CaptureOuterAndLocalAnonPayloadAnonInner<'a>;
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
pub type CaptureOuterAndLocalAnonPayloadAnonInnerCombinatorAlias = Mapped<Pair<U8, CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator, CaptureOuterAndLocalAnonPayloadAnonInnerCont0>, CaptureOuterAndLocalAnonPayloadAnonInnerMapper>;


pub open spec fn spec_capture_outer_and_local_anon_payload_anon_inner(frame_len: u8) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator {
    SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_outer_and_local_anon_payload_anon_inner_cont0(frame_len, deps)),
        mapper: CaptureOuterAndLocalAnonPayloadAnonInnerMapper,
    })
}

pub open spec fn spec_capture_outer_and_local_anon_payload_anon_inner_cont0(frame_len: u8, deps: u8) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator {
    let tag = deps;
    spec_capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len, tag)
}

impl View for CaptureOuterAndLocalAnonPayloadAnonInnerCont0 {
    type V = spec_fn(u8) -> SpecCaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_outer_and_local_anon_payload_anon_inner_cont0(self.frame_len@, deps)
        }
    }
}

pub fn capture_outer_and_local_anon_payload_anon_inner<'a>(frame_len: u8) -> (o: CaptureOuterAndLocalAnonPayloadAnonInnerCombinator)
    requires
        ((frame_len) >= 1),

    ensures o@ == spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalAnonPayloadAnonInnerCombinator(
    Mapped {
        inner: Pair::new(U8, CaptureOuterAndLocalAnonPayloadAnonInnerCont0 { frame_len }),
        mapper: CaptureOuterAndLocalAnonPayloadAnonInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_anon_payload_anon_inner<'a>(input: &'a [u8], frame_len: u8) -> (res: PResult<<CaptureOuterAndLocalAnonPayloadAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_parse(input@) is None,
        spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_anon_payload_anon_inner<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).wf(v@),
        ((frame_len) >= 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner( frame_len );
    combinator.serialize(v, data, pos)
}

pub fn capture_outer_and_local_anon_payload_anon_inner_len<'a>(v: <CaptureOuterAndLocalAnonPayloadAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, frame_len: u8) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).wf(v@),
        spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_serialize(v@).len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        serialize_len == spec_capture_outer_and_local_anon_payload_anon_inner(frame_len@).spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_anon_payload_anon_inner( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureOuterAndLocalAnonPayloadAnonInnerCont0 {
    pub frame_len: u8,
}
type CaptureOuterAndLocalAnonPayloadAnonInnerCont0Type<'a, 'b> = &'b u8;
type CaptureOuterAndLocalAnonPayloadAnonInnerCont0SType<'a, 'x> = &'x u8;
type CaptureOuterAndLocalAnonPayloadAnonInnerCont0Input<'a, 'b, 'x> = POrSType<CaptureOuterAndLocalAnonPayloadAnonInnerCont0Type<'a, 'b>, CaptureOuterAndLocalAnonPayloadAnonInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureOuterAndLocalAnonPayloadAnonInnerCont0Input<'a, 'b, 'x>> for CaptureOuterAndLocalAnonPayloadAnonInnerCont0 {
    type Output = CaptureOuterAndLocalAnonPayloadAnonInnerAnonBodyCombinator;

    open spec fn requires(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerCont0Input<'a, 'b, 'x>) -> bool {        let frame_len = self.frame_len@;

        &&& ((self.frame_len@) >= 1)
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_outer_and_local_anon_payload_anon_inner_cont0(self.frame_len@, deps@)
    }

    fn apply(&self, deps: CaptureOuterAndLocalAnonPayloadAnonInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = deps;
                let frame_len = self.frame_len;
                let tag = *tag;
                capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len, tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let frame_len = self.frame_len;
                let tag = *tag;
                capture_outer_and_local_anon_payload_anon_inner_anon_body(frame_len, tag)
            }
        }
    }
}
pub type SpecCaptureOuterAndLocalAnonPayload = SpecCaptureOuterAndLocalAnonPayloadAnonInner;
pub type CaptureOuterAndLocalAnonPayload<'a> = CaptureOuterAndLocalAnonPayloadAnonInner<'a>;
pub type CaptureOuterAndLocalAnonPayloadRef<'a> = &'a CaptureOuterAndLocalAnonPayloadAnonInner<'a>;


pub struct SpecCaptureOuterAndLocalAnonPayloadCombinator(pub SpecCaptureOuterAndLocalAnonPayloadCombinatorAlias);

impl SpecCombinator for SpecCaptureOuterAndLocalAnonPayloadCombinator {
    type Type = SpecCaptureOuterAndLocalAnonPayload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureOuterAndLocalAnonPayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureOuterAndLocalAnonPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureOuterAndLocalAnonPayloadCombinatorAlias = AndThen<bytes::Variable, SpecCaptureOuterAndLocalAnonPayloadAnonInnerCombinator>;

pub struct CaptureOuterAndLocalAnonPayloadCombinator(pub CaptureOuterAndLocalAnonPayloadCombinatorAlias);

impl View for CaptureOuterAndLocalAnonPayloadCombinator {
    type V = SpecCaptureOuterAndLocalAnonPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureOuterAndLocalAnonPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureOuterAndLocalAnonPayloadCombinator {
    type Type = CaptureOuterAndLocalAnonPayload<'a>;
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
pub type CaptureOuterAndLocalAnonPayloadCombinatorAlias = AndThen<bytes::Variable, CaptureOuterAndLocalAnonPayloadAnonInnerCombinator>;


pub open spec fn spec_capture_outer_and_local_anon_payload(frame_len: u8) -> SpecCaptureOuterAndLocalAnonPayloadCombinator {
    SpecCaptureOuterAndLocalAnonPayloadCombinator(AndThen(bytes::Variable((usize::spec_from(frame_len)) as usize), spec_capture_outer_and_local_anon_payload_anon_inner(frame_len)))
}

pub fn capture_outer_and_local_anon_payload<'a>(frame_len: u8) -> (o: CaptureOuterAndLocalAnonPayloadCombinator)
    requires
        ((frame_len) >= 1),

    ensures o@ == spec_capture_outer_and_local_anon_payload(frame_len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureOuterAndLocalAnonPayloadCombinator(AndThen(bytes::Variable((usize::ex_from(frame_len)) as usize), capture_outer_and_local_anon_payload_anon_inner(frame_len)));
    // assert({
    //     &&& combinator@ == spec_capture_outer_and_local_anon_payload(frame_len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_outer_and_local_anon_payload<'a>(input: &'a [u8], frame_len: u8) -> (res: PResult<<CaptureOuterAndLocalAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        res matches Ok((n, v)) ==> spec_capture_outer_and_local_anon_payload(frame_len@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_outer_and_local_anon_payload(frame_len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_outer_and_local_anon_payload(frame_len@).spec_parse(input@) is None,
        spec_capture_outer_and_local_anon_payload(frame_len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_outer_and_local_anon_payload( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_outer_and_local_anon_payload<'a>(v: <CaptureOuterAndLocalAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, frame_len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_outer_and_local_anon_payload(frame_len@).wf(v@),
        ((frame_len) >= 1),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_outer_and_local_anon_payload(frame_len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_outer_and_local_anon_payload(frame_len@).spec_serialize(v@))
        },
{
    let combinator = capture_outer_and_local_anon_payload( frame_len );
    combinator.serialize(v, data, pos)
}

pub fn capture_outer_and_local_anon_payload_len<'a>(v: <CaptureOuterAndLocalAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, frame_len: u8) -> (serialize_len: usize)
    requires
        spec_capture_outer_and_local_anon_payload(frame_len@).wf(v@),
        spec_capture_outer_and_local_anon_payload(frame_len@).spec_serialize(v@).len() <= usize::MAX,
        ((frame_len) >= 1),

    ensures
        serialize_len == spec_capture_outer_and_local_anon_payload(frame_len@).spec_serialize(v@).len(),
{
    let combinator = capture_outer_and_local_anon_payload( frame_len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureOuterAndLocal {
    pub frame_len: u8,
    pub payload: SpecCaptureOuterAndLocalAnonPayload,
}

pub type SpecCaptureOuterAndLocalInner = (u8, SpecCaptureOuterAndLocalAnonPayload);


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
    pub payload: CaptureOuterAndLocalAnonPayload<'a>,
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
pub type CaptureOuterAndLocalInner<'a> = (u8, CaptureOuterAndLocalAnonPayload<'a>);

pub type CaptureOuterAndLocalInnerRef<'a> = (&'a u8, &'a CaptureOuterAndLocalAnonPayload<'a>);
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
pub type SpecCaptureOuterAndLocalCombinatorAlias = Mapped<SpecPair<Refined<U8, Predicate2172399096230090262>, SpecCaptureOuterAndLocalAnonPayloadCombinator>, CaptureOuterAndLocalMapper>;
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
pub type CaptureOuterAndLocalCombinatorAlias = Mapped<Pair<Refined<U8, Predicate2172399096230090262>, CaptureOuterAndLocalAnonPayloadCombinator, CaptureOuterAndLocalCont0>, CaptureOuterAndLocalMapper>;


pub open spec fn spec_capture_outer_and_local() -> SpecCaptureOuterAndLocalCombinator {
    SpecCaptureOuterAndLocalCombinator(
    Mapped {
        inner: Pair::spec_new(Refined { inner: U8, predicate: Predicate2172399096230090262 }, |deps| spec_capture_outer_and_local_cont0(deps)),
        mapper: CaptureOuterAndLocalMapper,
    })
}

pub open spec fn spec_capture_outer_and_local_cont0(deps: u8) -> SpecCaptureOuterAndLocalAnonPayloadCombinator {
    let frame_len = deps;
    spec_capture_outer_and_local_anon_payload(frame_len)
}

impl View for CaptureOuterAndLocalCont0 {
    type V = spec_fn(u8) -> SpecCaptureOuterAndLocalAnonPayloadCombinator;

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
    type Output = CaptureOuterAndLocalAnonPayloadCombinator;

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
                capture_outer_and_local_anon_payload(frame_len)
            }
            POrSType::S(deps) => {
                let frame_len = deps;
                let frame_len = *frame_len;
                capture_outer_and_local_anon_payload(frame_len)
            }
        }
    }
}
                

pub struct SpecNestedInnerStructAnonInnerAnonInner {
    pub x: u8,
    pub y: Seq<u8>,
}

pub type SpecNestedInnerStructAnonInnerAnonInnerInner = (u8, Seq<u8>);


impl SpecFrom<SpecNestedInnerStructAnonInnerAnonInner> for SpecNestedInnerStructAnonInnerAnonInnerInner {
    open spec fn spec_from(m: SpecNestedInnerStructAnonInnerAnonInner) -> SpecNestedInnerStructAnonInnerAnonInnerInner {
        (m.x, m.y)
    }
}

impl SpecFrom<SpecNestedInnerStructAnonInnerAnonInnerInner> for SpecNestedInnerStructAnonInnerAnonInner {
    open spec fn spec_from(m: SpecNestedInnerStructAnonInnerAnonInnerInner) -> SpecNestedInnerStructAnonInnerAnonInner {
        let (x, y) = m;
        SpecNestedInnerStructAnonInnerAnonInner { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct NestedInnerStructAnonInnerAnonInner<'a> {
    pub x: u8,
    pub y: &'a [u8],
}

impl View for NestedInnerStructAnonInnerAnonInner<'_> {
    type V = SpecNestedInnerStructAnonInnerAnonInner;

    open spec fn view(&self) -> Self::V {
        SpecNestedInnerStructAnonInnerAnonInner {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type NestedInnerStructAnonInnerAnonInnerInner<'a> = (u8, &'a [u8]);

pub type NestedInnerStructAnonInnerAnonInnerInnerRef<'a> = (&'a u8, &'a &'a [u8]);
impl<'a> From<&'a NestedInnerStructAnonInnerAnonInner<'a>> for NestedInnerStructAnonInnerAnonInnerInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerStructAnonInnerAnonInner) -> NestedInnerStructAnonInnerAnonInnerInnerRef<'a> {
        (&m.x, &m.y)
    }
}

impl<'a> From<NestedInnerStructAnonInnerAnonInnerInner<'a>> for NestedInnerStructAnonInnerAnonInner<'a> {
    fn ex_from(m: NestedInnerStructAnonInnerAnonInnerInner) -> NestedInnerStructAnonInnerAnonInner {
        let (x, y) = m;
        NestedInnerStructAnonInnerAnonInner { x, y }
    }
}

pub struct NestedInnerStructAnonInnerAnonInnerMapper;
impl View for NestedInnerStructAnonInnerAnonInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerStructAnonInnerAnonInnerMapper {
    type Src = SpecNestedInnerStructAnonInnerAnonInnerInner;
    type Dst = SpecNestedInnerStructAnonInnerAnonInner;
}
impl SpecIsoProof for NestedInnerStructAnonInnerAnonInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerStructAnonInnerAnonInnerMapper {
    type Src = NestedInnerStructAnonInnerAnonInnerInner<'a>;
    type Dst = NestedInnerStructAnonInnerAnonInner<'a>;
    type RefSrc = NestedInnerStructAnonInnerAnonInnerInnerRef<'a>;
}
type SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias1 = (U8, bytes::Tail);
pub struct SpecNestedInnerStructAnonInnerAnonInnerCombinator(pub SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias);

impl SpecCombinator for SpecNestedInnerStructAnonInnerAnonInnerCombinator {
    type Type = SpecNestedInnerStructAnonInnerAnonInner;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerStructAnonInnerAnonInnerCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias = Mapped<SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias1, NestedInnerStructAnonInnerAnonInnerMapper>;
type NestedInnerStructAnonInnerAnonInnerCombinatorAlias1 = (U8, bytes::Tail);
pub struct NestedInnerStructAnonInnerAnonInnerCombinator1(pub NestedInnerStructAnonInnerAnonInnerCombinatorAlias1);
impl View for NestedInnerStructAnonInnerAnonInnerCombinator1 {
    type V = SpecNestedInnerStructAnonInnerAnonInnerCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerStructAnonInnerAnonInnerCombinator1, NestedInnerStructAnonInnerAnonInnerCombinatorAlias1);

pub struct NestedInnerStructAnonInnerAnonInnerCombinator(pub NestedInnerStructAnonInnerAnonInnerCombinatorAlias);

impl View for NestedInnerStructAnonInnerAnonInnerCombinator {
    type V = SpecNestedInnerStructAnonInnerAnonInnerCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerStructAnonInnerAnonInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerStructAnonInnerAnonInnerCombinator {
    type Type = NestedInnerStructAnonInnerAnonInner<'a>;
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
pub type NestedInnerStructAnonInnerAnonInnerCombinatorAlias = Mapped<NestedInnerStructAnonInnerAnonInnerCombinator1, NestedInnerStructAnonInnerAnonInnerMapper>;


pub open spec fn spec_nested_inner_struct_anon_inner_anon_inner() -> SpecNestedInnerStructAnonInnerAnonInnerCombinator {
    SpecNestedInnerStructAnonInnerAnonInnerCombinator(
    Mapped {
        inner: (U8, bytes::Tail),
        mapper: NestedInnerStructAnonInnerAnonInnerMapper,
    })
}

                
pub fn nested_inner_struct_anon_inner_anon_inner<'a>() -> (o: NestedInnerStructAnonInnerAnonInnerCombinator)
    ensures o@ == spec_nested_inner_struct_anon_inner_anon_inner(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerStructAnonInnerAnonInnerCombinator(
    Mapped {
        inner: NestedInnerStructAnonInnerAnonInnerCombinator1((U8, bytes::Tail)),
        mapper: NestedInnerStructAnonInnerAnonInnerMapper,
    });
    // assert({
    //     &&& combinator@ == spec_nested_inner_struct_anon_inner_anon_inner()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_struct_anon_inner_anon_inner<'a>(input: &'a [u8]) -> (res: PResult<<NestedInnerStructAnonInnerAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_struct_anon_inner_anon_inner().spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_struct_anon_inner_anon_inner().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_struct_anon_inner_anon_inner().spec_parse(input@) is None,
        spec_nested_inner_struct_anon_inner_anon_inner().spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_struct_anon_inner_anon_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_struct_anon_inner_anon_inner<'a>(v: <NestedInnerStructAnonInnerAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_struct_anon_inner_anon_inner().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_struct_anon_inner_anon_inner().spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_struct_anon_inner_anon_inner().spec_serialize(v@))
        },
{
    let combinator = nested_inner_struct_anon_inner_anon_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, data, pos)
}

pub fn nested_inner_struct_anon_inner_anon_inner_len<'a>(v: <NestedInnerStructAnonInnerAnonInnerCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_nested_inner_struct_anon_inner_anon_inner().wf(v@),
        spec_nested_inner_struct_anon_inner_anon_inner().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_nested_inner_struct_anon_inner_anon_inner().spec_serialize(v@).len(),
{
    let combinator = nested_inner_struct_anon_inner_anon_inner();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                
pub type SpecNestedInnerStructAnonInner = SpecNestedInnerStructAnonInnerAnonInner;
pub type NestedInnerStructAnonInner<'a> = NestedInnerStructAnonInnerAnonInner<'a>;
pub type NestedInnerStructAnonInnerRef<'a> = &'a NestedInnerStructAnonInnerAnonInner<'a>;


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
pub type SpecNestedInnerStructAnonInnerCombinatorAlias = AndThen<bytes::Variable, SpecNestedInnerStructAnonInnerAnonInnerCombinator>;

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
pub type NestedInnerStructAnonInnerCombinatorAlias = AndThen<bytes::Variable, NestedInnerStructAnonInnerAnonInnerCombinator>;


pub open spec fn spec_nested_inner_struct_anon_inner(len: u32) -> SpecNestedInnerStructAnonInnerCombinator {
    SpecNestedInnerStructAnonInnerCombinator(AndThen(bytes::Variable((usize::spec_from(len)) as usize), spec_nested_inner_struct_anon_inner_anon_inner()))
}

pub fn nested_inner_struct_anon_inner<'a>(len: u32) -> (o: NestedInnerStructAnonInnerCombinator)

    ensures o@ == spec_nested_inner_struct_anon_inner(len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerStructAnonInnerCombinator(AndThen(bytes::Variable((usize::ex_from(len)) as usize), nested_inner_struct_anon_inner_anon_inner()));
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


pub enum SpecNestedInnerChoiceAnonX {
    A(SpecNestedInnerChoiceAnonXAnonA),
    B(u32),
}

pub type SpecNestedInnerChoiceAnonXInner = Either<SpecNestedInnerChoiceAnonXAnonA, u32>;

impl SpecFrom<SpecNestedInnerChoiceAnonX> for SpecNestedInnerChoiceAnonXInner {
    open spec fn spec_from(m: SpecNestedInnerChoiceAnonX) -> SpecNestedInnerChoiceAnonXInner {
        match m {
            SpecNestedInnerChoiceAnonX::A(m) => Either::Left(m),
            SpecNestedInnerChoiceAnonX::B(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecNestedInnerChoiceAnonXInner> for SpecNestedInnerChoiceAnonX {
    open spec fn spec_from(m: SpecNestedInnerChoiceAnonXInner) -> SpecNestedInnerChoiceAnonX {
        match m {
            Either::Left(m) => SpecNestedInnerChoiceAnonX::A(m),
            Either::Right(m) => SpecNestedInnerChoiceAnonX::B(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NestedInnerChoiceAnonX {
    A(NestedInnerChoiceAnonXAnonA),
    B(u32),
}

pub type NestedInnerChoiceAnonXInner = Either<NestedInnerChoiceAnonXAnonA, u32>;

pub type NestedInnerChoiceAnonXInnerRef<'a> = Either<&'a NestedInnerChoiceAnonXAnonA, &'a u32>;


impl View for NestedInnerChoiceAnonX {
    type V = SpecNestedInnerChoiceAnonX;
    open spec fn view(&self) -> Self::V {
        match self {
            NestedInnerChoiceAnonX::A(m) => SpecNestedInnerChoiceAnonX::A(m@),
            NestedInnerChoiceAnonX::B(m) => SpecNestedInnerChoiceAnonX::B(m@),
        }
    }
}


impl<'a> From<&'a NestedInnerChoiceAnonX> for NestedInnerChoiceAnonXInnerRef<'a> {
    fn ex_from(m: &'a NestedInnerChoiceAnonX) -> NestedInnerChoiceAnonXInnerRef<'a> {
        match m {
            NestedInnerChoiceAnonX::A(m) => Either::Left(m),
            NestedInnerChoiceAnonX::B(m) => Either::Right(m),
        }
    }

}

impl From<NestedInnerChoiceAnonXInner> for NestedInnerChoiceAnonX {
    fn ex_from(m: NestedInnerChoiceAnonXInner) -> NestedInnerChoiceAnonX {
        match m {
            Either::Left(m) => NestedInnerChoiceAnonX::A(m),
            Either::Right(m) => NestedInnerChoiceAnonX::B(m),
        }
    }
    
}


pub struct NestedInnerChoiceAnonXMapper;
impl View for NestedInnerChoiceAnonXMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NestedInnerChoiceAnonXMapper {
    type Src = SpecNestedInnerChoiceAnonXInner;
    type Dst = SpecNestedInnerChoiceAnonX;
}
impl SpecIsoProof for NestedInnerChoiceAnonXMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for NestedInnerChoiceAnonXMapper {
    type Src = NestedInnerChoiceAnonXInner;
    type Dst = NestedInnerChoiceAnonX;
    type RefSrc = NestedInnerChoiceAnonXInnerRef<'a>;
}

type SpecNestedInnerChoiceAnonXCombinatorAlias1 = Choice<Cond<SpecNestedInnerChoiceAnonXAnonACombinator>, Cond<U32Le>>;
pub struct SpecNestedInnerChoiceAnonXCombinator(pub SpecNestedInnerChoiceAnonXCombinatorAlias);

impl SpecCombinator for SpecNestedInnerChoiceAnonXCombinator {
    type Type = SpecNestedInnerChoiceAnonX;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNestedInnerChoiceAnonXCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecNestedInnerChoiceAnonXCombinatorAlias::is_prefix_secure() }
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
pub type SpecNestedInnerChoiceAnonXCombinatorAlias = Mapped<SpecNestedInnerChoiceAnonXCombinatorAlias1, NestedInnerChoiceAnonXMapper>;
type NestedInnerChoiceAnonXCombinatorAlias1 = Choice<Cond<NestedInnerChoiceAnonXAnonACombinator>, Cond<U32Le>>;
pub struct NestedInnerChoiceAnonXCombinator1(pub NestedInnerChoiceAnonXCombinatorAlias1);
impl View for NestedInnerChoiceAnonXCombinator1 {
    type V = SpecNestedInnerChoiceAnonXCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(NestedInnerChoiceAnonXCombinator1, NestedInnerChoiceAnonXCombinatorAlias1);

pub struct NestedInnerChoiceAnonXCombinator(pub NestedInnerChoiceAnonXCombinatorAlias);

impl View for NestedInnerChoiceAnonXCombinator {
    type V = SpecNestedInnerChoiceAnonXCombinator;
    open spec fn view(&self) -> Self::V { SpecNestedInnerChoiceAnonXCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NestedInnerChoiceAnonXCombinator {
    type Type = NestedInnerChoiceAnonX;
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
pub type NestedInnerChoiceAnonXCombinatorAlias = Mapped<NestedInnerChoiceAnonXCombinator1, NestedInnerChoiceAnonXMapper>;


pub open spec fn spec_nested_inner_choice_anon_x(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecNestedInnerChoiceAnonXCombinator {
    SpecNestedInnerChoiceAnonXCombinator(Mapped { inner: Choice(Cond { cond: choice1 == AOrB::A, inner: spec_nested_inner_choice_anon_x_anon_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: U32Le }), mapper: NestedInnerChoiceAnonXMapper })
}

pub fn nested_inner_choice_anon_x<'a>(choice1: AOrB, choice2: COrD) -> (o: NestedInnerChoiceAnonXCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_nested_inner_choice_anon_x(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = NestedInnerChoiceAnonXCombinator(Mapped { inner: NestedInnerChoiceAnonXCombinator1(Choice::new(Cond { cond: choice1 == AOrB::A, inner: nested_inner_choice_anon_x_anon_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: U32Le })), mapper: NestedInnerChoiceAnonXMapper });
    // assert({
    //     &&& combinator@ == spec_nested_inner_choice_anon_x(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_nested_inner_choice_anon_x<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<NestedInnerChoiceAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_parse(input@) is None,
        spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = nested_inner_choice_anon_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_nested_inner_choice_anon_x<'a>(v: <NestedInnerChoiceAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_nested_inner_choice_anon_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = nested_inner_choice_anon_x( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn nested_inner_choice_anon_x_len<'a>(v: <NestedInnerChoiceAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_nested_inner_choice_anon_x(choice1@, choice2@).wf(v@),
        spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_nested_inner_choice_anon_x(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = nested_inner_choice_anon_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub enum SpecCaptureParamAndLocalAnonXAnonAAnonPayload {
    C(Seq<u8>),
    D(Seq<u8>),
}

pub type SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner = Either<Seq<u8>, Seq<u8>>;

impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonAAnonPayload> for SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonAAnonPayload) -> SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner {
        match m {
            SpecCaptureParamAndLocalAnonXAnonAAnonPayload::C(m) => Either::Left(m),
            SpecCaptureParamAndLocalAnonXAnonAAnonPayload::D(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner> for SpecCaptureParamAndLocalAnonXAnonAAnonPayload {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner) -> SpecCaptureParamAndLocalAnonXAnonAAnonPayload {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalAnonXAnonAAnonPayload::C(m),
            Either::Right(m) => SpecCaptureParamAndLocalAnonXAnonAAnonPayload::D(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalAnonXAnonAAnonPayload<'a> {
    C(&'a [u8]),
    D(&'a [u8]),
}

pub type CaptureParamAndLocalAnonXAnonAAnonPayloadInner<'a> = Either<&'a [u8], &'a [u8]>;

pub type CaptureParamAndLocalAnonXAnonAAnonPayloadInnerRef<'a> = Either<&'a &'a [u8], &'a &'a [u8]>;


impl<'a> View for CaptureParamAndLocalAnonXAnonAAnonPayload<'a> {
    type V = SpecCaptureParamAndLocalAnonXAnonAAnonPayload;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalAnonXAnonAAnonPayload::C(m) => SpecCaptureParamAndLocalAnonXAnonAAnonPayload::C(m@),
            CaptureParamAndLocalAnonXAnonAAnonPayload::D(m) => SpecCaptureParamAndLocalAnonXAnonAAnonPayload::D(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalAnonXAnonAAnonPayload<'a>> for CaptureParamAndLocalAnonXAnonAAnonPayloadInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalAnonXAnonAAnonPayload<'a>) -> CaptureParamAndLocalAnonXAnonAAnonPayloadInnerRef<'a> {
        match m {
            CaptureParamAndLocalAnonXAnonAAnonPayload::C(m) => Either::Left(m),
            CaptureParamAndLocalAnonXAnonAAnonPayload::D(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureParamAndLocalAnonXAnonAAnonPayloadInner<'a>> for CaptureParamAndLocalAnonXAnonAAnonPayload<'a> {
    fn ex_from(m: CaptureParamAndLocalAnonXAnonAAnonPayloadInner<'a>) -> CaptureParamAndLocalAnonXAnonAAnonPayload<'a> {
        match m {
            Either::Left(m) => CaptureParamAndLocalAnonXAnonAAnonPayload::C(m),
            Either::Right(m) => CaptureParamAndLocalAnonXAnonAAnonPayload::D(m),
        }
    }
    
}


pub struct CaptureParamAndLocalAnonXAnonAAnonPayloadMapper;
impl View for CaptureParamAndLocalAnonXAnonAAnonPayloadMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalAnonXAnonAAnonPayloadMapper {
    type Src = SpecCaptureParamAndLocalAnonXAnonAAnonPayloadInner;
    type Dst = SpecCaptureParamAndLocalAnonXAnonAAnonPayload;
}
impl SpecIsoProof for CaptureParamAndLocalAnonXAnonAAnonPayloadMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalAnonXAnonAAnonPayloadMapper {
    type Src = CaptureParamAndLocalAnonXAnonAAnonPayloadInner<'a>;
    type Dst = CaptureParamAndLocalAnonXAnonAAnonPayload<'a>;
    type RefSrc = CaptureParamAndLocalAnonXAnonAAnonPayloadInnerRef<'a>;
}

type SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<bytes::Variable>>;
pub struct SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator(pub SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    type Type = SpecCaptureParamAndLocalAnonXAnonAAnonPayload;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias = Mapped<SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1, CaptureParamAndLocalAnonXAnonAAnonPayloadMapper>;
type CaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1 = Choice<Cond<bytes::Variable>, Cond<bytes::Variable>>;
pub struct CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator1(pub CaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1);
impl View for CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator1 {
    type V = SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator1, CaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias1);

pub struct CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator(pub CaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias);

impl View for CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    type V = SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    type Type = CaptureParamAndLocalAnonXAnonAAnonPayload<'a>;
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
pub type CaptureParamAndLocalAnonXAnonAAnonPayloadCombinatorAlias = Mapped<CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator1, CaptureParamAndLocalAnonXAnonAAnonPayloadMapper>;


pub open spec fn spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2: SpecCOrD, len: u8) -> SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator(Mapped { inner: Choice(Cond { cond: choice2 == COrD::C, inner: bytes::Variable((usize::spec_from(len)) as usize) }, Cond { cond: choice2 == COrD::D, inner: bytes::Variable((usize::spec_from(len)) as usize) }), mapper: CaptureParamAndLocalAnonXAnonAAnonPayloadMapper })
}

pub fn capture_param_and_local_anon_x_anon_a_anon_payload<'a>(choice2: COrD, len: u8) -> (o: CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator(Mapped { inner: CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator1(Choice::new(Cond { cond: choice2 == COrD::C, inner: bytes::Variable((usize::ex_from(len)) as usize) }, Cond { cond: choice2 == COrD::D, inner: bytes::Variable((usize::ex_from(len)) as usize) })), mapper: CaptureParamAndLocalAnonXAnonAAnonPayloadMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_anon_x_anon_a_anon_payload<'a>(input: &'a [u8], choice2: COrD, len: u8) -> (res: PResult<<CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_parse(input@) is None,
        spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_anon_x_anon_a_anon_payload( choice2, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_anon_x_anon_a_anon_payload<'a>(v: <CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD, len: u8) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_anon_x_anon_a_anon_payload( choice2, len );
    combinator.serialize(v, data, pos)
}

pub fn capture_param_and_local_anon_x_anon_a_anon_payload_len<'a>(v: <CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD, len: u8) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).wf(v@),
        spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2@, len@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_anon_x_anon_a_anon_payload( choice2, len );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecCaptureParamAndLocalAnonXAnonA {
    pub len: u8,
    pub payload: SpecCaptureParamAndLocalAnonXAnonAAnonPayload,
}

pub type SpecCaptureParamAndLocalAnonXAnonAInner = (u8, SpecCaptureParamAndLocalAnonXAnonAAnonPayload);


impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonA> for SpecCaptureParamAndLocalAnonXAnonAInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonA) -> SpecCaptureParamAndLocalAnonXAnonAInner {
        (m.len, m.payload)
    }
}

impl SpecFrom<SpecCaptureParamAndLocalAnonXAnonAInner> for SpecCaptureParamAndLocalAnonXAnonA {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXAnonAInner) -> SpecCaptureParamAndLocalAnonXAnonA {
        let (len, payload) = m;
        SpecCaptureParamAndLocalAnonXAnonA { len, payload }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CaptureParamAndLocalAnonXAnonA<'a> {
    pub len: u8,
    pub payload: CaptureParamAndLocalAnonXAnonAAnonPayload<'a>,
}

impl View for CaptureParamAndLocalAnonXAnonA<'_> {
    type V = SpecCaptureParamAndLocalAnonXAnonA;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocalAnonXAnonA {
            len: self.len@,
            payload: self.payload@,
        }
    }
}
pub type CaptureParamAndLocalAnonXAnonAInner<'a> = (u8, CaptureParamAndLocalAnonXAnonAAnonPayload<'a>);

pub type CaptureParamAndLocalAnonXAnonAInnerRef<'a> = (&'a u8, &'a CaptureParamAndLocalAnonXAnonAAnonPayload<'a>);
impl<'a> From<&'a CaptureParamAndLocalAnonXAnonA<'a>> for CaptureParamAndLocalAnonXAnonAInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalAnonXAnonA) -> CaptureParamAndLocalAnonXAnonAInnerRef<'a> {
        (&m.len, &m.payload)
    }
}

impl<'a> From<CaptureParamAndLocalAnonXAnonAInner<'a>> for CaptureParamAndLocalAnonXAnonA<'a> {
    fn ex_from(m: CaptureParamAndLocalAnonXAnonAInner) -> CaptureParamAndLocalAnonXAnonA {
        let (len, payload) = m;
        CaptureParamAndLocalAnonXAnonA { len, payload }
    }
}

pub struct CaptureParamAndLocalAnonXAnonAMapper;
impl View for CaptureParamAndLocalAnonXAnonAMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalAnonXAnonAMapper {
    type Src = SpecCaptureParamAndLocalAnonXAnonAInner;
    type Dst = SpecCaptureParamAndLocalAnonXAnonA;
}
impl SpecIsoProof for CaptureParamAndLocalAnonXAnonAMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalAnonXAnonAMapper {
    type Src = CaptureParamAndLocalAnonXAnonAInner<'a>;
    type Dst = CaptureParamAndLocalAnonXAnonA<'a>;
    type RefSrc = CaptureParamAndLocalAnonXAnonAInnerRef<'a>;
}

pub struct SpecCaptureParamAndLocalAnonXAnonACombinator(pub SpecCaptureParamAndLocalAnonXAnonACombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalAnonXAnonACombinator {
    type Type = SpecCaptureParamAndLocalAnonXAnonA;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalAnonXAnonACombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalAnonXAnonACombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalAnonXAnonACombinatorAlias = Mapped<SpecPair<U8, SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator>, CaptureParamAndLocalAnonXAnonAMapper>;

pub struct CaptureParamAndLocalAnonXAnonACombinator(pub CaptureParamAndLocalAnonXAnonACombinatorAlias);

impl View for CaptureParamAndLocalAnonXAnonACombinator {
    type V = SpecCaptureParamAndLocalAnonXAnonACombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalAnonXAnonACombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalAnonXAnonACombinator {
    type Type = CaptureParamAndLocalAnonXAnonA<'a>;
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
pub type CaptureParamAndLocalAnonXAnonACombinatorAlias = Mapped<Pair<U8, CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator, CaptureParamAndLocalAnonXAnonACont0>, CaptureParamAndLocalAnonXAnonAMapper>;


pub open spec fn spec_capture_param_and_local_anon_x_anon_a(choice2: SpecCOrD) -> SpecCaptureParamAndLocalAnonXAnonACombinator {
    SpecCaptureParamAndLocalAnonXAnonACombinator(
    Mapped {
        inner: Pair::spec_new(U8, |deps| spec_capture_param_and_local_anon_x_anon_a_cont0(choice2, deps)),
        mapper: CaptureParamAndLocalAnonXAnonAMapper,
    })
}

pub open spec fn spec_capture_param_and_local_anon_x_anon_a_cont0(choice2: SpecCOrD, deps: u8) -> SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator {
    let len = deps;
    spec_capture_param_and_local_anon_x_anon_a_anon_payload(choice2, len)
}

impl View for CaptureParamAndLocalAnonXAnonACont0 {
    type V = spec_fn(u8) -> SpecCaptureParamAndLocalAnonXAnonAAnonPayloadCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_capture_param_and_local_anon_x_anon_a_cont0(self.choice2@, deps)
        }
    }
}

pub fn capture_param_and_local_anon_x_anon_a<'a>(choice2: COrD) -> (o: CaptureParamAndLocalAnonXAnonACombinator)
    requires
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_anon_x_anon_a(choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalAnonXAnonACombinator(
    Mapped {
        inner: Pair::new(U8, CaptureParamAndLocalAnonXAnonACont0 { choice2 }),
        mapper: CaptureParamAndLocalAnonXAnonAMapper,
    });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_anon_x_anon_a(choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_anon_x_anon_a<'a>(input: &'a [u8], choice2: COrD) -> (res: PResult<<CaptureParamAndLocalAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_parse(input@) is None,
        spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_anon_x_anon_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_anon_x_anon_a<'a>(v: <CaptureParamAndLocalAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_anon_x_anon_a(choice2@).wf(v@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_anon_x_anon_a( choice2 );
    combinator.serialize(v, data, pos)
}

pub fn capture_param_and_local_anon_x_anon_a_len<'a>(v: <CaptureParamAndLocalAnonXAnonACombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_anon_x_anon_a(choice2@).wf(v@),
        spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_anon_x_anon_a(choice2@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_anon_x_anon_a( choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

pub struct CaptureParamAndLocalAnonXAnonACont0 {
    pub choice2: COrD,
}
type CaptureParamAndLocalAnonXAnonACont0Type<'a, 'b> = &'b u8;
type CaptureParamAndLocalAnonXAnonACont0SType<'a, 'x> = &'x u8;
type CaptureParamAndLocalAnonXAnonACont0Input<'a, 'b, 'x> = POrSType<CaptureParamAndLocalAnonXAnonACont0Type<'a, 'b>, CaptureParamAndLocalAnonXAnonACont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CaptureParamAndLocalAnonXAnonACont0Input<'a, 'b, 'x>> for CaptureParamAndLocalAnonXAnonACont0 {
    type Output = CaptureParamAndLocalAnonXAnonAAnonPayloadCombinator;

    open spec fn requires(&self, deps: CaptureParamAndLocalAnonXAnonACont0Input<'a, 'b, 'x>) -> bool {        let choice2 = self.choice2@;

        &&& spec_c_or_d().wf(self.choice2@)
        &&& (U8).wf(deps@)
        }

    open spec fn ensures(&self, deps: CaptureParamAndLocalAnonXAnonACont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o)
        &&& o@ == spec_capture_param_and_local_anon_x_anon_a_cont0(self.choice2@, deps@)
    }

    fn apply(&self, deps: CaptureParamAndLocalAnonXAnonACont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let len = deps;
                let choice2 = self.choice2;
                let len = *len;
                capture_param_and_local_anon_x_anon_a_anon_payload(choice2, len)
            }
            POrSType::S(deps) => {
                let len = deps;
                let choice2 = self.choice2;
                let len = *len;
                capture_param_and_local_anon_x_anon_a_anon_payload(choice2, len)
            }
        }
    }
}

pub enum SpecCaptureParamAndLocalAnonX {
    A(SpecCaptureParamAndLocalAnonXAnonA),
    B(SpecCaptureParamAndLocalAnonXAnonB),
}

pub type SpecCaptureParamAndLocalAnonXInner = Either<SpecCaptureParamAndLocalAnonXAnonA, SpecCaptureParamAndLocalAnonXAnonB>;

impl SpecFrom<SpecCaptureParamAndLocalAnonX> for SpecCaptureParamAndLocalAnonXInner {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonX) -> SpecCaptureParamAndLocalAnonXInner {
        match m {
            SpecCaptureParamAndLocalAnonX::A(m) => Either::Left(m),
            SpecCaptureParamAndLocalAnonX::B(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecCaptureParamAndLocalAnonXInner> for SpecCaptureParamAndLocalAnonX {
    open spec fn spec_from(m: SpecCaptureParamAndLocalAnonXInner) -> SpecCaptureParamAndLocalAnonX {
        match m {
            Either::Left(m) => SpecCaptureParamAndLocalAnonX::A(m),
            Either::Right(m) => SpecCaptureParamAndLocalAnonX::B(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaptureParamAndLocalAnonX<'a> {
    A(CaptureParamAndLocalAnonXAnonA<'a>),
    B(CaptureParamAndLocalAnonXAnonB),
}

pub type CaptureParamAndLocalAnonXInner<'a> = Either<CaptureParamAndLocalAnonXAnonA<'a>, CaptureParamAndLocalAnonXAnonB>;

pub type CaptureParamAndLocalAnonXInnerRef<'a> = Either<&'a CaptureParamAndLocalAnonXAnonA<'a>, &'a CaptureParamAndLocalAnonXAnonB>;


impl<'a> View for CaptureParamAndLocalAnonX<'a> {
    type V = SpecCaptureParamAndLocalAnonX;
    open spec fn view(&self) -> Self::V {
        match self {
            CaptureParamAndLocalAnonX::A(m) => SpecCaptureParamAndLocalAnonX::A(m@),
            CaptureParamAndLocalAnonX::B(m) => SpecCaptureParamAndLocalAnonX::B(m@),
        }
    }
}


impl<'a> From<&'a CaptureParamAndLocalAnonX<'a>> for CaptureParamAndLocalAnonXInnerRef<'a> {
    fn ex_from(m: &'a CaptureParamAndLocalAnonX<'a>) -> CaptureParamAndLocalAnonXInnerRef<'a> {
        match m {
            CaptureParamAndLocalAnonX::A(m) => Either::Left(m),
            CaptureParamAndLocalAnonX::B(m) => Either::Right(m),
        }
    }

}

impl<'a> From<CaptureParamAndLocalAnonXInner<'a>> for CaptureParamAndLocalAnonX<'a> {
    fn ex_from(m: CaptureParamAndLocalAnonXInner<'a>) -> CaptureParamAndLocalAnonX<'a> {
        match m {
            Either::Left(m) => CaptureParamAndLocalAnonX::A(m),
            Either::Right(m) => CaptureParamAndLocalAnonX::B(m),
        }
    }
    
}


pub struct CaptureParamAndLocalAnonXMapper;
impl View for CaptureParamAndLocalAnonXMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CaptureParamAndLocalAnonXMapper {
    type Src = SpecCaptureParamAndLocalAnonXInner;
    type Dst = SpecCaptureParamAndLocalAnonX;
}
impl SpecIsoProof for CaptureParamAndLocalAnonXMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CaptureParamAndLocalAnonXMapper {
    type Src = CaptureParamAndLocalAnonXInner<'a>;
    type Dst = CaptureParamAndLocalAnonX<'a>;
    type RefSrc = CaptureParamAndLocalAnonXInnerRef<'a>;
}

type SpecCaptureParamAndLocalAnonXCombinatorAlias1 = Choice<Cond<SpecCaptureParamAndLocalAnonXAnonACombinator>, Cond<SpecCaptureParamAndLocalAnonXAnonBCombinator>>;
pub struct SpecCaptureParamAndLocalAnonXCombinator(pub SpecCaptureParamAndLocalAnonXCombinatorAlias);

impl SpecCombinator for SpecCaptureParamAndLocalAnonXCombinator {
    type Type = SpecCaptureParamAndLocalAnonX;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCaptureParamAndLocalAnonXCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecCaptureParamAndLocalAnonXCombinatorAlias::is_prefix_secure() }
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
pub type SpecCaptureParamAndLocalAnonXCombinatorAlias = Mapped<SpecCaptureParamAndLocalAnonXCombinatorAlias1, CaptureParamAndLocalAnonXMapper>;
type CaptureParamAndLocalAnonXCombinatorAlias1 = Choice<Cond<CaptureParamAndLocalAnonXAnonACombinator>, Cond<CaptureParamAndLocalAnonXAnonBCombinator>>;
pub struct CaptureParamAndLocalAnonXCombinator1(pub CaptureParamAndLocalAnonXCombinatorAlias1);
impl View for CaptureParamAndLocalAnonXCombinator1 {
    type V = SpecCaptureParamAndLocalAnonXCombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(CaptureParamAndLocalAnonXCombinator1, CaptureParamAndLocalAnonXCombinatorAlias1);

pub struct CaptureParamAndLocalAnonXCombinator(pub CaptureParamAndLocalAnonXCombinatorAlias);

impl View for CaptureParamAndLocalAnonXCombinator {
    type V = SpecCaptureParamAndLocalAnonXCombinator;
    open spec fn view(&self) -> Self::V { SpecCaptureParamAndLocalAnonXCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CaptureParamAndLocalAnonXCombinator {
    type Type = CaptureParamAndLocalAnonX<'a>;
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
pub type CaptureParamAndLocalAnonXCombinatorAlias = Mapped<CaptureParamAndLocalAnonXCombinator1, CaptureParamAndLocalAnonXMapper>;


pub open spec fn spec_capture_param_and_local_anon_x(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecCaptureParamAndLocalAnonXCombinator {
    SpecCaptureParamAndLocalAnonXCombinator(Mapped { inner: Choice(Cond { cond: choice1 == AOrB::A, inner: spec_capture_param_and_local_anon_x_anon_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: spec_capture_param_and_local_anon_x_anon_b() }), mapper: CaptureParamAndLocalAnonXMapper })
}

pub fn capture_param_and_local_anon_x<'a>(choice1: AOrB, choice2: COrD) -> (o: CaptureParamAndLocalAnonXCombinator)
    requires
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures o@ == spec_capture_param_and_local_anon_x(choice1@, choice2@),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = CaptureParamAndLocalAnonXCombinator(Mapped { inner: CaptureParamAndLocalAnonXCombinator1(Choice::new(Cond { cond: choice1 == AOrB::A, inner: capture_param_and_local_anon_x_anon_a(choice2) }, Cond { cond: choice1 == AOrB::B, inner: capture_param_and_local_anon_x_anon_b() })), mapper: CaptureParamAndLocalAnonXMapper });
    // assert({
    //     &&& combinator@ == spec_capture_param_and_local_anon_x(choice1@, choice2@)
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_capture_param_and_local_anon_x<'a>(input: &'a [u8], choice1: AOrB, choice2: COrD) -> (res: PResult<<CaptureParamAndLocalAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        res matches Ok((n, v)) ==> spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_parse(input@) == Some((n as int, v@)),
        spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_parse(input@) is None,
        spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_parse(input@) is None ==> res is Err,
{
    let combinator = capture_param_and_local_anon_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_capture_param_and_local_anon_x<'a>(v: <CaptureParamAndLocalAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize, choice1: AOrB, choice2: COrD) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_capture_param_and_local_anon_x(choice1@, choice2@).wf(v@),
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        o matches Ok(n) ==> {
            &&& data@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= data@.len()
            &&& n == spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_serialize(v@).len()
            &&& data@ == seq_splice(old(data)@, pos, spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_serialize(v@))
        },
{
    let combinator = capture_param_and_local_anon_x( choice1, choice2 );
    combinator.serialize(v, data, pos)
}

pub fn capture_param_and_local_anon_x_len<'a>(v: <CaptureParamAndLocalAnonXCombinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, choice1: AOrB, choice2: COrD) -> (serialize_len: usize)
    requires
        spec_capture_param_and_local_anon_x(choice1@, choice2@).wf(v@),
        spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_serialize(v@).len() <= usize::MAX,
        spec_a_or_b().wf(choice1@),
        spec_c_or_d().wf(choice2@),

    ensures
        serialize_len == spec_capture_param_and_local_anon_x(choice1@, choice2@).spec_serialize(v@).len(),
{
    let combinator = capture_param_and_local_anon_x( choice1, choice2 );
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}


pub struct SpecNestedInnerChoice {
    pub x: SpecNestedInnerChoiceAnonX,
}

pub type SpecNestedInnerChoiceInner = SpecNestedInnerChoiceAnonX;


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
    pub x: NestedInnerChoiceAnonX,
}

impl View for NestedInnerChoice {
    type V = SpecNestedInnerChoice;

    open spec fn view(&self) -> Self::V {
        SpecNestedInnerChoice {
            x: self.x@,
        }
    }
}
pub type NestedInnerChoiceInner = NestedInnerChoiceAnonX;

pub type NestedInnerChoiceInnerRef<'a> = &'a NestedInnerChoiceAnonX;
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
pub type SpecNestedInnerChoiceCombinatorAlias = Mapped<SpecNestedInnerChoiceAnonXCombinator, NestedInnerChoiceMapper>;

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
pub type NestedInnerChoiceCombinatorAlias = Mapped<NestedInnerChoiceAnonXCombinator, NestedInnerChoiceMapper>;


pub open spec fn spec_nested_inner_choice(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecNestedInnerChoiceCombinator {
    SpecNestedInnerChoiceCombinator(
    Mapped {
        inner: spec_nested_inner_choice_anon_x(choice1, choice2),
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
        inner: nested_inner_choice_anon_x(choice1, choice2),
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
    pub x: SpecCaptureParamAndLocalAnonX,
}

pub type SpecCaptureParamAndLocalInner = SpecCaptureParamAndLocalAnonX;


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
    pub x: CaptureParamAndLocalAnonX<'a>,
}

impl View for CaptureParamAndLocal<'_> {
    type V = SpecCaptureParamAndLocal;

    open spec fn view(&self) -> Self::V {
        SpecCaptureParamAndLocal {
            x: self.x@,
        }
    }
}
pub type CaptureParamAndLocalInner<'a> = CaptureParamAndLocalAnonX<'a>;

pub type CaptureParamAndLocalInnerRef<'a> = &'a CaptureParamAndLocalAnonX<'a>;
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
pub type SpecCaptureParamAndLocalCombinatorAlias = Mapped<SpecCaptureParamAndLocalAnonXCombinator, CaptureParamAndLocalMapper>;

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
pub type CaptureParamAndLocalCombinatorAlias = Mapped<CaptureParamAndLocalAnonXCombinator, CaptureParamAndLocalMapper>;


pub open spec fn spec_capture_param_and_local(choice1: SpecAOrB, choice2: SpecCOrD) -> SpecCaptureParamAndLocalCombinator {
    SpecCaptureParamAndLocalCombinator(
    Mapped {
        inner: spec_capture_param_and_local_anon_x(choice1, choice2),
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
        inner: capture_param_and_local_anon_x(choice1, choice2),
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

                

pub struct SpecCaptureLocalInAnonStruct {
    pub wrapper: SpecCaptureLocalInAnonStructAnonWrapper,
}

pub type SpecCaptureLocalInAnonStructInner = SpecCaptureLocalInAnonStructAnonWrapper;


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
    pub wrapper: CaptureLocalInAnonStructAnonWrapper<'a>,
}

impl View for CaptureLocalInAnonStruct<'_> {
    type V = SpecCaptureLocalInAnonStruct;

    open spec fn view(&self) -> Self::V {
        SpecCaptureLocalInAnonStruct {
            wrapper: self.wrapper@,
        }
    }
}
pub type CaptureLocalInAnonStructInner<'a> = CaptureLocalInAnonStructAnonWrapper<'a>;

pub type CaptureLocalInAnonStructInnerRef<'a> = &'a CaptureLocalInAnonStructAnonWrapper<'a>;
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
pub type SpecCaptureLocalInAnonStructCombinatorAlias = Mapped<SpecCaptureLocalInAnonStructAnonWrapperCombinator, CaptureLocalInAnonStructMapper>;

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
pub type CaptureLocalInAnonStructCombinatorAlias = Mapped<CaptureLocalInAnonStructAnonWrapperCombinator, CaptureLocalInAnonStructMapper>;


pub open spec fn spec_capture_local_in_anon_struct() -> SpecCaptureLocalInAnonStructCombinator {
    SpecCaptureLocalInAnonStructCombinator(
    Mapped {
        inner: spec_capture_local_in_anon_struct_anon_wrapper(),
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
        inner: capture_local_in_anon_struct_anon_wrapper(),
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
