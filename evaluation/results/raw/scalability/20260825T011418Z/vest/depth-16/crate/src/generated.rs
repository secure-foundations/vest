
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
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
            }
        } // verus!
    };
}
verus!{

pub struct SpecDepth0 {
    pub value: u8,
}

pub type SpecDepth0Inner = u8;


impl SpecFrom<SpecDepth0> for SpecDepth0Inner {
    open spec fn spec_from(m: SpecDepth0) -> SpecDepth0Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth0Inner> for SpecDepth0 {
    open spec fn spec_from(m: SpecDepth0Inner) -> SpecDepth0 {
        let value = m;
        SpecDepth0 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth0 {
    pub value: u8,
}

impl View for Depth0 {
    type V = SpecDepth0;

    open spec fn view(&self) -> Self::V {
        SpecDepth0 {
            value: self.value@,
        }
    }
}
pub type Depth0Inner = u8;

pub type Depth0InnerRef<'a> = &'a u8;
impl<'a> From<&'a Depth0> for Depth0InnerRef<'a> {
    fn ex_from(m: &'a Depth0) -> Depth0InnerRef<'a> {
        &m.value
    }
}

impl From<Depth0Inner> for Depth0 {
    fn ex_from(m: Depth0Inner) -> Depth0 {
        let value = m;
        Depth0 { value }
    }
}

pub struct Depth0Mapper;
impl View for Depth0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth0Mapper {
    type Src = SpecDepth0Inner;
    type Dst = SpecDepth0;
}
impl SpecIsoProof for Depth0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth0Mapper {
    type Src = Depth0Inner;
    type Dst = Depth0;
    type RefSrc = Depth0InnerRef<'a>;
}

pub struct SpecDepth0Combinator(pub SpecDepth0CombinatorAlias);

impl SpecCombinator for SpecDepth0Combinator {
    type Type = SpecDepth0;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth0Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth0CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth0CombinatorAlias = Mapped<U8, Depth0Mapper>;

pub struct Depth0Combinator(pub Depth0CombinatorAlias);

impl View for Depth0Combinator {
    type V = SpecDepth0Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth0Combinator {
    type Type = Depth0;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth0CombinatorAlias = Mapped<U8, Depth0Mapper>;


pub open spec fn spec_depth0() -> SpecDepth0Combinator {
    SpecDepth0Combinator(
    Mapped {
        inner: U8,
        mapper: Depth0Mapper,
    })
}

                
pub fn depth0<'a>() -> (o: Depth0Combinator)
    ensures o@ == spec_depth0(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth0Combinator(
    Mapped {
        inner: U8,
        mapper: Depth0Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth0()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth0<'a>(input: &'a [u8]) -> (res: PResult<<Depth0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth0().spec_parse(input@) == Some((n as int, v@)),
        spec_depth0().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth0().spec_parse(input@) is None,
        spec_depth0().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth0<'a>(v: <Depth0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth0().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth0().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth0().spec_serialize(v@))
        },
{
    let combinator = depth0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth0_len<'a>(v: <Depth0Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth0().wf(v@),
        spec_depth0().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth0().spec_serialize(v@).len(),
{
    let combinator = depth0();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth1 {
    pub value: SpecDepth0,
}

pub type SpecDepth1Inner = SpecDepth0;


impl SpecFrom<SpecDepth1> for SpecDepth1Inner {
    open spec fn spec_from(m: SpecDepth1) -> SpecDepth1Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth1Inner> for SpecDepth1 {
    open spec fn spec_from(m: SpecDepth1Inner) -> SpecDepth1 {
        let value = m;
        SpecDepth1 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth1 {
    pub value: Depth0,
}

impl View for Depth1 {
    type V = SpecDepth1;

    open spec fn view(&self) -> Self::V {
        SpecDepth1 {
            value: self.value@,
        }
    }
}
pub type Depth1Inner = Depth0;

pub type Depth1InnerRef<'a> = &'a Depth0;
impl<'a> From<&'a Depth1> for Depth1InnerRef<'a> {
    fn ex_from(m: &'a Depth1) -> Depth1InnerRef<'a> {
        &m.value
    }
}

impl From<Depth1Inner> for Depth1 {
    fn ex_from(m: Depth1Inner) -> Depth1 {
        let value = m;
        Depth1 { value }
    }
}

pub struct Depth1Mapper;
impl View for Depth1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth1Mapper {
    type Src = SpecDepth1Inner;
    type Dst = SpecDepth1;
}
impl SpecIsoProof for Depth1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth1Mapper {
    type Src = Depth1Inner;
    type Dst = Depth1;
    type RefSrc = Depth1InnerRef<'a>;
}

pub struct SpecDepth1Combinator(pub SpecDepth1CombinatorAlias);

impl SpecCombinator for SpecDepth1Combinator {
    type Type = SpecDepth1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth1Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth1CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth1CombinatorAlias = Mapped<SpecDepth0Combinator, Depth1Mapper>;

pub struct Depth1Combinator(pub Depth1CombinatorAlias);

impl View for Depth1Combinator {
    type V = SpecDepth1Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth1Combinator {
    type Type = Depth1;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth1CombinatorAlias = Mapped<Depth0Combinator, Depth1Mapper>;


pub open spec fn spec_depth1() -> SpecDepth1Combinator {
    SpecDepth1Combinator(
    Mapped {
        inner: spec_depth0(),
        mapper: Depth1Mapper,
    })
}

                
pub fn depth1<'a>() -> (o: Depth1Combinator)
    ensures o@ == spec_depth1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth1Combinator(
    Mapped {
        inner: depth0(),
        mapper: Depth1Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth1<'a>(input: &'a [u8]) -> (res: PResult<<Depth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth1().spec_parse(input@) == Some((n as int, v@)),
        spec_depth1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth1().spec_parse(input@) is None,
        spec_depth1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth1<'a>(v: <Depth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth1().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth1().spec_serialize(v@))
        },
{
    let combinator = depth1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth1_len<'a>(v: <Depth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth1().wf(v@),
        spec_depth1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth1().spec_serialize(v@).len(),
{
    let combinator = depth1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth2 {
    pub value: SpecDepth1,
}

pub type SpecDepth2Inner = SpecDepth1;


impl SpecFrom<SpecDepth2> for SpecDepth2Inner {
    open spec fn spec_from(m: SpecDepth2) -> SpecDepth2Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth2Inner> for SpecDepth2 {
    open spec fn spec_from(m: SpecDepth2Inner) -> SpecDepth2 {
        let value = m;
        SpecDepth2 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth2 {
    pub value: Depth1,
}

impl View for Depth2 {
    type V = SpecDepth2;

    open spec fn view(&self) -> Self::V {
        SpecDepth2 {
            value: self.value@,
        }
    }
}
pub type Depth2Inner = Depth1;

pub type Depth2InnerRef<'a> = &'a Depth1;
impl<'a> From<&'a Depth2> for Depth2InnerRef<'a> {
    fn ex_from(m: &'a Depth2) -> Depth2InnerRef<'a> {
        &m.value
    }
}

impl From<Depth2Inner> for Depth2 {
    fn ex_from(m: Depth2Inner) -> Depth2 {
        let value = m;
        Depth2 { value }
    }
}

pub struct Depth2Mapper;
impl View for Depth2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth2Mapper {
    type Src = SpecDepth2Inner;
    type Dst = SpecDepth2;
}
impl SpecIsoProof for Depth2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth2Mapper {
    type Src = Depth2Inner;
    type Dst = Depth2;
    type RefSrc = Depth2InnerRef<'a>;
}

pub struct SpecDepth2Combinator(pub SpecDepth2CombinatorAlias);

impl SpecCombinator for SpecDepth2Combinator {
    type Type = SpecDepth2;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth2Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth2CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth2CombinatorAlias = Mapped<SpecDepth1Combinator, Depth2Mapper>;

pub struct Depth2Combinator(pub Depth2CombinatorAlias);

impl View for Depth2Combinator {
    type V = SpecDepth2Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth2Combinator {
    type Type = Depth2;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth2CombinatorAlias = Mapped<Depth1Combinator, Depth2Mapper>;


pub open spec fn spec_depth2() -> SpecDepth2Combinator {
    SpecDepth2Combinator(
    Mapped {
        inner: spec_depth1(),
        mapper: Depth2Mapper,
    })
}

                
pub fn depth2<'a>() -> (o: Depth2Combinator)
    ensures o@ == spec_depth2(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth2Combinator(
    Mapped {
        inner: depth1(),
        mapper: Depth2Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth2()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth2<'a>(input: &'a [u8]) -> (res: PResult<<Depth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth2().spec_parse(input@) == Some((n as int, v@)),
        spec_depth2().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth2().spec_parse(input@) is None,
        spec_depth2().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth2<'a>(v: <Depth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth2().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth2().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth2().spec_serialize(v@))
        },
{
    let combinator = depth2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth2_len<'a>(v: <Depth2Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth2().wf(v@),
        spec_depth2().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth2().spec_serialize(v@).len(),
{
    let combinator = depth2();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth3 {
    pub value: SpecDepth2,
}

pub type SpecDepth3Inner = SpecDepth2;


impl SpecFrom<SpecDepth3> for SpecDepth3Inner {
    open spec fn spec_from(m: SpecDepth3) -> SpecDepth3Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth3Inner> for SpecDepth3 {
    open spec fn spec_from(m: SpecDepth3Inner) -> SpecDepth3 {
        let value = m;
        SpecDepth3 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth3 {
    pub value: Depth2,
}

impl View for Depth3 {
    type V = SpecDepth3;

    open spec fn view(&self) -> Self::V {
        SpecDepth3 {
            value: self.value@,
        }
    }
}
pub type Depth3Inner = Depth2;

pub type Depth3InnerRef<'a> = &'a Depth2;
impl<'a> From<&'a Depth3> for Depth3InnerRef<'a> {
    fn ex_from(m: &'a Depth3) -> Depth3InnerRef<'a> {
        &m.value
    }
}

impl From<Depth3Inner> for Depth3 {
    fn ex_from(m: Depth3Inner) -> Depth3 {
        let value = m;
        Depth3 { value }
    }
}

pub struct Depth3Mapper;
impl View for Depth3Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth3Mapper {
    type Src = SpecDepth3Inner;
    type Dst = SpecDepth3;
}
impl SpecIsoProof for Depth3Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth3Mapper {
    type Src = Depth3Inner;
    type Dst = Depth3;
    type RefSrc = Depth3InnerRef<'a>;
}

pub struct SpecDepth3Combinator(pub SpecDepth3CombinatorAlias);

impl SpecCombinator for SpecDepth3Combinator {
    type Type = SpecDepth3;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth3Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth3CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth3CombinatorAlias = Mapped<SpecDepth2Combinator, Depth3Mapper>;

pub struct Depth3Combinator(pub Depth3CombinatorAlias);

impl View for Depth3Combinator {
    type V = SpecDepth3Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth3Combinator {
    type Type = Depth3;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth3CombinatorAlias = Mapped<Depth2Combinator, Depth3Mapper>;


pub open spec fn spec_depth3() -> SpecDepth3Combinator {
    SpecDepth3Combinator(
    Mapped {
        inner: spec_depth2(),
        mapper: Depth3Mapper,
    })
}

                
pub fn depth3<'a>() -> (o: Depth3Combinator)
    ensures o@ == spec_depth3(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth3Combinator(
    Mapped {
        inner: depth2(),
        mapper: Depth3Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth3()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth3<'a>(input: &'a [u8]) -> (res: PResult<<Depth3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth3().spec_parse(input@) == Some((n as int, v@)),
        spec_depth3().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth3().spec_parse(input@) is None,
        spec_depth3().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth3<'a>(v: <Depth3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth3().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth3().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth3().spec_serialize(v@))
        },
{
    let combinator = depth3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth3_len<'a>(v: <Depth3Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth3().wf(v@),
        spec_depth3().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth3().spec_serialize(v@).len(),
{
    let combinator = depth3();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth4 {
    pub value: SpecDepth3,
}

pub type SpecDepth4Inner = SpecDepth3;


impl SpecFrom<SpecDepth4> for SpecDepth4Inner {
    open spec fn spec_from(m: SpecDepth4) -> SpecDepth4Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth4Inner> for SpecDepth4 {
    open spec fn spec_from(m: SpecDepth4Inner) -> SpecDepth4 {
        let value = m;
        SpecDepth4 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth4 {
    pub value: Depth3,
}

impl View for Depth4 {
    type V = SpecDepth4;

    open spec fn view(&self) -> Self::V {
        SpecDepth4 {
            value: self.value@,
        }
    }
}
pub type Depth4Inner = Depth3;

pub type Depth4InnerRef<'a> = &'a Depth3;
impl<'a> From<&'a Depth4> for Depth4InnerRef<'a> {
    fn ex_from(m: &'a Depth4) -> Depth4InnerRef<'a> {
        &m.value
    }
}

impl From<Depth4Inner> for Depth4 {
    fn ex_from(m: Depth4Inner) -> Depth4 {
        let value = m;
        Depth4 { value }
    }
}

pub struct Depth4Mapper;
impl View for Depth4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth4Mapper {
    type Src = SpecDepth4Inner;
    type Dst = SpecDepth4;
}
impl SpecIsoProof for Depth4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth4Mapper {
    type Src = Depth4Inner;
    type Dst = Depth4;
    type RefSrc = Depth4InnerRef<'a>;
}

pub struct SpecDepth4Combinator(pub SpecDepth4CombinatorAlias);

impl SpecCombinator for SpecDepth4Combinator {
    type Type = SpecDepth4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth4Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth4CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth4CombinatorAlias = Mapped<SpecDepth3Combinator, Depth4Mapper>;

pub struct Depth4Combinator(pub Depth4CombinatorAlias);

impl View for Depth4Combinator {
    type V = SpecDepth4Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth4Combinator {
    type Type = Depth4;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth4CombinatorAlias = Mapped<Depth3Combinator, Depth4Mapper>;


pub open spec fn spec_depth4() -> SpecDepth4Combinator {
    SpecDepth4Combinator(
    Mapped {
        inner: spec_depth3(),
        mapper: Depth4Mapper,
    })
}

                
pub fn depth4<'a>() -> (o: Depth4Combinator)
    ensures o@ == spec_depth4(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth4Combinator(
    Mapped {
        inner: depth3(),
        mapper: Depth4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth4()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth4<'a>(input: &'a [u8]) -> (res: PResult<<Depth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth4().spec_parse(input@) == Some((n as int, v@)),
        spec_depth4().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth4().spec_parse(input@) is None,
        spec_depth4().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth4<'a>(v: <Depth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth4().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth4().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth4().spec_serialize(v@))
        },
{
    let combinator = depth4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth4_len<'a>(v: <Depth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth4().wf(v@),
        spec_depth4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth4().spec_serialize(v@).len(),
{
    let combinator = depth4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth5 {
    pub value: SpecDepth4,
}

pub type SpecDepth5Inner = SpecDepth4;


impl SpecFrom<SpecDepth5> for SpecDepth5Inner {
    open spec fn spec_from(m: SpecDepth5) -> SpecDepth5Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth5Inner> for SpecDepth5 {
    open spec fn spec_from(m: SpecDepth5Inner) -> SpecDepth5 {
        let value = m;
        SpecDepth5 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth5 {
    pub value: Depth4,
}

impl View for Depth5 {
    type V = SpecDepth5;

    open spec fn view(&self) -> Self::V {
        SpecDepth5 {
            value: self.value@,
        }
    }
}
pub type Depth5Inner = Depth4;

pub type Depth5InnerRef<'a> = &'a Depth4;
impl<'a> From<&'a Depth5> for Depth5InnerRef<'a> {
    fn ex_from(m: &'a Depth5) -> Depth5InnerRef<'a> {
        &m.value
    }
}

impl From<Depth5Inner> for Depth5 {
    fn ex_from(m: Depth5Inner) -> Depth5 {
        let value = m;
        Depth5 { value }
    }
}

pub struct Depth5Mapper;
impl View for Depth5Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth5Mapper {
    type Src = SpecDepth5Inner;
    type Dst = SpecDepth5;
}
impl SpecIsoProof for Depth5Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth5Mapper {
    type Src = Depth5Inner;
    type Dst = Depth5;
    type RefSrc = Depth5InnerRef<'a>;
}

pub struct SpecDepth5Combinator(pub SpecDepth5CombinatorAlias);

impl SpecCombinator for SpecDepth5Combinator {
    type Type = SpecDepth5;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth5Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth5CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth5CombinatorAlias = Mapped<SpecDepth4Combinator, Depth5Mapper>;

pub struct Depth5Combinator(pub Depth5CombinatorAlias);

impl View for Depth5Combinator {
    type V = SpecDepth5Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth5Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth5Combinator {
    type Type = Depth5;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth5CombinatorAlias = Mapped<Depth4Combinator, Depth5Mapper>;


pub open spec fn spec_depth5() -> SpecDepth5Combinator {
    SpecDepth5Combinator(
    Mapped {
        inner: spec_depth4(),
        mapper: Depth5Mapper,
    })
}

                
pub fn depth5<'a>() -> (o: Depth5Combinator)
    ensures o@ == spec_depth5(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth5Combinator(
    Mapped {
        inner: depth4(),
        mapper: Depth5Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth5()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth5<'a>(input: &'a [u8]) -> (res: PResult<<Depth5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth5().spec_parse(input@) == Some((n as int, v@)),
        spec_depth5().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth5().spec_parse(input@) is None,
        spec_depth5().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth5<'a>(v: <Depth5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth5().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth5().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth5().spec_serialize(v@))
        },
{
    let combinator = depth5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth5_len<'a>(v: <Depth5Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth5().wf(v@),
        spec_depth5().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth5().spec_serialize(v@).len(),
{
    let combinator = depth5();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth6 {
    pub value: SpecDepth5,
}

pub type SpecDepth6Inner = SpecDepth5;


impl SpecFrom<SpecDepth6> for SpecDepth6Inner {
    open spec fn spec_from(m: SpecDepth6) -> SpecDepth6Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth6Inner> for SpecDepth6 {
    open spec fn spec_from(m: SpecDepth6Inner) -> SpecDepth6 {
        let value = m;
        SpecDepth6 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth6 {
    pub value: Depth5,
}

impl View for Depth6 {
    type V = SpecDepth6;

    open spec fn view(&self) -> Self::V {
        SpecDepth6 {
            value: self.value@,
        }
    }
}
pub type Depth6Inner = Depth5;

pub type Depth6InnerRef<'a> = &'a Depth5;
impl<'a> From<&'a Depth6> for Depth6InnerRef<'a> {
    fn ex_from(m: &'a Depth6) -> Depth6InnerRef<'a> {
        &m.value
    }
}

impl From<Depth6Inner> for Depth6 {
    fn ex_from(m: Depth6Inner) -> Depth6 {
        let value = m;
        Depth6 { value }
    }
}

pub struct Depth6Mapper;
impl View for Depth6Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth6Mapper {
    type Src = SpecDepth6Inner;
    type Dst = SpecDepth6;
}
impl SpecIsoProof for Depth6Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth6Mapper {
    type Src = Depth6Inner;
    type Dst = Depth6;
    type RefSrc = Depth6InnerRef<'a>;
}

pub struct SpecDepth6Combinator(pub SpecDepth6CombinatorAlias);

impl SpecCombinator for SpecDepth6Combinator {
    type Type = SpecDepth6;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth6Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth6CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth6CombinatorAlias = Mapped<SpecDepth5Combinator, Depth6Mapper>;

pub struct Depth6Combinator(pub Depth6CombinatorAlias);

impl View for Depth6Combinator {
    type V = SpecDepth6Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth6Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth6Combinator {
    type Type = Depth6;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth6CombinatorAlias = Mapped<Depth5Combinator, Depth6Mapper>;


pub open spec fn spec_depth6() -> SpecDepth6Combinator {
    SpecDepth6Combinator(
    Mapped {
        inner: spec_depth5(),
        mapper: Depth6Mapper,
    })
}

                
pub fn depth6<'a>() -> (o: Depth6Combinator)
    ensures o@ == spec_depth6(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth6Combinator(
    Mapped {
        inner: depth5(),
        mapper: Depth6Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth6()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth6<'a>(input: &'a [u8]) -> (res: PResult<<Depth6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth6().spec_parse(input@) == Some((n as int, v@)),
        spec_depth6().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth6().spec_parse(input@) is None,
        spec_depth6().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth6<'a>(v: <Depth6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth6().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth6().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth6().spec_serialize(v@))
        },
{
    let combinator = depth6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth6_len<'a>(v: <Depth6Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth6().wf(v@),
        spec_depth6().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth6().spec_serialize(v@).len(),
{
    let combinator = depth6();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth7 {
    pub value: SpecDepth6,
}

pub type SpecDepth7Inner = SpecDepth6;


impl SpecFrom<SpecDepth7> for SpecDepth7Inner {
    open spec fn spec_from(m: SpecDepth7) -> SpecDepth7Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth7Inner> for SpecDepth7 {
    open spec fn spec_from(m: SpecDepth7Inner) -> SpecDepth7 {
        let value = m;
        SpecDepth7 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth7 {
    pub value: Depth6,
}

impl View for Depth7 {
    type V = SpecDepth7;

    open spec fn view(&self) -> Self::V {
        SpecDepth7 {
            value: self.value@,
        }
    }
}
pub type Depth7Inner = Depth6;

pub type Depth7InnerRef<'a> = &'a Depth6;
impl<'a> From<&'a Depth7> for Depth7InnerRef<'a> {
    fn ex_from(m: &'a Depth7) -> Depth7InnerRef<'a> {
        &m.value
    }
}

impl From<Depth7Inner> for Depth7 {
    fn ex_from(m: Depth7Inner) -> Depth7 {
        let value = m;
        Depth7 { value }
    }
}

pub struct Depth7Mapper;
impl View for Depth7Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth7Mapper {
    type Src = SpecDepth7Inner;
    type Dst = SpecDepth7;
}
impl SpecIsoProof for Depth7Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth7Mapper {
    type Src = Depth7Inner;
    type Dst = Depth7;
    type RefSrc = Depth7InnerRef<'a>;
}

pub struct SpecDepth7Combinator(pub SpecDepth7CombinatorAlias);

impl SpecCombinator for SpecDepth7Combinator {
    type Type = SpecDepth7;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth7Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth7CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth7CombinatorAlias = Mapped<SpecDepth6Combinator, Depth7Mapper>;

pub struct Depth7Combinator(pub Depth7CombinatorAlias);

impl View for Depth7Combinator {
    type V = SpecDepth7Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth7Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth7Combinator {
    type Type = Depth7;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth7CombinatorAlias = Mapped<Depth6Combinator, Depth7Mapper>;


pub open spec fn spec_depth7() -> SpecDepth7Combinator {
    SpecDepth7Combinator(
    Mapped {
        inner: spec_depth6(),
        mapper: Depth7Mapper,
    })
}

                
pub fn depth7<'a>() -> (o: Depth7Combinator)
    ensures o@ == spec_depth7(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth7Combinator(
    Mapped {
        inner: depth6(),
        mapper: Depth7Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth7()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth7<'a>(input: &'a [u8]) -> (res: PResult<<Depth7Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth7().spec_parse(input@) == Some((n as int, v@)),
        spec_depth7().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth7().spec_parse(input@) is None,
        spec_depth7().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth7();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth7<'a>(v: <Depth7Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth7().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth7().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth7().spec_serialize(v@))
        },
{
    let combinator = depth7();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth7_len<'a>(v: <Depth7Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth7().wf(v@),
        spec_depth7().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth7().spec_serialize(v@).len(),
{
    let combinator = depth7();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth8 {
    pub value: SpecDepth7,
}

pub type SpecDepth8Inner = SpecDepth7;


impl SpecFrom<SpecDepth8> for SpecDepth8Inner {
    open spec fn spec_from(m: SpecDepth8) -> SpecDepth8Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth8Inner> for SpecDepth8 {
    open spec fn spec_from(m: SpecDepth8Inner) -> SpecDepth8 {
        let value = m;
        SpecDepth8 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth8 {
    pub value: Depth7,
}

impl View for Depth8 {
    type V = SpecDepth8;

    open spec fn view(&self) -> Self::V {
        SpecDepth8 {
            value: self.value@,
        }
    }
}
pub type Depth8Inner = Depth7;

pub type Depth8InnerRef<'a> = &'a Depth7;
impl<'a> From<&'a Depth8> for Depth8InnerRef<'a> {
    fn ex_from(m: &'a Depth8) -> Depth8InnerRef<'a> {
        &m.value
    }
}

impl From<Depth8Inner> for Depth8 {
    fn ex_from(m: Depth8Inner) -> Depth8 {
        let value = m;
        Depth8 { value }
    }
}

pub struct Depth8Mapper;
impl View for Depth8Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth8Mapper {
    type Src = SpecDepth8Inner;
    type Dst = SpecDepth8;
}
impl SpecIsoProof for Depth8Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth8Mapper {
    type Src = Depth8Inner;
    type Dst = Depth8;
    type RefSrc = Depth8InnerRef<'a>;
}

pub struct SpecDepth8Combinator(pub SpecDepth8CombinatorAlias);

impl SpecCombinator for SpecDepth8Combinator {
    type Type = SpecDepth8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth8Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth8CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth8CombinatorAlias = Mapped<SpecDepth7Combinator, Depth8Mapper>;

pub struct Depth8Combinator(pub Depth8CombinatorAlias);

impl View for Depth8Combinator {
    type V = SpecDepth8Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth8Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth8Combinator {
    type Type = Depth8;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth8CombinatorAlias = Mapped<Depth7Combinator, Depth8Mapper>;


pub open spec fn spec_depth8() -> SpecDepth8Combinator {
    SpecDepth8Combinator(
    Mapped {
        inner: spec_depth7(),
        mapper: Depth8Mapper,
    })
}

                
pub fn depth8<'a>() -> (o: Depth8Combinator)
    ensures o@ == spec_depth8(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth8Combinator(
    Mapped {
        inner: depth7(),
        mapper: Depth8Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth8()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth8<'a>(input: &'a [u8]) -> (res: PResult<<Depth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth8().spec_parse(input@) == Some((n as int, v@)),
        spec_depth8().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth8().spec_parse(input@) is None,
        spec_depth8().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth8<'a>(v: <Depth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth8().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth8().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth8().spec_serialize(v@))
        },
{
    let combinator = depth8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth8_len<'a>(v: <Depth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth8().wf(v@),
        spec_depth8().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth8().spec_serialize(v@).len(),
{
    let combinator = depth8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth9 {
    pub value: SpecDepth8,
}

pub type SpecDepth9Inner = SpecDepth8;


impl SpecFrom<SpecDepth9> for SpecDepth9Inner {
    open spec fn spec_from(m: SpecDepth9) -> SpecDepth9Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth9Inner> for SpecDepth9 {
    open spec fn spec_from(m: SpecDepth9Inner) -> SpecDepth9 {
        let value = m;
        SpecDepth9 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth9 {
    pub value: Depth8,
}

impl View for Depth9 {
    type V = SpecDepth9;

    open spec fn view(&self) -> Self::V {
        SpecDepth9 {
            value: self.value@,
        }
    }
}
pub type Depth9Inner = Depth8;

pub type Depth9InnerRef<'a> = &'a Depth8;
impl<'a> From<&'a Depth9> for Depth9InnerRef<'a> {
    fn ex_from(m: &'a Depth9) -> Depth9InnerRef<'a> {
        &m.value
    }
}

impl From<Depth9Inner> for Depth9 {
    fn ex_from(m: Depth9Inner) -> Depth9 {
        let value = m;
        Depth9 { value }
    }
}

pub struct Depth9Mapper;
impl View for Depth9Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth9Mapper {
    type Src = SpecDepth9Inner;
    type Dst = SpecDepth9;
}
impl SpecIsoProof for Depth9Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth9Mapper {
    type Src = Depth9Inner;
    type Dst = Depth9;
    type RefSrc = Depth9InnerRef<'a>;
}

pub struct SpecDepth9Combinator(pub SpecDepth9CombinatorAlias);

impl SpecCombinator for SpecDepth9Combinator {
    type Type = SpecDepth9;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth9Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth9CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth9CombinatorAlias = Mapped<SpecDepth8Combinator, Depth9Mapper>;

pub struct Depth9Combinator(pub Depth9CombinatorAlias);

impl View for Depth9Combinator {
    type V = SpecDepth9Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth9Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth9Combinator {
    type Type = Depth9;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth9CombinatorAlias = Mapped<Depth8Combinator, Depth9Mapper>;


pub open spec fn spec_depth9() -> SpecDepth9Combinator {
    SpecDepth9Combinator(
    Mapped {
        inner: spec_depth8(),
        mapper: Depth9Mapper,
    })
}

                
pub fn depth9<'a>() -> (o: Depth9Combinator)
    ensures o@ == spec_depth9(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth9Combinator(
    Mapped {
        inner: depth8(),
        mapper: Depth9Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth9()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth9<'a>(input: &'a [u8]) -> (res: PResult<<Depth9Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth9().spec_parse(input@) == Some((n as int, v@)),
        spec_depth9().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth9().spec_parse(input@) is None,
        spec_depth9().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth9();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth9<'a>(v: <Depth9Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth9().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth9().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth9().spec_serialize(v@))
        },
{
    let combinator = depth9();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth9_len<'a>(v: <Depth9Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth9().wf(v@),
        spec_depth9().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth9().spec_serialize(v@).len(),
{
    let combinator = depth9();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth10 {
    pub value: SpecDepth9,
}

pub type SpecDepth10Inner = SpecDepth9;


impl SpecFrom<SpecDepth10> for SpecDepth10Inner {
    open spec fn spec_from(m: SpecDepth10) -> SpecDepth10Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth10Inner> for SpecDepth10 {
    open spec fn spec_from(m: SpecDepth10Inner) -> SpecDepth10 {
        let value = m;
        SpecDepth10 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth10 {
    pub value: Depth9,
}

impl View for Depth10 {
    type V = SpecDepth10;

    open spec fn view(&self) -> Self::V {
        SpecDepth10 {
            value: self.value@,
        }
    }
}
pub type Depth10Inner = Depth9;

pub type Depth10InnerRef<'a> = &'a Depth9;
impl<'a> From<&'a Depth10> for Depth10InnerRef<'a> {
    fn ex_from(m: &'a Depth10) -> Depth10InnerRef<'a> {
        &m.value
    }
}

impl From<Depth10Inner> for Depth10 {
    fn ex_from(m: Depth10Inner) -> Depth10 {
        let value = m;
        Depth10 { value }
    }
}

pub struct Depth10Mapper;
impl View for Depth10Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth10Mapper {
    type Src = SpecDepth10Inner;
    type Dst = SpecDepth10;
}
impl SpecIsoProof for Depth10Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth10Mapper {
    type Src = Depth10Inner;
    type Dst = Depth10;
    type RefSrc = Depth10InnerRef<'a>;
}

pub struct SpecDepth10Combinator(pub SpecDepth10CombinatorAlias);

impl SpecCombinator for SpecDepth10Combinator {
    type Type = SpecDepth10;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth10Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth10CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth10CombinatorAlias = Mapped<SpecDepth9Combinator, Depth10Mapper>;

pub struct Depth10Combinator(pub Depth10CombinatorAlias);

impl View for Depth10Combinator {
    type V = SpecDepth10Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth10Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth10Combinator {
    type Type = Depth10;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth10CombinatorAlias = Mapped<Depth9Combinator, Depth10Mapper>;


pub open spec fn spec_depth10() -> SpecDepth10Combinator {
    SpecDepth10Combinator(
    Mapped {
        inner: spec_depth9(),
        mapper: Depth10Mapper,
    })
}

                
pub fn depth10<'a>() -> (o: Depth10Combinator)
    ensures o@ == spec_depth10(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth10Combinator(
    Mapped {
        inner: depth9(),
        mapper: Depth10Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth10()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth10<'a>(input: &'a [u8]) -> (res: PResult<<Depth10Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth10().spec_parse(input@) == Some((n as int, v@)),
        spec_depth10().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth10().spec_parse(input@) is None,
        spec_depth10().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth10();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth10<'a>(v: <Depth10Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth10().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth10().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth10().spec_serialize(v@))
        },
{
    let combinator = depth10();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth10_len<'a>(v: <Depth10Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth10().wf(v@),
        spec_depth10().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth10().spec_serialize(v@).len(),
{
    let combinator = depth10();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth11 {
    pub value: SpecDepth10,
}

pub type SpecDepth11Inner = SpecDepth10;


impl SpecFrom<SpecDepth11> for SpecDepth11Inner {
    open spec fn spec_from(m: SpecDepth11) -> SpecDepth11Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth11Inner> for SpecDepth11 {
    open spec fn spec_from(m: SpecDepth11Inner) -> SpecDepth11 {
        let value = m;
        SpecDepth11 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth11 {
    pub value: Depth10,
}

impl View for Depth11 {
    type V = SpecDepth11;

    open spec fn view(&self) -> Self::V {
        SpecDepth11 {
            value: self.value@,
        }
    }
}
pub type Depth11Inner = Depth10;

pub type Depth11InnerRef<'a> = &'a Depth10;
impl<'a> From<&'a Depth11> for Depth11InnerRef<'a> {
    fn ex_from(m: &'a Depth11) -> Depth11InnerRef<'a> {
        &m.value
    }
}

impl From<Depth11Inner> for Depth11 {
    fn ex_from(m: Depth11Inner) -> Depth11 {
        let value = m;
        Depth11 { value }
    }
}

pub struct Depth11Mapper;
impl View for Depth11Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth11Mapper {
    type Src = SpecDepth11Inner;
    type Dst = SpecDepth11;
}
impl SpecIsoProof for Depth11Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth11Mapper {
    type Src = Depth11Inner;
    type Dst = Depth11;
    type RefSrc = Depth11InnerRef<'a>;
}

pub struct SpecDepth11Combinator(pub SpecDepth11CombinatorAlias);

impl SpecCombinator for SpecDepth11Combinator {
    type Type = SpecDepth11;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth11Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth11CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth11CombinatorAlias = Mapped<SpecDepth10Combinator, Depth11Mapper>;

pub struct Depth11Combinator(pub Depth11CombinatorAlias);

impl View for Depth11Combinator {
    type V = SpecDepth11Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth11Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth11Combinator {
    type Type = Depth11;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth11CombinatorAlias = Mapped<Depth10Combinator, Depth11Mapper>;


pub open spec fn spec_depth11() -> SpecDepth11Combinator {
    SpecDepth11Combinator(
    Mapped {
        inner: spec_depth10(),
        mapper: Depth11Mapper,
    })
}

                
pub fn depth11<'a>() -> (o: Depth11Combinator)
    ensures o@ == spec_depth11(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth11Combinator(
    Mapped {
        inner: depth10(),
        mapper: Depth11Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth11()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth11<'a>(input: &'a [u8]) -> (res: PResult<<Depth11Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth11().spec_parse(input@) == Some((n as int, v@)),
        spec_depth11().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth11().spec_parse(input@) is None,
        spec_depth11().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth11();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth11<'a>(v: <Depth11Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth11().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth11().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth11().spec_serialize(v@))
        },
{
    let combinator = depth11();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth11_len<'a>(v: <Depth11Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth11().wf(v@),
        spec_depth11().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth11().spec_serialize(v@).len(),
{
    let combinator = depth11();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth12 {
    pub value: SpecDepth11,
}

pub type SpecDepth12Inner = SpecDepth11;


impl SpecFrom<SpecDepth12> for SpecDepth12Inner {
    open spec fn spec_from(m: SpecDepth12) -> SpecDepth12Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth12Inner> for SpecDepth12 {
    open spec fn spec_from(m: SpecDepth12Inner) -> SpecDepth12 {
        let value = m;
        SpecDepth12 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth12 {
    pub value: Depth11,
}

impl View for Depth12 {
    type V = SpecDepth12;

    open spec fn view(&self) -> Self::V {
        SpecDepth12 {
            value: self.value@,
        }
    }
}
pub type Depth12Inner = Depth11;

pub type Depth12InnerRef<'a> = &'a Depth11;
impl<'a> From<&'a Depth12> for Depth12InnerRef<'a> {
    fn ex_from(m: &'a Depth12) -> Depth12InnerRef<'a> {
        &m.value
    }
}

impl From<Depth12Inner> for Depth12 {
    fn ex_from(m: Depth12Inner) -> Depth12 {
        let value = m;
        Depth12 { value }
    }
}

pub struct Depth12Mapper;
impl View for Depth12Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth12Mapper {
    type Src = SpecDepth12Inner;
    type Dst = SpecDepth12;
}
impl SpecIsoProof for Depth12Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth12Mapper {
    type Src = Depth12Inner;
    type Dst = Depth12;
    type RefSrc = Depth12InnerRef<'a>;
}

pub struct SpecDepth12Combinator(pub SpecDepth12CombinatorAlias);

impl SpecCombinator for SpecDepth12Combinator {
    type Type = SpecDepth12;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth12Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth12CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth12CombinatorAlias = Mapped<SpecDepth11Combinator, Depth12Mapper>;

pub struct Depth12Combinator(pub Depth12CombinatorAlias);

impl View for Depth12Combinator {
    type V = SpecDepth12Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth12Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth12Combinator {
    type Type = Depth12;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth12CombinatorAlias = Mapped<Depth11Combinator, Depth12Mapper>;


pub open spec fn spec_depth12() -> SpecDepth12Combinator {
    SpecDepth12Combinator(
    Mapped {
        inner: spec_depth11(),
        mapper: Depth12Mapper,
    })
}

                
pub fn depth12<'a>() -> (o: Depth12Combinator)
    ensures o@ == spec_depth12(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth12Combinator(
    Mapped {
        inner: depth11(),
        mapper: Depth12Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth12()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth12<'a>(input: &'a [u8]) -> (res: PResult<<Depth12Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth12().spec_parse(input@) == Some((n as int, v@)),
        spec_depth12().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth12().spec_parse(input@) is None,
        spec_depth12().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth12();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth12<'a>(v: <Depth12Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth12().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth12().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth12().spec_serialize(v@))
        },
{
    let combinator = depth12();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth12_len<'a>(v: <Depth12Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth12().wf(v@),
        spec_depth12().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth12().spec_serialize(v@).len(),
{
    let combinator = depth12();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth13 {
    pub value: SpecDepth12,
}

pub type SpecDepth13Inner = SpecDepth12;


impl SpecFrom<SpecDepth13> for SpecDepth13Inner {
    open spec fn spec_from(m: SpecDepth13) -> SpecDepth13Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth13Inner> for SpecDepth13 {
    open spec fn spec_from(m: SpecDepth13Inner) -> SpecDepth13 {
        let value = m;
        SpecDepth13 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth13 {
    pub value: Depth12,
}

impl View for Depth13 {
    type V = SpecDepth13;

    open spec fn view(&self) -> Self::V {
        SpecDepth13 {
            value: self.value@,
        }
    }
}
pub type Depth13Inner = Depth12;

pub type Depth13InnerRef<'a> = &'a Depth12;
impl<'a> From<&'a Depth13> for Depth13InnerRef<'a> {
    fn ex_from(m: &'a Depth13) -> Depth13InnerRef<'a> {
        &m.value
    }
}

impl From<Depth13Inner> for Depth13 {
    fn ex_from(m: Depth13Inner) -> Depth13 {
        let value = m;
        Depth13 { value }
    }
}

pub struct Depth13Mapper;
impl View for Depth13Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth13Mapper {
    type Src = SpecDepth13Inner;
    type Dst = SpecDepth13;
}
impl SpecIsoProof for Depth13Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth13Mapper {
    type Src = Depth13Inner;
    type Dst = Depth13;
    type RefSrc = Depth13InnerRef<'a>;
}

pub struct SpecDepth13Combinator(pub SpecDepth13CombinatorAlias);

impl SpecCombinator for SpecDepth13Combinator {
    type Type = SpecDepth13;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth13Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth13CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth13CombinatorAlias = Mapped<SpecDepth12Combinator, Depth13Mapper>;

pub struct Depth13Combinator(pub Depth13CombinatorAlias);

impl View for Depth13Combinator {
    type V = SpecDepth13Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth13Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth13Combinator {
    type Type = Depth13;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth13CombinatorAlias = Mapped<Depth12Combinator, Depth13Mapper>;


pub open spec fn spec_depth13() -> SpecDepth13Combinator {
    SpecDepth13Combinator(
    Mapped {
        inner: spec_depth12(),
        mapper: Depth13Mapper,
    })
}

                
pub fn depth13<'a>() -> (o: Depth13Combinator)
    ensures o@ == spec_depth13(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth13Combinator(
    Mapped {
        inner: depth12(),
        mapper: Depth13Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth13()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth13<'a>(input: &'a [u8]) -> (res: PResult<<Depth13Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth13().spec_parse(input@) == Some((n as int, v@)),
        spec_depth13().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth13().spec_parse(input@) is None,
        spec_depth13().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth13();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth13<'a>(v: <Depth13Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth13().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth13().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth13().spec_serialize(v@))
        },
{
    let combinator = depth13();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth13_len<'a>(v: <Depth13Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth13().wf(v@),
        spec_depth13().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth13().spec_serialize(v@).len(),
{
    let combinator = depth13();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth14 {
    pub value: SpecDepth13,
}

pub type SpecDepth14Inner = SpecDepth13;


impl SpecFrom<SpecDepth14> for SpecDepth14Inner {
    open spec fn spec_from(m: SpecDepth14) -> SpecDepth14Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth14Inner> for SpecDepth14 {
    open spec fn spec_from(m: SpecDepth14Inner) -> SpecDepth14 {
        let value = m;
        SpecDepth14 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth14 {
    pub value: Depth13,
}

impl View for Depth14 {
    type V = SpecDepth14;

    open spec fn view(&self) -> Self::V {
        SpecDepth14 {
            value: self.value@,
        }
    }
}
pub type Depth14Inner = Depth13;

pub type Depth14InnerRef<'a> = &'a Depth13;
impl<'a> From<&'a Depth14> for Depth14InnerRef<'a> {
    fn ex_from(m: &'a Depth14) -> Depth14InnerRef<'a> {
        &m.value
    }
}

impl From<Depth14Inner> for Depth14 {
    fn ex_from(m: Depth14Inner) -> Depth14 {
        let value = m;
        Depth14 { value }
    }
}

pub struct Depth14Mapper;
impl View for Depth14Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth14Mapper {
    type Src = SpecDepth14Inner;
    type Dst = SpecDepth14;
}
impl SpecIsoProof for Depth14Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth14Mapper {
    type Src = Depth14Inner;
    type Dst = Depth14;
    type RefSrc = Depth14InnerRef<'a>;
}

pub struct SpecDepth14Combinator(pub SpecDepth14CombinatorAlias);

impl SpecCombinator for SpecDepth14Combinator {
    type Type = SpecDepth14;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth14Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth14CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth14CombinatorAlias = Mapped<SpecDepth13Combinator, Depth14Mapper>;

pub struct Depth14Combinator(pub Depth14CombinatorAlias);

impl View for Depth14Combinator {
    type V = SpecDepth14Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth14Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth14Combinator {
    type Type = Depth14;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth14CombinatorAlias = Mapped<Depth13Combinator, Depth14Mapper>;


pub open spec fn spec_depth14() -> SpecDepth14Combinator {
    SpecDepth14Combinator(
    Mapped {
        inner: spec_depth13(),
        mapper: Depth14Mapper,
    })
}

                
pub fn depth14<'a>() -> (o: Depth14Combinator)
    ensures o@ == spec_depth14(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth14Combinator(
    Mapped {
        inner: depth13(),
        mapper: Depth14Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth14()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth14<'a>(input: &'a [u8]) -> (res: PResult<<Depth14Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth14().spec_parse(input@) == Some((n as int, v@)),
        spec_depth14().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth14().spec_parse(input@) is None,
        spec_depth14().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth14();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth14<'a>(v: <Depth14Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth14().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth14().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth14().spec_serialize(v@))
        },
{
    let combinator = depth14();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth14_len<'a>(v: <Depth14Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth14().wf(v@),
        spec_depth14().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth14().spec_serialize(v@).len(),
{
    let combinator = depth14();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth15 {
    pub value: SpecDepth14,
}

pub type SpecDepth15Inner = SpecDepth14;


impl SpecFrom<SpecDepth15> for SpecDepth15Inner {
    open spec fn spec_from(m: SpecDepth15) -> SpecDepth15Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth15Inner> for SpecDepth15 {
    open spec fn spec_from(m: SpecDepth15Inner) -> SpecDepth15 {
        let value = m;
        SpecDepth15 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth15 {
    pub value: Depth14,
}

impl View for Depth15 {
    type V = SpecDepth15;

    open spec fn view(&self) -> Self::V {
        SpecDepth15 {
            value: self.value@,
        }
    }
}
pub type Depth15Inner = Depth14;

pub type Depth15InnerRef<'a> = &'a Depth14;
impl<'a> From<&'a Depth15> for Depth15InnerRef<'a> {
    fn ex_from(m: &'a Depth15) -> Depth15InnerRef<'a> {
        &m.value
    }
}

impl From<Depth15Inner> for Depth15 {
    fn ex_from(m: Depth15Inner) -> Depth15 {
        let value = m;
        Depth15 { value }
    }
}

pub struct Depth15Mapper;
impl View for Depth15Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth15Mapper {
    type Src = SpecDepth15Inner;
    type Dst = SpecDepth15;
}
impl SpecIsoProof for Depth15Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth15Mapper {
    type Src = Depth15Inner;
    type Dst = Depth15;
    type RefSrc = Depth15InnerRef<'a>;
}

pub struct SpecDepth15Combinator(pub SpecDepth15CombinatorAlias);

impl SpecCombinator for SpecDepth15Combinator {
    type Type = SpecDepth15;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth15Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth15CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth15CombinatorAlias = Mapped<SpecDepth14Combinator, Depth15Mapper>;

pub struct Depth15Combinator(pub Depth15CombinatorAlias);

impl View for Depth15Combinator {
    type V = SpecDepth15Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth15Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth15Combinator {
    type Type = Depth15;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth15CombinatorAlias = Mapped<Depth14Combinator, Depth15Mapper>;


pub open spec fn spec_depth15() -> SpecDepth15Combinator {
    SpecDepth15Combinator(
    Mapped {
        inner: spec_depth14(),
        mapper: Depth15Mapper,
    })
}

                
pub fn depth15<'a>() -> (o: Depth15Combinator)
    ensures o@ == spec_depth15(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth15Combinator(
    Mapped {
        inner: depth14(),
        mapper: Depth15Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth15()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth15<'a>(input: &'a [u8]) -> (res: PResult<<Depth15Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth15().spec_parse(input@) == Some((n as int, v@)),
        spec_depth15().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth15().spec_parse(input@) is None,
        spec_depth15().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth15();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth15<'a>(v: <Depth15Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth15().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth15().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth15().spec_serialize(v@))
        },
{
    let combinator = depth15();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth15_len<'a>(v: <Depth15Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth15().wf(v@),
        spec_depth15().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth15().spec_serialize(v@).len(),
{
    let combinator = depth15();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

pub struct SpecDepth16 {
    pub value: SpecDepth15,
}

pub type SpecDepth16Inner = SpecDepth15;


impl SpecFrom<SpecDepth16> for SpecDepth16Inner {
    open spec fn spec_from(m: SpecDepth16) -> SpecDepth16Inner {
        m.value
    }
}

impl SpecFrom<SpecDepth16Inner> for SpecDepth16 {
    open spec fn spec_from(m: SpecDepth16Inner) -> SpecDepth16 {
        let value = m;
        SpecDepth16 { value }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Depth16 {
    pub value: Depth15,
}

impl View for Depth16 {
    type V = SpecDepth16;

    open spec fn view(&self) -> Self::V {
        SpecDepth16 {
            value: self.value@,
        }
    }
}
pub type Depth16Inner = Depth15;

pub type Depth16InnerRef<'a> = &'a Depth15;
impl<'a> From<&'a Depth16> for Depth16InnerRef<'a> {
    fn ex_from(m: &'a Depth16) -> Depth16InnerRef<'a> {
        &m.value
    }
}

impl From<Depth16Inner> for Depth16 {
    fn ex_from(m: Depth16Inner) -> Depth16 {
        let value = m;
        Depth16 { value }
    }
}

pub struct Depth16Mapper;
impl View for Depth16Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Depth16Mapper {
    type Src = SpecDepth16Inner;
    type Dst = SpecDepth16;
}
impl SpecIsoProof for Depth16Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for Depth16Mapper {
    type Src = Depth16Inner;
    type Dst = Depth16;
    type RefSrc = Depth16InnerRef<'a>;
}

pub struct SpecDepth16Combinator(pub SpecDepth16CombinatorAlias);

impl SpecCombinator for SpecDepth16Combinator {
    type Type = SpecDepth16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDepth16Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecDepth16CombinatorAlias::is_prefix_secure() }
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
pub type SpecDepth16CombinatorAlias = Mapped<SpecDepth15Combinator, Depth16Mapper>;

pub struct Depth16Combinator(pub Depth16CombinatorAlias);

impl View for Depth16Combinator {
    type V = SpecDepth16Combinator;
    open spec fn view(&self) -> Self::V { SpecDepth16Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Depth16Combinator {
    type Type = Depth16;
    type SType = &'a Self::Type;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    open spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, &mut *data, pos) }
}
pub type Depth16CombinatorAlias = Mapped<Depth15Combinator, Depth16Mapper>;


pub open spec fn spec_depth16() -> SpecDepth16Combinator {
    SpecDepth16Combinator(
    Mapped {
        inner: spec_depth15(),
        mapper: Depth16Mapper,
    })
}

                
pub fn depth16<'a>() -> (o: Depth16Combinator)
    ensures o@ == spec_depth16(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = Depth16Combinator(
    Mapped {
        inner: depth15(),
        mapper: Depth16Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_depth16()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_depth16<'a>(input: &'a [u8]) -> (res: PResult<<Depth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_depth16().spec_parse(input@) == Some((n as int, v@)),
        spec_depth16().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_depth16().spec_parse(input@) is None,
        spec_depth16().spec_parse(input@) is None ==> res is Err,
{
    let combinator = depth16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_depth16<'a>(v: <Depth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_depth16().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_depth16().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_depth16().spec_serialize(v@))
        },
{
    let combinator = depth16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn depth16_len<'a>(v: <Depth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_depth16().wf(v@),
        spec_depth16().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_depth16().spec_serialize(v@).len(),
{
    let combinator = depth16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
