
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

                

}
