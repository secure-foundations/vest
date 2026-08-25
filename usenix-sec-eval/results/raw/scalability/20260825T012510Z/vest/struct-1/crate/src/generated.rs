
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

pub struct SpecStructWidth1 {
    pub field0: u8,
}

pub type SpecStructWidth1Inner = u8;


impl SpecFrom<SpecStructWidth1> for SpecStructWidth1Inner {
    open spec fn spec_from(m: SpecStructWidth1) -> SpecStructWidth1Inner {
        m.field0
    }
}

impl SpecFrom<SpecStructWidth1Inner> for SpecStructWidth1 {
    open spec fn spec_from(m: SpecStructWidth1Inner) -> SpecStructWidth1 {
        let field0 = m;
        SpecStructWidth1 { field0 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct StructWidth1 {
    pub field0: u8,
}

impl View for StructWidth1 {
    type V = SpecStructWidth1;

    open spec fn view(&self) -> Self::V {
        SpecStructWidth1 {
            field0: self.field0@,
        }
    }
}
pub type StructWidth1Inner = u8;

pub type StructWidth1InnerRef<'a> = &'a u8;
impl<'a> From<&'a StructWidth1> for StructWidth1InnerRef<'a> {
    fn ex_from(m: &'a StructWidth1) -> StructWidth1InnerRef<'a> {
        &m.field0
    }
}

impl From<StructWidth1Inner> for StructWidth1 {
    fn ex_from(m: StructWidth1Inner) -> StructWidth1 {
        let field0 = m;
        StructWidth1 { field0 }
    }
}

pub struct StructWidth1Mapper;
impl View for StructWidth1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StructWidth1Mapper {
    type Src = SpecStructWidth1Inner;
    type Dst = SpecStructWidth1;
}
impl SpecIsoProof for StructWidth1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StructWidth1Mapper {
    type Src = StructWidth1Inner;
    type Dst = StructWidth1;
    type RefSrc = StructWidth1InnerRef<'a>;
}

pub struct SpecStructWidth1Combinator(pub SpecStructWidth1CombinatorAlias);

impl SpecCombinator for SpecStructWidth1Combinator {
    type Type = SpecStructWidth1;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStructWidth1Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecStructWidth1CombinatorAlias::is_prefix_secure() }
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
pub type SpecStructWidth1CombinatorAlias = Mapped<U8, StructWidth1Mapper>;

pub struct StructWidth1Combinator(pub StructWidth1CombinatorAlias);

impl View for StructWidth1Combinator {
    type V = SpecStructWidth1Combinator;
    open spec fn view(&self) -> Self::V { SpecStructWidth1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StructWidth1Combinator {
    type Type = StructWidth1;
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
pub type StructWidth1CombinatorAlias = Mapped<U8, StructWidth1Mapper>;


pub open spec fn spec_struct_width1() -> SpecStructWidth1Combinator {
    SpecStructWidth1Combinator(
    Mapped {
        inner: U8,
        mapper: StructWidth1Mapper,
    })
}

                
pub fn struct_width1<'a>() -> (o: StructWidth1Combinator)
    ensures o@ == spec_struct_width1(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = StructWidth1Combinator(
    Mapped {
        inner: U8,
        mapper: StructWidth1Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_struct_width1()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_struct_width1<'a>(input: &'a [u8]) -> (res: PResult<<StructWidth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_struct_width1().spec_parse(input@) == Some((n as int, v@)),
        spec_struct_width1().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_struct_width1().spec_parse(input@) is None,
        spec_struct_width1().spec_parse(input@) is None ==> res is Err,
{
    let combinator = struct_width1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_struct_width1<'a>(v: <StructWidth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_struct_width1().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_struct_width1().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_struct_width1().spec_serialize(v@))
        },
{
    let combinator = struct_width1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn struct_width1_len<'a>(v: <StructWidth1Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_struct_width1().wf(v@),
        spec_struct_width1().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_struct_width1().spec_serialize(v@).len(),
{
    let combinator = struct_width1();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
