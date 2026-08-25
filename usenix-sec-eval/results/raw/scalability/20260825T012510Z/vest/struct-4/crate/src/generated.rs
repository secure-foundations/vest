
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

pub struct SpecStructWidth4 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
}

pub type SpecStructWidth4Inner = (u8, (u8, (u8, u8)));


impl SpecFrom<SpecStructWidth4> for SpecStructWidth4Inner {
    open spec fn spec_from(m: SpecStructWidth4) -> SpecStructWidth4Inner {
        (m.field0, (m.field1, (m.field2, m.field3)))
    }
}

impl SpecFrom<SpecStructWidth4Inner> for SpecStructWidth4 {
    open spec fn spec_from(m: SpecStructWidth4Inner) -> SpecStructWidth4 {
        let (field0, (field1, (field2, field3))) = m;
        SpecStructWidth4 { field0, field1, field2, field3 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct StructWidth4 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
}

impl View for StructWidth4 {
    type V = SpecStructWidth4;

    open spec fn view(&self) -> Self::V {
        SpecStructWidth4 {
            field0: self.field0@,
            field1: self.field1@,
            field2: self.field2@,
            field3: self.field3@,
        }
    }
}
pub type StructWidth4Inner = (u8, (u8, (u8, u8)));

pub type StructWidth4InnerRef<'a> = (&'a u8, (&'a u8, (&'a u8, &'a u8)));
impl<'a> From<&'a StructWidth4> for StructWidth4InnerRef<'a> {
    fn ex_from(m: &'a StructWidth4) -> StructWidth4InnerRef<'a> {
        (&m.field0, (&m.field1, (&m.field2, &m.field3)))
    }
}

impl From<StructWidth4Inner> for StructWidth4 {
    fn ex_from(m: StructWidth4Inner) -> StructWidth4 {
        let (field0, (field1, (field2, field3))) = m;
        StructWidth4 { field0, field1, field2, field3 }
    }
}

pub struct StructWidth4Mapper;
impl View for StructWidth4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StructWidth4Mapper {
    type Src = SpecStructWidth4Inner;
    type Dst = SpecStructWidth4;
}
impl SpecIsoProof for StructWidth4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StructWidth4Mapper {
    type Src = StructWidth4Inner;
    type Dst = StructWidth4;
    type RefSrc = StructWidth4InnerRef<'a>;
}
type SpecStructWidth4CombinatorAlias1 = (U8, U8);
type SpecStructWidth4CombinatorAlias2 = (U8, SpecStructWidth4CombinatorAlias1);
type SpecStructWidth4CombinatorAlias3 = (U8, SpecStructWidth4CombinatorAlias2);
pub struct SpecStructWidth4Combinator(pub SpecStructWidth4CombinatorAlias);

impl SpecCombinator for SpecStructWidth4Combinator {
    type Type = SpecStructWidth4;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStructWidth4Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecStructWidth4CombinatorAlias::is_prefix_secure() }
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
pub type SpecStructWidth4CombinatorAlias = Mapped<SpecStructWidth4CombinatorAlias3, StructWidth4Mapper>;
type StructWidth4CombinatorAlias1 = (U8, U8);
type StructWidth4CombinatorAlias2 = (U8, StructWidth4Combinator1);
type StructWidth4CombinatorAlias3 = (U8, StructWidth4Combinator2);
pub struct StructWidth4Combinator1(pub StructWidth4CombinatorAlias1);
impl View for StructWidth4Combinator1 {
    type V = SpecStructWidth4CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth4Combinator1, StructWidth4CombinatorAlias1);

pub struct StructWidth4Combinator2(pub StructWidth4CombinatorAlias2);
impl View for StructWidth4Combinator2 {
    type V = SpecStructWidth4CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth4Combinator2, StructWidth4CombinatorAlias2);

pub struct StructWidth4Combinator3(pub StructWidth4CombinatorAlias3);
impl View for StructWidth4Combinator3 {
    type V = SpecStructWidth4CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth4Combinator3, StructWidth4CombinatorAlias3);

pub struct StructWidth4Combinator(pub StructWidth4CombinatorAlias);

impl View for StructWidth4Combinator {
    type V = SpecStructWidth4Combinator;
    open spec fn view(&self) -> Self::V { SpecStructWidth4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StructWidth4Combinator {
    type Type = StructWidth4;
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
pub type StructWidth4CombinatorAlias = Mapped<StructWidth4Combinator3, StructWidth4Mapper>;


pub open spec fn spec_struct_width4() -> SpecStructWidth4Combinator {
    SpecStructWidth4Combinator(
    Mapped {
        inner: (U8, (U8, (U8, U8))),
        mapper: StructWidth4Mapper,
    })
}

                
pub fn struct_width4<'a>() -> (o: StructWidth4Combinator)
    ensures o@ == spec_struct_width4(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = StructWidth4Combinator(
    Mapped {
        inner: StructWidth4Combinator3((U8, StructWidth4Combinator2((U8, StructWidth4Combinator1((U8, U8)))))),
        mapper: StructWidth4Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_struct_width4()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_struct_width4<'a>(input: &'a [u8]) -> (res: PResult<<StructWidth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_struct_width4().spec_parse(input@) == Some((n as int, v@)),
        spec_struct_width4().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_struct_width4().spec_parse(input@) is None,
        spec_struct_width4().spec_parse(input@) is None ==> res is Err,
{
    let combinator = struct_width4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_struct_width4<'a>(v: <StructWidth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_struct_width4().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_struct_width4().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_struct_width4().spec_serialize(v@))
        },
{
    let combinator = struct_width4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn struct_width4_len<'a>(v: <StructWidth4Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_struct_width4().wf(v@),
        spec_struct_width4().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_struct_width4().spec_serialize(v@).len(),
{
    let combinator = struct_width4();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
