
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

pub struct SpecStructWidth8 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
}

pub type SpecStructWidth8Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))));


impl SpecFrom<SpecStructWidth8> for SpecStructWidth8Inner {
    open spec fn spec_from(m: SpecStructWidth8) -> SpecStructWidth8Inner {
        (m.field0, (m.field1, (m.field2, (m.field3, (m.field4, (m.field5, (m.field6, m.field7)))))))
    }
}

impl SpecFrom<SpecStructWidth8Inner> for SpecStructWidth8 {
    open spec fn spec_from(m: SpecStructWidth8Inner) -> SpecStructWidth8 {
        let (field0, (field1, (field2, (field3, (field4, (field5, (field6, field7))))))) = m;
        SpecStructWidth8 { field0, field1, field2, field3, field4, field5, field6, field7 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct StructWidth8 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
}

impl View for StructWidth8 {
    type V = SpecStructWidth8;

    open spec fn view(&self) -> Self::V {
        SpecStructWidth8 {
            field0: self.field0@,
            field1: self.field1@,
            field2: self.field2@,
            field3: self.field3@,
            field4: self.field4@,
            field5: self.field5@,
            field6: self.field6@,
            field7: self.field7@,
        }
    }
}
pub type StructWidth8Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))));

pub type StructWidth8InnerRef<'a> = (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u8)))))));
impl<'a> From<&'a StructWidth8> for StructWidth8InnerRef<'a> {
    fn ex_from(m: &'a StructWidth8) -> StructWidth8InnerRef<'a> {
        (&m.field0, (&m.field1, (&m.field2, (&m.field3, (&m.field4, (&m.field5, (&m.field6, &m.field7)))))))
    }
}

impl From<StructWidth8Inner> for StructWidth8 {
    fn ex_from(m: StructWidth8Inner) -> StructWidth8 {
        let (field0, (field1, (field2, (field3, (field4, (field5, (field6, field7))))))) = m;
        StructWidth8 { field0, field1, field2, field3, field4, field5, field6, field7 }
    }
}

pub struct StructWidth8Mapper;
impl View for StructWidth8Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StructWidth8Mapper {
    type Src = SpecStructWidth8Inner;
    type Dst = SpecStructWidth8;
}
impl SpecIsoProof for StructWidth8Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StructWidth8Mapper {
    type Src = StructWidth8Inner;
    type Dst = StructWidth8;
    type RefSrc = StructWidth8InnerRef<'a>;
}
type SpecStructWidth8CombinatorAlias1 = (U8, U8);
type SpecStructWidth8CombinatorAlias2 = (U8, SpecStructWidth8CombinatorAlias1);
type SpecStructWidth8CombinatorAlias3 = (U8, SpecStructWidth8CombinatorAlias2);
type SpecStructWidth8CombinatorAlias4 = (U8, SpecStructWidth8CombinatorAlias3);
type SpecStructWidth8CombinatorAlias5 = (U8, SpecStructWidth8CombinatorAlias4);
type SpecStructWidth8CombinatorAlias6 = (U8, SpecStructWidth8CombinatorAlias5);
type SpecStructWidth8CombinatorAlias7 = (U8, SpecStructWidth8CombinatorAlias6);
pub struct SpecStructWidth8Combinator(pub SpecStructWidth8CombinatorAlias);

impl SpecCombinator for SpecStructWidth8Combinator {
    type Type = SpecStructWidth8;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStructWidth8Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecStructWidth8CombinatorAlias::is_prefix_secure() }
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
pub type SpecStructWidth8CombinatorAlias = Mapped<SpecStructWidth8CombinatorAlias7, StructWidth8Mapper>;
type StructWidth8CombinatorAlias1 = (U8, U8);
type StructWidth8CombinatorAlias2 = (U8, StructWidth8Combinator1);
type StructWidth8CombinatorAlias3 = (U8, StructWidth8Combinator2);
type StructWidth8CombinatorAlias4 = (U8, StructWidth8Combinator3);
type StructWidth8CombinatorAlias5 = (U8, StructWidth8Combinator4);
type StructWidth8CombinatorAlias6 = (U8, StructWidth8Combinator5);
type StructWidth8CombinatorAlias7 = (U8, StructWidth8Combinator6);
pub struct StructWidth8Combinator1(pub StructWidth8CombinatorAlias1);
impl View for StructWidth8Combinator1 {
    type V = SpecStructWidth8CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator1, StructWidth8CombinatorAlias1);

pub struct StructWidth8Combinator2(pub StructWidth8CombinatorAlias2);
impl View for StructWidth8Combinator2 {
    type V = SpecStructWidth8CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator2, StructWidth8CombinatorAlias2);

pub struct StructWidth8Combinator3(pub StructWidth8CombinatorAlias3);
impl View for StructWidth8Combinator3 {
    type V = SpecStructWidth8CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator3, StructWidth8CombinatorAlias3);

pub struct StructWidth8Combinator4(pub StructWidth8CombinatorAlias4);
impl View for StructWidth8Combinator4 {
    type V = SpecStructWidth8CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator4, StructWidth8CombinatorAlias4);

pub struct StructWidth8Combinator5(pub StructWidth8CombinatorAlias5);
impl View for StructWidth8Combinator5 {
    type V = SpecStructWidth8CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator5, StructWidth8CombinatorAlias5);

pub struct StructWidth8Combinator6(pub StructWidth8CombinatorAlias6);
impl View for StructWidth8Combinator6 {
    type V = SpecStructWidth8CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator6, StructWidth8CombinatorAlias6);

pub struct StructWidth8Combinator7(pub StructWidth8CombinatorAlias7);
impl View for StructWidth8Combinator7 {
    type V = SpecStructWidth8CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth8Combinator7, StructWidth8CombinatorAlias7);

pub struct StructWidth8Combinator(pub StructWidth8CombinatorAlias);

impl View for StructWidth8Combinator {
    type V = SpecStructWidth8Combinator;
    open spec fn view(&self) -> Self::V { SpecStructWidth8Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StructWidth8Combinator {
    type Type = StructWidth8;
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
pub type StructWidth8CombinatorAlias = Mapped<StructWidth8Combinator7, StructWidth8Mapper>;


pub open spec fn spec_struct_width8() -> SpecStructWidth8Combinator {
    SpecStructWidth8Combinator(
    Mapped {
        inner: (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8))))))),
        mapper: StructWidth8Mapper,
    })
}

                
pub fn struct_width8<'a>() -> (o: StructWidth8Combinator)
    ensures o@ == spec_struct_width8(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = StructWidth8Combinator(
    Mapped {
        inner: StructWidth8Combinator7((U8, StructWidth8Combinator6((U8, StructWidth8Combinator5((U8, StructWidth8Combinator4((U8, StructWidth8Combinator3((U8, StructWidth8Combinator2((U8, StructWidth8Combinator1((U8, U8)))))))))))))),
        mapper: StructWidth8Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_struct_width8()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_struct_width8<'a>(input: &'a [u8]) -> (res: PResult<<StructWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_struct_width8().spec_parse(input@) == Some((n as int, v@)),
        spec_struct_width8().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_struct_width8().spec_parse(input@) is None,
        spec_struct_width8().spec_parse(input@) is None ==> res is Err,
{
    let combinator = struct_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_struct_width8<'a>(v: <StructWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_struct_width8().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_struct_width8().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_struct_width8().spec_serialize(v@))
        },
{
    let combinator = struct_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn struct_width8_len<'a>(v: <StructWidth8Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_struct_width8().wf(v@),
        spec_struct_width8().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_struct_width8().spec_serialize(v@).len(),
{
    let combinator = struct_width8();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
