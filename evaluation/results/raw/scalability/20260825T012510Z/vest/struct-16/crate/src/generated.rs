
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

pub struct SpecStructWidth16 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
    pub field8: u8,
    pub field9: u8,
    pub field10: u8,
    pub field11: u8,
    pub field12: u8,
    pub field13: u8,
    pub field14: u8,
    pub field15: u8,
}

pub type SpecStructWidth16Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))))))))))));


impl SpecFrom<SpecStructWidth16> for SpecStructWidth16Inner {
    open spec fn spec_from(m: SpecStructWidth16) -> SpecStructWidth16Inner {
        (m.field0, (m.field1, (m.field2, (m.field3, (m.field4, (m.field5, (m.field6, (m.field7, (m.field8, (m.field9, (m.field10, (m.field11, (m.field12, (m.field13, (m.field14, m.field15)))))))))))))))
    }
}

impl SpecFrom<SpecStructWidth16Inner> for SpecStructWidth16 {
    open spec fn spec_from(m: SpecStructWidth16Inner) -> SpecStructWidth16 {
        let (field0, (field1, (field2, (field3, (field4, (field5, (field6, (field7, (field8, (field9, (field10, (field11, (field12, (field13, (field14, field15))))))))))))))) = m;
        SpecStructWidth16 { field0, field1, field2, field3, field4, field5, field6, field7, field8, field9, field10, field11, field12, field13, field14, field15 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct StructWidth16 {
    pub field0: u8,
    pub field1: u8,
    pub field2: u8,
    pub field3: u8,
    pub field4: u8,
    pub field5: u8,
    pub field6: u8,
    pub field7: u8,
    pub field8: u8,
    pub field9: u8,
    pub field10: u8,
    pub field11: u8,
    pub field12: u8,
    pub field13: u8,
    pub field14: u8,
    pub field15: u8,
}

impl View for StructWidth16 {
    type V = SpecStructWidth16;

    open spec fn view(&self) -> Self::V {
        SpecStructWidth16 {
            field0: self.field0@,
            field1: self.field1@,
            field2: self.field2@,
            field3: self.field3@,
            field4: self.field4@,
            field5: self.field5@,
            field6: self.field6@,
            field7: self.field7@,
            field8: self.field8@,
            field9: self.field9@,
            field10: self.field10@,
            field11: self.field11@,
            field12: self.field12@,
            field13: self.field13@,
            field14: self.field14@,
            field15: self.field15@,
        }
    }
}
pub type StructWidth16Inner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))))))))))));

pub type StructWidth16InnerRef<'a> = (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u8)))))))))))))));
impl<'a> From<&'a StructWidth16> for StructWidth16InnerRef<'a> {
    fn ex_from(m: &'a StructWidth16) -> StructWidth16InnerRef<'a> {
        (&m.field0, (&m.field1, (&m.field2, (&m.field3, (&m.field4, (&m.field5, (&m.field6, (&m.field7, (&m.field8, (&m.field9, (&m.field10, (&m.field11, (&m.field12, (&m.field13, (&m.field14, &m.field15)))))))))))))))
    }
}

impl From<StructWidth16Inner> for StructWidth16 {
    fn ex_from(m: StructWidth16Inner) -> StructWidth16 {
        let (field0, (field1, (field2, (field3, (field4, (field5, (field6, (field7, (field8, (field9, (field10, (field11, (field12, (field13, (field14, field15))))))))))))))) = m;
        StructWidth16 { field0, field1, field2, field3, field4, field5, field6, field7, field8, field9, field10, field11, field12, field13, field14, field15 }
    }
}

pub struct StructWidth16Mapper;
impl View for StructWidth16Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StructWidth16Mapper {
    type Src = SpecStructWidth16Inner;
    type Dst = SpecStructWidth16;
}
impl SpecIsoProof for StructWidth16Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StructWidth16Mapper {
    type Src = StructWidth16Inner;
    type Dst = StructWidth16;
    type RefSrc = StructWidth16InnerRef<'a>;
}
type SpecStructWidth16CombinatorAlias1 = (U8, U8);
type SpecStructWidth16CombinatorAlias2 = (U8, SpecStructWidth16CombinatorAlias1);
type SpecStructWidth16CombinatorAlias3 = (U8, SpecStructWidth16CombinatorAlias2);
type SpecStructWidth16CombinatorAlias4 = (U8, SpecStructWidth16CombinatorAlias3);
type SpecStructWidth16CombinatorAlias5 = (U8, SpecStructWidth16CombinatorAlias4);
type SpecStructWidth16CombinatorAlias6 = (U8, SpecStructWidth16CombinatorAlias5);
type SpecStructWidth16CombinatorAlias7 = (U8, SpecStructWidth16CombinatorAlias6);
type SpecStructWidth16CombinatorAlias8 = (U8, SpecStructWidth16CombinatorAlias7);
type SpecStructWidth16CombinatorAlias9 = (U8, SpecStructWidth16CombinatorAlias8);
type SpecStructWidth16CombinatorAlias10 = (U8, SpecStructWidth16CombinatorAlias9);
type SpecStructWidth16CombinatorAlias11 = (U8, SpecStructWidth16CombinatorAlias10);
type SpecStructWidth16CombinatorAlias12 = (U8, SpecStructWidth16CombinatorAlias11);
type SpecStructWidth16CombinatorAlias13 = (U8, SpecStructWidth16CombinatorAlias12);
type SpecStructWidth16CombinatorAlias14 = (U8, SpecStructWidth16CombinatorAlias13);
type SpecStructWidth16CombinatorAlias15 = (U8, SpecStructWidth16CombinatorAlias14);
pub struct SpecStructWidth16Combinator(pub SpecStructWidth16CombinatorAlias);

impl SpecCombinator for SpecStructWidth16Combinator {
    type Type = SpecStructWidth16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStructWidth16Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecStructWidth16CombinatorAlias::is_prefix_secure() }
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
pub type SpecStructWidth16CombinatorAlias = Mapped<SpecStructWidth16CombinatorAlias15, StructWidth16Mapper>;
type StructWidth16CombinatorAlias1 = (U8, U8);
type StructWidth16CombinatorAlias2 = (U8, StructWidth16Combinator1);
type StructWidth16CombinatorAlias3 = (U8, StructWidth16Combinator2);
type StructWidth16CombinatorAlias4 = (U8, StructWidth16Combinator3);
type StructWidth16CombinatorAlias5 = (U8, StructWidth16Combinator4);
type StructWidth16CombinatorAlias6 = (U8, StructWidth16Combinator5);
type StructWidth16CombinatorAlias7 = (U8, StructWidth16Combinator6);
type StructWidth16CombinatorAlias8 = (U8, StructWidth16Combinator7);
type StructWidth16CombinatorAlias9 = (U8, StructWidth16Combinator8);
type StructWidth16CombinatorAlias10 = (U8, StructWidth16Combinator9);
type StructWidth16CombinatorAlias11 = (U8, StructWidth16Combinator10);
type StructWidth16CombinatorAlias12 = (U8, StructWidth16Combinator11);
type StructWidth16CombinatorAlias13 = (U8, StructWidth16Combinator12);
type StructWidth16CombinatorAlias14 = (U8, StructWidth16Combinator13);
type StructWidth16CombinatorAlias15 = (U8, StructWidth16Combinator14);
pub struct StructWidth16Combinator1(pub StructWidth16CombinatorAlias1);
impl View for StructWidth16Combinator1 {
    type V = SpecStructWidth16CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator1, StructWidth16CombinatorAlias1);

pub struct StructWidth16Combinator2(pub StructWidth16CombinatorAlias2);
impl View for StructWidth16Combinator2 {
    type V = SpecStructWidth16CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator2, StructWidth16CombinatorAlias2);

pub struct StructWidth16Combinator3(pub StructWidth16CombinatorAlias3);
impl View for StructWidth16Combinator3 {
    type V = SpecStructWidth16CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator3, StructWidth16CombinatorAlias3);

pub struct StructWidth16Combinator4(pub StructWidth16CombinatorAlias4);
impl View for StructWidth16Combinator4 {
    type V = SpecStructWidth16CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator4, StructWidth16CombinatorAlias4);

pub struct StructWidth16Combinator5(pub StructWidth16CombinatorAlias5);
impl View for StructWidth16Combinator5 {
    type V = SpecStructWidth16CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator5, StructWidth16CombinatorAlias5);

pub struct StructWidth16Combinator6(pub StructWidth16CombinatorAlias6);
impl View for StructWidth16Combinator6 {
    type V = SpecStructWidth16CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator6, StructWidth16CombinatorAlias6);

pub struct StructWidth16Combinator7(pub StructWidth16CombinatorAlias7);
impl View for StructWidth16Combinator7 {
    type V = SpecStructWidth16CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator7, StructWidth16CombinatorAlias7);

pub struct StructWidth16Combinator8(pub StructWidth16CombinatorAlias8);
impl View for StructWidth16Combinator8 {
    type V = SpecStructWidth16CombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator8, StructWidth16CombinatorAlias8);

pub struct StructWidth16Combinator9(pub StructWidth16CombinatorAlias9);
impl View for StructWidth16Combinator9 {
    type V = SpecStructWidth16CombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator9, StructWidth16CombinatorAlias9);

pub struct StructWidth16Combinator10(pub StructWidth16CombinatorAlias10);
impl View for StructWidth16Combinator10 {
    type V = SpecStructWidth16CombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator10, StructWidth16CombinatorAlias10);

pub struct StructWidth16Combinator11(pub StructWidth16CombinatorAlias11);
impl View for StructWidth16Combinator11 {
    type V = SpecStructWidth16CombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator11, StructWidth16CombinatorAlias11);

pub struct StructWidth16Combinator12(pub StructWidth16CombinatorAlias12);
impl View for StructWidth16Combinator12 {
    type V = SpecStructWidth16CombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator12, StructWidth16CombinatorAlias12);

pub struct StructWidth16Combinator13(pub StructWidth16CombinatorAlias13);
impl View for StructWidth16Combinator13 {
    type V = SpecStructWidth16CombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator13, StructWidth16CombinatorAlias13);

pub struct StructWidth16Combinator14(pub StructWidth16CombinatorAlias14);
impl View for StructWidth16Combinator14 {
    type V = SpecStructWidth16CombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator14, StructWidth16CombinatorAlias14);

pub struct StructWidth16Combinator15(pub StructWidth16CombinatorAlias15);
impl View for StructWidth16Combinator15 {
    type V = SpecStructWidth16CombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(StructWidth16Combinator15, StructWidth16CombinatorAlias15);

pub struct StructWidth16Combinator(pub StructWidth16CombinatorAlias);

impl View for StructWidth16Combinator {
    type V = SpecStructWidth16Combinator;
    open spec fn view(&self) -> Self::V { SpecStructWidth16Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StructWidth16Combinator {
    type Type = StructWidth16;
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
pub type StructWidth16CombinatorAlias = Mapped<StructWidth16Combinator15, StructWidth16Mapper>;


pub open spec fn spec_struct_width16() -> SpecStructWidth16Combinator {
    SpecStructWidth16Combinator(
    Mapped {
        inner: (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8))))))))))))))),
        mapper: StructWidth16Mapper,
    })
}

                
pub fn struct_width16<'a>() -> (o: StructWidth16Combinator)
    ensures o@ == spec_struct_width16(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = StructWidth16Combinator(
    Mapped {
        inner: StructWidth16Combinator15((U8, StructWidth16Combinator14((U8, StructWidth16Combinator13((U8, StructWidth16Combinator12((U8, StructWidth16Combinator11((U8, StructWidth16Combinator10((U8, StructWidth16Combinator9((U8, StructWidth16Combinator8((U8, StructWidth16Combinator7((U8, StructWidth16Combinator6((U8, StructWidth16Combinator5((U8, StructWidth16Combinator4((U8, StructWidth16Combinator3((U8, StructWidth16Combinator2((U8, StructWidth16Combinator1((U8, U8)))))))))))))))))))))))))))))),
        mapper: StructWidth16Mapper,
    });
    // assert({
    //     &&& combinator@ == spec_struct_width16()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_struct_width16<'a>(input: &'a [u8]) -> (res: PResult<<StructWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_struct_width16().spec_parse(input@) == Some((n as int, v@)),
        spec_struct_width16().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_struct_width16().spec_parse(input@) is None,
        spec_struct_width16().spec_parse(input@) is None ==> res is Err,
{
    let combinator = struct_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_struct_width16<'a>(v: <StructWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_struct_width16().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_struct_width16().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_struct_width16().spec_serialize(v@))
        },
{
    let combinator = struct_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn struct_width16_len<'a>(v: <StructWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_struct_width16().wf(v@),
        spec_struct_width16().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_struct_width16().spec_serialize(v@).len(),
{
    let combinator = struct_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
