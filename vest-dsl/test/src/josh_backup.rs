#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vest::bitcoin::varint::{BtcVarint, VarInt};
use vest::properties::*;
use vest::regular::bytes;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::leb128::*;
use vest::regular::modifier::*;
use vest::regular::repetition::*;
use vest::regular::sequence::*;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::regular::variant::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

pub struct SpecPairStress {
    pub f1: u8,
    pub f2: u8,
    pub f3: u8,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
}

pub type SpecPairStressInner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))))));


impl SpecFrom<SpecPairStress> for SpecPairStressInner {
    open spec fn spec_from(m: SpecPairStress) -> SpecPairStressInner {
        (m.f1, (m.f2, (m.f3, (m.f4, (m.f5, (m.f6, (m.f7, (m.f8, (m.f9, m.f10)))))))))
    }
}

impl SpecFrom<SpecPairStressInner> for SpecPairStress {
    open spec fn spec_from(m: SpecPairStressInner) -> SpecPairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, f10))))))))) = m;
        SpecPairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PairStress {
    pub f1: u8,
    pub f2: u8,
    pub f3: u8,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
}

impl View for PairStress {
    type V = SpecPairStress;

    open spec fn view(&self) -> Self::V {
        SpecPairStress {
            f1: self.f1@,
            f2: self.f2@,
            f3: self.f3@,
            f4: self.f4@,
            f5: self.f5@,
            f6: self.f6@,
            f7: self.f7@,
            f8: self.f8@,
            f9: self.f9@,
            f10: self.f10@,
        }
    }
}
pub type PairStressInner = (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8)))))))));

pub type PairStressInnerRef<'a> = (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u8)))))))));
impl<'a> From<&'a PairStress> for PairStressInnerRef<'a> {
    fn ex_from(m: &'a PairStress) -> PairStressInnerRef<'a> {
        (&m.f1, (&m.f2, (&m.f3, (&m.f4, (&m.f5, (&m.f6, (&m.f7, (&m.f8, (&m.f9, &m.f10)))))))))
    }
}

impl From<PairStressInner> for PairStress {
    fn ex_from(m: PairStressInner) -> PairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, f10))))))))) = m;
        PairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10 }
    }
}

pub struct PairStressMapper;
impl View for PairStressMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PairStressMapper {
    type Src = SpecPairStressInner;
    type Dst = SpecPairStress;
}
impl SpecIsoProof for PairStressMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for PairStressMapper {
    type Src = PairStressInner;
    type Dst = PairStress;
    type RefSrc = PairStressInnerRef<'a>;
}

// pub struct SpecPairStressCombinator(SpecPairStressCombinatorAlias);
struct SpecPairStressCombinator1(SpecPairStressCombinatorAlias1);
struct SpecPairStressCombinator2(SpecPairStressCombinatorAlias2);
struct SpecPairStressCombinator3(SpecPairStressCombinatorAlias3);
struct SpecPairStressCombinator4(SpecPairStressCombinatorAlias4);
struct SpecPairStressCombinator5(SpecPairStressCombinatorAlias5);
struct SpecPairStressCombinator6(SpecPairStressCombinatorAlias6);
struct SpecPairStressCombinator7(SpecPairStressCombinatorAlias7);
struct SpecPairStressCombinator8(SpecPairStressCombinatorAlias8);
struct SpecPairStressCombinator9(SpecPairStressCombinatorAlias9);
pub struct SpecPairStressCombinator(SpecPairStressCombinatorAlias);

macro_rules! impl_wrapper_spec_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::builtin_macros::verus! {
            impl SpecCombinator for $combinator {
                type Type = <$combinator_alias as SpecCombinator>::Type;
                closed spec fn requires(&self) -> bool
                { self.0.requires() }
                closed spec fn wf(&self, v: Self::Type) -> bool
                { self.0.wf(v) }
                closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
                { self.0.spec_parse(s) }
                closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
                { self.0.spec_serialize(v) }
            }
            impl SecureSpecCombinator for $combinator {
                open spec fn is_prefix_secure() -> bool
                { <$combinator_alias as SecureSpecCombinator>::is_prefix_secure() }
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
        } // verus!
    };
}

impl_wrapper_spec_combinator!(SpecPairStressCombinator1, SpecPairStressCombinatorAlias1);
impl_wrapper_spec_combinator!(SpecPairStressCombinator2, SpecPairStressCombinatorAlias2);
impl_wrapper_spec_combinator!(SpecPairStressCombinator3, SpecPairStressCombinatorAlias3);
impl_wrapper_spec_combinator!(SpecPairStressCombinator4, SpecPairStressCombinatorAlias4);
impl_wrapper_spec_combinator!(SpecPairStressCombinator5, SpecPairStressCombinatorAlias5);
impl_wrapper_spec_combinator!(SpecPairStressCombinator6, SpecPairStressCombinatorAlias6);
impl_wrapper_spec_combinator!(SpecPairStressCombinator7, SpecPairStressCombinatorAlias7);
impl_wrapper_spec_combinator!(SpecPairStressCombinator8, SpecPairStressCombinatorAlias8);
impl_wrapper_spec_combinator!(SpecPairStressCombinator9, SpecPairStressCombinatorAlias9);

impl SpecCombinator for SpecPairStressCombinator {
    type Type = SpecPairStress;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPairStressCombinator {
    open spec fn is_prefix_secure() -> bool
    { <SpecPairStressCombinatorAlias as SecureSpecCombinator>::is_prefix_secure() }
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
// pub type SpecPairStressCombinatorAlias = Mapped<(U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8))))))))), PairStressMapper>;

type SpecPairStressCombinatorAlias1 = (U8, U8);
type SpecPairStressCombinatorAlias2 = (U8, SpecPairStressCombinator1);
type SpecPairStressCombinatorAlias3 = (U8, SpecPairStressCombinator2);
type SpecPairStressCombinatorAlias4 = (U8, SpecPairStressCombinator3);
type SpecPairStressCombinatorAlias5 = (U8, SpecPairStressCombinator4);
type SpecPairStressCombinatorAlias6 = (U8, SpecPairStressCombinator5);
type SpecPairStressCombinatorAlias7 = (U8, SpecPairStressCombinator6);
type SpecPairStressCombinatorAlias8 = (U8, SpecPairStressCombinator7);
type SpecPairStressCombinatorAlias9 = (U8, SpecPairStressCombinator8);
pub type SpecPairStressCombinatorAlias = Mapped<SpecPairStressCombinator9, PairStressMapper>;

struct PairStressCombinator1(PairStressCombinatorAlias1);
struct PairStressCombinator2(PairStressCombinatorAlias2);
struct PairStressCombinator3(PairStressCombinatorAlias3);
struct PairStressCombinator4(PairStressCombinatorAlias4);
struct PairStressCombinator5(PairStressCombinatorAlias5);
struct PairStressCombinator6(PairStressCombinatorAlias6);
struct PairStressCombinator7(PairStressCombinatorAlias7);
struct PairStressCombinator8(PairStressCombinatorAlias8);
struct PairStressCombinator9(PairStressCombinatorAlias9);
pub struct PairStressCombinator(PairStressCombinatorAlias);

impl View for PairStressCombinator1 {
    type V = SpecPairStressCombinator1;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator1(self.0@) }
}
impl View for PairStressCombinator2 {
    type V = SpecPairStressCombinator2;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator2(self.0@) }
}
impl View for PairStressCombinator3 {
    type V = SpecPairStressCombinator3;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator3(self.0@) }
}
impl View for PairStressCombinator4 {
    type V = SpecPairStressCombinator4;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator4(self.0@) }
}
impl View for PairStressCombinator5 {
    type V = SpecPairStressCombinator5;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator5(self.0@) }
}
impl View for PairStressCombinator6 {
    type V = SpecPairStressCombinator6;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator6(self.0@) }
}
impl View for PairStressCombinator7 {
    type V = SpecPairStressCombinator7;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator7(self.0@) }
}
impl View for PairStressCombinator8 {
    type V = SpecPairStressCombinator8;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator8(self.0@) }
}
impl View for PairStressCombinator9 {
    type V = SpecPairStressCombinator9;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator9(self.0@) }
}
impl View for PairStressCombinator {
    type V = SpecPairStressCombinator;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator(self.0@) }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator1 {
    type Type = <PairStressCombinatorAlias1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator2 {
    type Type = <PairStressCombinatorAlias2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias2 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator3 {
    type Type = <PairStressCombinatorAlias3 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias3 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator4 {
    type Type = <PairStressCombinatorAlias4 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias4 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator5 {
    type Type = <PairStressCombinatorAlias5 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias5 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator6 {
    type Type = <PairStressCombinatorAlias6 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias6 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator7 {
    type Type = <PairStressCombinatorAlias7 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias7 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator8 {
    type Type = <PairStressCombinatorAlias8 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias8 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator9 {
    type Type = <PairStressCombinatorAlias9 as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
    type SType = <PairStressCombinatorAlias9 as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
    fn length(&self, v: Self::SType) -> usize
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
    closed spec fn ex_requires(&self) -> bool
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PairStressCombinator {
    type Type = PairStress;
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
// pub type PairStressCombinatorAlias = Mapped<(U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8))))))))), PairStressMapper>;
type PairStressCombinatorAlias1 = (U8, U8);
type PairStressCombinatorAlias2 = (U8, PairStressCombinator1);
type PairStressCombinatorAlias3 = (U8, PairStressCombinator2);
type PairStressCombinatorAlias4 = (U8, PairStressCombinator3);
type PairStressCombinatorAlias5 = (U8, PairStressCombinator4);
type PairStressCombinatorAlias6 = (U8, PairStressCombinator5);
type PairStressCombinatorAlias7 = (U8, PairStressCombinator6);
type PairStressCombinatorAlias8 = (U8, PairStressCombinator7);
type PairStressCombinatorAlias9 = (U8, PairStressCombinator8);
pub type PairStressCombinatorAlias = Mapped<PairStressCombinator9, PairStressMapper>;

pub closed spec fn spec_pair_stress() -> SpecPairStressCombinator {
    SpecPairStressCombinator(
    Mapped {
        // inner: (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8))))))))),
        inner: SpecPairStressCombinator9((U8, SpecPairStressCombinator8((U8, SpecPairStressCombinator7((U8, SpecPairStressCombinator6((U8, SpecPairStressCombinator5((U8, SpecPairStressCombinator4((U8, SpecPairStressCombinator3((U8, SpecPairStressCombinator2((U8, SpecPairStressCombinator1((U8, U8)))))))))))))))))),
        mapper: PairStressMapper,
    })
}


pub fn pair_stress() -> (o: PairStressCombinator)
    ensures o@ == spec_pair_stress(),
{
    PairStressCombinator(
    Mapped {
        inner: PairStressCombinator9((U8, PairStressCombinator8((U8, PairStressCombinator7((U8, PairStressCombinator6((U8, PairStressCombinator5((U8, PairStressCombinator4((U8, PairStressCombinator3((U8, PairStressCombinator2((U8, PairStressCombinator1((U8, U8)))))))))))))))))),
        mapper: PairStressMapper,
    })
}



}
