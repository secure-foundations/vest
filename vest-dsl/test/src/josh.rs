#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
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
verus!{

pub struct SpecDependentStress {
    pub tag1: u8,
    pub data1: Seq<u8>,
    pub tag2: u8,
    pub data2: Seq<u8>,
}

pub type SpecDependentStressInner = ((u8, (Seq<u8>, u8)), Seq<u8>);


impl SpecFrom<SpecDependentStress> for SpecDependentStressInner {
    open spec fn spec_from(m: SpecDependentStress) -> SpecDependentStressInner {
        ((m.tag1, (m.data1, m.tag2)), m.data2)
    }
}

impl SpecFrom<SpecDependentStressInner> for SpecDependentStress {
    open spec fn spec_from(m: SpecDependentStressInner) -> SpecDependentStress {
        let ((tag1, (data1, tag2)), data2) = m;
        SpecDependentStress { tag1, data1, tag2, data2 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct DependentStress<'a> {
    pub tag1: u8,
    pub data1: &'a [u8],
    pub tag2: u8,
    pub data2: &'a [u8],
}

impl View for DependentStress<'_> {
    type V = SpecDependentStress;

    open spec fn view(&self) -> Self::V {
        SpecDependentStress {
            tag1: self.tag1@,
            data1: self.data1@,
            tag2: self.tag2@,
            data2: self.data2@,
        }
    }
}
pub type DependentStressInner<'a> = ((u8, (&'a [u8], u8)), &'a [u8]);

pub type DependentStressInnerRef<'a> = ((&'a u8, (&'a &'a [u8], &'a u8)), &'a &'a [u8]);
impl<'a> From<&'a DependentStress<'a>> for DependentStressInnerRef<'a> {
    fn ex_from(m: &'a DependentStress) -> DependentStressInnerRef<'a> {
        ((&m.tag1, (&m.data1, &m.tag2)), &m.data2)
    }
}

impl<'a> From<DependentStressInner<'a>> for DependentStress<'a> {
    fn ex_from(m: DependentStressInner) -> DependentStress {
        let ((tag1, (data1, tag2)), data2) = m;
        DependentStress { tag1, data1, tag2, data2 }
    }
}

pub struct DependentStressMapper;
impl View for DependentStressMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DependentStressMapper {
    type Src = SpecDependentStressInner;
    type Dst = SpecDependentStress;
}
impl SpecIsoProof for DependentStressMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DependentStressMapper {
    type Src = DependentStressInner<'a>;
    type Dst = DependentStress<'a>;
    type RefSrc = DependentStressInnerRef<'a>;
}

pub struct SpecDependentStressCombinator(SpecDependentStressCombinatorAlias);

impl SpecCombinator for SpecDependentStressCombinator {
    type Type = SpecDependentStress;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDependentStressCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDependentStressCombinatorAlias::is_prefix_secure() }
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
pub type SpecDependentStressCombinatorAlias = Mapped<SpecPair<SpecPair<U8, (bytes::Variable, U8)>, bytes::Variable>, DependentStressMapper>;

pub struct DependentStressCombinator(DependentStressCombinatorAlias);

impl View for DependentStressCombinator {
    type V = SpecDependentStressCombinator;
    closed spec fn view(&self) -> Self::V { SpecDependentStressCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DependentStressCombinator {
    type Type = DependentStress<'a>;
    type SType = &'a Self::Type;
    closed spec fn spec_length(&self) -> Option<usize> 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::spec_length(&self.0) }
    fn length(&self) -> Option<usize> 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0) }
    closed spec fn ex_requires(&self) -> bool 
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&self.0) }
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) 
    { <_ as Combinator<'a, &'a [u8],Vec<u8>>>::parse(&self.0, s) }
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&self.0, v, data, pos) }
} 
pub type DependentStressCombinatorAlias = Mapped<Pair<Pair<U8, (bytes::Variable, U8), DependentStressCont1>, bytes::Variable, DependentStressCont0>, DependentStressMapper>;


pub closed spec fn spec_dependent_stress() -> SpecDependentStressCombinator {
    SpecDependentStressCombinator(
    Mapped {
        inner: Pair::spec_new(Pair::spec_new(U8, |deps| spec_dependent_stress_cont1(deps)), |deps| spec_dependent_stress_cont0(deps)),
        mapper: DependentStressMapper,
    })
}

pub open spec fn spec_dependent_stress_cont1(deps: u8) -> (bytes::Variable, U8) {
    let tag1 = deps;
    (bytes::Variable(tag1.spec_into()), U8)
}

impl View for DependentStressCont1 {
    type V = spec_fn(u8) -> (bytes::Variable, U8);

    open spec fn view(&self) -> Self::V {
        |deps: u8| {
            spec_dependent_stress_cont1(deps)
        }
    }
}

pub open spec fn spec_dependent_stress_cont0(deps: (u8, (Seq<u8>, u8))) -> bytes::Variable {
    let (tag1, (_, tag2)) = deps;
    bytes::Variable(tag2.spec_into())
}

impl View for DependentStressCont0 {
    type V = spec_fn((u8, (Seq<u8>, u8))) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        |deps: (u8, (Seq<u8>, u8))| {
            spec_dependent_stress_cont0(deps)
        }
    }
}

                
pub fn dependent_stress() -> (o: DependentStressCombinator)
    ensures o@ == spec_dependent_stress(),
{
    DependentStressCombinator(
    Mapped {
        inner: Pair::new(Pair::new(U8, DependentStressCont1), DependentStressCont0),
        mapper: DependentStressMapper,
    })
}

pub struct DependentStressCont1;
type DependentStressCont1Type<'a, 'b> = &'b u8;
type DependentStressCont1SType<'a, 'x> = &'x u8;
type DependentStressCont1Input<'a, 'b, 'x> = POrSType<DependentStressCont1Type<'a, 'b>, DependentStressCont1SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DependentStressCont1Input<'a, 'b, 'x>> for DependentStressCont1 {
    type Output = (bytes::Variable, U8);

    open spec fn requires(&self, deps: DependentStressCont1Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: DependentStressCont1Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_dependent_stress_cont1(deps@)
    }

    fn apply(&self, deps: DependentStressCont1Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag1 = *deps;
                (bytes::Variable(tag1.ex_into()), U8)
            }
            POrSType::S(deps) => {
                let tag1 = deps;
                let tag1 = *tag1;
                (bytes::Variable(tag1.ex_into()), U8)
            }
        }
    }
}
pub struct DependentStressCont0;
type DependentStressCont0Type<'a, 'b> = &'b (u8, (&'a [u8], u8));
type DependentStressCont0SType<'a, 'x> = (&'x u8, (&'x &'a [u8], &'x u8));
type DependentStressCont0Input<'a, 'b, 'x> = POrSType<DependentStressCont0Type<'a, 'b>, DependentStressCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DependentStressCont0Input<'a, 'b, 'x>> for DependentStressCont0 {
    type Output = bytes::Variable;

    open spec fn requires(&self, deps: DependentStressCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: DependentStressCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_dependent_stress_cont0(deps@)
    }

    fn apply(&self, deps: DependentStressCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let (tag1, (_, tag2)) = *deps;
                bytes::Variable(tag2.ex_into())
            }
            POrSType::S(deps) => {
                let (tag1, (_, tag2)) = deps;
                let (tag1, tag2) = (*tag1, *tag2);
                bytes::Variable(tag2.ex_into())
            }
        }
    }
}
                

}
