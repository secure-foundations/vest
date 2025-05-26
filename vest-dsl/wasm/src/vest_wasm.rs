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

pub spec const SPEC_Numtype_I32: u8 = 127;
pub spec const SPEC_Numtype_I64: u8 = 126;
pub spec const SPEC_Numtype_F32: u8 = 125;
pub spec const SPEC_Numtype_F64: u8 = 124;
pub exec static EXEC_Numtype_I32: u8 ensures EXEC_Numtype_I32 == SPEC_Numtype_I32 { 127 }
pub exec static EXEC_Numtype_I64: u8 ensures EXEC_Numtype_I64 == SPEC_Numtype_I64 { 126 }
pub exec static EXEC_Numtype_F32: u8 ensures EXEC_Numtype_F32 == SPEC_Numtype_F32 { 125 }
pub exec static EXEC_Numtype_F64: u8 ensures EXEC_Numtype_F64 == SPEC_Numtype_F64 { 124 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Numtype {
    I32 = 127,
I64 = 126,
F32 = 125,
F64 = 124
}
pub type SpecNumtype = Numtype;

pub type NumtypeInner = u8;

pub type NumtypeInnerRef<'a> = &'a u8;

impl View for Numtype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<NumtypeInner> for Numtype {
    type Error = ();

    open spec fn spec_try_from(v: NumtypeInner) -> Result<Numtype, ()> {
        match v {
            127u8 => Ok(Numtype::I32),
            126u8 => Ok(Numtype::I64),
            125u8 => Ok(Numtype::F32),
            124u8 => Ok(Numtype::F64),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Numtype> for NumtypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Numtype) -> Result<NumtypeInner, ()> {
        match v {
            Numtype::I32 => Ok(SPEC_Numtype_I32),
            Numtype::I64 => Ok(SPEC_Numtype_I64),
            Numtype::F32 => Ok(SPEC_Numtype_F32),
            Numtype::F64 => Ok(SPEC_Numtype_F64),
        }
    }
}

impl TryFrom<NumtypeInner> for Numtype {
    type Error = ();

    fn ex_try_from(v: NumtypeInner) -> Result<Numtype, ()> {
        match v {
            127u8 => Ok(Numtype::I32),
            126u8 => Ok(Numtype::I64),
            125u8 => Ok(Numtype::F32),
            124u8 => Ok(Numtype::F64),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a Numtype> for NumtypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a Numtype) -> Result<NumtypeInnerRef<'a>, ()> {
        match v {
            Numtype::I32 => Ok(&EXEC_Numtype_I32),
            Numtype::I64 => Ok(&EXEC_Numtype_I64),
            Numtype::F32 => Ok(&EXEC_Numtype_F32),
            Numtype::F64 => Ok(&EXEC_Numtype_F64),
        }
    }
}

pub struct NumtypeMapper;

impl View for NumtypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for NumtypeMapper {
    type Src = NumtypeInner;
    type Dst = Numtype;
}

impl SpecPartialIsoProof for NumtypeMapper {
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

impl<'a> PartialIso<'a> for NumtypeMapper {
    type Src = NumtypeInner;
    type Dst = Numtype;
    type RefSrc = NumtypeInnerRef<'a>;
}


pub struct SpecNumtypeCombinator(SpecNumtypeCombinatorAlias);

impl SpecCombinator for SpecNumtypeCombinator {
    type Type = SpecNumtype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNumtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNumtypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecNumtypeCombinatorAlias = TryMap<U8, NumtypeMapper>;

pub struct NumtypeCombinator(NumtypeCombinatorAlias);

impl View for NumtypeCombinator {
    type V = SpecNumtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecNumtypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NumtypeCombinator {
    type Type = Numtype;
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
pub type NumtypeCombinatorAlias = TryMap<U8, NumtypeMapper>;


pub closed spec fn spec_numtype() -> SpecNumtypeCombinator {
    SpecNumtypeCombinator(TryMap { inner: U8, mapper: NumtypeMapper })
}

                
pub fn numtype() -> (o: NumtypeCombinator)
    ensures o@ == spec_numtype(),
{
    NumtypeCombinator(TryMap { inner: U8, mapper: NumtypeMapper })
}

                

pub spec const SPEC_Vectype_V128: u8 = 123;
pub exec static EXEC_Vectype_V128: u8 ensures EXEC_Vectype_V128 == SPEC_Vectype_V128 { 123 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Vectype {
    V128 = 123
}
pub type SpecVectype = Vectype;

pub type VectypeInner = u8;

pub type VectypeInnerRef<'a> = &'a u8;

impl View for Vectype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<VectypeInner> for Vectype {
    type Error = ();

    open spec fn spec_try_from(v: VectypeInner) -> Result<Vectype, ()> {
        match v {
            123u8 => Ok(Vectype::V128),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Vectype> for VectypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Vectype) -> Result<VectypeInner, ()> {
        match v {
            Vectype::V128 => Ok(SPEC_Vectype_V128),
        }
    }
}

impl TryFrom<VectypeInner> for Vectype {
    type Error = ();

    fn ex_try_from(v: VectypeInner) -> Result<Vectype, ()> {
        match v {
            123u8 => Ok(Vectype::V128),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a Vectype> for VectypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a Vectype) -> Result<VectypeInnerRef<'a>, ()> {
        match v {
            Vectype::V128 => Ok(&EXEC_Vectype_V128),
        }
    }
}

pub struct VectypeMapper;

impl View for VectypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for VectypeMapper {
    type Src = VectypeInner;
    type Dst = Vectype;
}

impl SpecPartialIsoProof for VectypeMapper {
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

impl<'a> PartialIso<'a> for VectypeMapper {
    type Src = VectypeInner;
    type Dst = Vectype;
    type RefSrc = VectypeInnerRef<'a>;
}


pub struct SpecVectypeCombinator(SpecVectypeCombinatorAlias);

impl SpecCombinator for SpecVectypeCombinator {
    type Type = SpecVectype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecVectypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecVectypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecVectypeCombinatorAlias = TryMap<U8, VectypeMapper>;

pub struct VectypeCombinator(VectypeCombinatorAlias);

impl View for VectypeCombinator {
    type V = SpecVectypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecVectypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for VectypeCombinator {
    type Type = Vectype;
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
pub type VectypeCombinatorAlias = TryMap<U8, VectypeMapper>;


pub closed spec fn spec_vectype() -> SpecVectypeCombinator {
    SpecVectypeCombinator(TryMap { inner: U8, mapper: VectypeMapper })
}

                
pub fn vectype() -> (o: VectypeCombinator)
    ensures o@ == spec_vectype(),
{
    VectypeCombinator(TryMap { inner: U8, mapper: VectypeMapper })
}

                

pub spec const SPEC_Reftype_FuncRef: u8 = 112;
pub spec const SPEC_Reftype_ExternRef: u8 = 111;
pub exec static EXEC_Reftype_FuncRef: u8 ensures EXEC_Reftype_FuncRef == SPEC_Reftype_FuncRef { 112 }
pub exec static EXEC_Reftype_ExternRef: u8 ensures EXEC_Reftype_ExternRef == SPEC_Reftype_ExternRef { 111 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum Reftype {
    FuncRef = 112,
ExternRef = 111
}
pub type SpecReftype = Reftype;

pub type ReftypeInner = u8;

pub type ReftypeInnerRef<'a> = &'a u8;

impl View for Reftype {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ReftypeInner> for Reftype {
    type Error = ();

    open spec fn spec_try_from(v: ReftypeInner) -> Result<Reftype, ()> {
        match v {
            112u8 => Ok(Reftype::FuncRef),
            111u8 => Ok(Reftype::ExternRef),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<Reftype> for ReftypeInner {
    type Error = ();

    open spec fn spec_try_from(v: Reftype) -> Result<ReftypeInner, ()> {
        match v {
            Reftype::FuncRef => Ok(SPEC_Reftype_FuncRef),
            Reftype::ExternRef => Ok(SPEC_Reftype_ExternRef),
        }
    }
}

impl TryFrom<ReftypeInner> for Reftype {
    type Error = ();

    fn ex_try_from(v: ReftypeInner) -> Result<Reftype, ()> {
        match v {
            112u8 => Ok(Reftype::FuncRef),
            111u8 => Ok(Reftype::ExternRef),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a Reftype> for ReftypeInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a Reftype) -> Result<ReftypeInnerRef<'a>, ()> {
        match v {
            Reftype::FuncRef => Ok(&EXEC_Reftype_FuncRef),
            Reftype::ExternRef => Ok(&EXEC_Reftype_ExternRef),
        }
    }
}

pub struct ReftypeMapper;

impl View for ReftypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for ReftypeMapper {
    type Src = ReftypeInner;
    type Dst = Reftype;
}

impl SpecPartialIsoProof for ReftypeMapper {
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

impl<'a> PartialIso<'a> for ReftypeMapper {
    type Src = ReftypeInner;
    type Dst = Reftype;
    type RefSrc = ReftypeInnerRef<'a>;
}


pub struct SpecReftypeCombinator(SpecReftypeCombinatorAlias);

impl SpecCombinator for SpecReftypeCombinator {
    type Type = SpecReftype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecReftypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecReftypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecReftypeCombinatorAlias = TryMap<U8, ReftypeMapper>;

pub struct ReftypeCombinator(ReftypeCombinatorAlias);

impl View for ReftypeCombinator {
    type V = SpecReftypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecReftypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ReftypeCombinator {
    type Type = Reftype;
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
pub type ReftypeCombinatorAlias = TryMap<U8, ReftypeMapper>;


pub closed spec fn spec_reftype() -> SpecReftypeCombinator {
    SpecReftypeCombinator(TryMap { inner: U8, mapper: ReftypeMapper })
}

                
pub fn reftype() -> (o: ReftypeCombinator)
    ensures o@ == spec_reftype(),
{
    ReftypeCombinator(TryMap { inner: U8, mapper: ReftypeMapper })
}

                

pub enum SpecValtype {
    NumTy(SpecNumtype),
    VecTy(SpecVectype),
    RefTy(SpecReftype),
}

pub type SpecValtypeInner = Either<SpecNumtype, Either<SpecVectype, SpecReftype>>;

impl SpecFrom<SpecValtype> for SpecValtypeInner {
    open spec fn spec_from(m: SpecValtype) -> SpecValtypeInner {
        match m {
            SpecValtype::NumTy(m) => Either::Left(m),
            SpecValtype::VecTy(m) => Either::Right(Either::Left(m)),
            SpecValtype::RefTy(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecValtypeInner> for SpecValtype {
    open spec fn spec_from(m: SpecValtypeInner) -> SpecValtype {
        match m {
            Either::Left(m) => SpecValtype::NumTy(m),
            Either::Right(Either::Left(m)) => SpecValtype::VecTy(m),
            Either::Right(Either::Right(m)) => SpecValtype::RefTy(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Valtype {
    NumTy(Numtype),
    VecTy(Vectype),
    RefTy(Reftype),
}

pub type ValtypeInner = Either<Numtype, Either<Vectype, Reftype>>;

pub type ValtypeInnerRef<'a> = Either<&'a Numtype, Either<&'a Vectype, &'a Reftype>>;


impl View for Valtype {
    type V = SpecValtype;
    open spec fn view(&self) -> Self::V {
        match self {
            Valtype::NumTy(m) => SpecValtype::NumTy(m@),
            Valtype::VecTy(m) => SpecValtype::VecTy(m@),
            Valtype::RefTy(m) => SpecValtype::RefTy(m@),
        }
    }
}


impl<'a> From<&'a Valtype> for ValtypeInnerRef<'a> {
    fn ex_from(m: &'a Valtype) -> ValtypeInnerRef<'a> {
        match m {
            Valtype::NumTy(m) => Either::Left(m),
            Valtype::VecTy(m) => Either::Right(Either::Left(m)),
            Valtype::RefTy(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ValtypeInner> for Valtype {
    fn ex_from(m: ValtypeInner) -> Valtype {
        match m {
            Either::Left(m) => Valtype::NumTy(m),
            Either::Right(Either::Left(m)) => Valtype::VecTy(m),
            Either::Right(Either::Right(m)) => Valtype::RefTy(m),
        }
    }
    
}


pub struct ValtypeMapper;
impl View for ValtypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ValtypeMapper {
    type Src = SpecValtypeInner;
    type Dst = SpecValtype;
}
impl SpecIsoProof for ValtypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ValtypeMapper {
    type Src = ValtypeInner;
    type Dst = Valtype;
    type RefSrc = ValtypeInnerRef<'a>;
}


impl DisjointFrom<SpecNumtypeCombinator> for SpecVectypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecNumtypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecNumtypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecNumtypeCombinator> for SpecReftypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecNumtypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecNumtypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecVectypeCombinator> for SpecReftypeCombinator {
    closed spec fn disjoint_from(&self, other: &SpecVectypeCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecVectypeCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}
pub struct SpecValtypeCombinator(SpecValtypeCombinatorAlias);

impl SpecCombinator for SpecValtypeCombinator {
    type Type = SpecValtype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecValtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecValtypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecValtypeCombinatorAlias = Mapped<Choice<SpecNumtypeCombinator, Choice<SpecVectypeCombinator, SpecReftypeCombinator>>, ValtypeMapper>;

pub struct ValtypeCombinator(ValtypeCombinatorAlias);

impl View for ValtypeCombinator {
    type V = SpecValtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecValtypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ValtypeCombinator {
    type Type = Valtype;
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
pub type ValtypeCombinatorAlias = Mapped<Choice<NumtypeCombinator, Choice<VectypeCombinator, ReftypeCombinator>>, ValtypeMapper>;


pub closed spec fn spec_valtype() -> SpecValtypeCombinator {
    SpecValtypeCombinator(Mapped { inner: Choice(spec_numtype(), Choice(spec_vectype(), spec_reftype())), mapper: ValtypeMapper })
}

                
pub fn valtype() -> (o: ValtypeCombinator)
    ensures o@ == spec_valtype(),
{
    ValtypeCombinator(Mapped { inner: Choice::new(numtype(), Choice::new(vectype(), reftype())), mapper: ValtypeMapper })
}

                

pub spec const SPEC_MutT_Const: u8 = 0;
pub spec const SPEC_MutT_Var: u8 = 1;
pub exec static EXEC_MutT_Const: u8 ensures EXEC_MutT_Const == SPEC_MutT_Const { 0 }
pub exec static EXEC_MutT_Var: u8 ensures EXEC_MutT_Var == SPEC_MutT_Var { 1 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum MutT {
    Const = 0,
Var = 1
}
pub type SpecMutT = MutT;

pub type MutTInner = u8;

pub type MutTInnerRef<'a> = &'a u8;

impl View for MutT {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<MutTInner> for MutT {
    type Error = ();

    open spec fn spec_try_from(v: MutTInner) -> Result<MutT, ()> {
        match v {
            0u8 => Ok(MutT::Const),
            1u8 => Ok(MutT::Var),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<MutT> for MutTInner {
    type Error = ();

    open spec fn spec_try_from(v: MutT) -> Result<MutTInner, ()> {
        match v {
            MutT::Const => Ok(SPEC_MutT_Const),
            MutT::Var => Ok(SPEC_MutT_Var),
        }
    }
}

impl TryFrom<MutTInner> for MutT {
    type Error = ();

    fn ex_try_from(v: MutTInner) -> Result<MutT, ()> {
        match v {
            0u8 => Ok(MutT::Const),
            1u8 => Ok(MutT::Var),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a MutT> for MutTInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a MutT) -> Result<MutTInnerRef<'a>, ()> {
        match v {
            MutT::Const => Ok(&EXEC_MutT_Const),
            MutT::Var => Ok(&EXEC_MutT_Var),
        }
    }
}

pub struct MutTMapper;

impl View for MutTMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for MutTMapper {
    type Src = MutTInner;
    type Dst = MutT;
}

impl SpecPartialIsoProof for MutTMapper {
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

impl<'a> PartialIso<'a> for MutTMapper {
    type Src = MutTInner;
    type Dst = MutT;
    type RefSrc = MutTInnerRef<'a>;
}


pub struct SpecMutTCombinator(SpecMutTCombinatorAlias);

impl SpecCombinator for SpecMutTCombinator {
    type Type = SpecMutT;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMutTCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMutTCombinatorAlias::is_prefix_secure() }
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
pub type SpecMutTCombinatorAlias = TryMap<U8, MutTMapper>;

pub struct MutTCombinator(MutTCombinatorAlias);

impl View for MutTCombinator {
    type V = SpecMutTCombinator;
    closed spec fn view(&self) -> Self::V { SpecMutTCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MutTCombinator {
    type Type = MutT;
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
pub type MutTCombinatorAlias = TryMap<U8, MutTMapper>;


pub closed spec fn spec_mut_t() -> SpecMutTCombinator {
    SpecMutTCombinator(TryMap { inner: U8, mapper: MutTMapper })
}

                
pub fn mut_t() -> (o: MutTCombinator)
    ensures o@ == spec_mut_t(),
{
    MutTCombinator(TryMap { inner: U8, mapper: MutTMapper })
}

                

pub struct SpecGlobaltype {
    pub t: SpecValtype,
    pub m: SpecMutT,
}

pub type SpecGlobaltypeInner = (SpecValtype, SpecMutT);


impl SpecFrom<SpecGlobaltype> for SpecGlobaltypeInner {
    open spec fn spec_from(m: SpecGlobaltype) -> SpecGlobaltypeInner {
        (m.t, m.m)
    }
}

impl SpecFrom<SpecGlobaltypeInner> for SpecGlobaltype {
    open spec fn spec_from(m: SpecGlobaltypeInner) -> SpecGlobaltype {
        let (t, m) = m;
        SpecGlobaltype { t, m }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Globaltype {
    pub t: Valtype,
    pub m: MutT,
}

impl View for Globaltype {
    type V = SpecGlobaltype;

    open spec fn view(&self) -> Self::V {
        SpecGlobaltype {
            t: self.t@,
            m: self.m@,
        }
    }
}
pub type GlobaltypeInner = (Valtype, MutT);

pub type GlobaltypeInnerRef<'a> = (&'a Valtype, &'a MutT);
impl<'a> From<&'a Globaltype> for GlobaltypeInnerRef<'a> {
    fn ex_from(m: &'a Globaltype) -> GlobaltypeInnerRef<'a> {
        (&m.t, &m.m)
    }
}

impl From<GlobaltypeInner> for Globaltype {
    fn ex_from(m: GlobaltypeInner) -> Globaltype {
        let (t, m) = m;
        Globaltype { t, m }
    }
}

pub struct GlobaltypeMapper;
impl View for GlobaltypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobaltypeMapper {
    type Src = SpecGlobaltypeInner;
    type Dst = SpecGlobaltype;
}
impl SpecIsoProof for GlobaltypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GlobaltypeMapper {
    type Src = GlobaltypeInner;
    type Dst = Globaltype;
    type RefSrc = GlobaltypeInnerRef<'a>;
}

pub struct SpecGlobaltypeCombinator(SpecGlobaltypeCombinatorAlias);

impl SpecCombinator for SpecGlobaltypeCombinator {
    type Type = SpecGlobaltype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobaltypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobaltypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecGlobaltypeCombinatorAlias = Mapped<(SpecValtypeCombinator, SpecMutTCombinator), GlobaltypeMapper>;

pub struct GlobaltypeCombinator(GlobaltypeCombinatorAlias);

impl View for GlobaltypeCombinator {
    type V = SpecGlobaltypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobaltypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GlobaltypeCombinator {
    type Type = Globaltype;
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
pub type GlobaltypeCombinatorAlias = Mapped<(ValtypeCombinator, MutTCombinator), GlobaltypeMapper>;


pub closed spec fn spec_globaltype() -> SpecGlobaltypeCombinator {
    SpecGlobaltypeCombinator(
    Mapped {
        inner: (spec_valtype(), spec_mut_t()),
        mapper: GlobaltypeMapper,
    })
}

                
pub fn globaltype() -> (o: GlobaltypeCombinator)
    ensures o@ == spec_globaltype(),
{
    GlobaltypeCombinator(
    Mapped {
        inner: (valtype(), mut_t()),
        mapper: GlobaltypeMapper,
    })
}

                
pub type SpecInstrBytecode = u8;
pub type InstrBytecode = u8;
pub type InstrBytecodeRef<'a> = &'a u8;


pub struct SpecInstrBytecodeCombinator(SpecInstrBytecodeCombinatorAlias);

impl SpecCombinator for SpecInstrBytecodeCombinator {
    type Type = SpecInstrBytecode;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrBytecodeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrBytecodeCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrBytecodeCombinatorAlias = U8;

pub struct InstrBytecodeCombinator(InstrBytecodeCombinatorAlias);

impl View for InstrBytecodeCombinator {
    type V = SpecInstrBytecodeCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrBytecodeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrBytecodeCombinator {
    type Type = InstrBytecode;
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
pub type InstrBytecodeCombinatorAlias = U8;


pub closed spec fn spec_instr_bytecode() -> SpecInstrBytecodeCombinator {
    SpecInstrBytecodeCombinator(U8)
}

                
pub fn instr_bytecode() -> (o: InstrBytecodeCombinator)
    ensures o@ == spec_instr_bytecode(),
{
    InstrBytecodeCombinator(U8)
}

                
pub type SpecLocalidx = u64;
pub type Localidx = u64;
pub type LocalidxRef<'a> = &'a u64;


pub struct SpecLocalidxCombinator(SpecLocalidxCombinatorAlias);

impl SpecCombinator for SpecLocalidxCombinator {
    type Type = SpecLocalidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecLocalidxCombinatorAlias = UnsignedLEB128;

pub struct LocalidxCombinator(LocalidxCombinatorAlias);

impl View for LocalidxCombinator {
    type V = SpecLocalidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LocalidxCombinator {
    type Type = Localidx;
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
pub type LocalidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_localidx() -> SpecLocalidxCombinator {
    SpecLocalidxCombinator(UnsignedLEB128)
}

                
pub fn localidx() -> (o: LocalidxCombinator)
    ensures o@ == spec_localidx(),
{
    LocalidxCombinator(UnsignedLEB128)
}

                
pub type SpecGlobalidx = u64;
pub type Globalidx = u64;
pub type GlobalidxRef<'a> = &'a u64;


pub struct SpecGlobalidxCombinator(SpecGlobalidxCombinatorAlias);

impl SpecCombinator for SpecGlobalidxCombinator {
    type Type = SpecGlobalidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecGlobalidxCombinatorAlias = UnsignedLEB128;

pub struct GlobalidxCombinator(GlobalidxCombinatorAlias);

impl View for GlobalidxCombinator {
    type V = SpecGlobalidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GlobalidxCombinator {
    type Type = Globalidx;
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
pub type GlobalidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_globalidx() -> SpecGlobalidxCombinator {
    SpecGlobalidxCombinator(UnsignedLEB128)
}

                
pub fn globalidx() -> (o: GlobalidxCombinator)
    ensures o@ == spec_globalidx(),
{
    GlobalidxCombinator(UnsignedLEB128)
}

                

pub enum SpecInstrVariable {
    LocalGet(SpecLocalidx),
    LocalSet(SpecLocalidx),
    LocalTee(SpecLocalidx),
    GlobalGet(SpecGlobalidx),
    GlobalSet(SpecGlobalidx),
}

pub type SpecInstrVariableInner = Either<SpecLocalidx, Either<SpecLocalidx, Either<SpecLocalidx, Either<SpecGlobalidx, SpecGlobalidx>>>>;

impl SpecFrom<SpecInstrVariable> for SpecInstrVariableInner {
    open spec fn spec_from(m: SpecInstrVariable) -> SpecInstrVariableInner {
        match m {
            SpecInstrVariable::LocalGet(m) => Either::Left(m),
            SpecInstrVariable::LocalSet(m) => Either::Right(Either::Left(m)),
            SpecInstrVariable::LocalTee(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrVariable::GlobalGet(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrVariable::GlobalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

                
impl SpecFrom<SpecInstrVariableInner> for SpecInstrVariable {
    open spec fn spec_from(m: SpecInstrVariableInner) -> SpecInstrVariable {
        match m {
            Either::Left(m) => SpecInstrVariable::LocalGet(m),
            Either::Right(Either::Left(m)) => SpecInstrVariable::LocalSet(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrVariable::LocalTee(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrVariable::GlobalGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => SpecInstrVariable::GlobalSet(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrVariable {
    LocalGet(Localidx),
    LocalSet(Localidx),
    LocalTee(Localidx),
    GlobalGet(Globalidx),
    GlobalSet(Globalidx),
}

pub type InstrVariableInner = Either<Localidx, Either<Localidx, Either<Localidx, Either<Globalidx, Globalidx>>>>;

pub type InstrVariableInnerRef<'a> = Either<&'a Localidx, Either<&'a Localidx, Either<&'a Localidx, Either<&'a Globalidx, &'a Globalidx>>>>;


impl View for InstrVariable {
    type V = SpecInstrVariable;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrVariable::LocalGet(m) => SpecInstrVariable::LocalGet(m@),
            InstrVariable::LocalSet(m) => SpecInstrVariable::LocalSet(m@),
            InstrVariable::LocalTee(m) => SpecInstrVariable::LocalTee(m@),
            InstrVariable::GlobalGet(m) => SpecInstrVariable::GlobalGet(m@),
            InstrVariable::GlobalSet(m) => SpecInstrVariable::GlobalSet(m@),
        }
    }
}


impl<'a> From<&'a InstrVariable> for InstrVariableInnerRef<'a> {
    fn ex_from(m: &'a InstrVariable) -> InstrVariableInnerRef<'a> {
        match m {
            InstrVariable::LocalGet(m) => Either::Left(m),
            InstrVariable::LocalSet(m) => Either::Right(Either::Left(m)),
            InstrVariable::LocalTee(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrVariable::GlobalGet(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrVariable::GlobalSet(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

impl From<InstrVariableInner> for InstrVariable {
    fn ex_from(m: InstrVariableInner) -> InstrVariable {
        match m {
            Either::Left(m) => InstrVariable::LocalGet(m),
            Either::Right(Either::Left(m)) => InstrVariable::LocalSet(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrVariable::LocalTee(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrVariable::GlobalGet(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => InstrVariable::GlobalSet(m),
        }
    }
    
}


pub struct InstrVariableMapper;
impl View for InstrVariableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrVariableMapper {
    type Src = SpecInstrVariableInner;
    type Dst = SpecInstrVariable;
}
impl SpecIsoProof for InstrVariableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrVariableMapper {
    type Src = InstrVariableInner;
    type Dst = InstrVariable;
    type RefSrc = InstrVariableInnerRef<'a>;
}


pub struct SpecInstrVariableCombinator(SpecInstrVariableCombinatorAlias);

impl SpecCombinator for SpecInstrVariableCombinator {
    type Type = SpecInstrVariable;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrVariableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrVariableCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrVariableCombinatorAlias = Mapped<Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<SpecLocalidxCombinator>, Choice<Cond<SpecGlobalidxCombinator>, Cond<SpecGlobalidxCombinator>>>>>, InstrVariableMapper>;

pub struct InstrVariableCombinator(InstrVariableCombinatorAlias);

impl View for InstrVariableCombinator {
    type V = SpecInstrVariableCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrVariableCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrVariableCombinator {
    type Type = InstrVariable;
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
pub type InstrVariableCombinatorAlias = Mapped<Choice<Cond<LocalidxCombinator>, Choice<Cond<LocalidxCombinator>, Choice<Cond<LocalidxCombinator>, Choice<Cond<GlobalidxCombinator>, Cond<GlobalidxCombinator>>>>>, InstrVariableMapper>;


pub closed spec fn spec_instr_variable(opcode: SpecInstrBytecode) -> SpecInstrVariableCombinator {
    SpecInstrVariableCombinator(Mapped { inner: Choice(Cond { cond: opcode == 32, inner: spec_localidx() }, Choice(Cond { cond: opcode == 33, inner: spec_localidx() }, Choice(Cond { cond: opcode == 34, inner: spec_localidx() }, Choice(Cond { cond: opcode == 35, inner: spec_globalidx() }, Cond { cond: opcode == 36, inner: spec_globalidx() })))), mapper: InstrVariableMapper })
}

pub fn instr_variable<'a>(opcode: InstrBytecode) -> (o: InstrVariableCombinator)
    ensures o@ == spec_instr_variable(opcode@),
{
    InstrVariableCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 32, inner: localidx() }, Choice::new(Cond { cond: opcode == 33, inner: localidx() }, Choice::new(Cond { cond: opcode == 34, inner: localidx() }, Choice::new(Cond { cond: opcode == 35, inner: globalidx() }, Cond { cond: opcode == 36, inner: globalidx() })))), mapper: InstrVariableMapper })
}

pub type SpecEmpty = Seq<u8>;
pub type Empty<'a> = &'a [u8];
pub type EmptyRef<'a> = &'a &'a [u8];


pub struct SpecEmptyCombinator(SpecEmptyCombinatorAlias);

impl SpecCombinator for SpecEmptyCombinator {
    type Type = SpecEmpty;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEmptyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyCombinatorAlias::is_prefix_secure() }
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
pub type SpecEmptyCombinatorAlias = bytes::Fixed<0>;

pub struct EmptyCombinator(EmptyCombinatorAlias);

impl View for EmptyCombinator {
    type V = SpecEmptyCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EmptyCombinator {
    type Type = Empty<'a>;
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
pub type EmptyCombinatorAlias = bytes::Fixed<0>;


pub closed spec fn spec_empty() -> SpecEmptyCombinator {
    SpecEmptyCombinator(bytes::Fixed::<0>)
}

                
pub fn empty() -> (o: EmptyCombinator)
    ensures o@ == spec_empty(),
{
    EmptyCombinator(bytes::Fixed::<0>)
}

                
pub type SpecLabelidx = u64;
pub type Labelidx = u64;
pub type LabelidxRef<'a> = &'a u64;


pub struct SpecLabelidxCombinator(SpecLabelidxCombinatorAlias);

impl SpecCombinator for SpecLabelidxCombinator {
    type Type = SpecLabelidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLabelidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLabelidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecLabelidxCombinatorAlias = UnsignedLEB128;

pub struct LabelidxCombinator(LabelidxCombinatorAlias);

impl View for LabelidxCombinator {
    type V = SpecLabelidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLabelidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LabelidxCombinator {
    type Type = Labelidx;
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
pub type LabelidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_labelidx() -> SpecLabelidxCombinator {
    SpecLabelidxCombinator(UnsignedLEB128)
}

                
pub fn labelidx() -> (o: LabelidxCombinator)
    ensures o@ == spec_labelidx(),
{
    LabelidxCombinator(UnsignedLEB128)
}

                
pub type SpecFuncidx = u64;
pub type Funcidx = u64;
pub type FuncidxRef<'a> = &'a u64;


pub struct SpecFuncidxCombinator(SpecFuncidxCombinatorAlias);

impl SpecCombinator for SpecFuncidxCombinator {
    type Type = SpecFuncidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecFuncidxCombinatorAlias = UnsignedLEB128;

pub struct FuncidxCombinator(FuncidxCombinatorAlias);

impl View for FuncidxCombinator {
    type V = SpecFuncidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FuncidxCombinator {
    type Type = Funcidx;
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
pub type FuncidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_funcidx() -> SpecFuncidxCombinator {
    SpecFuncidxCombinator(UnsignedLEB128)
}

                
pub fn funcidx() -> (o: FuncidxCombinator)
    ensures o@ == spec_funcidx(),
{
    FuncidxCombinator(UnsignedLEB128)
}

                

pub struct SpecLabelidxVec {
    pub l: u64,
    pub v: Seq<SpecLabelidx>,
}

pub type SpecLabelidxVecInner = (u64, Seq<SpecLabelidx>);


impl SpecFrom<SpecLabelidxVec> for SpecLabelidxVecInner {
    open spec fn spec_from(m: SpecLabelidxVec) -> SpecLabelidxVecInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecLabelidxVecInner> for SpecLabelidxVec {
    open spec fn spec_from(m: SpecLabelidxVecInner) -> SpecLabelidxVec {
        let (l, v) = m;
        SpecLabelidxVec { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LabelidxVec {
    pub l: u64,
    pub v: RepeatResult<Labelidx>,
}

impl View for LabelidxVec {
    type V = SpecLabelidxVec;

    open spec fn view(&self) -> Self::V {
        SpecLabelidxVec {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type LabelidxVecInner = (u64, RepeatResult<Labelidx>);

pub type LabelidxVecInnerRef<'a> = (&'a u64, &'a RepeatResult<Labelidx>);
impl<'a> From<&'a LabelidxVec> for LabelidxVecInnerRef<'a> {
    fn ex_from(m: &'a LabelidxVec) -> LabelidxVecInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<LabelidxVecInner> for LabelidxVec {
    fn ex_from(m: LabelidxVecInner) -> LabelidxVec {
        let (l, v) = m;
        LabelidxVec { l, v }
    }
}

pub struct LabelidxVecMapper;
impl View for LabelidxVecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LabelidxVecMapper {
    type Src = SpecLabelidxVecInner;
    type Dst = SpecLabelidxVec;
}
impl SpecIsoProof for LabelidxVecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LabelidxVecMapper {
    type Src = LabelidxVecInner;
    type Dst = LabelidxVec;
    type RefSrc = LabelidxVecInnerRef<'a>;
}

pub struct SpecLabelidxVecCombinator(SpecLabelidxVecCombinatorAlias);

impl SpecCombinator for SpecLabelidxVecCombinator {
    type Type = SpecLabelidxVec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLabelidxVecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLabelidxVecCombinatorAlias::is_prefix_secure() }
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
pub type SpecLabelidxVecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecLabelidxCombinator>>, LabelidxVecMapper>;

pub struct LabelidxVecCombinator(LabelidxVecCombinatorAlias);

impl View for LabelidxVecCombinator {
    type V = SpecLabelidxVecCombinator;
    closed spec fn view(&self) -> Self::V { SpecLabelidxVecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LabelidxVecCombinator {
    type Type = LabelidxVec;
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
pub type LabelidxVecCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<LabelidxCombinator>, LabelidxVecCont0>, LabelidxVecMapper>;


pub closed spec fn spec_labelidx_vec() -> SpecLabelidxVecCombinator {
    SpecLabelidxVecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_labelidx_vec_cont0(deps)),
        mapper: LabelidxVecMapper,
    })
}

pub open spec fn spec_labelidx_vec_cont0(deps: u64) -> RepeatN<SpecLabelidxCombinator> {
    let l = deps;
    RepeatN(spec_labelidx(), l.spec_into())
}

impl View for LabelidxVecCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecLabelidxCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_labelidx_vec_cont0(deps)
        }
    }
}

                
pub fn labelidx_vec() -> (o: LabelidxVecCombinator)
    ensures o@ == spec_labelidx_vec(),
{
    LabelidxVecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, LabelidxVecCont0),
        mapper: LabelidxVecMapper,
    })
}

pub struct LabelidxVecCont0;
type LabelidxVecCont0Type<'a, 'b> = &'b u64;
type LabelidxVecCont0SType<'a, 'x> = &'x u64;
type LabelidxVecCont0Input<'a, 'b, 'x> = POrSType<LabelidxVecCont0Type<'a, 'b>, LabelidxVecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<LabelidxVecCont0Input<'a, 'b, 'x>> for LabelidxVecCont0 {
    type Output = RepeatN<LabelidxCombinator>;

    open spec fn requires(&self, deps: LabelidxVecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: LabelidxVecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_labelidx_vec_cont0(deps@)
    }

    fn apply(&self, deps: LabelidxVecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(labelidx(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(labelidx(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecBrTable {
    pub l: SpecLabelidxVec,
    pub l_n: SpecLabelidx,
}

pub type SpecBrTableInner = (SpecLabelidxVec, SpecLabelidx);


impl SpecFrom<SpecBrTable> for SpecBrTableInner {
    open spec fn spec_from(m: SpecBrTable) -> SpecBrTableInner {
        (m.l, m.l_n)
    }
}

impl SpecFrom<SpecBrTableInner> for SpecBrTable {
    open spec fn spec_from(m: SpecBrTableInner) -> SpecBrTable {
        let (l, l_n) = m;
        SpecBrTable { l, l_n }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct BrTable {
    pub l: LabelidxVec,
    pub l_n: Labelidx,
}

impl View for BrTable {
    type V = SpecBrTable;

    open spec fn view(&self) -> Self::V {
        SpecBrTable {
            l: self.l@,
            l_n: self.l_n@,
        }
    }
}
pub type BrTableInner = (LabelidxVec, Labelidx);

pub type BrTableInnerRef<'a> = (&'a LabelidxVec, &'a Labelidx);
impl<'a> From<&'a BrTable> for BrTableInnerRef<'a> {
    fn ex_from(m: &'a BrTable) -> BrTableInnerRef<'a> {
        (&m.l, &m.l_n)
    }
}

impl From<BrTableInner> for BrTable {
    fn ex_from(m: BrTableInner) -> BrTable {
        let (l, l_n) = m;
        BrTable { l, l_n }
    }
}

pub struct BrTableMapper;
impl View for BrTableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BrTableMapper {
    type Src = SpecBrTableInner;
    type Dst = SpecBrTable;
}
impl SpecIsoProof for BrTableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for BrTableMapper {
    type Src = BrTableInner;
    type Dst = BrTable;
    type RefSrc = BrTableInnerRef<'a>;
}

pub struct SpecBrTableCombinator(SpecBrTableCombinatorAlias);

impl SpecCombinator for SpecBrTableCombinator {
    type Type = SpecBrTable;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBrTableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBrTableCombinatorAlias::is_prefix_secure() }
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
pub type SpecBrTableCombinatorAlias = Mapped<(SpecLabelidxVecCombinator, SpecLabelidxCombinator), BrTableMapper>;

pub struct BrTableCombinator(BrTableCombinatorAlias);

impl View for BrTableCombinator {
    type V = SpecBrTableCombinator;
    closed spec fn view(&self) -> Self::V { SpecBrTableCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for BrTableCombinator {
    type Type = BrTable;
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
pub type BrTableCombinatorAlias = Mapped<(LabelidxVecCombinator, LabelidxCombinator), BrTableMapper>;


pub closed spec fn spec_br_table() -> SpecBrTableCombinator {
    SpecBrTableCombinator(
    Mapped {
        inner: (spec_labelidx_vec(), spec_labelidx()),
        mapper: BrTableMapper,
    })
}

                
pub fn br_table() -> (o: BrTableCombinator)
    ensures o@ == spec_br_table(),
{
    BrTableCombinator(
    Mapped {
        inner: (labelidx_vec(), labelidx()),
        mapper: BrTableMapper,
    })
}

                
pub type SpecTypeidx = u64;
pub type Typeidx = u64;
pub type TypeidxRef<'a> = &'a u64;


pub struct SpecTypeidxCombinator(SpecTypeidxCombinatorAlias);

impl SpecCombinator for SpecTypeidxCombinator {
    type Type = SpecTypeidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypeidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypeidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecTypeidxCombinatorAlias = UnsignedLEB128;

pub struct TypeidxCombinator(TypeidxCombinatorAlias);

impl View for TypeidxCombinator {
    type V = SpecTypeidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypeidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TypeidxCombinator {
    type Type = Typeidx;
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
pub type TypeidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_typeidx() -> SpecTypeidxCombinator {
    SpecTypeidxCombinator(UnsignedLEB128)
}

                
pub fn typeidx() -> (o: TypeidxCombinator)
    ensures o@ == spec_typeidx(),
{
    TypeidxCombinator(UnsignedLEB128)
}

                
pub type SpecTableidx = u64;
pub type Tableidx = u64;
pub type TableidxRef<'a> = &'a u64;


pub struct SpecTableidxCombinator(SpecTableidxCombinatorAlias);

impl SpecCombinator for SpecTableidxCombinator {
    type Type = SpecTableidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableidxCombinatorAlias = UnsignedLEB128;

pub struct TableidxCombinator(TableidxCombinatorAlias);

impl View for TableidxCombinator {
    type V = SpecTableidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableidxCombinator {
    type Type = Tableidx;
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
pub type TableidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_tableidx() -> SpecTableidxCombinator {
    SpecTableidxCombinator(UnsignedLEB128)
}

                
pub fn tableidx() -> (o: TableidxCombinator)
    ensures o@ == spec_tableidx(),
{
    TableidxCombinator(UnsignedLEB128)
}

                

pub struct SpecCallIndirect {
    pub y: SpecTypeidx,
    pub x: SpecTableidx,
}

pub type SpecCallIndirectInner = (SpecTypeidx, SpecTableidx);


impl SpecFrom<SpecCallIndirect> for SpecCallIndirectInner {
    open spec fn spec_from(m: SpecCallIndirect) -> SpecCallIndirectInner {
        (m.y, m.x)
    }
}

impl SpecFrom<SpecCallIndirectInner> for SpecCallIndirect {
    open spec fn spec_from(m: SpecCallIndirectInner) -> SpecCallIndirect {
        let (y, x) = m;
        SpecCallIndirect { y, x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CallIndirect {
    pub y: Typeidx,
    pub x: Tableidx,
}

impl View for CallIndirect {
    type V = SpecCallIndirect;

    open spec fn view(&self) -> Self::V {
        SpecCallIndirect {
            y: self.y@,
            x: self.x@,
        }
    }
}
pub type CallIndirectInner = (Typeidx, Tableidx);

pub type CallIndirectInnerRef<'a> = (&'a Typeidx, &'a Tableidx);
impl<'a> From<&'a CallIndirect> for CallIndirectInnerRef<'a> {
    fn ex_from(m: &'a CallIndirect) -> CallIndirectInnerRef<'a> {
        (&m.y, &m.x)
    }
}

impl From<CallIndirectInner> for CallIndirect {
    fn ex_from(m: CallIndirectInner) -> CallIndirect {
        let (y, x) = m;
        CallIndirect { y, x }
    }
}

pub struct CallIndirectMapper;
impl View for CallIndirectMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CallIndirectMapper {
    type Src = SpecCallIndirectInner;
    type Dst = SpecCallIndirect;
}
impl SpecIsoProof for CallIndirectMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CallIndirectMapper {
    type Src = CallIndirectInner;
    type Dst = CallIndirect;
    type RefSrc = CallIndirectInnerRef<'a>;
}

pub struct SpecCallIndirectCombinator(SpecCallIndirectCombinatorAlias);

impl SpecCombinator for SpecCallIndirectCombinator {
    type Type = SpecCallIndirect;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCallIndirectCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCallIndirectCombinatorAlias::is_prefix_secure() }
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
pub type SpecCallIndirectCombinatorAlias = Mapped<(SpecTypeidxCombinator, SpecTableidxCombinator), CallIndirectMapper>;

pub struct CallIndirectCombinator(CallIndirectCombinatorAlias);

impl View for CallIndirectCombinator {
    type V = SpecCallIndirectCombinator;
    closed spec fn view(&self) -> Self::V { SpecCallIndirectCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CallIndirectCombinator {
    type Type = CallIndirect;
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
pub type CallIndirectCombinatorAlias = Mapped<(TypeidxCombinator, TableidxCombinator), CallIndirectMapper>;


pub closed spec fn spec_call_indirect() -> SpecCallIndirectCombinator {
    SpecCallIndirectCombinator(
    Mapped {
        inner: (spec_typeidx(), spec_tableidx()),
        mapper: CallIndirectMapper,
    })
}

                
pub fn call_indirect() -> (o: CallIndirectCombinator)
    ensures o@ == spec_call_indirect(),
{
    CallIndirectCombinator(
    Mapped {
        inner: (typeidx(), tableidx()),
        mapper: CallIndirectMapper,
    })
}

                

pub enum SpecInstrControl2 {
    End(SpecEmpty),
    BrIf(SpecLabelidx),
    Br(SpecLabelidx),
    Call(SpecFuncidx),
    Ret(SpecEmpty),
    BrTable(SpecBrTable),
    CallIndirect(SpecCallIndirect),
}

pub type SpecInstrControl2Inner = Either<SpecEmpty, Either<SpecLabelidx, Either<SpecLabelidx, Either<SpecFuncidx, Either<SpecEmpty, Either<SpecBrTable, SpecCallIndirect>>>>>>;

impl SpecFrom<SpecInstrControl2> for SpecInstrControl2Inner {
    open spec fn spec_from(m: SpecInstrControl2) -> SpecInstrControl2Inner {
        match m {
            SpecInstrControl2::End(m) => Either::Left(m),
            SpecInstrControl2::BrIf(m) => Either::Right(Either::Left(m)),
            SpecInstrControl2::Br(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrControl2::Call(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrControl2::Ret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrControl2::BrTable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrControl2::CallIndirect(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

                
impl SpecFrom<SpecInstrControl2Inner> for SpecInstrControl2 {
    open spec fn spec_from(m: SpecInstrControl2Inner) -> SpecInstrControl2 {
        match m {
            Either::Left(m) => SpecInstrControl2::End(m),
            Either::Right(Either::Left(m)) => SpecInstrControl2::BrIf(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrControl2::Br(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrControl2::Call(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrControl2::Ret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrControl2::BrTable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => SpecInstrControl2::CallIndirect(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrControl2<'a> {
    End(Empty<'a>),
    BrIf(Labelidx),
    Br(Labelidx),
    Call(Funcidx),
    Ret(Empty<'a>),
    BrTable(BrTable),
    CallIndirect(CallIndirect),
}

pub type InstrControl2Inner<'a> = Either<Empty<'a>, Either<Labelidx, Either<Labelidx, Either<Funcidx, Either<Empty<'a>, Either<BrTable, CallIndirect>>>>>>;

pub type InstrControl2InnerRef<'a> = Either<&'a Empty<'a>, Either<&'a Labelidx, Either<&'a Labelidx, Either<&'a Funcidx, Either<&'a Empty<'a>, Either<&'a BrTable, &'a CallIndirect>>>>>>;


impl<'a> View for InstrControl2<'a> {
    type V = SpecInstrControl2;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrControl2::End(m) => SpecInstrControl2::End(m@),
            InstrControl2::BrIf(m) => SpecInstrControl2::BrIf(m@),
            InstrControl2::Br(m) => SpecInstrControl2::Br(m@),
            InstrControl2::Call(m) => SpecInstrControl2::Call(m@),
            InstrControl2::Ret(m) => SpecInstrControl2::Ret(m@),
            InstrControl2::BrTable(m) => SpecInstrControl2::BrTable(m@),
            InstrControl2::CallIndirect(m) => SpecInstrControl2::CallIndirect(m@),
        }
    }
}


impl<'a> From<&'a InstrControl2<'a>> for InstrControl2InnerRef<'a> {
    fn ex_from(m: &'a InstrControl2<'a>) -> InstrControl2InnerRef<'a> {
        match m {
            InstrControl2::End(m) => Either::Left(m),
            InstrControl2::BrIf(m) => Either::Right(Either::Left(m)),
            InstrControl2::Br(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrControl2::Call(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrControl2::Ret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrControl2::BrTable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrControl2::CallIndirect(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

impl<'a> From<InstrControl2Inner<'a>> for InstrControl2<'a> {
    fn ex_from(m: InstrControl2Inner<'a>) -> InstrControl2<'a> {
        match m {
            Either::Left(m) => InstrControl2::End(m),
            Either::Right(Either::Left(m)) => InstrControl2::BrIf(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrControl2::Br(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrControl2::Call(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrControl2::Ret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrControl2::BrTable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => InstrControl2::CallIndirect(m),
        }
    }
    
}


pub struct InstrControl2Mapper;
impl View for InstrControl2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrControl2Mapper {
    type Src = SpecInstrControl2Inner;
    type Dst = SpecInstrControl2;
}
impl SpecIsoProof for InstrControl2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrControl2Mapper {
    type Src = InstrControl2Inner<'a>;
    type Dst = InstrControl2<'a>;
    type RefSrc = InstrControl2InnerRef<'a>;
}


pub struct SpecInstrControl2Combinator(SpecInstrControl2CombinatorAlias);

impl SpecCombinator for SpecInstrControl2Combinator {
    type Type = SpecInstrControl2;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrControl2Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrControl2CombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrControl2CombinatorAlias = Mapped<Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecLabelidxCombinator>, Choice<Cond<SpecLabelidxCombinator>, Choice<Cond<SpecFuncidxCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecBrTableCombinator>, Cond<SpecCallIndirectCombinator>>>>>>>, InstrControl2Mapper>;

pub struct InstrControl2Combinator(InstrControl2CombinatorAlias);

impl View for InstrControl2Combinator {
    type V = SpecInstrControl2Combinator;
    closed spec fn view(&self) -> Self::V { SpecInstrControl2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrControl2Combinator {
    type Type = InstrControl2<'a>;
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
pub type InstrControl2CombinatorAlias = Mapped<Choice<Cond<EmptyCombinator>, Choice<Cond<LabelidxCombinator>, Choice<Cond<LabelidxCombinator>, Choice<Cond<FuncidxCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<BrTableCombinator>, Cond<CallIndirectCombinator>>>>>>>, InstrControl2Mapper>;


pub closed spec fn spec_instr_control2(opcode: SpecInstrBytecode) -> SpecInstrControl2Combinator {
    SpecInstrControl2Combinator(Mapped { inner: Choice(Cond { cond: opcode == 11, inner: spec_empty() }, Choice(Cond { cond: opcode == 13, inner: spec_labelidx() }, Choice(Cond { cond: opcode == 12, inner: spec_labelidx() }, Choice(Cond { cond: opcode == 16, inner: spec_funcidx() }, Choice(Cond { cond: opcode == 15, inner: spec_empty() }, Choice(Cond { cond: opcode == 14, inner: spec_br_table() }, Cond { cond: opcode == 17, inner: spec_call_indirect() })))))), mapper: InstrControl2Mapper })
}

pub fn instr_control2<'a>(opcode: InstrBytecode) -> (o: InstrControl2Combinator)
    ensures o@ == spec_instr_control2(opcode@),
{
    InstrControl2Combinator(Mapped { inner: Choice::new(Cond { cond: opcode == 11, inner: empty() }, Choice::new(Cond { cond: opcode == 13, inner: labelidx() }, Choice::new(Cond { cond: opcode == 12, inner: labelidx() }, Choice::new(Cond { cond: opcode == 16, inner: funcidx() }, Choice::new(Cond { cond: opcode == 15, inner: empty() }, Choice::new(Cond { cond: opcode == 14, inner: br_table() }, Cond { cond: opcode == 17, inner: call_indirect() })))))), mapper: InstrControl2Mapper })
}


pub struct SpecEmptyBlock {
    pub tag: u8,
    pub body: SpecEmpty,
}

pub type SpecEmptyBlockInner = (u8, SpecEmpty);


impl SpecFrom<SpecEmptyBlock> for SpecEmptyBlockInner {
    open spec fn spec_from(m: SpecEmptyBlock) -> SpecEmptyBlockInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecEmptyBlockInner> for SpecEmptyBlock {
    open spec fn spec_from(m: SpecEmptyBlockInner) -> SpecEmptyBlock {
        let (tag, body) = m;
        SpecEmptyBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct EmptyBlock<'a> {
    pub tag: u8,
    pub body: Empty<'a>,
}

impl View for EmptyBlock<'_> {
    type V = SpecEmptyBlock;

    open spec fn view(&self) -> Self::V {
        SpecEmptyBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type EmptyBlockInner<'a> = (u8, Empty<'a>);

pub type EmptyBlockInnerRef<'a> = (&'a u8, &'a Empty<'a>);
impl<'a> From<&'a EmptyBlock<'a>> for EmptyBlockInnerRef<'a> {
    fn ex_from(m: &'a EmptyBlock) -> EmptyBlockInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl<'a> From<EmptyBlockInner<'a>> for EmptyBlock<'a> {
    fn ex_from(m: EmptyBlockInner) -> EmptyBlock {
        let (tag, body) = m;
        EmptyBlock { tag, body }
    }
}

pub struct EmptyBlockMapper;
impl View for EmptyBlockMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EmptyBlockMapper {
    type Src = SpecEmptyBlockInner;
    type Dst = SpecEmptyBlock;
}
impl SpecIsoProof for EmptyBlockMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for EmptyBlockMapper {
    type Src = EmptyBlockInner<'a>;
    type Dst = EmptyBlock<'a>;
    type RefSrc = EmptyBlockInnerRef<'a>;
}

pub struct SpecEmptyBlockCombinator(SpecEmptyBlockCombinatorAlias);

impl SpecCombinator for SpecEmptyBlockCombinator {
    type Type = SpecEmptyBlock;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecEmptyBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyBlockCombinatorAlias::is_prefix_secure() }
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
pub type SpecEmptyBlockCombinatorAlias = Mapped<(Refined<U8, Predicate16713707613369419146>, SpecEmptyCombinator), EmptyBlockMapper>;
pub struct Predicate16713707613369419146;
impl View for Predicate16713707613369419146 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16713707613369419146 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 64)
    }
}
impl SpecPred<u8> for Predicate16713707613369419146 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 64)
    }
}

pub struct EmptyBlockCombinator(EmptyBlockCombinatorAlias);

impl View for EmptyBlockCombinator {
    type V = SpecEmptyBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyBlockCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for EmptyBlockCombinator {
    type Type = EmptyBlock<'a>;
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
pub type EmptyBlockCombinatorAlias = Mapped<(Refined<U8, Predicate16713707613369419146>, EmptyCombinator), EmptyBlockMapper>;


pub closed spec fn spec_empty_block() -> SpecEmptyBlockCombinator {
    SpecEmptyBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate16713707613369419146 }, spec_empty()),
        mapper: EmptyBlockMapper,
    })
}

                
pub fn empty_block() -> (o: EmptyBlockCombinator)
    ensures o@ == spec_empty_block(),
{
    EmptyBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate16713707613369419146 }, empty()),
        mapper: EmptyBlockMapper,
    })
}

                

pub struct SpecValtypeBlock {
    pub tag: u8,
    pub body: SpecEmpty,
}

pub type SpecValtypeBlockInner = (u8, SpecEmpty);


impl SpecFrom<SpecValtypeBlock> for SpecValtypeBlockInner {
    open spec fn spec_from(m: SpecValtypeBlock) -> SpecValtypeBlockInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecValtypeBlockInner> for SpecValtypeBlock {
    open spec fn spec_from(m: SpecValtypeBlockInner) -> SpecValtypeBlock {
        let (tag, body) = m;
        SpecValtypeBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ValtypeBlock<'a> {
    pub tag: u8,
    pub body: Empty<'a>,
}

impl View for ValtypeBlock<'_> {
    type V = SpecValtypeBlock;

    open spec fn view(&self) -> Self::V {
        SpecValtypeBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type ValtypeBlockInner<'a> = (u8, Empty<'a>);

pub type ValtypeBlockInnerRef<'a> = (&'a u8, &'a Empty<'a>);
impl<'a> From<&'a ValtypeBlock<'a>> for ValtypeBlockInnerRef<'a> {
    fn ex_from(m: &'a ValtypeBlock) -> ValtypeBlockInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl<'a> From<ValtypeBlockInner<'a>> for ValtypeBlock<'a> {
    fn ex_from(m: ValtypeBlockInner) -> ValtypeBlock {
        let (tag, body) = m;
        ValtypeBlock { tag, body }
    }
}

pub struct ValtypeBlockMapper;
impl View for ValtypeBlockMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ValtypeBlockMapper {
    type Src = SpecValtypeBlockInner;
    type Dst = SpecValtypeBlock;
}
impl SpecIsoProof for ValtypeBlockMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ValtypeBlockMapper {
    type Src = ValtypeBlockInner<'a>;
    type Dst = ValtypeBlock<'a>;
    type RefSrc = ValtypeBlockInnerRef<'a>;
}

pub struct SpecValtypeBlockCombinator(SpecValtypeBlockCombinatorAlias);

impl SpecCombinator for SpecValtypeBlockCombinator {
    type Type = SpecValtypeBlock;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecValtypeBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecValtypeBlockCombinatorAlias::is_prefix_secure() }
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
pub type SpecValtypeBlockCombinatorAlias = Mapped<(Refined<U8, Predicate17051755724411564727>, SpecEmptyCombinator), ValtypeBlockMapper>;
pub struct Predicate17051755724411564727;
impl View for Predicate17051755724411564727 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate17051755724411564727 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112)
    }
}
impl SpecPred<u8> for Predicate17051755724411564727 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112)
    }
}

pub struct ValtypeBlockCombinator(ValtypeBlockCombinatorAlias);

impl View for ValtypeBlockCombinator {
    type V = SpecValtypeBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecValtypeBlockCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ValtypeBlockCombinator {
    type Type = ValtypeBlock<'a>;
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
pub type ValtypeBlockCombinatorAlias = Mapped<(Refined<U8, Predicate17051755724411564727>, EmptyCombinator), ValtypeBlockMapper>;


pub closed spec fn spec_valtype_block() -> SpecValtypeBlockCombinator {
    SpecValtypeBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate17051755724411564727 }, spec_empty()),
        mapper: ValtypeBlockMapper,
    })
}

                
pub fn valtype_block() -> (o: ValtypeBlockCombinator)
    ensures o@ == spec_valtype_block(),
{
    ValtypeBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate17051755724411564727 }, empty()),
        mapper: ValtypeBlockMapper,
    })
}

                

pub struct SpecTypeidxBlock {
    pub tag: u8,
    pub body: u64,
}

pub type SpecTypeidxBlockInner = (u8, u64);


impl SpecFrom<SpecTypeidxBlock> for SpecTypeidxBlockInner {
    open spec fn spec_from(m: SpecTypeidxBlock) -> SpecTypeidxBlockInner {
        (m.tag, m.body)
    }
}

impl SpecFrom<SpecTypeidxBlockInner> for SpecTypeidxBlock {
    open spec fn spec_from(m: SpecTypeidxBlockInner) -> SpecTypeidxBlock {
        let (tag, body) = m;
        SpecTypeidxBlock { tag, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TypeidxBlock {
    pub tag: u8,
    pub body: u64,
}

impl View for TypeidxBlock {
    type V = SpecTypeidxBlock;

    open spec fn view(&self) -> Self::V {
        SpecTypeidxBlock {
            tag: self.tag@,
            body: self.body@,
        }
    }
}
pub type TypeidxBlockInner = (u8, u64);

pub type TypeidxBlockInnerRef<'a> = (&'a u8, &'a u64);
impl<'a> From<&'a TypeidxBlock> for TypeidxBlockInnerRef<'a> {
    fn ex_from(m: &'a TypeidxBlock) -> TypeidxBlockInnerRef<'a> {
        (&m.tag, &m.body)
    }
}

impl From<TypeidxBlockInner> for TypeidxBlock {
    fn ex_from(m: TypeidxBlockInner) -> TypeidxBlock {
        let (tag, body) = m;
        TypeidxBlock { tag, body }
    }
}

pub struct TypeidxBlockMapper;
impl View for TypeidxBlockMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypeidxBlockMapper {
    type Src = SpecTypeidxBlockInner;
    type Dst = SpecTypeidxBlock;
}
impl SpecIsoProof for TypeidxBlockMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TypeidxBlockMapper {
    type Src = TypeidxBlockInner;
    type Dst = TypeidxBlock;
    type RefSrc = TypeidxBlockInnerRef<'a>;
}

pub struct SpecTypeidxBlockCombinator(SpecTypeidxBlockCombinatorAlias);

impl SpecCombinator for SpecTypeidxBlockCombinator {
    type Type = SpecTypeidxBlock;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypeidxBlockCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypeidxBlockCombinatorAlias::is_prefix_secure() }
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
pub type SpecTypeidxBlockCombinatorAlias = Mapped<(Refined<U8, Predicate2396169508742552609>, UnsignedLEB128), TypeidxBlockMapper>;
pub struct Predicate2396169508742552609;
impl View for Predicate2396169508742552609 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2396169508742552609 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        !((i == 64) || (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112))
    }
}
impl SpecPred<u8> for Predicate2396169508742552609 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        !((i == 64) || (i == 123) || (i == 124) || (i == 125) || (i == 126) || (i == 127) || (i == 111) || (i == 112))
    }
}

pub struct TypeidxBlockCombinator(TypeidxBlockCombinatorAlias);

impl View for TypeidxBlockCombinator {
    type V = SpecTypeidxBlockCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypeidxBlockCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TypeidxBlockCombinator {
    type Type = TypeidxBlock;
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
pub type TypeidxBlockCombinatorAlias = Mapped<(Refined<U8, Predicate2396169508742552609>, UnsignedLEB128), TypeidxBlockMapper>;


pub closed spec fn spec_typeidx_block() -> SpecTypeidxBlockCombinator {
    SpecTypeidxBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate2396169508742552609 }, UnsignedLEB128),
        mapper: TypeidxBlockMapper,
    })
}

                
pub fn typeidx_block() -> (o: TypeidxBlockCombinator)
    ensures o@ == spec_typeidx_block(),
{
    TypeidxBlockCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate2396169508742552609 }, UnsignedLEB128),
        mapper: TypeidxBlockMapper,
    })
}

                

pub enum SpecBlocktype {
    Empty(SpecEmptyBlock),
    ValType(SpecValtypeBlock),
    TypeIdx(SpecTypeidxBlock),
}

pub type SpecBlocktypeInner = Either<SpecEmptyBlock, Either<SpecValtypeBlock, SpecTypeidxBlock>>;

impl SpecFrom<SpecBlocktype> for SpecBlocktypeInner {
    open spec fn spec_from(m: SpecBlocktype) -> SpecBlocktypeInner {
        match m {
            SpecBlocktype::Empty(m) => Either::Left(m),
            SpecBlocktype::ValType(m) => Either::Right(Either::Left(m)),
            SpecBlocktype::TypeIdx(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecBlocktypeInner> for SpecBlocktype {
    open spec fn spec_from(m: SpecBlocktypeInner) -> SpecBlocktype {
        match m {
            Either::Left(m) => SpecBlocktype::Empty(m),
            Either::Right(Either::Left(m)) => SpecBlocktype::ValType(m),
            Either::Right(Either::Right(m)) => SpecBlocktype::TypeIdx(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Blocktype<'a> {
    Empty(EmptyBlock<'a>),
    ValType(ValtypeBlock<'a>),
    TypeIdx(TypeidxBlock),
}

pub type BlocktypeInner<'a> = Either<EmptyBlock<'a>, Either<ValtypeBlock<'a>, TypeidxBlock>>;

pub type BlocktypeInnerRef<'a> = Either<&'a EmptyBlock<'a>, Either<&'a ValtypeBlock<'a>, &'a TypeidxBlock>>;


impl<'a> View for Blocktype<'a> {
    type V = SpecBlocktype;
    open spec fn view(&self) -> Self::V {
        match self {
            Blocktype::Empty(m) => SpecBlocktype::Empty(m@),
            Blocktype::ValType(m) => SpecBlocktype::ValType(m@),
            Blocktype::TypeIdx(m) => SpecBlocktype::TypeIdx(m@),
        }
    }
}


impl<'a> From<&'a Blocktype<'a>> for BlocktypeInnerRef<'a> {
    fn ex_from(m: &'a Blocktype<'a>) -> BlocktypeInnerRef<'a> {
        match m {
            Blocktype::Empty(m) => Either::Left(m),
            Blocktype::ValType(m) => Either::Right(Either::Left(m)),
            Blocktype::TypeIdx(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<BlocktypeInner<'a>> for Blocktype<'a> {
    fn ex_from(m: BlocktypeInner<'a>) -> Blocktype<'a> {
        match m {
            Either::Left(m) => Blocktype::Empty(m),
            Either::Right(Either::Left(m)) => Blocktype::ValType(m),
            Either::Right(Either::Right(m)) => Blocktype::TypeIdx(m),
        }
    }
    
}


pub struct BlocktypeMapper;
impl View for BlocktypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for BlocktypeMapper {
    type Src = SpecBlocktypeInner;
    type Dst = SpecBlocktype;
}
impl SpecIsoProof for BlocktypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for BlocktypeMapper {
    type Src = BlocktypeInner<'a>;
    type Dst = Blocktype<'a>;
    type RefSrc = BlocktypeInnerRef<'a>;
}


impl DisjointFrom<SpecEmptyBlockCombinator> for SpecValtypeBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecEmptyBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecEmptyBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecEmptyBlockCombinator> for SpecTypeidxBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecEmptyBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecEmptyBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}

impl DisjointFrom<SpecValtypeBlockCombinator> for SpecTypeidxBlockCombinator {
    closed spec fn disjoint_from(&self, other: &SpecValtypeBlockCombinator) -> bool
    { self.0.disjoint_from(&other.0) }
    proof fn parse_disjoint_on(&self, other: &SpecValtypeBlockCombinator, buf: Seq<u8>) 
    { self.0.parse_disjoint_on(&other.0, buf); }
}
pub struct SpecBlocktypeCombinator(SpecBlocktypeCombinatorAlias);

impl SpecCombinator for SpecBlocktypeCombinator {
    type Type = SpecBlocktype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecBlocktypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecBlocktypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecBlocktypeCombinatorAlias = Mapped<Choice<SpecEmptyBlockCombinator, Choice<SpecValtypeBlockCombinator, SpecTypeidxBlockCombinator>>, BlocktypeMapper>;

pub struct BlocktypeCombinator(BlocktypeCombinatorAlias);

impl View for BlocktypeCombinator {
    type V = SpecBlocktypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecBlocktypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for BlocktypeCombinator {
    type Type = Blocktype<'a>;
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
pub type BlocktypeCombinatorAlias = Mapped<Choice<EmptyBlockCombinator, Choice<ValtypeBlockCombinator, TypeidxBlockCombinator>>, BlocktypeMapper>;


pub closed spec fn spec_blocktype() -> SpecBlocktypeCombinator {
    SpecBlocktypeCombinator(Mapped { inner: Choice(spec_empty_block(), Choice(spec_valtype_block(), spec_typeidx_block())), mapper: BlocktypeMapper })
}

                
pub fn blocktype() -> (o: BlocktypeCombinator)
    ensures o@ == spec_blocktype(),
{
    BlocktypeCombinator(Mapped { inner: Choice::new(empty_block(), Choice::new(valtype_block(), typeidx_block())), mapper: BlocktypeMapper })
}

                

pub enum SpecInstrControl1 {
    If(SpecBlocktype),
    Block(SpecBlocktype),
    Loop(SpecBlocktype),
    Else(SpecEmpty),
    Unreachable(SpecEmpty),
    Nop(SpecEmpty),
}

pub type SpecInstrControl1Inner = Either<SpecBlocktype, Either<SpecBlocktype, Either<SpecBlocktype, Either<SpecEmpty, Either<SpecEmpty, SpecEmpty>>>>>;

impl SpecFrom<SpecInstrControl1> for SpecInstrControl1Inner {
    open spec fn spec_from(m: SpecInstrControl1) -> SpecInstrControl1Inner {
        match m {
            SpecInstrControl1::If(m) => Either::Left(m),
            SpecInstrControl1::Block(m) => Either::Right(Either::Left(m)),
            SpecInstrControl1::Loop(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrControl1::Else(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrControl1::Unreachable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrControl1::Nop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

                
impl SpecFrom<SpecInstrControl1Inner> for SpecInstrControl1 {
    open spec fn spec_from(m: SpecInstrControl1Inner) -> SpecInstrControl1 {
        match m {
            Either::Left(m) => SpecInstrControl1::If(m),
            Either::Right(Either::Left(m)) => SpecInstrControl1::Block(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrControl1::Loop(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrControl1::Else(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrControl1::Unreachable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => SpecInstrControl1::Nop(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrControl1<'a> {
    If(Blocktype<'a>),
    Block(Blocktype<'a>),
    Loop(Blocktype<'a>),
    Else(Empty<'a>),
    Unreachable(Empty<'a>),
    Nop(Empty<'a>),
}

pub type InstrControl1Inner<'a> = Either<Blocktype<'a>, Either<Blocktype<'a>, Either<Blocktype<'a>, Either<Empty<'a>, Either<Empty<'a>, Empty<'a>>>>>>;

pub type InstrControl1InnerRef<'a> = Either<&'a Blocktype<'a>, Either<&'a Blocktype<'a>, Either<&'a Blocktype<'a>, Either<&'a Empty<'a>, Either<&'a Empty<'a>, &'a Empty<'a>>>>>>;


impl<'a> View for InstrControl1<'a> {
    type V = SpecInstrControl1;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrControl1::If(m) => SpecInstrControl1::If(m@),
            InstrControl1::Block(m) => SpecInstrControl1::Block(m@),
            InstrControl1::Loop(m) => SpecInstrControl1::Loop(m@),
            InstrControl1::Else(m) => SpecInstrControl1::Else(m@),
            InstrControl1::Unreachable(m) => SpecInstrControl1::Unreachable(m@),
            InstrControl1::Nop(m) => SpecInstrControl1::Nop(m@),
        }
    }
}


impl<'a> From<&'a InstrControl1<'a>> for InstrControl1InnerRef<'a> {
    fn ex_from(m: &'a InstrControl1<'a>) -> InstrControl1InnerRef<'a> {
        match m {
            InstrControl1::If(m) => Either::Left(m),
            InstrControl1::Block(m) => Either::Right(Either::Left(m)),
            InstrControl1::Loop(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrControl1::Else(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrControl1::Unreachable(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrControl1::Nop(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))),
        }
    }

}

impl<'a> From<InstrControl1Inner<'a>> for InstrControl1<'a> {
    fn ex_from(m: InstrControl1Inner<'a>) -> InstrControl1<'a> {
        match m {
            Either::Left(m) => InstrControl1::If(m),
            Either::Right(Either::Left(m)) => InstrControl1::Block(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrControl1::Loop(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrControl1::Else(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrControl1::Unreachable(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))) => InstrControl1::Nop(m),
        }
    }
    
}


pub struct InstrControl1Mapper;
impl View for InstrControl1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrControl1Mapper {
    type Src = SpecInstrControl1Inner;
    type Dst = SpecInstrControl1;
}
impl SpecIsoProof for InstrControl1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrControl1Mapper {
    type Src = InstrControl1Inner<'a>;
    type Dst = InstrControl1<'a>;
    type RefSrc = InstrControl1InnerRef<'a>;
}


pub struct SpecInstrControl1Combinator(SpecInstrControl1CombinatorAlias);

impl SpecCombinator for SpecInstrControl1Combinator {
    type Type = SpecInstrControl1;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrControl1Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrControl1CombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrControl1CombinatorAlias = Mapped<Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecBlocktypeCombinator>, Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Cond<SpecEmptyCombinator>>>>>>, InstrControl1Mapper>;

pub struct InstrControl1Combinator(InstrControl1CombinatorAlias);

impl View for InstrControl1Combinator {
    type V = SpecInstrControl1Combinator;
    closed spec fn view(&self) -> Self::V { SpecInstrControl1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrControl1Combinator {
    type Type = InstrControl1<'a>;
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
pub type InstrControl1CombinatorAlias = Mapped<Choice<Cond<BlocktypeCombinator>, Choice<Cond<BlocktypeCombinator>, Choice<Cond<BlocktypeCombinator>, Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Cond<EmptyCombinator>>>>>>, InstrControl1Mapper>;


pub closed spec fn spec_instr_control1(opcode: SpecInstrBytecode) -> SpecInstrControl1Combinator {
    SpecInstrControl1Combinator(Mapped { inner: Choice(Cond { cond: opcode == 4, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 2, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 3, inner: spec_blocktype() }, Choice(Cond { cond: opcode == 5, inner: spec_empty() }, Choice(Cond { cond: opcode == 0, inner: spec_empty() }, Cond { cond: opcode == 1, inner: spec_empty() }))))), mapper: InstrControl1Mapper })
}

pub fn instr_control1<'a>(opcode: InstrBytecode) -> (o: InstrControl1Combinator)
    ensures o@ == spec_instr_control1(opcode@),
{
    InstrControl1Combinator(Mapped { inner: Choice::new(Cond { cond: opcode == 4, inner: blocktype() }, Choice::new(Cond { cond: opcode == 2, inner: blocktype() }, Choice::new(Cond { cond: opcode == 3, inner: blocktype() }, Choice::new(Cond { cond: opcode == 5, inner: empty() }, Choice::new(Cond { cond: opcode == 0, inner: empty() }, Cond { cond: opcode == 1, inner: empty() }))))), mapper: InstrControl1Mapper })
}


pub struct SpecMemarg {
    pub align: u64,
    pub offset: u64,
}

pub type SpecMemargInner = (u64, u64);


impl SpecFrom<SpecMemarg> for SpecMemargInner {
    open spec fn spec_from(m: SpecMemarg) -> SpecMemargInner {
        (m.align, m.offset)
    }
}

impl SpecFrom<SpecMemargInner> for SpecMemarg {
    open spec fn spec_from(m: SpecMemargInner) -> SpecMemarg {
        let (align, offset) = m;
        SpecMemarg { align, offset }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Memarg {
    pub align: u64,
    pub offset: u64,
}

impl View for Memarg {
    type V = SpecMemarg;

    open spec fn view(&self) -> Self::V {
        SpecMemarg {
            align: self.align@,
            offset: self.offset@,
        }
    }
}
pub type MemargInner = (u64, u64);

pub type MemargInnerRef<'a> = (&'a u64, &'a u64);
impl<'a> From<&'a Memarg> for MemargInnerRef<'a> {
    fn ex_from(m: &'a Memarg) -> MemargInnerRef<'a> {
        (&m.align, &m.offset)
    }
}

impl From<MemargInner> for Memarg {
    fn ex_from(m: MemargInner) -> Memarg {
        let (align, offset) = m;
        Memarg { align, offset }
    }
}

pub struct MemargMapper;
impl View for MemargMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemargMapper {
    type Src = SpecMemargInner;
    type Dst = SpecMemarg;
}
impl SpecIsoProof for MemargMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemargMapper {
    type Src = MemargInner;
    type Dst = Memarg;
    type RefSrc = MemargInnerRef<'a>;
}

pub struct SpecMemargCombinator(SpecMemargCombinatorAlias);

impl SpecCombinator for SpecMemargCombinator {
    type Type = SpecMemarg;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemargCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemargCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemargCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), MemargMapper>;

pub struct MemargCombinator(MemargCombinatorAlias);

impl View for MemargCombinator {
    type V = SpecMemargCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemargCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemargCombinator {
    type Type = Memarg;
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
pub type MemargCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), MemargMapper>;


pub closed spec fn spec_memarg() -> SpecMemargCombinator {
    SpecMemargCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: MemargMapper,
    })
}

                
pub fn memarg() -> (o: MemargCombinator)
    ensures o@ == spec_memarg(),
{
    MemargCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: MemargMapper,
    })
}

                

pub struct SpecByteZero {
    pub zero: u8,
}

pub type SpecByteZeroInner = u8;


impl SpecFrom<SpecByteZero> for SpecByteZeroInner {
    open spec fn spec_from(m: SpecByteZero) -> SpecByteZeroInner {
        m.zero
    }
}

impl SpecFrom<SpecByteZeroInner> for SpecByteZero {
    open spec fn spec_from(m: SpecByteZeroInner) -> SpecByteZero {
        let zero = m;
        SpecByteZero { zero }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ByteZero {
    pub zero: u8,
}

impl View for ByteZero {
    type V = SpecByteZero;

    open spec fn view(&self) -> Self::V {
        SpecByteZero {
            zero: self.zero@,
        }
    }
}
pub type ByteZeroInner = u8;

pub type ByteZeroInnerRef<'a> = &'a u8;
impl<'a> From<&'a ByteZero> for ByteZeroInnerRef<'a> {
    fn ex_from(m: &'a ByteZero) -> ByteZeroInnerRef<'a> {
        &m.zero
    }
}

impl From<ByteZeroInner> for ByteZero {
    fn ex_from(m: ByteZeroInner) -> ByteZero {
        let zero = m;
        ByteZero { zero }
    }
}

pub struct ByteZeroMapper;
impl View for ByteZeroMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ByteZeroMapper {
    type Src = SpecByteZeroInner;
    type Dst = SpecByteZero;
}
impl SpecIsoProof for ByteZeroMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ByteZeroMapper {
    type Src = ByteZeroInner;
    type Dst = ByteZero;
    type RefSrc = ByteZeroInnerRef<'a>;
}
pub const BYTEZEROZERO_CONST: u8 = 0;

pub struct SpecByteZeroCombinator(SpecByteZeroCombinatorAlias);

impl SpecCombinator for SpecByteZeroCombinator {
    type Type = SpecByteZero;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecByteZeroCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecByteZeroCombinatorAlias::is_prefix_secure() }
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
pub type SpecByteZeroCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ByteZeroMapper>;

pub struct ByteZeroCombinator(ByteZeroCombinatorAlias);

impl View for ByteZeroCombinator {
    type V = SpecByteZeroCombinator;
    closed spec fn view(&self) -> Self::V { SpecByteZeroCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ByteZeroCombinator {
    type Type = ByteZero;
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
pub type ByteZeroCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ByteZeroMapper>;


pub closed spec fn spec_byte_zero() -> SpecByteZeroCombinator {
    SpecByteZeroCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(BYTEZEROZERO_CONST) },
        mapper: ByteZeroMapper,
    })
}

                
pub fn byte_zero() -> (o: ByteZeroCombinator)
    ensures o@ == spec_byte_zero(),
{
    ByteZeroCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(BYTEZEROZERO_CONST) },
        mapper: ByteZeroMapper,
    })
}

                

pub enum SpecInstrMemory {
    I32Store(SpecMemarg),
    I32Load(SpecMemarg),
    I64Store(SpecMemarg),
    I64Load(SpecMemarg),
    MemorySize(SpecByteZero),
    MemoryGrow(SpecByteZero),
    Unrecognized(SpecMemarg),
}

pub type SpecInstrMemoryInner = Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecByteZero, Either<SpecByteZero, SpecMemarg>>>>>>;

impl SpecFrom<SpecInstrMemory> for SpecInstrMemoryInner {
    open spec fn spec_from(m: SpecInstrMemory) -> SpecInstrMemoryInner {
        match m {
            SpecInstrMemory::I32Store(m) => Either::Left(m),
            SpecInstrMemory::I32Load(m) => Either::Right(Either::Left(m)),
            SpecInstrMemory::I64Store(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrMemory::I64Load(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrMemory::MemorySize(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrMemory::MemoryGrow(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrMemory::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

                
impl SpecFrom<SpecInstrMemoryInner> for SpecInstrMemory {
    open spec fn spec_from(m: SpecInstrMemoryInner) -> SpecInstrMemory {
        match m {
            Either::Left(m) => SpecInstrMemory::I32Store(m),
            Either::Right(Either::Left(m)) => SpecInstrMemory::I32Load(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrMemory::I64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrMemory::I64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrMemory::MemorySize(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrMemory::MemoryGrow(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => SpecInstrMemory::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrMemory {
    I32Store(Memarg),
    I32Load(Memarg),
    I64Store(Memarg),
    I64Load(Memarg),
    MemorySize(ByteZero),
    MemoryGrow(ByteZero),
    Unrecognized(Memarg),
}

pub type InstrMemoryInner = Either<Memarg, Either<Memarg, Either<Memarg, Either<Memarg, Either<ByteZero, Either<ByteZero, Memarg>>>>>>;

pub type InstrMemoryInnerRef<'a> = Either<&'a Memarg, Either<&'a Memarg, Either<&'a Memarg, Either<&'a Memarg, Either<&'a ByteZero, Either<&'a ByteZero, &'a Memarg>>>>>>;


impl View for InstrMemory {
    type V = SpecInstrMemory;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrMemory::I32Store(m) => SpecInstrMemory::I32Store(m@),
            InstrMemory::I32Load(m) => SpecInstrMemory::I32Load(m@),
            InstrMemory::I64Store(m) => SpecInstrMemory::I64Store(m@),
            InstrMemory::I64Load(m) => SpecInstrMemory::I64Load(m@),
            InstrMemory::MemorySize(m) => SpecInstrMemory::MemorySize(m@),
            InstrMemory::MemoryGrow(m) => SpecInstrMemory::MemoryGrow(m@),
            InstrMemory::Unrecognized(m) => SpecInstrMemory::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a InstrMemory> for InstrMemoryInnerRef<'a> {
    fn ex_from(m: &'a InstrMemory) -> InstrMemoryInnerRef<'a> {
        match m {
            InstrMemory::I32Store(m) => Either::Left(m),
            InstrMemory::I32Load(m) => Either::Right(Either::Left(m)),
            InstrMemory::I64Store(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrMemory::I64Load(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrMemory::MemorySize(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrMemory::MemoryGrow(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrMemory::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))),
        }
    }

}

impl From<InstrMemoryInner> for InstrMemory {
    fn ex_from(m: InstrMemoryInner) -> InstrMemory {
        match m {
            Either::Left(m) => InstrMemory::I32Store(m),
            Either::Right(Either::Left(m)) => InstrMemory::I32Load(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrMemory::I64Store(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrMemory::I64Load(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrMemory::MemorySize(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrMemory::MemoryGrow(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))) => InstrMemory::Unrecognized(m),
        }
    }
    
}


pub struct InstrMemoryMapper;
impl View for InstrMemoryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrMemoryMapper {
    type Src = SpecInstrMemoryInner;
    type Dst = SpecInstrMemory;
}
impl SpecIsoProof for InstrMemoryMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrMemoryMapper {
    type Src = InstrMemoryInner;
    type Dst = InstrMemory;
    type RefSrc = InstrMemoryInnerRef<'a>;
}


pub struct SpecInstrMemoryCombinator(SpecInstrMemoryCombinatorAlias);

impl SpecCombinator for SpecInstrMemoryCombinator {
    type Type = SpecInstrMemory;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrMemoryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrMemoryCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrMemoryCombinatorAlias = Mapped<Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecByteZeroCombinator>, Choice<Cond<SpecByteZeroCombinator>, Cond<SpecMemargCombinator>>>>>>>, InstrMemoryMapper>;

pub struct InstrMemoryCombinator(InstrMemoryCombinatorAlias);

impl View for InstrMemoryCombinator {
    type V = SpecInstrMemoryCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrMemoryCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrMemoryCombinator {
    type Type = InstrMemory;
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
pub type InstrMemoryCombinatorAlias = Mapped<Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<ByteZeroCombinator>, Choice<Cond<ByteZeroCombinator>, Cond<MemargCombinator>>>>>>>, InstrMemoryMapper>;


pub closed spec fn spec_instr_memory(opcode: SpecInstrBytecode) -> SpecInstrMemoryCombinator {
    SpecInstrMemoryCombinator(Mapped { inner: Choice(Cond { cond: opcode == 54, inner: spec_memarg() }, Choice(Cond { cond: opcode == 40, inner: spec_memarg() }, Choice(Cond { cond: opcode == 55, inner: spec_memarg() }, Choice(Cond { cond: opcode == 41, inner: spec_memarg() }, Choice(Cond { cond: opcode == 63, inner: spec_byte_zero() }, Choice(Cond { cond: opcode == 64, inner: spec_byte_zero() }, Cond { cond: !(opcode == 54 || opcode == 40 || opcode == 55 || opcode == 41 || opcode == 63 || opcode == 64), inner: spec_memarg() })))))), mapper: InstrMemoryMapper })
}

pub fn instr_memory<'a>(opcode: InstrBytecode) -> (o: InstrMemoryCombinator)
    ensures o@ == spec_instr_memory(opcode@),
{
    InstrMemoryCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 54, inner: memarg() }, Choice::new(Cond { cond: opcode == 40, inner: memarg() }, Choice::new(Cond { cond: opcode == 55, inner: memarg() }, Choice::new(Cond { cond: opcode == 41, inner: memarg() }, Choice::new(Cond { cond: opcode == 63, inner: byte_zero() }, Choice::new(Cond { cond: opcode == 64, inner: byte_zero() }, Cond { cond: !(opcode == 54 || opcode == 40 || opcode == 55 || opcode == 41 || opcode == 63 || opcode == 64), inner: memarg() })))))), mapper: InstrMemoryMapper })
}


pub enum SpecInstrReference {
    RefNull(SpecReftype),
    RefIsNull(SpecEmpty),
    RefFunc(SpecFuncidx),
}

pub type SpecInstrReferenceInner = Either<SpecReftype, Either<SpecEmpty, SpecFuncidx>>;

impl SpecFrom<SpecInstrReference> for SpecInstrReferenceInner {
    open spec fn spec_from(m: SpecInstrReference) -> SpecInstrReferenceInner {
        match m {
            SpecInstrReference::RefNull(m) => Either::Left(m),
            SpecInstrReference::RefIsNull(m) => Either::Right(Either::Left(m)),
            SpecInstrReference::RefFunc(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecInstrReferenceInner> for SpecInstrReference {
    open spec fn spec_from(m: SpecInstrReferenceInner) -> SpecInstrReference {
        match m {
            Either::Left(m) => SpecInstrReference::RefNull(m),
            Either::Right(Either::Left(m)) => SpecInstrReference::RefIsNull(m),
            Either::Right(Either::Right(m)) => SpecInstrReference::RefFunc(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrReference<'a> {
    RefNull(Reftype),
    RefIsNull(Empty<'a>),
    RefFunc(Funcidx),
}

pub type InstrReferenceInner<'a> = Either<Reftype, Either<Empty<'a>, Funcidx>>;

pub type InstrReferenceInnerRef<'a> = Either<&'a Reftype, Either<&'a Empty<'a>, &'a Funcidx>>;


impl<'a> View for InstrReference<'a> {
    type V = SpecInstrReference;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrReference::RefNull(m) => SpecInstrReference::RefNull(m@),
            InstrReference::RefIsNull(m) => SpecInstrReference::RefIsNull(m@),
            InstrReference::RefFunc(m) => SpecInstrReference::RefFunc(m@),
        }
    }
}


impl<'a> From<&'a InstrReference<'a>> for InstrReferenceInnerRef<'a> {
    fn ex_from(m: &'a InstrReference<'a>) -> InstrReferenceInnerRef<'a> {
        match m {
            InstrReference::RefNull(m) => Either::Left(m),
            InstrReference::RefIsNull(m) => Either::Right(Either::Left(m)),
            InstrReference::RefFunc(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<InstrReferenceInner<'a>> for InstrReference<'a> {
    fn ex_from(m: InstrReferenceInner<'a>) -> InstrReference<'a> {
        match m {
            Either::Left(m) => InstrReference::RefNull(m),
            Either::Right(Either::Left(m)) => InstrReference::RefIsNull(m),
            Either::Right(Either::Right(m)) => InstrReference::RefFunc(m),
        }
    }
    
}


pub struct InstrReferenceMapper;
impl View for InstrReferenceMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrReferenceMapper {
    type Src = SpecInstrReferenceInner;
    type Dst = SpecInstrReference;
}
impl SpecIsoProof for InstrReferenceMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrReferenceMapper {
    type Src = InstrReferenceInner<'a>;
    type Dst = InstrReference<'a>;
    type RefSrc = InstrReferenceInnerRef<'a>;
}


pub struct SpecInstrReferenceCombinator(SpecInstrReferenceCombinatorAlias);

impl SpecCombinator for SpecInstrReferenceCombinator {
    type Type = SpecInstrReference;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrReferenceCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrReferenceCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrReferenceCombinatorAlias = Mapped<Choice<Cond<SpecReftypeCombinator>, Choice<Cond<SpecEmptyCombinator>, Cond<SpecFuncidxCombinator>>>, InstrReferenceMapper>;

pub struct InstrReferenceCombinator(InstrReferenceCombinatorAlias);

impl View for InstrReferenceCombinator {
    type V = SpecInstrReferenceCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrReferenceCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrReferenceCombinator {
    type Type = InstrReference<'a>;
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
pub type InstrReferenceCombinatorAlias = Mapped<Choice<Cond<ReftypeCombinator>, Choice<Cond<EmptyCombinator>, Cond<FuncidxCombinator>>>, InstrReferenceMapper>;


pub closed spec fn spec_instr_reference(opcode: SpecInstrBytecode) -> SpecInstrReferenceCombinator {
    SpecInstrReferenceCombinator(Mapped { inner: Choice(Cond { cond: opcode == 208, inner: spec_reftype() }, Choice(Cond { cond: opcode == 209, inner: spec_empty() }, Cond { cond: opcode == 210, inner: spec_funcidx() })), mapper: InstrReferenceMapper })
}

pub fn instr_reference<'a>(opcode: InstrBytecode) -> (o: InstrReferenceCombinator)
    ensures o@ == spec_instr_reference(opcode@),
{
    InstrReferenceCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 208, inner: reftype() }, Choice::new(Cond { cond: opcode == 209, inner: empty() }, Cond { cond: opcode == 210, inner: funcidx() })), mapper: InstrReferenceMapper })
}


pub struct SpecSelectT {
    pub l: u64,
    pub v: Seq<SpecValtype>,
}

pub type SpecSelectTInner = (u64, Seq<SpecValtype>);


impl SpecFrom<SpecSelectT> for SpecSelectTInner {
    open spec fn spec_from(m: SpecSelectT) -> SpecSelectTInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecSelectTInner> for SpecSelectT {
    open spec fn spec_from(m: SpecSelectTInner) -> SpecSelectT {
        let (l, v) = m;
        SpecSelectT { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct SelectT {
    pub l: u64,
    pub v: RepeatResult<Valtype>,
}

impl View for SelectT {
    type V = SpecSelectT;

    open spec fn view(&self) -> Self::V {
        SpecSelectT {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type SelectTInner = (u64, RepeatResult<Valtype>);

pub type SelectTInnerRef<'a> = (&'a u64, &'a RepeatResult<Valtype>);
impl<'a> From<&'a SelectT> for SelectTInnerRef<'a> {
    fn ex_from(m: &'a SelectT) -> SelectTInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<SelectTInner> for SelectT {
    fn ex_from(m: SelectTInner) -> SelectT {
        let (l, v) = m;
        SelectT { l, v }
    }
}

pub struct SelectTMapper;
impl View for SelectTMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SelectTMapper {
    type Src = SpecSelectTInner;
    type Dst = SpecSelectT;
}
impl SpecIsoProof for SelectTMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for SelectTMapper {
    type Src = SelectTInner;
    type Dst = SelectT;
    type RefSrc = SelectTInnerRef<'a>;
}

pub struct SpecSelectTCombinator(SpecSelectTCombinatorAlias);

impl SpecCombinator for SpecSelectTCombinator {
    type Type = SpecSelectT;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSelectTCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSelectTCombinatorAlias::is_prefix_secure() }
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
pub type SpecSelectTCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecValtypeCombinator>>, SelectTMapper>;

pub struct SelectTCombinator(SelectTCombinatorAlias);

impl View for SelectTCombinator {
    type V = SpecSelectTCombinator;
    closed spec fn view(&self) -> Self::V { SpecSelectTCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for SelectTCombinator {
    type Type = SelectT;
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
pub type SelectTCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ValtypeCombinator>, SelectTCont0>, SelectTMapper>;


pub closed spec fn spec_select_t() -> SpecSelectTCombinator {
    SpecSelectTCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_select_t_cont0(deps)),
        mapper: SelectTMapper,
    })
}

pub open spec fn spec_select_t_cont0(deps: u64) -> RepeatN<SpecValtypeCombinator> {
    let l = deps;
    RepeatN(spec_valtype(), l.spec_into())
}

impl View for SelectTCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecValtypeCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_select_t_cont0(deps)
        }
    }
}

                
pub fn select_t() -> (o: SelectTCombinator)
    ensures o@ == spec_select_t(),
{
    SelectTCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, SelectTCont0),
        mapper: SelectTMapper,
    })
}

pub struct SelectTCont0;
type SelectTCont0Type<'a, 'b> = &'b u64;
type SelectTCont0SType<'a, 'x> = &'x u64;
type SelectTCont0Input<'a, 'b, 'x> = POrSType<SelectTCont0Type<'a, 'b>, SelectTCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<SelectTCont0Input<'a, 'b, 'x>> for SelectTCont0 {
    type Output = RepeatN<ValtypeCombinator>;

    open spec fn requires(&self, deps: SelectTCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: SelectTCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_select_t_cont0(deps@)
    }

    fn apply(&self, deps: SelectTCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(valtype(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(valtype(), l.ex_into())
            }
        }
    }
}
                

pub enum SpecInstrParametric {
    Drop(SpecEmpty),
    Select(SpecEmpty),
    SelectT(SpecSelectT),
}

pub type SpecInstrParametricInner = Either<SpecEmpty, Either<SpecEmpty, SpecSelectT>>;

impl SpecFrom<SpecInstrParametric> for SpecInstrParametricInner {
    open spec fn spec_from(m: SpecInstrParametric) -> SpecInstrParametricInner {
        match m {
            SpecInstrParametric::Drop(m) => Either::Left(m),
            SpecInstrParametric::Select(m) => Either::Right(Either::Left(m)),
            SpecInstrParametric::SelectT(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecInstrParametricInner> for SpecInstrParametric {
    open spec fn spec_from(m: SpecInstrParametricInner) -> SpecInstrParametric {
        match m {
            Either::Left(m) => SpecInstrParametric::Drop(m),
            Either::Right(Either::Left(m)) => SpecInstrParametric::Select(m),
            Either::Right(Either::Right(m)) => SpecInstrParametric::SelectT(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrParametric<'a> {
    Drop(Empty<'a>),
    Select(Empty<'a>),
    SelectT(SelectT),
}

pub type InstrParametricInner<'a> = Either<Empty<'a>, Either<Empty<'a>, SelectT>>;

pub type InstrParametricInnerRef<'a> = Either<&'a Empty<'a>, Either<&'a Empty<'a>, &'a SelectT>>;


impl<'a> View for InstrParametric<'a> {
    type V = SpecInstrParametric;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrParametric::Drop(m) => SpecInstrParametric::Drop(m@),
            InstrParametric::Select(m) => SpecInstrParametric::Select(m@),
            InstrParametric::SelectT(m) => SpecInstrParametric::SelectT(m@),
        }
    }
}


impl<'a> From<&'a InstrParametric<'a>> for InstrParametricInnerRef<'a> {
    fn ex_from(m: &'a InstrParametric<'a>) -> InstrParametricInnerRef<'a> {
        match m {
            InstrParametric::Drop(m) => Either::Left(m),
            InstrParametric::Select(m) => Either::Right(Either::Left(m)),
            InstrParametric::SelectT(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<InstrParametricInner<'a>> for InstrParametric<'a> {
    fn ex_from(m: InstrParametricInner<'a>) -> InstrParametric<'a> {
        match m {
            Either::Left(m) => InstrParametric::Drop(m),
            Either::Right(Either::Left(m)) => InstrParametric::Select(m),
            Either::Right(Either::Right(m)) => InstrParametric::SelectT(m),
        }
    }
    
}


pub struct InstrParametricMapper;
impl View for InstrParametricMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrParametricMapper {
    type Src = SpecInstrParametricInner;
    type Dst = SpecInstrParametric;
}
impl SpecIsoProof for InstrParametricMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrParametricMapper {
    type Src = InstrParametricInner<'a>;
    type Dst = InstrParametric<'a>;
    type RefSrc = InstrParametricInnerRef<'a>;
}


pub struct SpecInstrParametricCombinator(SpecInstrParametricCombinatorAlias);

impl SpecCombinator for SpecInstrParametricCombinator {
    type Type = SpecInstrParametric;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrParametricCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrParametricCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrParametricCombinatorAlias = Mapped<Choice<Cond<SpecEmptyCombinator>, Choice<Cond<SpecEmptyCombinator>, Cond<SpecSelectTCombinator>>>, InstrParametricMapper>;

pub struct InstrParametricCombinator(InstrParametricCombinatorAlias);

impl View for InstrParametricCombinator {
    type V = SpecInstrParametricCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrParametricCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrParametricCombinator {
    type Type = InstrParametric<'a>;
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
pub type InstrParametricCombinatorAlias = Mapped<Choice<Cond<EmptyCombinator>, Choice<Cond<EmptyCombinator>, Cond<SelectTCombinator>>>, InstrParametricMapper>;


pub closed spec fn spec_instr_parametric(opcode: SpecInstrBytecode) -> SpecInstrParametricCombinator {
    SpecInstrParametricCombinator(Mapped { inner: Choice(Cond { cond: opcode == 26, inner: spec_empty() }, Choice(Cond { cond: opcode == 27, inner: spec_empty() }, Cond { cond: opcode == 28, inner: spec_select_t() })), mapper: InstrParametricMapper })
}

pub fn instr_parametric<'a>(opcode: InstrBytecode) -> (o: InstrParametricCombinator)
    ensures o@ == spec_instr_parametric(opcode@),
{
    InstrParametricCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 26, inner: empty() }, Choice::new(Cond { cond: opcode == 27, inner: empty() }, Cond { cond: opcode == 28, inner: select_t() })), mapper: InstrParametricMapper })
}


pub enum SpecInstrTable {
    TableGet(SpecTableidx),
    TableSet(SpecTableidx),
}

pub type SpecInstrTableInner = Either<SpecTableidx, SpecTableidx>;

impl SpecFrom<SpecInstrTable> for SpecInstrTableInner {
    open spec fn spec_from(m: SpecInstrTable) -> SpecInstrTableInner {
        match m {
            SpecInstrTable::TableGet(m) => Either::Left(m),
            SpecInstrTable::TableSet(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecInstrTableInner> for SpecInstrTable {
    open spec fn spec_from(m: SpecInstrTableInner) -> SpecInstrTable {
        match m {
            Either::Left(m) => SpecInstrTable::TableGet(m),
            Either::Right(m) => SpecInstrTable::TableSet(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrTable {
    TableGet(Tableidx),
    TableSet(Tableidx),
}

pub type InstrTableInner = Either<Tableidx, Tableidx>;

pub type InstrTableInnerRef<'a> = Either<&'a Tableidx, &'a Tableidx>;


impl View for InstrTable {
    type V = SpecInstrTable;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrTable::TableGet(m) => SpecInstrTable::TableGet(m@),
            InstrTable::TableSet(m) => SpecInstrTable::TableSet(m@),
        }
    }
}


impl<'a> From<&'a InstrTable> for InstrTableInnerRef<'a> {
    fn ex_from(m: &'a InstrTable) -> InstrTableInnerRef<'a> {
        match m {
            InstrTable::TableGet(m) => Either::Left(m),
            InstrTable::TableSet(m) => Either::Right(m),
        }
    }

}

impl From<InstrTableInner> for InstrTable {
    fn ex_from(m: InstrTableInner) -> InstrTable {
        match m {
            Either::Left(m) => InstrTable::TableGet(m),
            Either::Right(m) => InstrTable::TableSet(m),
        }
    }
    
}


pub struct InstrTableMapper;
impl View for InstrTableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrTableMapper {
    type Src = SpecInstrTableInner;
    type Dst = SpecInstrTable;
}
impl SpecIsoProof for InstrTableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrTableMapper {
    type Src = InstrTableInner;
    type Dst = InstrTable;
    type RefSrc = InstrTableInnerRef<'a>;
}


pub struct SpecInstrTableCombinator(SpecInstrTableCombinatorAlias);

impl SpecCombinator for SpecInstrTableCombinator {
    type Type = SpecInstrTable;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrTableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrTableCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrTableCombinatorAlias = Mapped<Choice<Cond<SpecTableidxCombinator>, Cond<SpecTableidxCombinator>>, InstrTableMapper>;

pub struct InstrTableCombinator(InstrTableCombinatorAlias);

impl View for InstrTableCombinator {
    type V = SpecInstrTableCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrTableCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrTableCombinator {
    type Type = InstrTable;
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
pub type InstrTableCombinatorAlias = Mapped<Choice<Cond<TableidxCombinator>, Cond<TableidxCombinator>>, InstrTableMapper>;


pub closed spec fn spec_instr_table(opcode: SpecInstrBytecode) -> SpecInstrTableCombinator {
    SpecInstrTableCombinator(Mapped { inner: Choice(Cond { cond: opcode == 37, inner: spec_tableidx() }, Cond { cond: opcode == 38, inner: spec_tableidx() }), mapper: InstrTableMapper })
}

pub fn instr_table<'a>(opcode: InstrBytecode) -> (o: InstrTableCombinator)
    ensures o@ == spec_instr_table(opcode@),
{
    InstrTableCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 37, inner: tableidx() }, Cond { cond: opcode == 38, inner: tableidx() }), mapper: InstrTableMapper })
}

pub type SpecF32 = Seq<u8>;
pub type F32<'a> = &'a [u8];
pub type F32Ref<'a> = &'a &'a [u8];


pub struct SpecF32Combinator(SpecF32CombinatorAlias);

impl SpecCombinator for SpecF32Combinator {
    type Type = SpecF32;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecF32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecF32CombinatorAlias::is_prefix_secure() }
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
pub type SpecF32CombinatorAlias = bytes::Fixed<4>;

pub struct F32Combinator(F32CombinatorAlias);

impl View for F32Combinator {
    type V = SpecF32Combinator;
    closed spec fn view(&self) -> Self::V { SpecF32Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for F32Combinator {
    type Type = F32<'a>;
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
pub type F32CombinatorAlias = bytes::Fixed<4>;


pub closed spec fn spec_f32() -> SpecF32Combinator {
    SpecF32Combinator(bytes::Fixed::<4>)
}

                
pub fn f32() -> (o: F32Combinator)
    ensures o@ == spec_f32(),
{
    F32Combinator(bytes::Fixed::<4>)
}

                
pub type SpecF64 = Seq<u8>;
pub type F64<'a> = &'a [u8];
pub type F64Ref<'a> = &'a &'a [u8];


pub struct SpecF64Combinator(SpecF64CombinatorAlias);

impl SpecCombinator for SpecF64Combinator {
    type Type = SpecF64;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecF64Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecF64CombinatorAlias::is_prefix_secure() }
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
pub type SpecF64CombinatorAlias = bytes::Fixed<8>;

pub struct F64Combinator(F64CombinatorAlias);

impl View for F64Combinator {
    type V = SpecF64Combinator;
    closed spec fn view(&self) -> Self::V { SpecF64Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for F64Combinator {
    type Type = F64<'a>;
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
pub type F64CombinatorAlias = bytes::Fixed<8>;


pub closed spec fn spec_f64() -> SpecF64Combinator {
    SpecF64Combinator(bytes::Fixed::<8>)
}

                
pub fn f64() -> (o: F64Combinator)
    ensures o@ == spec_f64(),
{
    F64Combinator(bytes::Fixed::<8>)
}

                

pub enum SpecInstrNumeric {
    I32Const(u64),
    I64Const(u64),
    F32Const(SpecF32),
    F64Const(SpecF64),
    Unrecognized(SpecEmpty),
}

pub type SpecInstrNumericInner = Either<u64, Either<u64, Either<SpecF32, Either<SpecF64, SpecEmpty>>>>;

impl SpecFrom<SpecInstrNumeric> for SpecInstrNumericInner {
    open spec fn spec_from(m: SpecInstrNumeric) -> SpecInstrNumericInner {
        match m {
            SpecInstrNumeric::I32Const(m) => Either::Left(m),
            SpecInstrNumeric::I64Const(m) => Either::Right(Either::Left(m)),
            SpecInstrNumeric::F32Const(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrNumeric::F64Const(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrNumeric::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

                
impl SpecFrom<SpecInstrNumericInner> for SpecInstrNumeric {
    open spec fn spec_from(m: SpecInstrNumericInner) -> SpecInstrNumeric {
        match m {
            Either::Left(m) => SpecInstrNumeric::I32Const(m),
            Either::Right(Either::Left(m)) => SpecInstrNumeric::I64Const(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrNumeric::F32Const(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrNumeric::F64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => SpecInstrNumeric::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrNumeric<'a> {
    I32Const(u64),
    I64Const(u64),
    F32Const(F32<'a>),
    F64Const(F64<'a>),
    Unrecognized(Empty<'a>),
}

pub type InstrNumericInner<'a> = Either<u64, Either<u64, Either<F32<'a>, Either<F64<'a>, Empty<'a>>>>>;

pub type InstrNumericInnerRef<'a> = Either<&'a u64, Either<&'a u64, Either<&'a F32<'a>, Either<&'a F64<'a>, &'a Empty<'a>>>>>;


impl<'a> View for InstrNumeric<'a> {
    type V = SpecInstrNumeric;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrNumeric::I32Const(m) => SpecInstrNumeric::I32Const(m@),
            InstrNumeric::I64Const(m) => SpecInstrNumeric::I64Const(m@),
            InstrNumeric::F32Const(m) => SpecInstrNumeric::F32Const(m@),
            InstrNumeric::F64Const(m) => SpecInstrNumeric::F64Const(m@),
            InstrNumeric::Unrecognized(m) => SpecInstrNumeric::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a InstrNumeric<'a>> for InstrNumericInnerRef<'a> {
    fn ex_from(m: &'a InstrNumeric<'a>) -> InstrNumericInnerRef<'a> {
        match m {
            InstrNumeric::I32Const(m) => Either::Left(m),
            InstrNumeric::I64Const(m) => Either::Right(Either::Left(m)),
            InstrNumeric::F32Const(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrNumeric::F64Const(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrNumeric::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(m)))),
        }
    }

}

impl<'a> From<InstrNumericInner<'a>> for InstrNumeric<'a> {
    fn ex_from(m: InstrNumericInner<'a>) -> InstrNumeric<'a> {
        match m {
            Either::Left(m) => InstrNumeric::I32Const(m),
            Either::Right(Either::Left(m)) => InstrNumeric::I64Const(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrNumeric::F32Const(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrNumeric::F64Const(m),
            Either::Right(Either::Right(Either::Right(Either::Right(m)))) => InstrNumeric::Unrecognized(m),
        }
    }
    
}


pub struct InstrNumericMapper;
impl View for InstrNumericMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrNumericMapper {
    type Src = SpecInstrNumericInner;
    type Dst = SpecInstrNumeric;
}
impl SpecIsoProof for InstrNumericMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrNumericMapper {
    type Src = InstrNumericInner<'a>;
    type Dst = InstrNumeric<'a>;
    type RefSrc = InstrNumericInnerRef<'a>;
}


pub struct SpecInstrNumericCombinator(SpecInstrNumericCombinatorAlias);

impl SpecCombinator for SpecInstrNumericCombinator {
    type Type = SpecInstrNumeric;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrNumericCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrNumericCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrNumericCombinatorAlias = Mapped<Choice<Cond<UnsignedLEB128>, Choice<Cond<UnsignedLEB128>, Choice<Cond<SpecF32Combinator>, Choice<Cond<SpecF64Combinator>, Cond<SpecEmptyCombinator>>>>>, InstrNumericMapper>;

pub struct InstrNumericCombinator(InstrNumericCombinatorAlias);

impl View for InstrNumericCombinator {
    type V = SpecInstrNumericCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrNumericCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrNumericCombinator {
    type Type = InstrNumeric<'a>;
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
pub type InstrNumericCombinatorAlias = Mapped<Choice<Cond<UnsignedLEB128>, Choice<Cond<UnsignedLEB128>, Choice<Cond<F32Combinator>, Choice<Cond<F64Combinator>, Cond<EmptyCombinator>>>>>, InstrNumericMapper>;


pub closed spec fn spec_instr_numeric(opcode: SpecInstrBytecode) -> SpecInstrNumericCombinator {
    SpecInstrNumericCombinator(Mapped { inner: Choice(Cond { cond: opcode == 65, inner: UnsignedLEB128 }, Choice(Cond { cond: opcode == 66, inner: UnsignedLEB128 }, Choice(Cond { cond: opcode == 67, inner: spec_f32() }, Choice(Cond { cond: opcode == 68, inner: spec_f64() }, Cond { cond: !(opcode == 65 || opcode == 66 || opcode == 67 || opcode == 68), inner: spec_empty() })))), mapper: InstrNumericMapper })
}

pub fn instr_numeric<'a>(opcode: InstrBytecode) -> (o: InstrNumericCombinator)
    ensures o@ == spec_instr_numeric(opcode@),
{
    InstrNumericCombinator(Mapped { inner: Choice::new(Cond { cond: opcode == 65, inner: UnsignedLEB128 }, Choice::new(Cond { cond: opcode == 66, inner: UnsignedLEB128 }, Choice::new(Cond { cond: opcode == 67, inner: f32() }, Choice::new(Cond { cond: opcode == 68, inner: f64() }, Cond { cond: !(opcode == 65 || opcode == 66 || opcode == 67 || opcode == 68), inner: empty() })))), mapper: InstrNumericMapper })
}

pub type SpecElemidx = u64;
pub type Elemidx = u64;
pub type ElemidxRef<'a> = &'a u64;


pub struct SpecElemidxCombinator(SpecElemidxCombinatorAlias);

impl SpecCombinator for SpecElemidxCombinator {
    type Type = SpecElemidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemidxCombinatorAlias = UnsignedLEB128;

pub struct ElemidxCombinator(ElemidxCombinatorAlias);

impl View for ElemidxCombinator {
    type V = SpecElemidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemidxCombinator {
    type Type = Elemidx;
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
pub type ElemidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_elemidx() -> SpecElemidxCombinator {
    SpecElemidxCombinator(UnsignedLEB128)
}

                
pub fn elemidx() -> (o: ElemidxCombinator)
    ensures o@ == spec_elemidx(),
{
    ElemidxCombinator(UnsignedLEB128)
}

                

pub struct SpecTableInit {
    pub y: SpecElemidx,
    pub x: SpecTableidx,
}

pub type SpecTableInitInner = (SpecElemidx, SpecTableidx);


impl SpecFrom<SpecTableInit> for SpecTableInitInner {
    open spec fn spec_from(m: SpecTableInit) -> SpecTableInitInner {
        (m.y, m.x)
    }
}

impl SpecFrom<SpecTableInitInner> for SpecTableInit {
    open spec fn spec_from(m: SpecTableInitInner) -> SpecTableInit {
        let (y, x) = m;
        SpecTableInit { y, x }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TableInit {
    pub y: Elemidx,
    pub x: Tableidx,
}

impl View for TableInit {
    type V = SpecTableInit;

    open spec fn view(&self) -> Self::V {
        SpecTableInit {
            y: self.y@,
            x: self.x@,
        }
    }
}
pub type TableInitInner = (Elemidx, Tableidx);

pub type TableInitInnerRef<'a> = (&'a Elemidx, &'a Tableidx);
impl<'a> From<&'a TableInit> for TableInitInnerRef<'a> {
    fn ex_from(m: &'a TableInit) -> TableInitInnerRef<'a> {
        (&m.y, &m.x)
    }
}

impl From<TableInitInner> for TableInit {
    fn ex_from(m: TableInitInner) -> TableInit {
        let (y, x) = m;
        TableInit { y, x }
    }
}

pub struct TableInitMapper;
impl View for TableInitMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableInitMapper {
    type Src = SpecTableInitInner;
    type Dst = SpecTableInit;
}
impl SpecIsoProof for TableInitMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TableInitMapper {
    type Src = TableInitInner;
    type Dst = TableInit;
    type RefSrc = TableInitInnerRef<'a>;
}

pub struct SpecTableInitCombinator(SpecTableInitCombinatorAlias);

impl SpecCombinator for SpecTableInitCombinator {
    type Type = SpecTableInit;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableInitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableInitCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableInitCombinatorAlias = Mapped<(SpecElemidxCombinator, SpecTableidxCombinator), TableInitMapper>;

pub struct TableInitCombinator(TableInitCombinatorAlias);

impl View for TableInitCombinator {
    type V = SpecTableInitCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableInitCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableInitCombinator {
    type Type = TableInit;
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
pub type TableInitCombinatorAlias = Mapped<(ElemidxCombinator, TableidxCombinator), TableInitMapper>;


pub closed spec fn spec_table_init() -> SpecTableInitCombinator {
    SpecTableInitCombinator(
    Mapped {
        inner: (spec_elemidx(), spec_tableidx()),
        mapper: TableInitMapper,
    })
}

                
pub fn table_init() -> (o: TableInitCombinator)
    ensures o@ == spec_table_init(),
{
    TableInitCombinator(
    Mapped {
        inner: (elemidx(), tableidx()),
        mapper: TableInitMapper,
    })
}

                
pub type SpecElemDrop = SpecElemidx;
pub type ElemDrop = Elemidx;
pub type ElemDropRef<'a> = &'a Elemidx;


pub struct SpecElemDropCombinator(SpecElemDropCombinatorAlias);

impl SpecCombinator for SpecElemDropCombinator {
    type Type = SpecElemDrop;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemDropCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemDropCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemDropCombinatorAlias = SpecElemidxCombinator;

pub struct ElemDropCombinator(ElemDropCombinatorAlias);

impl View for ElemDropCombinator {
    type V = SpecElemDropCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemDropCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemDropCombinator {
    type Type = ElemDrop;
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
pub type ElemDropCombinatorAlias = ElemidxCombinator;


pub closed spec fn spec_elem_drop() -> SpecElemDropCombinator {
    SpecElemDropCombinator(spec_elemidx())
}

                
pub fn elem_drop() -> (o: ElemDropCombinator)
    ensures o@ == spec_elem_drop(),
{
    ElemDropCombinator(elemidx())
}

                

pub struct SpecTableCopy {
    pub x: SpecTableidx,
    pub y: SpecTableidx,
}

pub type SpecTableCopyInner = (SpecTableidx, SpecTableidx);


impl SpecFrom<SpecTableCopy> for SpecTableCopyInner {
    open spec fn spec_from(m: SpecTableCopy) -> SpecTableCopyInner {
        (m.x, m.y)
    }
}

impl SpecFrom<SpecTableCopyInner> for SpecTableCopy {
    open spec fn spec_from(m: SpecTableCopyInner) -> SpecTableCopy {
        let (x, y) = m;
        SpecTableCopy { x, y }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TableCopy {
    pub x: Tableidx,
    pub y: Tableidx,
}

impl View for TableCopy {
    type V = SpecTableCopy;

    open spec fn view(&self) -> Self::V {
        SpecTableCopy {
            x: self.x@,
            y: self.y@,
        }
    }
}
pub type TableCopyInner = (Tableidx, Tableidx);

pub type TableCopyInnerRef<'a> = (&'a Tableidx, &'a Tableidx);
impl<'a> From<&'a TableCopy> for TableCopyInnerRef<'a> {
    fn ex_from(m: &'a TableCopy) -> TableCopyInnerRef<'a> {
        (&m.x, &m.y)
    }
}

impl From<TableCopyInner> for TableCopy {
    fn ex_from(m: TableCopyInner) -> TableCopy {
        let (x, y) = m;
        TableCopy { x, y }
    }
}

pub struct TableCopyMapper;
impl View for TableCopyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableCopyMapper {
    type Src = SpecTableCopyInner;
    type Dst = SpecTableCopy;
}
impl SpecIsoProof for TableCopyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TableCopyMapper {
    type Src = TableCopyInner;
    type Dst = TableCopy;
    type RefSrc = TableCopyInnerRef<'a>;
}

pub struct SpecTableCopyCombinator(SpecTableCopyCombinatorAlias);

impl SpecCombinator for SpecTableCopyCombinator {
    type Type = SpecTableCopy;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableCopyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableCopyCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableCopyCombinatorAlias = Mapped<(SpecTableidxCombinator, SpecTableidxCombinator), TableCopyMapper>;

pub struct TableCopyCombinator(TableCopyCombinatorAlias);

impl View for TableCopyCombinator {
    type V = SpecTableCopyCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableCopyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableCopyCombinator {
    type Type = TableCopy;
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
pub type TableCopyCombinatorAlias = Mapped<(TableidxCombinator, TableidxCombinator), TableCopyMapper>;


pub closed spec fn spec_table_copy() -> SpecTableCopyCombinator {
    SpecTableCopyCombinator(
    Mapped {
        inner: (spec_tableidx(), spec_tableidx()),
        mapper: TableCopyMapper,
    })
}

                
pub fn table_copy() -> (o: TableCopyCombinator)
    ensures o@ == spec_table_copy(),
{
    TableCopyCombinator(
    Mapped {
        inner: (tableidx(), tableidx()),
        mapper: TableCopyMapper,
    })
}

                
pub type SpecTableGrow = SpecTableidx;
pub type TableGrow = Tableidx;
pub type TableGrowRef<'a> = &'a Tableidx;


pub struct SpecTableGrowCombinator(SpecTableGrowCombinatorAlias);

impl SpecCombinator for SpecTableGrowCombinator {
    type Type = SpecTableGrow;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableGrowCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableGrowCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableGrowCombinatorAlias = SpecTableidxCombinator;

pub struct TableGrowCombinator(TableGrowCombinatorAlias);

impl View for TableGrowCombinator {
    type V = SpecTableGrowCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableGrowCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableGrowCombinator {
    type Type = TableGrow;
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
pub type TableGrowCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_grow() -> SpecTableGrowCombinator {
    SpecTableGrowCombinator(spec_tableidx())
}

                
pub fn table_grow() -> (o: TableGrowCombinator)
    ensures o@ == spec_table_grow(),
{
    TableGrowCombinator(tableidx())
}

                
pub type SpecTableSize = SpecTableidx;
pub type TableSize = Tableidx;
pub type TableSizeRef<'a> = &'a Tableidx;


pub struct SpecTableSizeCombinator(SpecTableSizeCombinatorAlias);

impl SpecCombinator for SpecTableSizeCombinator {
    type Type = SpecTableSize;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableSizeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableSizeCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableSizeCombinatorAlias = SpecTableidxCombinator;

pub struct TableSizeCombinator(TableSizeCombinatorAlias);

impl View for TableSizeCombinator {
    type V = SpecTableSizeCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableSizeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableSizeCombinator {
    type Type = TableSize;
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
pub type TableSizeCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_size() -> SpecTableSizeCombinator {
    SpecTableSizeCombinator(spec_tableidx())
}

                
pub fn table_size() -> (o: TableSizeCombinator)
    ensures o@ == spec_table_size(),
{
    TableSizeCombinator(tableidx())
}

                
pub type SpecTableFill = SpecTableidx;
pub type TableFill = Tableidx;
pub type TableFillRef<'a> = &'a Tableidx;


pub struct SpecTableFillCombinator(SpecTableFillCombinatorAlias);

impl SpecCombinator for SpecTableFillCombinator {
    type Type = SpecTableFill;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableFillCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableFillCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableFillCombinatorAlias = SpecTableidxCombinator;

pub struct TableFillCombinator(TableFillCombinatorAlias);

impl View for TableFillCombinator {
    type V = SpecTableFillCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableFillCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableFillCombinator {
    type Type = TableFill;
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
pub type TableFillCombinatorAlias = TableidxCombinator;


pub closed spec fn spec_table_fill() -> SpecTableFillCombinator {
    SpecTableFillCombinator(spec_tableidx())
}

                
pub fn table_fill() -> (o: TableFillCombinator)
    ensures o@ == spec_table_fill(),
{
    TableFillCombinator(tableidx())
}

                
pub type SpecDataidx = u64;
pub type Dataidx = u64;
pub type DataidxRef<'a> = &'a u64;


pub struct SpecDataidxCombinator(SpecDataidxCombinatorAlias);

impl SpecCombinator for SpecDataidxCombinator {
    type Type = SpecDataidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecDataidxCombinatorAlias = UnsignedLEB128;

pub struct DataidxCombinator(DataidxCombinatorAlias);

impl View for DataidxCombinator {
    type V = SpecDataidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DataidxCombinator {
    type Type = Dataidx;
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
pub type DataidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_dataidx() -> SpecDataidxCombinator {
    SpecDataidxCombinator(UnsignedLEB128)
}

                
pub fn dataidx() -> (o: DataidxCombinator)
    ensures o@ == spec_dataidx(),
{
    DataidxCombinator(UnsignedLEB128)
}

                
pub type SpecMemoryInit = SpecDataidx;
pub type MemoryInit = Dataidx;
pub type MemoryInitRef<'a> = &'a Dataidx;


pub const MemoryInit_0_BACK_CONST: u8 = 0;

pub struct SpecMemoryInitCombinator(SpecMemoryInitCombinatorAlias);

impl SpecCombinator for SpecMemoryInitCombinator {
    type Type = SpecMemoryInit;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryInitCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryInitCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemoryInitCombinatorAlias = Terminated<SpecDataidxCombinator, Tag<U8, u8>>;


pub struct MemoryInitCombinator(MemoryInitCombinatorAlias);

impl View for MemoryInitCombinator {
    type V = SpecMemoryInitCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryInitCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemoryInitCombinator {
    type Type = MemoryInit;
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
pub type MemoryInitCombinatorAlias = Terminated<DataidxCombinator, Tag<U8, u8>>;


pub closed spec fn spec_memory_init() -> SpecMemoryInitCombinator {
    SpecMemoryInitCombinator(Terminated(spec_dataidx(), Tag::spec_new(U8, MemoryInit_0_BACK_CONST)))
}

                
pub fn memory_init() -> (o: MemoryInitCombinator)
    ensures o@ == spec_memory_init(),
{
    MemoryInitCombinator(Terminated(dataidx(), Tag::new(U8, MemoryInit_0_BACK_CONST)))
}

                
pub type SpecDataDrop = SpecDataidx;
pub type DataDrop = Dataidx;
pub type DataDropRef<'a> = &'a Dataidx;


pub struct SpecDataDropCombinator(SpecDataDropCombinatorAlias);

impl SpecCombinator for SpecDataDropCombinator {
    type Type = SpecDataDrop;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataDropCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataDropCombinatorAlias::is_prefix_secure() }
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
pub type SpecDataDropCombinatorAlias = SpecDataidxCombinator;

pub struct DataDropCombinator(DataDropCombinatorAlias);

impl View for DataDropCombinator {
    type V = SpecDataDropCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataDropCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DataDropCombinator {
    type Type = DataDrop;
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
pub type DataDropCombinatorAlias = DataidxCombinator;


pub closed spec fn spec_data_drop() -> SpecDataDropCombinator {
    SpecDataDropCombinator(spec_dataidx())
}

                
pub fn data_drop() -> (o: DataDropCombinator)
    ensures o@ == spec_data_drop(),
{
    DataDropCombinator(dataidx())
}

                

pub struct SpecMemoryCopy {
    pub reserved: Seq<u8>,
}

pub type SpecMemoryCopyInner = Seq<u8>;


impl SpecFrom<SpecMemoryCopy> for SpecMemoryCopyInner {
    open spec fn spec_from(m: SpecMemoryCopy) -> SpecMemoryCopyInner {
        m.reserved
    }
}

impl SpecFrom<SpecMemoryCopyInner> for SpecMemoryCopy {
    open spec fn spec_from(m: SpecMemoryCopyInner) -> SpecMemoryCopy {
        let reserved = m;
        SpecMemoryCopy { reserved }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemoryCopy<'a> {
    pub reserved: &'a [u8],
}

impl View for MemoryCopy<'_> {
    type V = SpecMemoryCopy;

    open spec fn view(&self) -> Self::V {
        SpecMemoryCopy {
            reserved: self.reserved@,
        }
    }
}
pub type MemoryCopyInner<'a> = &'a [u8];

pub type MemoryCopyInnerRef<'a> = &'a &'a [u8];
impl<'a> From<&'a MemoryCopy<'a>> for MemoryCopyInnerRef<'a> {
    fn ex_from(m: &'a MemoryCopy) -> MemoryCopyInnerRef<'a> {
        &m.reserved
    }
}

impl<'a> From<MemoryCopyInner<'a>> for MemoryCopy<'a> {
    fn ex_from(m: MemoryCopyInner) -> MemoryCopy {
        let reserved = m;
        MemoryCopy { reserved }
    }
}

pub struct MemoryCopyMapper;
impl View for MemoryCopyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemoryCopyMapper {
    type Src = SpecMemoryCopyInner;
    type Dst = SpecMemoryCopy;
}
impl SpecIsoProof for MemoryCopyMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemoryCopyMapper {
    type Src = MemoryCopyInner<'a>;
    type Dst = MemoryCopy<'a>;
    type RefSrc = MemoryCopyInnerRef<'a>;
}
pub spec const SPEC_MEMORYCOPYRESERVED_CONST: Seq<u8> = seq![0, 0];
pub struct SpecMemoryCopyCombinator(SpecMemoryCopyCombinatorAlias);

impl SpecCombinator for SpecMemoryCopyCombinator {
    type Type = SpecMemoryCopy;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryCopyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryCopyCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemoryCopyCombinatorAlias = Mapped<Refined<bytes::Fixed<2>, TagPred<Seq<u8>>>, MemoryCopyMapper>;
pub exec static MEMORYCOPYRESERVED_CONST: [u8; 2]
    ensures MEMORYCOPYRESERVED_CONST@ == SPEC_MEMORYCOPYRESERVED_CONST,
{
    let arr: [u8; 2] = [0, 0];
    assert(arr@ == SPEC_MEMORYCOPYRESERVED_CONST);
    arr
}

pub struct MemoryCopyCombinator(MemoryCopyCombinatorAlias);

impl View for MemoryCopyCombinator {
    type V = SpecMemoryCopyCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryCopyCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemoryCopyCombinator {
    type Type = MemoryCopy<'a>;
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
pub type MemoryCopyCombinatorAlias = Mapped<Refined<bytes::Fixed<2>, TagPred<[u8; 2]>>, MemoryCopyMapper>;


pub closed spec fn spec_memory_copy() -> SpecMemoryCopyCombinator {
    SpecMemoryCopyCombinator(
    Mapped {
        inner: Refined { inner: bytes::Fixed::<2>, predicate: TagPred(SPEC_MEMORYCOPYRESERVED_CONST) },
        mapper: MemoryCopyMapper,
    })
}

                
pub fn memory_copy() -> (o: MemoryCopyCombinator)
    ensures o@ == spec_memory_copy(),
{
    MemoryCopyCombinator(
    Mapped {
        inner: Refined { inner: bytes::Fixed::<2>, predicate: TagPred(MEMORYCOPYRESERVED_CONST) },
        mapper: MemoryCopyMapper,
    })
}

                

pub struct SpecMemoryFill {
    pub reserved: u8,
}

pub type SpecMemoryFillInner = u8;


impl SpecFrom<SpecMemoryFill> for SpecMemoryFillInner {
    open spec fn spec_from(m: SpecMemoryFill) -> SpecMemoryFillInner {
        m.reserved
    }
}

impl SpecFrom<SpecMemoryFillInner> for SpecMemoryFill {
    open spec fn spec_from(m: SpecMemoryFillInner) -> SpecMemoryFill {
        let reserved = m;
        SpecMemoryFill { reserved }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemoryFill {
    pub reserved: u8,
}

impl View for MemoryFill {
    type V = SpecMemoryFill;

    open spec fn view(&self) -> Self::V {
        SpecMemoryFill {
            reserved: self.reserved@,
        }
    }
}
pub type MemoryFillInner = u8;

pub type MemoryFillInnerRef<'a> = &'a u8;
impl<'a> From<&'a MemoryFill> for MemoryFillInnerRef<'a> {
    fn ex_from(m: &'a MemoryFill) -> MemoryFillInnerRef<'a> {
        &m.reserved
    }
}

impl From<MemoryFillInner> for MemoryFill {
    fn ex_from(m: MemoryFillInner) -> MemoryFill {
        let reserved = m;
        MemoryFill { reserved }
    }
}

pub struct MemoryFillMapper;
impl View for MemoryFillMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemoryFillMapper {
    type Src = SpecMemoryFillInner;
    type Dst = SpecMemoryFill;
}
impl SpecIsoProof for MemoryFillMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemoryFillMapper {
    type Src = MemoryFillInner;
    type Dst = MemoryFill;
    type RefSrc = MemoryFillInnerRef<'a>;
}
pub const MEMORYFILLRESERVED_CONST: u8 = 0;

pub struct SpecMemoryFillCombinator(SpecMemoryFillCombinatorAlias);

impl SpecCombinator for SpecMemoryFillCombinator {
    type Type = SpecMemoryFill;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemoryFillCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemoryFillCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemoryFillCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, MemoryFillMapper>;

pub struct MemoryFillCombinator(MemoryFillCombinatorAlias);

impl View for MemoryFillCombinator {
    type V = SpecMemoryFillCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemoryFillCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemoryFillCombinator {
    type Type = MemoryFill;
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
pub type MemoryFillCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, MemoryFillMapper>;


pub closed spec fn spec_memory_fill() -> SpecMemoryFillCombinator {
    SpecMemoryFillCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(MEMORYFILLRESERVED_CONST) },
        mapper: MemoryFillMapper,
    })
}

                
pub fn memory_fill() -> (o: MemoryFillCombinator)
    ensures o@ == spec_memory_fill(),
{
    MemoryFillCombinator(
    Mapped {
        inner: Refined { inner: U8, predicate: TagPred(MEMORYFILLRESERVED_CONST) },
        mapper: MemoryFillMapper,
    })
}

                

pub enum SpecInstrWithFcRest {
    Variant0(SpecTableInit),
    Variant1(SpecElemDrop),
    Variant2(SpecTableCopy),
    Variant3(SpecTableGrow),
    Variant4(SpecTableSize),
    Variant5(SpecTableFill),
    Variant6(SpecMemoryInit),
    Variant7(SpecDataDrop),
    Variant8(SpecMemoryCopy),
    Variant9(SpecMemoryFill),
    Variant10(SpecEmpty),
}

pub type SpecInstrWithFcRestInner = Either<SpecTableInit, Either<SpecElemDrop, Either<SpecTableCopy, Either<SpecTableGrow, Either<SpecTableSize, Either<SpecTableFill, Either<SpecMemoryInit, Either<SpecDataDrop, Either<SpecMemoryCopy, Either<SpecMemoryFill, SpecEmpty>>>>>>>>>>;

impl SpecFrom<SpecInstrWithFcRest> for SpecInstrWithFcRestInner {
    open spec fn spec_from(m: SpecInstrWithFcRest) -> SpecInstrWithFcRestInner {
        match m {
            SpecInstrWithFcRest::Variant0(m) => Either::Left(m),
            SpecInstrWithFcRest::Variant1(m) => Either::Right(Either::Left(m)),
            SpecInstrWithFcRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrWithFcRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrWithFcRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrWithFcRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrWithFcRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrWithFcRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecInstrWithFcRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecInstrWithFcRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecInstrWithFcRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

                
impl SpecFrom<SpecInstrWithFcRestInner> for SpecInstrWithFcRest {
    open spec fn spec_from(m: SpecInstrWithFcRestInner) -> SpecInstrWithFcRest {
        match m {
            Either::Left(m) => SpecInstrWithFcRest::Variant0(m),
            Either::Right(Either::Left(m)) => SpecInstrWithFcRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrWithFcRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrWithFcRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrWithFcRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrWithFcRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrWithFcRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecInstrWithFcRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecInstrWithFcRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecInstrWithFcRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecInstrWithFcRest::Variant10(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrWithFcRest<'a> {
    Variant0(TableInit),
    Variant1(ElemDrop),
    Variant2(TableCopy),
    Variant3(TableGrow),
    Variant4(TableSize),
    Variant5(TableFill),
    Variant6(MemoryInit),
    Variant7(DataDrop),
    Variant8(MemoryCopy<'a>),
    Variant9(MemoryFill),
    Variant10(Empty<'a>),
}

pub type InstrWithFcRestInner<'a> = Either<TableInit, Either<ElemDrop, Either<TableCopy, Either<TableGrow, Either<TableSize, Either<TableFill, Either<MemoryInit, Either<DataDrop, Either<MemoryCopy<'a>, Either<MemoryFill, Empty<'a>>>>>>>>>>>;

pub type InstrWithFcRestInnerRef<'a> = Either<&'a TableInit, Either<&'a ElemDrop, Either<&'a TableCopy, Either<&'a TableGrow, Either<&'a TableSize, Either<&'a TableFill, Either<&'a MemoryInit, Either<&'a DataDrop, Either<&'a MemoryCopy<'a>, Either<&'a MemoryFill, &'a Empty<'a>>>>>>>>>>>;


impl<'a> View for InstrWithFcRest<'a> {
    type V = SpecInstrWithFcRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrWithFcRest::Variant0(m) => SpecInstrWithFcRest::Variant0(m@),
            InstrWithFcRest::Variant1(m) => SpecInstrWithFcRest::Variant1(m@),
            InstrWithFcRest::Variant2(m) => SpecInstrWithFcRest::Variant2(m@),
            InstrWithFcRest::Variant3(m) => SpecInstrWithFcRest::Variant3(m@),
            InstrWithFcRest::Variant4(m) => SpecInstrWithFcRest::Variant4(m@),
            InstrWithFcRest::Variant5(m) => SpecInstrWithFcRest::Variant5(m@),
            InstrWithFcRest::Variant6(m) => SpecInstrWithFcRest::Variant6(m@),
            InstrWithFcRest::Variant7(m) => SpecInstrWithFcRest::Variant7(m@),
            InstrWithFcRest::Variant8(m) => SpecInstrWithFcRest::Variant8(m@),
            InstrWithFcRest::Variant9(m) => SpecInstrWithFcRest::Variant9(m@),
            InstrWithFcRest::Variant10(m) => SpecInstrWithFcRest::Variant10(m@),
        }
    }
}


impl<'a> From<&'a InstrWithFcRest<'a>> for InstrWithFcRestInnerRef<'a> {
    fn ex_from(m: &'a InstrWithFcRest<'a>) -> InstrWithFcRestInnerRef<'a> {
        match m {
            InstrWithFcRest::Variant0(m) => Either::Left(m),
            InstrWithFcRest::Variant1(m) => Either::Right(Either::Left(m)),
            InstrWithFcRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrWithFcRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrWithFcRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrWithFcRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrWithFcRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrWithFcRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            InstrWithFcRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            InstrWithFcRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            InstrWithFcRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

impl<'a> From<InstrWithFcRestInner<'a>> for InstrWithFcRest<'a> {
    fn ex_from(m: InstrWithFcRestInner<'a>) -> InstrWithFcRest<'a> {
        match m {
            Either::Left(m) => InstrWithFcRest::Variant0(m),
            Either::Right(Either::Left(m)) => InstrWithFcRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrWithFcRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrWithFcRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrWithFcRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrWithFcRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrWithFcRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => InstrWithFcRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => InstrWithFcRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => InstrWithFcRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => InstrWithFcRest::Variant10(m),
        }
    }
    
}


pub struct InstrWithFcRestMapper;
impl View for InstrWithFcRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFcRestMapper {
    type Src = SpecInstrWithFcRestInner;
    type Dst = SpecInstrWithFcRest;
}
impl SpecIsoProof for InstrWithFcRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrWithFcRestMapper {
    type Src = InstrWithFcRestInner<'a>;
    type Dst = InstrWithFcRest<'a>;
    type RefSrc = InstrWithFcRestInnerRef<'a>;
}


pub struct SpecInstrWithFcRestCombinator(SpecInstrWithFcRestCombinatorAlias);

impl SpecCombinator for SpecInstrWithFcRestCombinator {
    type Type = SpecInstrWithFcRest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFcRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFcRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrWithFcRestCombinatorAlias = Mapped<Choice<Cond<SpecTableInitCombinator>, Choice<Cond<SpecElemDropCombinator>, Choice<Cond<SpecTableCopyCombinator>, Choice<Cond<SpecTableGrowCombinator>, Choice<Cond<SpecTableSizeCombinator>, Choice<Cond<SpecTableFillCombinator>, Choice<Cond<SpecMemoryInitCombinator>, Choice<Cond<SpecDataDropCombinator>, Choice<Cond<SpecMemoryCopyCombinator>, Choice<Cond<SpecMemoryFillCombinator>, Cond<SpecEmptyCombinator>>>>>>>>>>>, InstrWithFcRestMapper>;

pub struct InstrWithFcRestCombinator(InstrWithFcRestCombinatorAlias);

impl View for InstrWithFcRestCombinator {
    type V = SpecInstrWithFcRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFcRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrWithFcRestCombinator {
    type Type = InstrWithFcRest<'a>;
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
pub type InstrWithFcRestCombinatorAlias = Mapped<Choice<Cond<TableInitCombinator>, Choice<Cond<ElemDropCombinator>, Choice<Cond<TableCopyCombinator>, Choice<Cond<TableGrowCombinator>, Choice<Cond<TableSizeCombinator>, Choice<Cond<TableFillCombinator>, Choice<Cond<MemoryInitCombinator>, Choice<Cond<DataDropCombinator>, Choice<Cond<MemoryCopyCombinator>, Choice<Cond<MemoryFillCombinator>, Cond<EmptyCombinator>>>>>>>>>>>, InstrWithFcRestMapper>;


pub closed spec fn spec_instr_with_fc_rest(tag: u64) -> SpecInstrWithFcRestCombinator {
    SpecInstrWithFcRestCombinator(Mapped { inner: Choice(Cond { cond: tag == 12, inner: spec_table_init() }, Choice(Cond { cond: tag == 13, inner: spec_elem_drop() }, Choice(Cond { cond: tag == 14, inner: spec_table_copy() }, Choice(Cond { cond: tag == 15, inner: spec_table_grow() }, Choice(Cond { cond: tag == 16, inner: spec_table_size() }, Choice(Cond { cond: tag == 17, inner: spec_table_fill() }, Choice(Cond { cond: tag == 8, inner: spec_memory_init() }, Choice(Cond { cond: tag == 9, inner: spec_data_drop() }, Choice(Cond { cond: tag == 10, inner: spec_memory_copy() }, Choice(Cond { cond: tag == 11, inner: spec_memory_fill() }, Cond { cond: !(tag == 12 || tag == 13 || tag == 14 || tag == 15 || tag == 16 || tag == 17 || tag == 8 || tag == 9 || tag == 10 || tag == 11), inner: spec_empty() })))))))))), mapper: InstrWithFcRestMapper })
}

pub fn instr_with_fc_rest<'a>(tag: u64) -> (o: InstrWithFcRestCombinator)
    ensures o@ == spec_instr_with_fc_rest(tag@),
{
    InstrWithFcRestCombinator(Mapped { inner: Choice::new(Cond { cond: tag == 12, inner: table_init() }, Choice::new(Cond { cond: tag == 13, inner: elem_drop() }, Choice::new(Cond { cond: tag == 14, inner: table_copy() }, Choice::new(Cond { cond: tag == 15, inner: table_grow() }, Choice::new(Cond { cond: tag == 16, inner: table_size() }, Choice::new(Cond { cond: tag == 17, inner: table_fill() }, Choice::new(Cond { cond: tag == 8, inner: memory_init() }, Choice::new(Cond { cond: tag == 9, inner: data_drop() }, Choice::new(Cond { cond: tag == 10, inner: memory_copy() }, Choice::new(Cond { cond: tag == 11, inner: memory_fill() }, Cond { cond: !(tag == 12 || tag == 13 || tag == 14 || tag == 15 || tag == 16 || tag == 17 || tag == 8 || tag == 9 || tag == 10 || tag == 11), inner: empty() })))))))))), mapper: InstrWithFcRestMapper })
}


pub struct SpecInstrWithFc {
    pub tag: u64,
    pub rest: SpecInstrWithFcRest,
}

pub type SpecInstrWithFcInner = (u64, SpecInstrWithFcRest);


impl SpecFrom<SpecInstrWithFc> for SpecInstrWithFcInner {
    open spec fn spec_from(m: SpecInstrWithFc) -> SpecInstrWithFcInner {
        (m.tag, m.rest)
    }
}

impl SpecFrom<SpecInstrWithFcInner> for SpecInstrWithFc {
    open spec fn spec_from(m: SpecInstrWithFcInner) -> SpecInstrWithFc {
        let (tag, rest) = m;
        SpecInstrWithFc { tag, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct InstrWithFc<'a> {
    pub tag: u64,
    pub rest: InstrWithFcRest<'a>,
}

impl View for InstrWithFc<'_> {
    type V = SpecInstrWithFc;

    open spec fn view(&self) -> Self::V {
        SpecInstrWithFc {
            tag: self.tag@,
            rest: self.rest@,
        }
    }
}
pub type InstrWithFcInner<'a> = (u64, InstrWithFcRest<'a>);

pub type InstrWithFcInnerRef<'a> = (&'a u64, &'a InstrWithFcRest<'a>);
impl<'a> From<&'a InstrWithFc<'a>> for InstrWithFcInnerRef<'a> {
    fn ex_from(m: &'a InstrWithFc) -> InstrWithFcInnerRef<'a> {
        (&m.tag, &m.rest)
    }
}

impl<'a> From<InstrWithFcInner<'a>> for InstrWithFc<'a> {
    fn ex_from(m: InstrWithFcInner) -> InstrWithFc {
        let (tag, rest) = m;
        InstrWithFc { tag, rest }
    }
}

pub struct InstrWithFcMapper;
impl View for InstrWithFcMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFcMapper {
    type Src = SpecInstrWithFcInner;
    type Dst = SpecInstrWithFc;
}
impl SpecIsoProof for InstrWithFcMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrWithFcMapper {
    type Src = InstrWithFcInner<'a>;
    type Dst = InstrWithFc<'a>;
    type RefSrc = InstrWithFcInnerRef<'a>;
}

pub struct SpecInstrWithFcCombinator(SpecInstrWithFcCombinatorAlias);

impl SpecCombinator for SpecInstrWithFcCombinator {
    type Type = SpecInstrWithFc;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFcCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFcCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrWithFcCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, SpecInstrWithFcRestCombinator>, InstrWithFcMapper>;

pub struct InstrWithFcCombinator(InstrWithFcCombinatorAlias);

impl View for InstrWithFcCombinator {
    type V = SpecInstrWithFcCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFcCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrWithFcCombinator {
    type Type = InstrWithFc<'a>;
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
pub type InstrWithFcCombinatorAlias = Mapped<Pair<UnsignedLEB128, InstrWithFcRestCombinator, InstrWithFcCont0>, InstrWithFcMapper>;


pub closed spec fn spec_instr_with_fc() -> SpecInstrWithFcCombinator {
    SpecInstrWithFcCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_instr_with_fc_cont0(deps)),
        mapper: InstrWithFcMapper,
    })
}

pub open spec fn spec_instr_with_fc_cont0(deps: u64) -> SpecInstrWithFcRestCombinator {
    let tag = deps;
    spec_instr_with_fc_rest(tag)
}

impl View for InstrWithFcCont0 {
    type V = spec_fn(u64) -> SpecInstrWithFcRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_instr_with_fc_cont0(deps)
        }
    }
}

                
pub fn instr_with_fc() -> (o: InstrWithFcCombinator)
    ensures o@ == spec_instr_with_fc(),
{
    InstrWithFcCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, InstrWithFcCont0),
        mapper: InstrWithFcMapper,
    })
}

pub struct InstrWithFcCont0;
type InstrWithFcCont0Type<'a, 'b> = &'b u64;
type InstrWithFcCont0SType<'a, 'x> = &'x u64;
type InstrWithFcCont0Input<'a, 'b, 'x> = POrSType<InstrWithFcCont0Type<'a, 'b>, InstrWithFcCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<InstrWithFcCont0Input<'a, 'b, 'x>> for InstrWithFcCont0 {
    type Output = InstrWithFcRestCombinator;

    open spec fn requires(&self, deps: InstrWithFcCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: InstrWithFcCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_instr_with_fc_cont0(deps@)
    }

    fn apply(&self, deps: InstrWithFcCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = *deps;
                instr_with_fc_rest(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                instr_with_fc_rest(tag)
            }
        }
    }
}
                
pub type SpecLaneidx = u8;
pub type Laneidx = u8;
pub type LaneidxRef<'a> = &'a u8;


pub struct SpecLaneidxCombinator(SpecLaneidxCombinatorAlias);

impl SpecCombinator for SpecLaneidxCombinator {
    type Type = SpecLaneidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLaneidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLaneidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecLaneidxCombinatorAlias = U8;

pub struct LaneidxCombinator(LaneidxCombinatorAlias);

impl View for LaneidxCombinator {
    type V = SpecLaneidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLaneidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LaneidxCombinator {
    type Type = Laneidx;
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
pub type LaneidxCombinatorAlias = U8;


pub closed spec fn spec_laneidx() -> SpecLaneidxCombinator {
    SpecLaneidxCombinator(U8)
}

                
pub fn laneidx() -> (o: LaneidxCombinator)
    ensures o@ == spec_laneidx(),
{
    LaneidxCombinator(U8)
}

                

pub struct SpecV128Lane {
    pub m: SpecMemarg,
    pub l: SpecLaneidx,
}

pub type SpecV128LaneInner = (SpecMemarg, SpecLaneidx);


impl SpecFrom<SpecV128Lane> for SpecV128LaneInner {
    open spec fn spec_from(m: SpecV128Lane) -> SpecV128LaneInner {
        (m.m, m.l)
    }
}

impl SpecFrom<SpecV128LaneInner> for SpecV128Lane {
    open spec fn spec_from(m: SpecV128LaneInner) -> SpecV128Lane {
        let (m, l) = m;
        SpecV128Lane { m, l }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct V128Lane {
    pub m: Memarg,
    pub l: Laneidx,
}

impl View for V128Lane {
    type V = SpecV128Lane;

    open spec fn view(&self) -> Self::V {
        SpecV128Lane {
            m: self.m@,
            l: self.l@,
        }
    }
}
pub type V128LaneInner = (Memarg, Laneidx);

pub type V128LaneInnerRef<'a> = (&'a Memarg, &'a Laneidx);
impl<'a> From<&'a V128Lane> for V128LaneInnerRef<'a> {
    fn ex_from(m: &'a V128Lane) -> V128LaneInnerRef<'a> {
        (&m.m, &m.l)
    }
}

impl From<V128LaneInner> for V128Lane {
    fn ex_from(m: V128LaneInner) -> V128Lane {
        let (m, l) = m;
        V128Lane { m, l }
    }
}

pub struct V128LaneMapper;
impl View for V128LaneMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for V128LaneMapper {
    type Src = SpecV128LaneInner;
    type Dst = SpecV128Lane;
}
impl SpecIsoProof for V128LaneMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for V128LaneMapper {
    type Src = V128LaneInner;
    type Dst = V128Lane;
    type RefSrc = V128LaneInnerRef<'a>;
}

pub struct SpecV128LaneCombinator(SpecV128LaneCombinatorAlias);

impl SpecCombinator for SpecV128LaneCombinator {
    type Type = SpecV128Lane;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecV128LaneCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecV128LaneCombinatorAlias::is_prefix_secure() }
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
pub type SpecV128LaneCombinatorAlias = Mapped<(SpecMemargCombinator, SpecLaneidxCombinator), V128LaneMapper>;

pub struct V128LaneCombinator(V128LaneCombinatorAlias);

impl View for V128LaneCombinator {
    type V = SpecV128LaneCombinator;
    closed spec fn view(&self) -> Self::V { SpecV128LaneCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for V128LaneCombinator {
    type Type = V128Lane;
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
pub type V128LaneCombinatorAlias = Mapped<(MemargCombinator, LaneidxCombinator), V128LaneMapper>;


pub closed spec fn spec_v128_lane() -> SpecV128LaneCombinator {
    SpecV128LaneCombinator(
    Mapped {
        inner: (spec_memarg(), spec_laneidx()),
        mapper: V128LaneMapper,
    })
}

                
pub fn v128_lane() -> (o: V128LaneCombinator)
    ensures o@ == spec_v128_lane(),
{
    V128LaneCombinator(
    Mapped {
        inner: (memarg(), laneidx()),
        mapper: V128LaneMapper,
    })
}

                
pub type SpecV128Const = Seq<u8>;
pub type V128Const<'a> = &'a [u8];
pub type V128ConstRef<'a> = &'a &'a [u8];


pub struct SpecV128ConstCombinator(SpecV128ConstCombinatorAlias);

impl SpecCombinator for SpecV128ConstCombinator {
    type Type = SpecV128Const;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecV128ConstCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecV128ConstCombinatorAlias::is_prefix_secure() }
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
pub type SpecV128ConstCombinatorAlias = bytes::Fixed<16>;

pub struct V128ConstCombinator(V128ConstCombinatorAlias);

impl View for V128ConstCombinator {
    type V = SpecV128ConstCombinator;
    closed spec fn view(&self) -> Self::V { SpecV128ConstCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for V128ConstCombinator {
    type Type = V128Const<'a>;
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
pub type V128ConstCombinatorAlias = bytes::Fixed<16>;


pub closed spec fn spec_v128_const() -> SpecV128ConstCombinator {
    SpecV128ConstCombinator(bytes::Fixed::<16>)
}

                
pub fn v128_const() -> (o: V128ConstCombinator)
    ensures o@ == spec_v128_const(),
{
    V128ConstCombinator(bytes::Fixed::<16>)
}

                
pub type SpecShuffle = Seq<SpecLaneidx>;
pub type Shuffle = RepeatResult<Laneidx>;
pub type ShuffleRef<'a> = &'a RepeatResult<Laneidx>;


pub struct SpecShuffleCombinator(SpecShuffleCombinatorAlias);

impl SpecCombinator for SpecShuffleCombinator {
    type Type = SpecShuffle;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecShuffleCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecShuffleCombinatorAlias::is_prefix_secure() }
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
pub type SpecShuffleCombinatorAlias = RepeatN<SpecLaneidxCombinator>;

pub struct ShuffleCombinator(ShuffleCombinatorAlias);

impl View for ShuffleCombinator {
    type V = SpecShuffleCombinator;
    closed spec fn view(&self) -> Self::V { SpecShuffleCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ShuffleCombinator {
    type Type = Shuffle;
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
pub type ShuffleCombinatorAlias = RepeatN<LaneidxCombinator>;


pub closed spec fn spec_shuffle() -> SpecShuffleCombinator {
    SpecShuffleCombinator(RepeatN(spec_laneidx(), 16))
}

                
pub fn shuffle() -> (o: ShuffleCombinator)
    ensures o@ == spec_shuffle(),
{
    ShuffleCombinator(RepeatN(laneidx(), 16))
}

                

pub enum SpecInstrWithFdRest {
    Variant0(SpecMemarg),
    Variant1(SpecMemarg),
    Variant2(SpecMemarg),
    Variant3(SpecV128Lane),
    Variant4(SpecV128Const),
    Variant5(SpecShuffle),
    Variant6(SpecLaneidx),
    Variant7(SpecEmpty),
}

pub type SpecInstrWithFdRestInner = Either<SpecMemarg, Either<SpecMemarg, Either<SpecMemarg, Either<SpecV128Lane, Either<SpecV128Const, Either<SpecShuffle, Either<SpecLaneidx, SpecEmpty>>>>>>>;

impl SpecFrom<SpecInstrWithFdRest> for SpecInstrWithFdRestInner {
    open spec fn spec_from(m: SpecInstrWithFdRest) -> SpecInstrWithFdRestInner {
        match m {
            SpecInstrWithFdRest::Variant0(m) => Either::Left(m),
            SpecInstrWithFdRest::Variant1(m) => Either::Right(Either::Left(m)),
            SpecInstrWithFdRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrWithFdRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrWithFdRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrWithFdRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrWithFdRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrWithFdRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

                
impl SpecFrom<SpecInstrWithFdRestInner> for SpecInstrWithFdRest {
    open spec fn spec_from(m: SpecInstrWithFdRestInner) -> SpecInstrWithFdRest {
        match m {
            Either::Left(m) => SpecInstrWithFdRest::Variant0(m),
            Either::Right(Either::Left(m)) => SpecInstrWithFdRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrWithFdRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrWithFdRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrWithFdRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrWithFdRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrWithFdRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => SpecInstrWithFdRest::Variant7(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrWithFdRest<'a> {
    Variant0(Memarg),
    Variant1(Memarg),
    Variant2(Memarg),
    Variant3(V128Lane),
    Variant4(V128Const<'a>),
    Variant5(Shuffle),
    Variant6(Laneidx),
    Variant7(Empty<'a>),
}

pub type InstrWithFdRestInner<'a> = Either<Memarg, Either<Memarg, Either<Memarg, Either<V128Lane, Either<V128Const<'a>, Either<Shuffle, Either<Laneidx, Empty<'a>>>>>>>>;

pub type InstrWithFdRestInnerRef<'a> = Either<&'a Memarg, Either<&'a Memarg, Either<&'a Memarg, Either<&'a V128Lane, Either<&'a V128Const<'a>, Either<&'a Shuffle, Either<&'a Laneidx, &'a Empty<'a>>>>>>>>;


impl<'a> View for InstrWithFdRest<'a> {
    type V = SpecInstrWithFdRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrWithFdRest::Variant0(m) => SpecInstrWithFdRest::Variant0(m@),
            InstrWithFdRest::Variant1(m) => SpecInstrWithFdRest::Variant1(m@),
            InstrWithFdRest::Variant2(m) => SpecInstrWithFdRest::Variant2(m@),
            InstrWithFdRest::Variant3(m) => SpecInstrWithFdRest::Variant3(m@),
            InstrWithFdRest::Variant4(m) => SpecInstrWithFdRest::Variant4(m@),
            InstrWithFdRest::Variant5(m) => SpecInstrWithFdRest::Variant5(m@),
            InstrWithFdRest::Variant6(m) => SpecInstrWithFdRest::Variant6(m@),
            InstrWithFdRest::Variant7(m) => SpecInstrWithFdRest::Variant7(m@),
        }
    }
}


impl<'a> From<&'a InstrWithFdRest<'a>> for InstrWithFdRestInnerRef<'a> {
    fn ex_from(m: &'a InstrWithFdRest<'a>) -> InstrWithFdRestInnerRef<'a> {
        match m {
            InstrWithFdRest::Variant0(m) => Either::Left(m),
            InstrWithFdRest::Variant1(m) => Either::Right(Either::Left(m)),
            InstrWithFdRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrWithFdRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrWithFdRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrWithFdRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrWithFdRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrWithFdRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl<'a> From<InstrWithFdRestInner<'a>> for InstrWithFdRest<'a> {
    fn ex_from(m: InstrWithFdRestInner<'a>) -> InstrWithFdRest<'a> {
        match m {
            Either::Left(m) => InstrWithFdRest::Variant0(m),
            Either::Right(Either::Left(m)) => InstrWithFdRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrWithFdRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrWithFdRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrWithFdRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrWithFdRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrWithFdRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => InstrWithFdRest::Variant7(m),
        }
    }
    
}


pub struct InstrWithFdRestMapper;
impl View for InstrWithFdRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFdRestMapper {
    type Src = SpecInstrWithFdRestInner;
    type Dst = SpecInstrWithFdRest;
}
impl SpecIsoProof for InstrWithFdRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrWithFdRestMapper {
    type Src = InstrWithFdRestInner<'a>;
    type Dst = InstrWithFdRest<'a>;
    type RefSrc = InstrWithFdRestInnerRef<'a>;
}


pub struct SpecInstrWithFdRestCombinator(SpecInstrWithFdRestCombinatorAlias);

impl SpecCombinator for SpecInstrWithFdRestCombinator {
    type Type = SpecInstrWithFdRest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFdRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFdRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrWithFdRestCombinatorAlias = Mapped<Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecMemargCombinator>, Choice<Cond<SpecV128LaneCombinator>, Choice<Cond<SpecV128ConstCombinator>, Choice<Cond<SpecShuffleCombinator>, Choice<Cond<SpecLaneidxCombinator>, Cond<SpecEmptyCombinator>>>>>>>>, InstrWithFdRestMapper>;

pub struct InstrWithFdRestCombinator(InstrWithFdRestCombinatorAlias);

impl View for InstrWithFdRestCombinator {
    type V = SpecInstrWithFdRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFdRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrWithFdRestCombinator {
    type Type = InstrWithFdRest<'a>;
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
pub type InstrWithFdRestCombinatorAlias = Mapped<Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<MemargCombinator>, Choice<Cond<V128LaneCombinator>, Choice<Cond<V128ConstCombinator>, Choice<Cond<ShuffleCombinator>, Choice<Cond<LaneidxCombinator>, Cond<EmptyCombinator>>>>>>>>, InstrWithFdRestMapper>;


pub closed spec fn spec_instr_with_fd_rest(tag: u64) -> SpecInstrWithFdRestCombinator {
    SpecInstrWithFdRestCombinator(Mapped { inner: Choice(Cond { cond: tag >= 0 && tag <= 11, inner: spec_memarg() }, Choice(Cond { cond: tag == 92, inner: spec_memarg() }, Choice(Cond { cond: tag == 93, inner: spec_memarg() }, Choice(Cond { cond: tag >= 84 && tag <= 91, inner: spec_v128_lane() }, Choice(Cond { cond: tag == 12, inner: spec_v128_const() }, Choice(Cond { cond: tag == 13, inner: spec_shuffle() }, Choice(Cond { cond: tag >= 21 && tag <= 34, inner: spec_laneidx() }, Cond { cond: !(tag >= 0 && tag <= 11 || tag == 92 || tag == 93 || tag >= 84 && tag <= 91 || tag == 12 || tag == 13 || tag >= 21 && tag <= 34), inner: spec_empty() }))))))), mapper: InstrWithFdRestMapper })
}

pub fn instr_with_fd_rest<'a>(tag: u64) -> (o: InstrWithFdRestCombinator)
    ensures o@ == spec_instr_with_fd_rest(tag@),
{
    InstrWithFdRestCombinator(Mapped { inner: Choice::new(Cond { cond: tag >= 0 && tag <= 11, inner: memarg() }, Choice::new(Cond { cond: tag == 92, inner: memarg() }, Choice::new(Cond { cond: tag == 93, inner: memarg() }, Choice::new(Cond { cond: tag >= 84 && tag <= 91, inner: v128_lane() }, Choice::new(Cond { cond: tag == 12, inner: v128_const() }, Choice::new(Cond { cond: tag == 13, inner: shuffle() }, Choice::new(Cond { cond: tag >= 21 && tag <= 34, inner: laneidx() }, Cond { cond: !(tag >= 0 && tag <= 11 || tag == 92 || tag == 93 || tag >= 84 && tag <= 91 || tag == 12 || tag == 13 || tag >= 21 && tag <= 34), inner: empty() }))))))), mapper: InstrWithFdRestMapper })
}


pub struct SpecInstrWithFd {
    pub tag: u64,
    pub rest: SpecInstrWithFdRest,
}

pub type SpecInstrWithFdInner = (u64, SpecInstrWithFdRest);


impl SpecFrom<SpecInstrWithFd> for SpecInstrWithFdInner {
    open spec fn spec_from(m: SpecInstrWithFd) -> SpecInstrWithFdInner {
        (m.tag, m.rest)
    }
}

impl SpecFrom<SpecInstrWithFdInner> for SpecInstrWithFd {
    open spec fn spec_from(m: SpecInstrWithFdInner) -> SpecInstrWithFd {
        let (tag, rest) = m;
        SpecInstrWithFd { tag, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct InstrWithFd<'a> {
    pub tag: u64,
    pub rest: InstrWithFdRest<'a>,
}

impl View for InstrWithFd<'_> {
    type V = SpecInstrWithFd;

    open spec fn view(&self) -> Self::V {
        SpecInstrWithFd {
            tag: self.tag@,
            rest: self.rest@,
        }
    }
}
pub type InstrWithFdInner<'a> = (u64, InstrWithFdRest<'a>);

pub type InstrWithFdInnerRef<'a> = (&'a u64, &'a InstrWithFdRest<'a>);
impl<'a> From<&'a InstrWithFd<'a>> for InstrWithFdInnerRef<'a> {
    fn ex_from(m: &'a InstrWithFd) -> InstrWithFdInnerRef<'a> {
        (&m.tag, &m.rest)
    }
}

impl<'a> From<InstrWithFdInner<'a>> for InstrWithFd<'a> {
    fn ex_from(m: InstrWithFdInner) -> InstrWithFd {
        let (tag, rest) = m;
        InstrWithFd { tag, rest }
    }
}

pub struct InstrWithFdMapper;
impl View for InstrWithFdMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrWithFdMapper {
    type Src = SpecInstrWithFdInner;
    type Dst = SpecInstrWithFd;
}
impl SpecIsoProof for InstrWithFdMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrWithFdMapper {
    type Src = InstrWithFdInner<'a>;
    type Dst = InstrWithFd<'a>;
    type RefSrc = InstrWithFdInnerRef<'a>;
}

pub struct SpecInstrWithFdCombinator(SpecInstrWithFdCombinatorAlias);

impl SpecCombinator for SpecInstrWithFdCombinator {
    type Type = SpecInstrWithFd;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrWithFdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrWithFdCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrWithFdCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, SpecInstrWithFdRestCombinator>, InstrWithFdMapper>;

pub struct InstrWithFdCombinator(InstrWithFdCombinatorAlias);

impl View for InstrWithFdCombinator {
    type V = SpecInstrWithFdCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrWithFdCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrWithFdCombinator {
    type Type = InstrWithFd<'a>;
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
pub type InstrWithFdCombinatorAlias = Mapped<Pair<UnsignedLEB128, InstrWithFdRestCombinator, InstrWithFdCont0>, InstrWithFdMapper>;


pub closed spec fn spec_instr_with_fd() -> SpecInstrWithFdCombinator {
    SpecInstrWithFdCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_instr_with_fd_cont0(deps)),
        mapper: InstrWithFdMapper,
    })
}

pub open spec fn spec_instr_with_fd_cont0(deps: u64) -> SpecInstrWithFdRestCombinator {
    let tag = deps;
    spec_instr_with_fd_rest(tag)
}

impl View for InstrWithFdCont0 {
    type V = spec_fn(u64) -> SpecInstrWithFdRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_instr_with_fd_cont0(deps)
        }
    }
}

                
pub fn instr_with_fd() -> (o: InstrWithFdCombinator)
    ensures o@ == spec_instr_with_fd(),
{
    InstrWithFdCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, InstrWithFdCont0),
        mapper: InstrWithFdMapper,
    })
}

pub struct InstrWithFdCont0;
type InstrWithFdCont0Type<'a, 'b> = &'b u64;
type InstrWithFdCont0SType<'a, 'x> = &'x u64;
type InstrWithFdCont0Input<'a, 'b, 'x> = POrSType<InstrWithFdCont0Type<'a, 'b>, InstrWithFdCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<InstrWithFdCont0Input<'a, 'b, 'x>> for InstrWithFdCont0 {
    type Output = InstrWithFdRestCombinator;

    open spec fn requires(&self, deps: InstrWithFdCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: InstrWithFdCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_instr_with_fd_cont0(deps@)
    }

    fn apply(&self, deps: InstrWithFdCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = *deps;
                instr_with_fd_rest(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                instr_with_fd_rest(tag)
            }
        }
    }
}
                

pub enum SpecInstrRest {
    Variant0(SpecInstrVariable),
    Variant1(SpecInstrControl2),
    Variant2(SpecInstrControl1),
    Variant3(SpecInstrMemory),
    Variant4(SpecInstrReference),
    Variant5(SpecInstrParametric),
    Variant6(SpecInstrTable),
    Variant7(SpecInstrNumeric),
    Variant8(SpecInstrWithFc),
    Variant9(SpecInstrWithFd),
    Variant10(SpecEmpty),
}

pub type SpecInstrRestInner = Either<SpecInstrVariable, Either<SpecInstrControl2, Either<SpecInstrControl1, Either<SpecInstrMemory, Either<SpecInstrReference, Either<SpecInstrParametric, Either<SpecInstrTable, Either<SpecInstrNumeric, Either<SpecInstrWithFc, Either<SpecInstrWithFd, SpecEmpty>>>>>>>>>>;

impl SpecFrom<SpecInstrRest> for SpecInstrRestInner {
    open spec fn spec_from(m: SpecInstrRest) -> SpecInstrRestInner {
        match m {
            SpecInstrRest::Variant0(m) => Either::Left(m),
            SpecInstrRest::Variant1(m) => Either::Right(Either::Left(m)),
            SpecInstrRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecInstrRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecInstrRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecInstrRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecInstrRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecInstrRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecInstrRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecInstrRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecInstrRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

                
impl SpecFrom<SpecInstrRestInner> for SpecInstrRest {
    open spec fn spec_from(m: SpecInstrRestInner) -> SpecInstrRest {
        match m {
            Either::Left(m) => SpecInstrRest::Variant0(m),
            Either::Right(Either::Left(m)) => SpecInstrRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecInstrRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecInstrRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecInstrRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecInstrRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecInstrRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecInstrRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecInstrRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecInstrRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecInstrRest::Variant10(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstrRest<'a> {
    Variant0(InstrVariable),
    Variant1(InstrControl2<'a>),
    Variant2(InstrControl1<'a>),
    Variant3(InstrMemory),
    Variant4(InstrReference<'a>),
    Variant5(InstrParametric<'a>),
    Variant6(InstrTable),
    Variant7(InstrNumeric<'a>),
    Variant8(InstrWithFc<'a>),
    Variant9(InstrWithFd<'a>),
    Variant10(Empty<'a>),
}

pub type InstrRestInner<'a> = Either<InstrVariable, Either<InstrControl2<'a>, Either<InstrControl1<'a>, Either<InstrMemory, Either<InstrReference<'a>, Either<InstrParametric<'a>, Either<InstrTable, Either<InstrNumeric<'a>, Either<InstrWithFc<'a>, Either<InstrWithFd<'a>, Empty<'a>>>>>>>>>>>;

pub type InstrRestInnerRef<'a> = Either<&'a InstrVariable, Either<&'a InstrControl2<'a>, Either<&'a InstrControl1<'a>, Either<&'a InstrMemory, Either<&'a InstrReference<'a>, Either<&'a InstrParametric<'a>, Either<&'a InstrTable, Either<&'a InstrNumeric<'a>, Either<&'a InstrWithFc<'a>, Either<&'a InstrWithFd<'a>, &'a Empty<'a>>>>>>>>>>>;


impl<'a> View for InstrRest<'a> {
    type V = SpecInstrRest;
    open spec fn view(&self) -> Self::V {
        match self {
            InstrRest::Variant0(m) => SpecInstrRest::Variant0(m@),
            InstrRest::Variant1(m) => SpecInstrRest::Variant1(m@),
            InstrRest::Variant2(m) => SpecInstrRest::Variant2(m@),
            InstrRest::Variant3(m) => SpecInstrRest::Variant3(m@),
            InstrRest::Variant4(m) => SpecInstrRest::Variant4(m@),
            InstrRest::Variant5(m) => SpecInstrRest::Variant5(m@),
            InstrRest::Variant6(m) => SpecInstrRest::Variant6(m@),
            InstrRest::Variant7(m) => SpecInstrRest::Variant7(m@),
            InstrRest::Variant8(m) => SpecInstrRest::Variant8(m@),
            InstrRest::Variant9(m) => SpecInstrRest::Variant9(m@),
            InstrRest::Variant10(m) => SpecInstrRest::Variant10(m@),
        }
    }
}


impl<'a> From<&'a InstrRest<'a>> for InstrRestInnerRef<'a> {
    fn ex_from(m: &'a InstrRest<'a>) -> InstrRestInnerRef<'a> {
        match m {
            InstrRest::Variant0(m) => Either::Left(m),
            InstrRest::Variant1(m) => Either::Right(Either::Left(m)),
            InstrRest::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            InstrRest::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            InstrRest::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            InstrRest::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            InstrRest::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            InstrRest::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            InstrRest::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            InstrRest::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            InstrRest::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }

}

impl<'a> From<InstrRestInner<'a>> for InstrRest<'a> {
    fn ex_from(m: InstrRestInner<'a>) -> InstrRest<'a> {
        match m {
            Either::Left(m) => InstrRest::Variant0(m),
            Either::Right(Either::Left(m)) => InstrRest::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => InstrRest::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => InstrRest::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => InstrRest::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => InstrRest::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => InstrRest::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => InstrRest::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => InstrRest::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => InstrRest::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => InstrRest::Variant10(m),
        }
    }
    
}


pub struct InstrRestMapper;
impl View for InstrRestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrRestMapper {
    type Src = SpecInstrRestInner;
    type Dst = SpecInstrRest;
}
impl SpecIsoProof for InstrRestMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrRestMapper {
    type Src = InstrRestInner<'a>;
    type Dst = InstrRest<'a>;
    type RefSrc = InstrRestInnerRef<'a>;
}


pub struct SpecInstrRestCombinator(SpecInstrRestCombinatorAlias);

impl SpecCombinator for SpecInstrRestCombinator {
    type Type = SpecInstrRest;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrRestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrRestCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrRestCombinatorAlias = Mapped<Choice<Cond<SpecInstrVariableCombinator>, Choice<Cond<SpecInstrControl2Combinator>, Choice<Cond<SpecInstrControl1Combinator>, Choice<Cond<SpecInstrMemoryCombinator>, Choice<Cond<SpecInstrReferenceCombinator>, Choice<Cond<SpecInstrParametricCombinator>, Choice<Cond<SpecInstrTableCombinator>, Choice<Cond<SpecInstrNumericCombinator>, Choice<Cond<SpecInstrWithFcCombinator>, Choice<Cond<SpecInstrWithFdCombinator>, Cond<SpecEmptyCombinator>>>>>>>>>>>, InstrRestMapper>;

pub struct InstrRestCombinator(InstrRestCombinatorAlias);

impl View for InstrRestCombinator {
    type V = SpecInstrRestCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrRestCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrRestCombinator {
    type Type = InstrRest<'a>;
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
pub type InstrRestCombinatorAlias = Mapped<Choice<Cond<InstrVariableCombinator>, Choice<Cond<InstrControl2Combinator>, Choice<Cond<InstrControl1Combinator>, Choice<Cond<InstrMemoryCombinator>, Choice<Cond<InstrReferenceCombinator>, Choice<Cond<InstrParametricCombinator>, Choice<Cond<InstrTableCombinator>, Choice<Cond<InstrNumericCombinator>, Choice<Cond<InstrWithFcCombinator>, Choice<Cond<InstrWithFdCombinator>, Cond<EmptyCombinator>>>>>>>>>>>, InstrRestMapper>;


pub closed spec fn spec_instr_rest(opcode: SpecInstrBytecode) -> SpecInstrRestCombinator {
    SpecInstrRestCombinator(Mapped { inner: Choice(Cond { cond: opcode >= 32 && opcode <= 36, inner: spec_instr_variable(opcode) }, Choice(Cond { cond: opcode >= 11 && opcode <= 17, inner: spec_instr_control2(opcode) }, Choice(Cond { cond: opcode >= 0 && opcode <= 5, inner: spec_instr_control1(opcode) }, Choice(Cond { cond: opcode >= 40 && opcode <= 64, inner: spec_instr_memory(opcode) }, Choice(Cond { cond: opcode >= 208 && opcode <= 210, inner: spec_instr_reference(opcode) }, Choice(Cond { cond: opcode >= 26 && opcode <= 28, inner: spec_instr_parametric(opcode) }, Choice(Cond { cond: opcode >= 37 && opcode <= 38, inner: spec_instr_table(opcode) }, Choice(Cond { cond: opcode >= 65 && opcode <= 68, inner: spec_instr_numeric(opcode) }, Choice(Cond { cond: opcode == 252, inner: spec_instr_with_fc() }, Choice(Cond { cond: opcode == 253, inner: spec_instr_with_fd() }, Cond { cond: !(opcode >= 32 && opcode <= 36 || opcode >= 11 && opcode <= 17 || opcode >= 0 && opcode <= 5 || opcode >= 40 && opcode <= 64 || opcode >= 208 && opcode <= 210 || opcode >= 26 && opcode <= 28 || opcode >= 37 && opcode <= 38 || opcode >= 65 && opcode <= 68 || opcode == 252 || opcode == 253), inner: spec_empty() })))))))))), mapper: InstrRestMapper })
}

pub fn instr_rest<'a>(opcode: InstrBytecode) -> (o: InstrRestCombinator)
    ensures o@ == spec_instr_rest(opcode@),
{
    InstrRestCombinator(Mapped { inner: Choice::new(Cond { cond: opcode >= 32 && opcode <= 36, inner: instr_variable(opcode) }, Choice::new(Cond { cond: opcode >= 11 && opcode <= 17, inner: instr_control2(opcode) }, Choice::new(Cond { cond: opcode >= 0 && opcode <= 5, inner: instr_control1(opcode) }, Choice::new(Cond { cond: opcode >= 40 && opcode <= 64, inner: instr_memory(opcode) }, Choice::new(Cond { cond: opcode >= 208 && opcode <= 210, inner: instr_reference(opcode) }, Choice::new(Cond { cond: opcode >= 26 && opcode <= 28, inner: instr_parametric(opcode) }, Choice::new(Cond { cond: opcode >= 37 && opcode <= 38, inner: instr_table(opcode) }, Choice::new(Cond { cond: opcode >= 65 && opcode <= 68, inner: instr_numeric(opcode) }, Choice::new(Cond { cond: opcode == 252, inner: instr_with_fc() }, Choice::new(Cond { cond: opcode == 253, inner: instr_with_fd() }, Cond { cond: !(opcode >= 32 && opcode <= 36 || opcode >= 11 && opcode <= 17 || opcode >= 0 && opcode <= 5 || opcode >= 40 && opcode <= 64 || opcode >= 208 && opcode <= 210 || opcode >= 26 && opcode <= 28 || opcode >= 37 && opcode <= 38 || opcode >= 65 && opcode <= 68 || opcode == 252 || opcode == 253), inner: empty() })))))))))), mapper: InstrRestMapper })
}


pub struct SpecInstr {
    pub opcode: SpecInstrBytecode,
    pub rest: SpecInstrRest,
}

pub type SpecInstrInner = (SpecInstrBytecode, SpecInstrRest);


impl SpecFrom<SpecInstr> for SpecInstrInner {
    open spec fn spec_from(m: SpecInstr) -> SpecInstrInner {
        (m.opcode, m.rest)
    }
}

impl SpecFrom<SpecInstrInner> for SpecInstr {
    open spec fn spec_from(m: SpecInstrInner) -> SpecInstr {
        let (opcode, rest) = m;
        SpecInstr { opcode, rest }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Instr<'a> {
    pub opcode: InstrBytecode,
    pub rest: InstrRest<'a>,
}

impl View for Instr<'_> {
    type V = SpecInstr;

    open spec fn view(&self) -> Self::V {
        SpecInstr {
            opcode: self.opcode@,
            rest: self.rest@,
        }
    }
}
pub type InstrInner<'a> = (InstrBytecode, InstrRest<'a>);

pub type InstrInnerRef<'a> = (&'a InstrBytecode, &'a InstrRest<'a>);
impl<'a> From<&'a Instr<'a>> for InstrInnerRef<'a> {
    fn ex_from(m: &'a Instr) -> InstrInnerRef<'a> {
        (&m.opcode, &m.rest)
    }
}

impl<'a> From<InstrInner<'a>> for Instr<'a> {
    fn ex_from(m: InstrInner) -> Instr {
        let (opcode, rest) = m;
        Instr { opcode, rest }
    }
}

pub struct InstrMapper;
impl View for InstrMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for InstrMapper {
    type Src = SpecInstrInner;
    type Dst = SpecInstr;
}
impl SpecIsoProof for InstrMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for InstrMapper {
    type Src = InstrInner<'a>;
    type Dst = Instr<'a>;
    type RefSrc = InstrInnerRef<'a>;
}

pub struct SpecInstrCombinator(SpecInstrCombinatorAlias);

impl SpecCombinator for SpecInstrCombinator {
    type Type = SpecInstr;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecInstrCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecInstrCombinatorAlias::is_prefix_secure() }
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
pub type SpecInstrCombinatorAlias = Mapped<SpecPair<SpecInstrBytecodeCombinator, SpecInstrRestCombinator>, InstrMapper>;

pub struct InstrCombinator(InstrCombinatorAlias);

impl View for InstrCombinator {
    type V = SpecInstrCombinator;
    closed spec fn view(&self) -> Self::V { SpecInstrCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for InstrCombinator {
    type Type = Instr<'a>;
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
pub type InstrCombinatorAlias = Mapped<Pair<InstrBytecodeCombinator, InstrRestCombinator, InstrCont0>, InstrMapper>;


pub closed spec fn spec_instr() -> SpecInstrCombinator {
    SpecInstrCombinator(
    Mapped {
        inner: Pair::spec_new(spec_instr_bytecode(), |deps| spec_instr_cont0(deps)),
        mapper: InstrMapper,
    })
}

pub open spec fn spec_instr_cont0(deps: SpecInstrBytecode) -> SpecInstrRestCombinator {
    let opcode = deps;
    spec_instr_rest(opcode)
}

impl View for InstrCont0 {
    type V = spec_fn(SpecInstrBytecode) -> SpecInstrRestCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecInstrBytecode| {
            spec_instr_cont0(deps)
        }
    }
}

                
pub fn instr() -> (o: InstrCombinator)
    ensures o@ == spec_instr(),
{
    InstrCombinator(
    Mapped {
        inner: Pair::new(instr_bytecode(), InstrCont0),
        mapper: InstrMapper,
    })
}

pub struct InstrCont0;
type InstrCont0Type<'a, 'b> = &'b InstrBytecode;
type InstrCont0SType<'a, 'x> = &'x InstrBytecode;
type InstrCont0Input<'a, 'b, 'x> = POrSType<InstrCont0Type<'a, 'b>, InstrCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<InstrCont0Input<'a, 'b, 'x>> for InstrCont0 {
    type Output = InstrRestCombinator;

    open spec fn requires(&self, deps: InstrCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: InstrCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_instr_cont0(deps@)
    }

    fn apply(&self, deps: InstrCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let opcode = *deps;
                instr_rest(opcode)
            }
            POrSType::S(deps) => {
                let opcode = deps;
                let opcode = *opcode;
                instr_rest(opcode)
            }
        }
    }
}
                

pub struct SpecExprInner {
    pub l: u64,
    pub v: Seq<SpecInstr>,
}

pub type SpecExprInnerInner = (u64, Seq<SpecInstr>);


impl SpecFrom<SpecExprInner> for SpecExprInnerInner {
    open spec fn spec_from(m: SpecExprInner) -> SpecExprInnerInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecExprInnerInner> for SpecExprInner {
    open spec fn spec_from(m: SpecExprInnerInner) -> SpecExprInner {
        let (l, v) = m;
        SpecExprInner { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ExprInner<'a> {
    pub l: u64,
    pub v: RepeatResult<Instr<'a>>,
}

impl View for ExprInner<'_> {
    type V = SpecExprInner;

    open spec fn view(&self) -> Self::V {
        SpecExprInner {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExprInnerInner<'a> = (u64, RepeatResult<Instr<'a>>);

pub type ExprInnerInnerRef<'a> = (&'a u64, &'a RepeatResult<Instr<'a>>);
impl<'a> From<&'a ExprInner<'a>> for ExprInnerInnerRef<'a> {
    fn ex_from(m: &'a ExprInner) -> ExprInnerInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<ExprInnerInner<'a>> for ExprInner<'a> {
    fn ex_from(m: ExprInnerInner) -> ExprInner {
        let (l, v) = m;
        ExprInner { l, v }
    }
}

pub struct ExprInnerMapper;
impl View for ExprInnerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExprInnerMapper {
    type Src = SpecExprInnerInner;
    type Dst = SpecExprInner;
}
impl SpecIsoProof for ExprInnerMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExprInnerMapper {
    type Src = ExprInnerInner<'a>;
    type Dst = ExprInner<'a>;
    type RefSrc = ExprInnerInnerRef<'a>;
}

pub struct SpecExprInnerCombinator(SpecExprInnerCombinatorAlias);

impl SpecCombinator for SpecExprInnerCombinator {
    type Type = SpecExprInner;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprInnerCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprInnerCombinatorAlias::is_prefix_secure() }
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
pub type SpecExprInnerCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecInstrCombinator>>, ExprInnerMapper>;

pub struct ExprInnerCombinator(ExprInnerCombinatorAlias);

impl View for ExprInnerCombinator {
    type V = SpecExprInnerCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprInnerCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExprInnerCombinator {
    type Type = ExprInner<'a>;
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
pub type ExprInnerCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<InstrCombinator>, ExprInnerCont0>, ExprInnerMapper>;


pub closed spec fn spec_expr_inner() -> SpecExprInnerCombinator {
    SpecExprInnerCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_expr_inner_cont0(deps)),
        mapper: ExprInnerMapper,
    })
}

pub open spec fn spec_expr_inner_cont0(deps: u64) -> RepeatN<SpecInstrCombinator> {
    let l = deps;
    RepeatN(spec_instr(), l.spec_into())
}

impl View for ExprInnerCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecInstrCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_expr_inner_cont0(deps)
        }
    }
}

                
pub fn expr_inner() -> (o: ExprInnerCombinator)
    ensures o@ == spec_expr_inner(),
{
    ExprInnerCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ExprInnerCont0),
        mapper: ExprInnerMapper,
    })
}

pub struct ExprInnerCont0;
type ExprInnerCont0Type<'a, 'b> = &'b u64;
type ExprInnerCont0SType<'a, 'x> = &'x u64;
type ExprInnerCont0Input<'a, 'b, 'x> = POrSType<ExprInnerCont0Type<'a, 'b>, ExprInnerCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ExprInnerCont0Input<'a, 'b, 'x>> for ExprInnerCont0 {
    type Output = RepeatN<InstrCombinator>;

    open spec fn requires(&self, deps: ExprInnerCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ExprInnerCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_expr_inner_cont0(deps@)
    }

    fn apply(&self, deps: ExprInnerCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(instr(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(instr(), l.ex_into())
            }
        }
    }
}
                
pub type SpecExpr = SpecExprInner;
pub type Expr<'a> = ExprInner<'a>;
pub type ExprRef<'a> = &'a ExprInner<'a>;


pub const Expr_0_BACK_CONST: u8 = 11;

pub struct SpecExprCombinator(SpecExprCombinatorAlias);

impl SpecCombinator for SpecExprCombinator {
    type Type = SpecExpr;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprCombinatorAlias::is_prefix_secure() }
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
pub type SpecExprCombinatorAlias = Terminated<SpecExprInnerCombinator, Tag<U8, u8>>;


pub struct ExprCombinator(ExprCombinatorAlias);

impl View for ExprCombinator {
    type V = SpecExprCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExprCombinator {
    type Type = Expr<'a>;
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
pub type ExprCombinatorAlias = Terminated<ExprInnerCombinator, Tag<U8, u8>>;


pub closed spec fn spec_expr() -> SpecExprCombinator {
    SpecExprCombinator(Terminated(spec_expr_inner(), Tag::spec_new(U8, Expr_0_BACK_CONST)))
}

                
pub fn expr() -> (o: ExprCombinator)
    ensures o@ == spec_expr(),
{
    ExprCombinator(Terminated(expr_inner(), Tag::new(U8, Expr_0_BACK_CONST)))
}

                

pub struct SpecGlobal {
    pub gt: SpecGlobaltype,
    pub init: SpecExpr,
}

pub type SpecGlobalInner = (SpecGlobaltype, SpecExpr);


impl SpecFrom<SpecGlobal> for SpecGlobalInner {
    open spec fn spec_from(m: SpecGlobal) -> SpecGlobalInner {
        (m.gt, m.init)
    }
}

impl SpecFrom<SpecGlobalInner> for SpecGlobal {
    open spec fn spec_from(m: SpecGlobalInner) -> SpecGlobal {
        let (gt, init) = m;
        SpecGlobal { gt, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Global<'a> {
    pub gt: Globaltype,
    pub init: Expr<'a>,
}

impl View for Global<'_> {
    type V = SpecGlobal;

    open spec fn view(&self) -> Self::V {
        SpecGlobal {
            gt: self.gt@,
            init: self.init@,
        }
    }
}
pub type GlobalInner<'a> = (Globaltype, Expr<'a>);

pub type GlobalInnerRef<'a> = (&'a Globaltype, &'a Expr<'a>);
impl<'a> From<&'a Global<'a>> for GlobalInnerRef<'a> {
    fn ex_from(m: &'a Global) -> GlobalInnerRef<'a> {
        (&m.gt, &m.init)
    }
}

impl<'a> From<GlobalInner<'a>> for Global<'a> {
    fn ex_from(m: GlobalInner) -> Global {
        let (gt, init) = m;
        Global { gt, init }
    }
}

pub struct GlobalMapper;
impl View for GlobalMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalMapper {
    type Src = SpecGlobalInner;
    type Dst = SpecGlobal;
}
impl SpecIsoProof for GlobalMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GlobalMapper {
    type Src = GlobalInner<'a>;
    type Dst = Global<'a>;
    type RefSrc = GlobalInnerRef<'a>;
}

pub struct SpecGlobalCombinator(SpecGlobalCombinatorAlias);

impl SpecCombinator for SpecGlobalCombinator {
    type Type = SpecGlobal;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalCombinatorAlias::is_prefix_secure() }
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
pub type SpecGlobalCombinatorAlias = Mapped<(SpecGlobaltypeCombinator, SpecExprCombinator), GlobalMapper>;

pub struct GlobalCombinator(GlobalCombinatorAlias);

impl View for GlobalCombinator {
    type V = SpecGlobalCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GlobalCombinator {
    type Type = Global<'a>;
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
pub type GlobalCombinatorAlias = Mapped<(GlobaltypeCombinator, ExprCombinator), GlobalMapper>;


pub closed spec fn spec_global() -> SpecGlobalCombinator {
    SpecGlobalCombinator(
    Mapped {
        inner: (spec_globaltype(), spec_expr()),
        mapper: GlobalMapper,
    })
}

                
pub fn global() -> (o: GlobalCombinator)
    ensures o@ == spec_global(),
{
    GlobalCombinator(
    Mapped {
        inner: (globaltype(), expr()),
        mapper: GlobalMapper,
    })
}

                

pub struct SpecGlobalsecContent {
    pub l: u64,
    pub v: Seq<SpecGlobal>,
}

pub type SpecGlobalsecContentInner = (u64, Seq<SpecGlobal>);


impl SpecFrom<SpecGlobalsecContent> for SpecGlobalsecContentInner {
    open spec fn spec_from(m: SpecGlobalsecContent) -> SpecGlobalsecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecGlobalsecContentInner> for SpecGlobalsecContent {
    open spec fn spec_from(m: SpecGlobalsecContentInner) -> SpecGlobalsecContent {
        let (l, v) = m;
        SpecGlobalsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct GlobalsecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Global<'a>>,
}

impl View for GlobalsecContent<'_> {
    type V = SpecGlobalsecContent;

    open spec fn view(&self) -> Self::V {
        SpecGlobalsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type GlobalsecContentInner<'a> = (u64, RepeatResult<Global<'a>>);

pub type GlobalsecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Global<'a>>);
impl<'a> From<&'a GlobalsecContent<'a>> for GlobalsecContentInnerRef<'a> {
    fn ex_from(m: &'a GlobalsecContent) -> GlobalsecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<GlobalsecContentInner<'a>> for GlobalsecContent<'a> {
    fn ex_from(m: GlobalsecContentInner) -> GlobalsecContent {
        let (l, v) = m;
        GlobalsecContent { l, v }
    }
}

pub struct GlobalsecContentMapper;
impl View for GlobalsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalsecContentMapper {
    type Src = SpecGlobalsecContentInner;
    type Dst = SpecGlobalsecContent;
}
impl SpecIsoProof for GlobalsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GlobalsecContentMapper {
    type Src = GlobalsecContentInner<'a>;
    type Dst = GlobalsecContent<'a>;
    type RefSrc = GlobalsecContentInnerRef<'a>;
}

pub struct SpecGlobalsecContentCombinator(SpecGlobalsecContentCombinatorAlias);

impl SpecCombinator for SpecGlobalsecContentCombinator {
    type Type = SpecGlobalsecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalsecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecGlobalsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecGlobalCombinator>>, GlobalsecContentMapper>;

pub struct GlobalsecContentCombinator(GlobalsecContentCombinatorAlias);

impl View for GlobalsecContentCombinator {
    type V = SpecGlobalsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalsecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GlobalsecContentCombinator {
    type Type = GlobalsecContent<'a>;
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
pub type GlobalsecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<GlobalCombinator>, GlobalsecContentCont0>, GlobalsecContentMapper>;


pub closed spec fn spec_globalsec_content() -> SpecGlobalsecContentCombinator {
    SpecGlobalsecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_globalsec_content_cont0(deps)),
        mapper: GlobalsecContentMapper,
    })
}

pub open spec fn spec_globalsec_content_cont0(deps: u64) -> RepeatN<SpecGlobalCombinator> {
    let l = deps;
    RepeatN(spec_global(), l.spec_into())
}

impl View for GlobalsecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecGlobalCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_globalsec_content_cont0(deps)
        }
    }
}

                
pub fn globalsec_content() -> (o: GlobalsecContentCombinator)
    ensures o@ == spec_globalsec_content(),
{
    GlobalsecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, GlobalsecContentCont0),
        mapper: GlobalsecContentMapper,
    })
}

pub struct GlobalsecContentCont0;
type GlobalsecContentCont0Type<'a, 'b> = &'b u64;
type GlobalsecContentCont0SType<'a, 'x> = &'x u64;
type GlobalsecContentCont0Input<'a, 'b, 'x> = POrSType<GlobalsecContentCont0Type<'a, 'b>, GlobalsecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<GlobalsecContentCont0Input<'a, 'b, 'x>> for GlobalsecContentCont0 {
    type Output = RepeatN<GlobalCombinator>;

    open spec fn requires(&self, deps: GlobalsecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: GlobalsecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_globalsec_content_cont0(deps@)
    }

    fn apply(&self, deps: GlobalsecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(global(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(global(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecFuncidxs {
    pub l: u64,
    pub v: Seq<SpecFuncidx>,
}

pub type SpecFuncidxsInner = (u64, Seq<SpecFuncidx>);


impl SpecFrom<SpecFuncidxs> for SpecFuncidxsInner {
    open spec fn spec_from(m: SpecFuncidxs) -> SpecFuncidxsInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecFuncidxsInner> for SpecFuncidxs {
    open spec fn spec_from(m: SpecFuncidxsInner) -> SpecFuncidxs {
        let (l, v) = m;
        SpecFuncidxs { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Funcidxs {
    pub l: u64,
    pub v: RepeatResult<Funcidx>,
}

impl View for Funcidxs {
    type V = SpecFuncidxs;

    open spec fn view(&self) -> Self::V {
        SpecFuncidxs {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type FuncidxsInner = (u64, RepeatResult<Funcidx>);

pub type FuncidxsInnerRef<'a> = (&'a u64, &'a RepeatResult<Funcidx>);
impl<'a> From<&'a Funcidxs> for FuncidxsInnerRef<'a> {
    fn ex_from(m: &'a Funcidxs) -> FuncidxsInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<FuncidxsInner> for Funcidxs {
    fn ex_from(m: FuncidxsInner) -> Funcidxs {
        let (l, v) = m;
        Funcidxs { l, v }
    }
}

pub struct FuncidxsMapper;
impl View for FuncidxsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncidxsMapper {
    type Src = SpecFuncidxsInner;
    type Dst = SpecFuncidxs;
}
impl SpecIsoProof for FuncidxsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FuncidxsMapper {
    type Src = FuncidxsInner;
    type Dst = Funcidxs;
    type RefSrc = FuncidxsInnerRef<'a>;
}

pub struct SpecFuncidxsCombinator(SpecFuncidxsCombinatorAlias);

impl SpecCombinator for SpecFuncidxsCombinator {
    type Type = SpecFuncidxs;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncidxsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncidxsCombinatorAlias::is_prefix_secure() }
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
pub type SpecFuncidxsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecFuncidxCombinator>>, FuncidxsMapper>;

pub struct FuncidxsCombinator(FuncidxsCombinatorAlias);

impl View for FuncidxsCombinator {
    type V = SpecFuncidxsCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncidxsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FuncidxsCombinator {
    type Type = Funcidxs;
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
pub type FuncidxsCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<FuncidxCombinator>, FuncidxsCont0>, FuncidxsMapper>;


pub closed spec fn spec_funcidxs() -> SpecFuncidxsCombinator {
    SpecFuncidxsCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_funcidxs_cont0(deps)),
        mapper: FuncidxsMapper,
    })
}

pub open spec fn spec_funcidxs_cont0(deps: u64) -> RepeatN<SpecFuncidxCombinator> {
    let l = deps;
    RepeatN(spec_funcidx(), l.spec_into())
}

impl View for FuncidxsCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecFuncidxCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_funcidxs_cont0(deps)
        }
    }
}

                
pub fn funcidxs() -> (o: FuncidxsCombinator)
    ensures o@ == spec_funcidxs(),
{
    FuncidxsCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, FuncidxsCont0),
        mapper: FuncidxsMapper,
    })
}

pub struct FuncidxsCont0;
type FuncidxsCont0Type<'a, 'b> = &'b u64;
type FuncidxsCont0SType<'a, 'x> = &'x u64;
type FuncidxsCont0Input<'a, 'b, 'x> = POrSType<FuncidxsCont0Type<'a, 'b>, FuncidxsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<FuncidxsCont0Input<'a, 'b, 'x>> for FuncidxsCont0 {
    type Output = RepeatN<FuncidxCombinator>;

    open spec fn requires(&self, deps: FuncidxsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: FuncidxsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_funcidxs_cont0(deps@)
    }

    fn apply(&self, deps: FuncidxsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(funcidx(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(funcidx(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecParsedElem0 {
    pub e: SpecExpr,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem0Inner = (SpecExpr, SpecFuncidxs);


impl SpecFrom<SpecParsedElem0> for SpecParsedElem0Inner {
    open spec fn spec_from(m: SpecParsedElem0) -> SpecParsedElem0Inner {
        (m.e, m.init)
    }
}

impl SpecFrom<SpecParsedElem0Inner> for SpecParsedElem0 {
    open spec fn spec_from(m: SpecParsedElem0Inner) -> SpecParsedElem0 {
        let (e, init) = m;
        SpecParsedElem0 { e, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem0<'a> {
    pub e: Expr<'a>,
    pub init: Funcidxs,
}

impl View for ParsedElem0<'_> {
    type V = SpecParsedElem0;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem0 {
            e: self.e@,
            init: self.init@,
        }
    }
}
pub type ParsedElem0Inner<'a> = (Expr<'a>, Funcidxs);

pub type ParsedElem0InnerRef<'a> = (&'a Expr<'a>, &'a Funcidxs);
impl<'a> From<&'a ParsedElem0<'a>> for ParsedElem0InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem0) -> ParsedElem0InnerRef<'a> {
        (&m.e, &m.init)
    }
}

impl<'a> From<ParsedElem0Inner<'a>> for ParsedElem0<'a> {
    fn ex_from(m: ParsedElem0Inner) -> ParsedElem0 {
        let (e, init) = m;
        ParsedElem0 { e, init }
    }
}

pub struct ParsedElem0Mapper;
impl View for ParsedElem0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem0Mapper {
    type Src = SpecParsedElem0Inner;
    type Dst = SpecParsedElem0;
}
impl SpecIsoProof for ParsedElem0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem0Mapper {
    type Src = ParsedElem0Inner<'a>;
    type Dst = ParsedElem0<'a>;
    type RefSrc = ParsedElem0InnerRef<'a>;
}

pub struct SpecParsedElem0Combinator(SpecParsedElem0CombinatorAlias);

impl SpecCombinator for SpecParsedElem0Combinator {
    type Type = SpecParsedElem0;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem0Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem0CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem0CombinatorAlias = Mapped<(SpecExprCombinator, SpecFuncidxsCombinator), ParsedElem0Mapper>;

pub struct ParsedElem0Combinator(ParsedElem0CombinatorAlias);

impl View for ParsedElem0Combinator {
    type V = SpecParsedElem0Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem0Combinator {
    type Type = ParsedElem0<'a>;
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
pub type ParsedElem0CombinatorAlias = Mapped<(ExprCombinator, FuncidxsCombinator), ParsedElem0Mapper>;


pub closed spec fn spec_parsed_elem0() -> SpecParsedElem0Combinator {
    SpecParsedElem0Combinator(
    Mapped {
        inner: (spec_expr(), spec_funcidxs()),
        mapper: ParsedElem0Mapper,
    })
}

                
pub fn parsed_elem0() -> (o: ParsedElem0Combinator)
    ensures o@ == spec_parsed_elem0(),
{
    ParsedElem0Combinator(
    Mapped {
        inner: (expr(), funcidxs()),
        mapper: ParsedElem0Mapper,
    })
}

                

pub struct SpecParsedElem1 {
    pub et: SpecELEMKIND,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem1Inner = (SpecELEMKIND, SpecFuncidxs);


impl SpecFrom<SpecParsedElem1> for SpecParsedElem1Inner {
    open spec fn spec_from(m: SpecParsedElem1) -> SpecParsedElem1Inner {
        (m.et, m.init)
    }
}

impl SpecFrom<SpecParsedElem1Inner> for SpecParsedElem1 {
    open spec fn spec_from(m: SpecParsedElem1Inner) -> SpecParsedElem1 {
        let (et, init) = m;
        SpecParsedElem1 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem1 {
    pub et: ELEMKIND,
    pub init: Funcidxs,
}

impl View for ParsedElem1 {
    type V = SpecParsedElem1;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem1 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem1Inner = (ELEMKIND, Funcidxs);

pub type ParsedElem1InnerRef<'a> = (&'a ELEMKIND, &'a Funcidxs);
impl<'a> From<&'a ParsedElem1> for ParsedElem1InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem1) -> ParsedElem1InnerRef<'a> {
        (&m.et, &m.init)
    }
}

impl From<ParsedElem1Inner> for ParsedElem1 {
    fn ex_from(m: ParsedElem1Inner) -> ParsedElem1 {
        let (et, init) = m;
        ParsedElem1 { et, init }
    }
}

pub struct ParsedElem1Mapper;
impl View for ParsedElem1Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem1Mapper {
    type Src = SpecParsedElem1Inner;
    type Dst = SpecParsedElem1;
}
impl SpecIsoProof for ParsedElem1Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem1Mapper {
    type Src = ParsedElem1Inner;
    type Dst = ParsedElem1;
    type RefSrc = ParsedElem1InnerRef<'a>;
}

pub struct SpecParsedElem1Combinator(SpecParsedElem1CombinatorAlias);

impl SpecCombinator for SpecParsedElem1Combinator {
    type Type = SpecParsedElem1;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem1Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem1CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem1CombinatorAlias = Mapped<(SpecELEMKINDCombinator, SpecFuncidxsCombinator), ParsedElem1Mapper>;

pub struct ParsedElem1Combinator(ParsedElem1CombinatorAlias);

impl View for ParsedElem1Combinator {
    type V = SpecParsedElem1Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem1Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem1Combinator {
    type Type = ParsedElem1;
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
pub type ParsedElem1CombinatorAlias = Mapped<(ELEMKINDCombinator, FuncidxsCombinator), ParsedElem1Mapper>;


pub closed spec fn spec_parsed_elem1() -> SpecParsedElem1Combinator {
    SpecParsedElem1Combinator(
    Mapped {
        inner: (spec_ELEMKIND(), spec_funcidxs()),
        mapper: ParsedElem1Mapper,
    })
}

                
pub fn parsed_elem1() -> (o: ParsedElem1Combinator)
    ensures o@ == spec_parsed_elem1(),
{
    ParsedElem1Combinator(
    Mapped {
        inner: (ELEMKIND(), funcidxs()),
        mapper: ParsedElem1Mapper,
    })
}

                

pub struct SpecParsedElem2 {
    pub table: SpecTableidx,
    pub offset: SpecExpr,
    pub et: SpecELEMKIND,
    pub init: SpecFuncidxs,
}

pub type SpecParsedElem2Inner = (SpecTableidx, (SpecExpr, (SpecELEMKIND, SpecFuncidxs)));


impl SpecFrom<SpecParsedElem2> for SpecParsedElem2Inner {
    open spec fn spec_from(m: SpecParsedElem2) -> SpecParsedElem2Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}

impl SpecFrom<SpecParsedElem2Inner> for SpecParsedElem2 {
    open spec fn spec_from(m: SpecParsedElem2Inner) -> SpecParsedElem2 {
        let (table, (offset, (et, init))) = m;
        SpecParsedElem2 { table, offset, et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem2<'a> {
    pub table: Tableidx,
    pub offset: Expr<'a>,
    pub et: ELEMKIND,
    pub init: Funcidxs,
}

impl View for ParsedElem2<'_> {
    type V = SpecParsedElem2;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem2 {
            table: self.table@,
            offset: self.offset@,
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem2Inner<'a> = (Tableidx, (Expr<'a>, (ELEMKIND, Funcidxs)));

pub type ParsedElem2InnerRef<'a> = (&'a Tableidx, (&'a Expr<'a>, (&'a ELEMKIND, &'a Funcidxs)));
impl<'a> From<&'a ParsedElem2<'a>> for ParsedElem2InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem2) -> ParsedElem2InnerRef<'a> {
        (&m.table, (&m.offset, (&m.et, &m.init)))
    }
}

impl<'a> From<ParsedElem2Inner<'a>> for ParsedElem2<'a> {
    fn ex_from(m: ParsedElem2Inner) -> ParsedElem2 {
        let (table, (offset, (et, init))) = m;
        ParsedElem2 { table, offset, et, init }
    }
}

pub struct ParsedElem2Mapper;
impl View for ParsedElem2Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem2Mapper {
    type Src = SpecParsedElem2Inner;
    type Dst = SpecParsedElem2;
}
impl SpecIsoProof for ParsedElem2Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem2Mapper {
    type Src = ParsedElem2Inner<'a>;
    type Dst = ParsedElem2<'a>;
    type RefSrc = ParsedElem2InnerRef<'a>;
}

pub struct SpecParsedElem2Combinator(SpecParsedElem2CombinatorAlias);

impl SpecCombinator for SpecParsedElem2Combinator {
    type Type = SpecParsedElem2;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem2Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem2CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem2CombinatorAlias = Mapped<(SpecTableidxCombinator, (SpecExprCombinator, (SpecELEMKINDCombinator, SpecFuncidxsCombinator))), ParsedElem2Mapper>;

pub struct ParsedElem2Combinator(ParsedElem2CombinatorAlias);

impl View for ParsedElem2Combinator {
    type V = SpecParsedElem2Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem2Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem2Combinator {
    type Type = ParsedElem2<'a>;
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
pub type ParsedElem2CombinatorAlias = Mapped<(TableidxCombinator, (ExprCombinator, (ELEMKINDCombinator, FuncidxsCombinator))), ParsedElem2Mapper>;


pub closed spec fn spec_parsed_elem2() -> SpecParsedElem2Combinator {
    SpecParsedElem2Combinator(
    Mapped {
        inner: (spec_tableidx(), (spec_expr(), (spec_ELEMKIND(), spec_funcidxs()))),
        mapper: ParsedElem2Mapper,
    })
}

                
pub fn parsed_elem2() -> (o: ParsedElem2Combinator)
    ensures o@ == spec_parsed_elem2(),
{
    ParsedElem2Combinator(
    Mapped {
        inner: (tableidx(), (expr(), (ELEMKIND(), funcidxs()))),
        mapper: ParsedElem2Mapper,
    })
}

                
pub type SpecParsedElem3 = SpecParsedElem1;
pub type ParsedElem3 = ParsedElem1;
pub type ParsedElem3Ref<'a> = &'a ParsedElem1;


pub struct SpecParsedElem3Combinator(SpecParsedElem3CombinatorAlias);

impl SpecCombinator for SpecParsedElem3Combinator {
    type Type = SpecParsedElem3;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem3Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem3CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem3CombinatorAlias = SpecParsedElem1Combinator;

pub struct ParsedElem3Combinator(ParsedElem3CombinatorAlias);

impl View for ParsedElem3Combinator {
    type V = SpecParsedElem3Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem3Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem3Combinator {
    type Type = ParsedElem3;
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
pub type ParsedElem3CombinatorAlias = ParsedElem1Combinator;


pub closed spec fn spec_parsed_elem3() -> SpecParsedElem3Combinator {
    SpecParsedElem3Combinator(spec_parsed_elem1())
}

                
pub fn parsed_elem3() -> (o: ParsedElem3Combinator)
    ensures o@ == spec_parsed_elem3(),
{
    ParsedElem3Combinator(parsed_elem1())
}

                

pub struct SpecExprs {
    pub l: u64,
    pub v: Seq<SpecExpr>,
}

pub type SpecExprsInner = (u64, Seq<SpecExpr>);


impl SpecFrom<SpecExprs> for SpecExprsInner {
    open spec fn spec_from(m: SpecExprs) -> SpecExprsInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecExprsInner> for SpecExprs {
    open spec fn spec_from(m: SpecExprsInner) -> SpecExprs {
        let (l, v) = m;
        SpecExprs { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exprs<'a> {
    pub l: u64,
    pub v: RepeatResult<Expr<'a>>,
}

impl View for Exprs<'_> {
    type V = SpecExprs;

    open spec fn view(&self) -> Self::V {
        SpecExprs {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExprsInner<'a> = (u64, RepeatResult<Expr<'a>>);

pub type ExprsInnerRef<'a> = (&'a u64, &'a RepeatResult<Expr<'a>>);
impl<'a> From<&'a Exprs<'a>> for ExprsInnerRef<'a> {
    fn ex_from(m: &'a Exprs) -> ExprsInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<ExprsInner<'a>> for Exprs<'a> {
    fn ex_from(m: ExprsInner) -> Exprs {
        let (l, v) = m;
        Exprs { l, v }
    }
}

pub struct ExprsMapper;
impl View for ExprsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExprsMapper {
    type Src = SpecExprsInner;
    type Dst = SpecExprs;
}
impl SpecIsoProof for ExprsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExprsMapper {
    type Src = ExprsInner<'a>;
    type Dst = Exprs<'a>;
    type RefSrc = ExprsInnerRef<'a>;
}

pub struct SpecExprsCombinator(SpecExprsCombinatorAlias);

impl SpecCombinator for SpecExprsCombinator {
    type Type = SpecExprs;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExprsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExprsCombinatorAlias::is_prefix_secure() }
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
pub type SpecExprsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecExprCombinator>>, ExprsMapper>;

pub struct ExprsCombinator(ExprsCombinatorAlias);

impl View for ExprsCombinator {
    type V = SpecExprsCombinator;
    closed spec fn view(&self) -> Self::V { SpecExprsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExprsCombinator {
    type Type = Exprs<'a>;
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
pub type ExprsCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ExprCombinator>, ExprsCont0>, ExprsMapper>;


pub closed spec fn spec_exprs() -> SpecExprsCombinator {
    SpecExprsCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_exprs_cont0(deps)),
        mapper: ExprsMapper,
    })
}

pub open spec fn spec_exprs_cont0(deps: u64) -> RepeatN<SpecExprCombinator> {
    let l = deps;
    RepeatN(spec_expr(), l.spec_into())
}

impl View for ExprsCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecExprCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_exprs_cont0(deps)
        }
    }
}

                
pub fn exprs() -> (o: ExprsCombinator)
    ensures o@ == spec_exprs(),
{
    ExprsCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ExprsCont0),
        mapper: ExprsMapper,
    })
}

pub struct ExprsCont0;
type ExprsCont0Type<'a, 'b> = &'b u64;
type ExprsCont0SType<'a, 'x> = &'x u64;
type ExprsCont0Input<'a, 'b, 'x> = POrSType<ExprsCont0Type<'a, 'b>, ExprsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ExprsCont0Input<'a, 'b, 'x>> for ExprsCont0 {
    type Output = RepeatN<ExprCombinator>;

    open spec fn requires(&self, deps: ExprsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ExprsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_exprs_cont0(deps@)
    }

    fn apply(&self, deps: ExprsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(expr(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(expr(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecParsedElem4 {
    pub offset: SpecExpr,
    pub init: SpecExprs,
}

pub type SpecParsedElem4Inner = (SpecExpr, SpecExprs);


impl SpecFrom<SpecParsedElem4> for SpecParsedElem4Inner {
    open spec fn spec_from(m: SpecParsedElem4) -> SpecParsedElem4Inner {
        (m.offset, m.init)
    }
}

impl SpecFrom<SpecParsedElem4Inner> for SpecParsedElem4 {
    open spec fn spec_from(m: SpecParsedElem4Inner) -> SpecParsedElem4 {
        let (offset, init) = m;
        SpecParsedElem4 { offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem4<'a> {
    pub offset: Expr<'a>,
    pub init: Exprs<'a>,
}

impl View for ParsedElem4<'_> {
    type V = SpecParsedElem4;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem4 {
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ParsedElem4Inner<'a> = (Expr<'a>, Exprs<'a>);

pub type ParsedElem4InnerRef<'a> = (&'a Expr<'a>, &'a Exprs<'a>);
impl<'a> From<&'a ParsedElem4<'a>> for ParsedElem4InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem4) -> ParsedElem4InnerRef<'a> {
        (&m.offset, &m.init)
    }
}

impl<'a> From<ParsedElem4Inner<'a>> for ParsedElem4<'a> {
    fn ex_from(m: ParsedElem4Inner) -> ParsedElem4 {
        let (offset, init) = m;
        ParsedElem4 { offset, init }
    }
}

pub struct ParsedElem4Mapper;
impl View for ParsedElem4Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem4Mapper {
    type Src = SpecParsedElem4Inner;
    type Dst = SpecParsedElem4;
}
impl SpecIsoProof for ParsedElem4Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem4Mapper {
    type Src = ParsedElem4Inner<'a>;
    type Dst = ParsedElem4<'a>;
    type RefSrc = ParsedElem4InnerRef<'a>;
}

pub struct SpecParsedElem4Combinator(SpecParsedElem4CombinatorAlias);

impl SpecCombinator for SpecParsedElem4Combinator {
    type Type = SpecParsedElem4;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem4Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem4CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem4CombinatorAlias = Mapped<(SpecExprCombinator, SpecExprsCombinator), ParsedElem4Mapper>;

pub struct ParsedElem4Combinator(ParsedElem4CombinatorAlias);

impl View for ParsedElem4Combinator {
    type V = SpecParsedElem4Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem4Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem4Combinator {
    type Type = ParsedElem4<'a>;
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
pub type ParsedElem4CombinatorAlias = Mapped<(ExprCombinator, ExprsCombinator), ParsedElem4Mapper>;


pub closed spec fn spec_parsed_elem4() -> SpecParsedElem4Combinator {
    SpecParsedElem4Combinator(
    Mapped {
        inner: (spec_expr(), spec_exprs()),
        mapper: ParsedElem4Mapper,
    })
}

                
pub fn parsed_elem4() -> (o: ParsedElem4Combinator)
    ensures o@ == spec_parsed_elem4(),
{
    ParsedElem4Combinator(
    Mapped {
        inner: (expr(), exprs()),
        mapper: ParsedElem4Mapper,
    })
}

                

pub struct SpecParsedElem5 {
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem5Inner = (SpecReftype, SpecExprs);


impl SpecFrom<SpecParsedElem5> for SpecParsedElem5Inner {
    open spec fn spec_from(m: SpecParsedElem5) -> SpecParsedElem5Inner {
        (m.et, m.init)
    }
}

impl SpecFrom<SpecParsedElem5Inner> for SpecParsedElem5 {
    open spec fn spec_from(m: SpecParsedElem5Inner) -> SpecParsedElem5 {
        let (et, init) = m;
        SpecParsedElem5 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem5<'a> {
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem5<'_> {
    type V = SpecParsedElem5;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem5 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem5Inner<'a> = (Reftype, Exprs<'a>);

pub type ParsedElem5InnerRef<'a> = (&'a Reftype, &'a Exprs<'a>);
impl<'a> From<&'a ParsedElem5<'a>> for ParsedElem5InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem5) -> ParsedElem5InnerRef<'a> {
        (&m.et, &m.init)
    }
}

impl<'a> From<ParsedElem5Inner<'a>> for ParsedElem5<'a> {
    fn ex_from(m: ParsedElem5Inner) -> ParsedElem5 {
        let (et, init) = m;
        ParsedElem5 { et, init }
    }
}

pub struct ParsedElem5Mapper;
impl View for ParsedElem5Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem5Mapper {
    type Src = SpecParsedElem5Inner;
    type Dst = SpecParsedElem5;
}
impl SpecIsoProof for ParsedElem5Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem5Mapper {
    type Src = ParsedElem5Inner<'a>;
    type Dst = ParsedElem5<'a>;
    type RefSrc = ParsedElem5InnerRef<'a>;
}

pub struct SpecParsedElem5Combinator(SpecParsedElem5CombinatorAlias);

impl SpecCombinator for SpecParsedElem5Combinator {
    type Type = SpecParsedElem5;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem5Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem5CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem5CombinatorAlias = Mapped<(SpecReftypeCombinator, SpecExprsCombinator), ParsedElem5Mapper>;

pub struct ParsedElem5Combinator(ParsedElem5CombinatorAlias);

impl View for ParsedElem5Combinator {
    type V = SpecParsedElem5Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem5Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem5Combinator {
    type Type = ParsedElem5<'a>;
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
pub type ParsedElem5CombinatorAlias = Mapped<(ReftypeCombinator, ExprsCombinator), ParsedElem5Mapper>;


pub closed spec fn spec_parsed_elem5() -> SpecParsedElem5Combinator {
    SpecParsedElem5Combinator(
    Mapped {
        inner: (spec_reftype(), spec_exprs()),
        mapper: ParsedElem5Mapper,
    })
}

                
pub fn parsed_elem5() -> (o: ParsedElem5Combinator)
    ensures o@ == spec_parsed_elem5(),
{
    ParsedElem5Combinator(
    Mapped {
        inner: (reftype(), exprs()),
        mapper: ParsedElem5Mapper,
    })
}

                

pub struct SpecParsedElem6 {
    pub table: SpecTableidx,
    pub offset: SpecExpr,
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem6Inner = (SpecTableidx, (SpecExpr, (SpecReftype, SpecExprs)));


impl SpecFrom<SpecParsedElem6> for SpecParsedElem6Inner {
    open spec fn spec_from(m: SpecParsedElem6) -> SpecParsedElem6Inner {
        (m.table, (m.offset, (m.et, m.init)))
    }
}

impl SpecFrom<SpecParsedElem6Inner> for SpecParsedElem6 {
    open spec fn spec_from(m: SpecParsedElem6Inner) -> SpecParsedElem6 {
        let (table, (offset, (et, init))) = m;
        SpecParsedElem6 { table, offset, et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem6<'a> {
    pub table: Tableidx,
    pub offset: Expr<'a>,
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem6<'_> {
    type V = SpecParsedElem6;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem6 {
            table: self.table@,
            offset: self.offset@,
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem6Inner<'a> = (Tableidx, (Expr<'a>, (Reftype, Exprs<'a>)));

pub type ParsedElem6InnerRef<'a> = (&'a Tableidx, (&'a Expr<'a>, (&'a Reftype, &'a Exprs<'a>)));
impl<'a> From<&'a ParsedElem6<'a>> for ParsedElem6InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem6) -> ParsedElem6InnerRef<'a> {
        (&m.table, (&m.offset, (&m.et, &m.init)))
    }
}

impl<'a> From<ParsedElem6Inner<'a>> for ParsedElem6<'a> {
    fn ex_from(m: ParsedElem6Inner) -> ParsedElem6 {
        let (table, (offset, (et, init))) = m;
        ParsedElem6 { table, offset, et, init }
    }
}

pub struct ParsedElem6Mapper;
impl View for ParsedElem6Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem6Mapper {
    type Src = SpecParsedElem6Inner;
    type Dst = SpecParsedElem6;
}
impl SpecIsoProof for ParsedElem6Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem6Mapper {
    type Src = ParsedElem6Inner<'a>;
    type Dst = ParsedElem6<'a>;
    type RefSrc = ParsedElem6InnerRef<'a>;
}

pub struct SpecParsedElem6Combinator(SpecParsedElem6CombinatorAlias);

impl SpecCombinator for SpecParsedElem6Combinator {
    type Type = SpecParsedElem6;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem6Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem6CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem6CombinatorAlias = Mapped<(SpecTableidxCombinator, (SpecExprCombinator, (SpecReftypeCombinator, SpecExprsCombinator))), ParsedElem6Mapper>;

pub struct ParsedElem6Combinator(ParsedElem6CombinatorAlias);

impl View for ParsedElem6Combinator {
    type V = SpecParsedElem6Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem6Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem6Combinator {
    type Type = ParsedElem6<'a>;
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
pub type ParsedElem6CombinatorAlias = Mapped<(TableidxCombinator, (ExprCombinator, (ReftypeCombinator, ExprsCombinator))), ParsedElem6Mapper>;


pub closed spec fn spec_parsed_elem6() -> SpecParsedElem6Combinator {
    SpecParsedElem6Combinator(
    Mapped {
        inner: (spec_tableidx(), (spec_expr(), (spec_reftype(), spec_exprs()))),
        mapper: ParsedElem6Mapper,
    })
}

                
pub fn parsed_elem6() -> (o: ParsedElem6Combinator)
    ensures o@ == spec_parsed_elem6(),
{
    ParsedElem6Combinator(
    Mapped {
        inner: (tableidx(), (expr(), (reftype(), exprs()))),
        mapper: ParsedElem6Mapper,
    })
}

                

pub struct SpecParsedElem7 {
    pub et: SpecReftype,
    pub init: SpecExprs,
}

pub type SpecParsedElem7Inner = (SpecReftype, SpecExprs);


impl SpecFrom<SpecParsedElem7> for SpecParsedElem7Inner {
    open spec fn spec_from(m: SpecParsedElem7) -> SpecParsedElem7Inner {
        (m.et, m.init)
    }
}

impl SpecFrom<SpecParsedElem7Inner> for SpecParsedElem7 {
    open spec fn spec_from(m: SpecParsedElem7Inner) -> SpecParsedElem7 {
        let (et, init) = m;
        SpecParsedElem7 { et, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ParsedElem7<'a> {
    pub et: Reftype,
    pub init: Exprs<'a>,
}

impl View for ParsedElem7<'_> {
    type V = SpecParsedElem7;

    open spec fn view(&self) -> Self::V {
        SpecParsedElem7 {
            et: self.et@,
            init: self.init@,
        }
    }
}
pub type ParsedElem7Inner<'a> = (Reftype, Exprs<'a>);

pub type ParsedElem7InnerRef<'a> = (&'a Reftype, &'a Exprs<'a>);
impl<'a> From<&'a ParsedElem7<'a>> for ParsedElem7InnerRef<'a> {
    fn ex_from(m: &'a ParsedElem7) -> ParsedElem7InnerRef<'a> {
        (&m.et, &m.init)
    }
}

impl<'a> From<ParsedElem7Inner<'a>> for ParsedElem7<'a> {
    fn ex_from(m: ParsedElem7Inner) -> ParsedElem7 {
        let (et, init) = m;
        ParsedElem7 { et, init }
    }
}

pub struct ParsedElem7Mapper;
impl View for ParsedElem7Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ParsedElem7Mapper {
    type Src = SpecParsedElem7Inner;
    type Dst = SpecParsedElem7;
}
impl SpecIsoProof for ParsedElem7Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ParsedElem7Mapper {
    type Src = ParsedElem7Inner<'a>;
    type Dst = ParsedElem7<'a>;
    type RefSrc = ParsedElem7InnerRef<'a>;
}

pub struct SpecParsedElem7Combinator(SpecParsedElem7CombinatorAlias);

impl SpecCombinator for SpecParsedElem7Combinator {
    type Type = SpecParsedElem7;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecParsedElem7Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecParsedElem7CombinatorAlias::is_prefix_secure() }
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
pub type SpecParsedElem7CombinatorAlias = Mapped<(SpecReftypeCombinator, SpecExprsCombinator), ParsedElem7Mapper>;

pub struct ParsedElem7Combinator(ParsedElem7CombinatorAlias);

impl View for ParsedElem7Combinator {
    type V = SpecParsedElem7Combinator;
    closed spec fn view(&self) -> Self::V { SpecParsedElem7Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ParsedElem7Combinator {
    type Type = ParsedElem7<'a>;
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
pub type ParsedElem7CombinatorAlias = Mapped<(ReftypeCombinator, ExprsCombinator), ParsedElem7Mapper>;


pub closed spec fn spec_parsed_elem7() -> SpecParsedElem7Combinator {
    SpecParsedElem7Combinator(
    Mapped {
        inner: (spec_reftype(), spec_exprs()),
        mapper: ParsedElem7Mapper,
    })
}

                
pub fn parsed_elem7() -> (o: ParsedElem7Combinator)
    ensures o@ == spec_parsed_elem7(),
{
    ParsedElem7Combinator(
    Mapped {
        inner: (reftype(), exprs()),
        mapper: ParsedElem7Mapper,
    })
}

                

pub enum SpecElem {
    Elem0(SpecParsedElem0),
    Elem1(SpecParsedElem1),
    Elem2(SpecParsedElem2),
    Elem3(SpecParsedElem3),
    Elem4(SpecParsedElem4),
    Elem5(SpecParsedElem5),
    Elem6(SpecParsedElem6),
    Elem7(SpecParsedElem7),
}

pub type SpecElemInner = Either<SpecParsedElem0, Either<SpecParsedElem1, Either<SpecParsedElem2, Either<SpecParsedElem3, Either<SpecParsedElem4, Either<SpecParsedElem5, Either<SpecParsedElem6, SpecParsedElem7>>>>>>>;

impl SpecFrom<SpecElem> for SpecElemInner {
    open spec fn spec_from(m: SpecElem) -> SpecElemInner {
        match m {
            SpecElem::Elem0(m) => Either::Left(m),
            SpecElem::Elem1(m) => Either::Right(Either::Left(m)),
            SpecElem::Elem2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecElem::Elem3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecElem::Elem4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecElem::Elem5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecElem::Elem6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecElem::Elem7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

                
impl SpecFrom<SpecElemInner> for SpecElem {
    open spec fn spec_from(m: SpecElemInner) -> SpecElem {
        match m {
            Either::Left(m) => SpecElem::Elem0(m),
            Either::Right(Either::Left(m)) => SpecElem::Elem1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecElem::Elem2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecElem::Elem3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecElem::Elem4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecElem::Elem5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecElem::Elem6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => SpecElem::Elem7(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Elem<'a> {
    Elem0(ParsedElem0<'a>),
    Elem1(ParsedElem1),
    Elem2(ParsedElem2<'a>),
    Elem3(ParsedElem3),
    Elem4(ParsedElem4<'a>),
    Elem5(ParsedElem5<'a>),
    Elem6(ParsedElem6<'a>),
    Elem7(ParsedElem7<'a>),
}

pub type ElemInner<'a> = Either<ParsedElem0<'a>, Either<ParsedElem1, Either<ParsedElem2<'a>, Either<ParsedElem3, Either<ParsedElem4<'a>, Either<ParsedElem5<'a>, Either<ParsedElem6<'a>, ParsedElem7<'a>>>>>>>>;

pub type ElemInnerRef<'a> = Either<&'a ParsedElem0<'a>, Either<&'a ParsedElem1, Either<&'a ParsedElem2<'a>, Either<&'a ParsedElem3, Either<&'a ParsedElem4<'a>, Either<&'a ParsedElem5<'a>, Either<&'a ParsedElem6<'a>, &'a ParsedElem7<'a>>>>>>>>;


impl<'a> View for Elem<'a> {
    type V = SpecElem;
    open spec fn view(&self) -> Self::V {
        match self {
            Elem::Elem0(m) => SpecElem::Elem0(m@),
            Elem::Elem1(m) => SpecElem::Elem1(m@),
            Elem::Elem2(m) => SpecElem::Elem2(m@),
            Elem::Elem3(m) => SpecElem::Elem3(m@),
            Elem::Elem4(m) => SpecElem::Elem4(m@),
            Elem::Elem5(m) => SpecElem::Elem5(m@),
            Elem::Elem6(m) => SpecElem::Elem6(m@),
            Elem::Elem7(m) => SpecElem::Elem7(m@),
        }
    }
}


impl<'a> From<&'a Elem<'a>> for ElemInnerRef<'a> {
    fn ex_from(m: &'a Elem<'a>) -> ElemInnerRef<'a> {
        match m {
            Elem::Elem0(m) => Either::Left(m),
            Elem::Elem1(m) => Either::Right(Either::Left(m)),
            Elem::Elem2(m) => Either::Right(Either::Right(Either::Left(m))),
            Elem::Elem3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            Elem::Elem4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            Elem::Elem5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            Elem::Elem6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            Elem::Elem7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))),
        }
    }

}

impl<'a> From<ElemInner<'a>> for Elem<'a> {
    fn ex_from(m: ElemInner<'a>) -> Elem<'a> {
        match m {
            Either::Left(m) => Elem::Elem0(m),
            Either::Right(Either::Left(m)) => Elem::Elem1(m),
            Either::Right(Either::Right(Either::Left(m))) => Elem::Elem2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => Elem::Elem3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => Elem::Elem4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => Elem::Elem5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => Elem::Elem6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))) => Elem::Elem7(m),
        }
    }
    
}


pub struct ElemMapper;
impl View for ElemMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemMapper {
    type Src = SpecElemInner;
    type Dst = SpecElem;
}
impl SpecIsoProof for ElemMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ElemMapper {
    type Src = ElemInner<'a>;
    type Dst = Elem<'a>;
    type RefSrc = ElemInnerRef<'a>;
}

pub const ELEMELEM0_0_FRONT_CONST: u64 = 0;

pub const ELEMELEM1_0_FRONT_CONST: u64 = 1;

pub const ELEMELEM2_0_FRONT_CONST: u64 = 2;

pub const ELEMELEM3_0_FRONT_CONST: u64 = 3;

pub const ELEMELEM4_0_FRONT_CONST: u64 = 4;

pub const ELEMELEM5_0_FRONT_CONST: u64 = 5;

pub const ELEMELEM6_0_FRONT_CONST: u64 = 6;

pub const ELEMELEM7_0_FRONT_CONST: u64 = 7;


pub struct SpecElemCombinator(SpecElemCombinatorAlias);

impl SpecCombinator for SpecElemCombinator {
    type Type = SpecElem;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem1Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem2Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem3Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem4Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem5Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem6Combinator>, Preceded<Tag<UnsignedLEB128, u64>, SpecParsedElem7Combinator>>>>>>>>, ElemMapper>;









pub struct ElemCombinator(ElemCombinatorAlias);

impl View for ElemCombinator {
    type V = SpecElemCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemCombinator {
    type Type = Elem<'a>;
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
pub type ElemCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem1Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem2Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem3Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem4Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem5Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, ParsedElem6Combinator>, Preceded<Tag<UnsignedLEB128, u64>, ParsedElem7Combinator>>>>>>>>, ElemMapper>;


pub closed spec fn spec_elem() -> SpecElemCombinator {
    SpecElemCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM0_0_FRONT_CONST), spec_parsed_elem0()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM1_0_FRONT_CONST), spec_parsed_elem1()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM2_0_FRONT_CONST), spec_parsed_elem2()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM3_0_FRONT_CONST), spec_parsed_elem3()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM4_0_FRONT_CONST), spec_parsed_elem4()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM5_0_FRONT_CONST), spec_parsed_elem5()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM6_0_FRONT_CONST), spec_parsed_elem6()), Preceded(Tag::spec_new(UnsignedLEB128, ELEMELEM7_0_FRONT_CONST), spec_parsed_elem7())))))))), mapper: ElemMapper })
}

                
pub fn elem() -> (o: ElemCombinator)
    ensures o@ == spec_elem(),
{
    ElemCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM0_0_FRONT_CONST), parsed_elem0()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM1_0_FRONT_CONST), parsed_elem1()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM2_0_FRONT_CONST), parsed_elem2()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM3_0_FRONT_CONST), parsed_elem3()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM4_0_FRONT_CONST), parsed_elem4()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM5_0_FRONT_CONST), parsed_elem5()), Choice::new(Preceded(Tag::new(UnsignedLEB128, ELEMELEM6_0_FRONT_CONST), parsed_elem6()), Preceded(Tag::new(UnsignedLEB128, ELEMELEM7_0_FRONT_CONST), parsed_elem7())))))))), mapper: ElemMapper })
}

                

pub struct SpecElemsecContent {
    pub l: u64,
    pub v: Seq<SpecElem>,
}

pub type SpecElemsecContentInner = (u64, Seq<SpecElem>);


impl SpecFrom<SpecElemsecContent> for SpecElemsecContentInner {
    open spec fn spec_from(m: SpecElemsecContent) -> SpecElemsecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecElemsecContentInner> for SpecElemsecContent {
    open spec fn spec_from(m: SpecElemsecContentInner) -> SpecElemsecContent {
        let (l, v) = m;
        SpecElemsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ElemsecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Elem<'a>>,
}

impl View for ElemsecContent<'_> {
    type V = SpecElemsecContent;

    open spec fn view(&self) -> Self::V {
        SpecElemsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ElemsecContentInner<'a> = (u64, RepeatResult<Elem<'a>>);

pub type ElemsecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Elem<'a>>);
impl<'a> From<&'a ElemsecContent<'a>> for ElemsecContentInnerRef<'a> {
    fn ex_from(m: &'a ElemsecContent) -> ElemsecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<ElemsecContentInner<'a>> for ElemsecContent<'a> {
    fn ex_from(m: ElemsecContentInner) -> ElemsecContent {
        let (l, v) = m;
        ElemsecContent { l, v }
    }
}

pub struct ElemsecContentMapper;
impl View for ElemsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemsecContentMapper {
    type Src = SpecElemsecContentInner;
    type Dst = SpecElemsecContent;
}
impl SpecIsoProof for ElemsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ElemsecContentMapper {
    type Src = ElemsecContentInner<'a>;
    type Dst = ElemsecContent<'a>;
    type RefSrc = ElemsecContentInnerRef<'a>;
}

pub struct SpecElemsecContentCombinator(SpecElemsecContentCombinatorAlias);

impl SpecCombinator for SpecElemsecContentCombinator {
    type Type = SpecElemsecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemsecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecElemCombinator>>, ElemsecContentMapper>;

pub struct ElemsecContentCombinator(ElemsecContentCombinatorAlias);

impl View for ElemsecContentCombinator {
    type V = SpecElemsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemsecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemsecContentCombinator {
    type Type = ElemsecContent<'a>;
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
pub type ElemsecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ElemCombinator>, ElemsecContentCont0>, ElemsecContentMapper>;


pub closed spec fn spec_elemsec_content() -> SpecElemsecContentCombinator {
    SpecElemsecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_elemsec_content_cont0(deps)),
        mapper: ElemsecContentMapper,
    })
}

pub open spec fn spec_elemsec_content_cont0(deps: u64) -> RepeatN<SpecElemCombinator> {
    let l = deps;
    RepeatN(spec_elem(), l.spec_into())
}

impl View for ElemsecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecElemCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_elemsec_content_cont0(deps)
        }
    }
}

                
pub fn elemsec_content() -> (o: ElemsecContentCombinator)
    ensures o@ == spec_elemsec_content(),
{
    ElemsecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ElemsecContentCont0),
        mapper: ElemsecContentMapper,
    })
}

pub struct ElemsecContentCont0;
type ElemsecContentCont0Type<'a, 'b> = &'b u64;
type ElemsecContentCont0SType<'a, 'x> = &'x u64;
type ElemsecContentCont0Input<'a, 'b, 'x> = POrSType<ElemsecContentCont0Type<'a, 'b>, ElemsecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ElemsecContentCont0Input<'a, 'b, 'x>> for ElemsecContentCont0 {
    type Output = RepeatN<ElemCombinator>;

    open spec fn requires(&self, deps: ElemsecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ElemsecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_elemsec_content_cont0(deps@)
    }

    fn apply(&self, deps: ElemsecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(elem(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(elem(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecLimitMin {
    pub min: u64,
}

pub type SpecLimitMinInner = u64;


impl SpecFrom<SpecLimitMin> for SpecLimitMinInner {
    open spec fn spec_from(m: SpecLimitMin) -> SpecLimitMinInner {
        m.min
    }
}

impl SpecFrom<SpecLimitMinInner> for SpecLimitMin {
    open spec fn spec_from(m: SpecLimitMinInner) -> SpecLimitMin {
        let min = m;
        SpecLimitMin { min }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LimitMin {
    pub min: u64,
}

impl View for LimitMin {
    type V = SpecLimitMin;

    open spec fn view(&self) -> Self::V {
        SpecLimitMin {
            min: self.min@,
        }
    }
}
pub type LimitMinInner = u64;

pub type LimitMinInnerRef<'a> = &'a u64;
impl<'a> From<&'a LimitMin> for LimitMinInnerRef<'a> {
    fn ex_from(m: &'a LimitMin) -> LimitMinInnerRef<'a> {
        &m.min
    }
}

impl From<LimitMinInner> for LimitMin {
    fn ex_from(m: LimitMinInner) -> LimitMin {
        let min = m;
        LimitMin { min }
    }
}

pub struct LimitMinMapper;
impl View for LimitMinMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitMinMapper {
    type Src = SpecLimitMinInner;
    type Dst = SpecLimitMin;
}
impl SpecIsoProof for LimitMinMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LimitMinMapper {
    type Src = LimitMinInner;
    type Dst = LimitMin;
    type RefSrc = LimitMinInnerRef<'a>;
}

pub struct SpecLimitMinCombinator(SpecLimitMinCombinatorAlias);

impl SpecCombinator for SpecLimitMinCombinator {
    type Type = SpecLimitMin;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitMinCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitMinCombinatorAlias::is_prefix_secure() }
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
pub type SpecLimitMinCombinatorAlias = Mapped<UnsignedLEB128, LimitMinMapper>;

pub struct LimitMinCombinator(LimitMinCombinatorAlias);

impl View for LimitMinCombinator {
    type V = SpecLimitMinCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitMinCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LimitMinCombinator {
    type Type = LimitMin;
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
pub type LimitMinCombinatorAlias = Mapped<UnsignedLEB128, LimitMinMapper>;


pub closed spec fn spec_limit_min() -> SpecLimitMinCombinator {
    SpecLimitMinCombinator(
    Mapped {
        inner: UnsignedLEB128,
        mapper: LimitMinMapper,
    })
}

                
pub fn limit_min() -> (o: LimitMinCombinator)
    ensures o@ == spec_limit_min(),
{
    LimitMinCombinator(
    Mapped {
        inner: UnsignedLEB128,
        mapper: LimitMinMapper,
    })
}

                

pub struct SpecLimitMinMax {
    pub min: u64,
    pub max: u64,
}

pub type SpecLimitMinMaxInner = (u64, u64);


impl SpecFrom<SpecLimitMinMax> for SpecLimitMinMaxInner {
    open spec fn spec_from(m: SpecLimitMinMax) -> SpecLimitMinMaxInner {
        (m.min, m.max)
    }
}

impl SpecFrom<SpecLimitMinMaxInner> for SpecLimitMinMax {
    open spec fn spec_from(m: SpecLimitMinMaxInner) -> SpecLimitMinMax {
        let (min, max) = m;
        SpecLimitMinMax { min, max }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LimitMinMax {
    pub min: u64,
    pub max: u64,
}

impl View for LimitMinMax {
    type V = SpecLimitMinMax;

    open spec fn view(&self) -> Self::V {
        SpecLimitMinMax {
            min: self.min@,
            max: self.max@,
        }
    }
}
pub type LimitMinMaxInner = (u64, u64);

pub type LimitMinMaxInnerRef<'a> = (&'a u64, &'a u64);
impl<'a> From<&'a LimitMinMax> for LimitMinMaxInnerRef<'a> {
    fn ex_from(m: &'a LimitMinMax) -> LimitMinMaxInnerRef<'a> {
        (&m.min, &m.max)
    }
}

impl From<LimitMinMaxInner> for LimitMinMax {
    fn ex_from(m: LimitMinMaxInner) -> LimitMinMax {
        let (min, max) = m;
        LimitMinMax { min, max }
    }
}

pub struct LimitMinMaxMapper;
impl View for LimitMinMaxMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitMinMaxMapper {
    type Src = SpecLimitMinMaxInner;
    type Dst = SpecLimitMinMax;
}
impl SpecIsoProof for LimitMinMaxMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LimitMinMaxMapper {
    type Src = LimitMinMaxInner;
    type Dst = LimitMinMax;
    type RefSrc = LimitMinMaxInnerRef<'a>;
}

pub struct SpecLimitMinMaxCombinator(SpecLimitMinMaxCombinatorAlias);

impl SpecCombinator for SpecLimitMinMaxCombinator {
    type Type = SpecLimitMinMax;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitMinMaxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitMinMaxCombinatorAlias::is_prefix_secure() }
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
pub type SpecLimitMinMaxCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), LimitMinMaxMapper>;

pub struct LimitMinMaxCombinator(LimitMinMaxCombinatorAlias);

impl View for LimitMinMaxCombinator {
    type V = SpecLimitMinMaxCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitMinMaxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LimitMinMaxCombinator {
    type Type = LimitMinMax;
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
pub type LimitMinMaxCombinatorAlias = Mapped<(UnsignedLEB128, UnsignedLEB128), LimitMinMaxMapper>;


pub closed spec fn spec_limit_min_max() -> SpecLimitMinMaxCombinator {
    SpecLimitMinMaxCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: LimitMinMaxMapper,
    })
}

                
pub fn limit_min_max() -> (o: LimitMinMaxCombinator)
    ensures o@ == spec_limit_min_max(),
{
    LimitMinMaxCombinator(
    Mapped {
        inner: (UnsignedLEB128, UnsignedLEB128),
        mapper: LimitMinMaxMapper,
    })
}

                

pub enum SpecLimits {
    NoMax(SpecLimitMin),
    Max(SpecLimitMinMax),
}

pub type SpecLimitsInner = Either<SpecLimitMin, SpecLimitMinMax>;

impl SpecFrom<SpecLimits> for SpecLimitsInner {
    open spec fn spec_from(m: SpecLimits) -> SpecLimitsInner {
        match m {
            SpecLimits::NoMax(m) => Either::Left(m),
            SpecLimits::Max(m) => Either::Right(m),
        }
    }

}

                
impl SpecFrom<SpecLimitsInner> for SpecLimits {
    open spec fn spec_from(m: SpecLimitsInner) -> SpecLimits {
        match m {
            Either::Left(m) => SpecLimits::NoMax(m),
            Either::Right(m) => SpecLimits::Max(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Limits {
    NoMax(LimitMin),
    Max(LimitMinMax),
}

pub type LimitsInner = Either<LimitMin, LimitMinMax>;

pub type LimitsInnerRef<'a> = Either<&'a LimitMin, &'a LimitMinMax>;


impl View for Limits {
    type V = SpecLimits;
    open spec fn view(&self) -> Self::V {
        match self {
            Limits::NoMax(m) => SpecLimits::NoMax(m@),
            Limits::Max(m) => SpecLimits::Max(m@),
        }
    }
}


impl<'a> From<&'a Limits> for LimitsInnerRef<'a> {
    fn ex_from(m: &'a Limits) -> LimitsInnerRef<'a> {
        match m {
            Limits::NoMax(m) => Either::Left(m),
            Limits::Max(m) => Either::Right(m),
        }
    }

}

impl From<LimitsInner> for Limits {
    fn ex_from(m: LimitsInner) -> Limits {
        match m {
            Either::Left(m) => Limits::NoMax(m),
            Either::Right(m) => Limits::Max(m),
        }
    }
    
}


pub struct LimitsMapper;
impl View for LimitsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LimitsMapper {
    type Src = SpecLimitsInner;
    type Dst = SpecLimits;
}
impl SpecIsoProof for LimitsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LimitsMapper {
    type Src = LimitsInner;
    type Dst = Limits;
    type RefSrc = LimitsInnerRef<'a>;
}

pub const LIMITSNOMAX_0_FRONT_CONST: u8 = 0;

pub const LIMITSMAX_0_FRONT_CONST: u8 = 1;


pub struct SpecLimitsCombinator(SpecLimitsCombinatorAlias);

impl SpecCombinator for SpecLimitsCombinator {
    type Type = SpecLimits;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLimitsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLimitsCombinatorAlias::is_prefix_secure() }
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
pub type SpecLimitsCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecLimitMinCombinator>, Preceded<Tag<U8, u8>, SpecLimitMinMaxCombinator>>, LimitsMapper>;



pub struct LimitsCombinator(LimitsCombinatorAlias);

impl View for LimitsCombinator {
    type V = SpecLimitsCombinator;
    closed spec fn view(&self) -> Self::V { SpecLimitsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LimitsCombinator {
    type Type = Limits;
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
pub type LimitsCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, LimitMinCombinator>, Preceded<Tag<U8, u8>, LimitMinMaxCombinator>>, LimitsMapper>;


pub closed spec fn spec_limits() -> SpecLimitsCombinator {
    SpecLimitsCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, LIMITSNOMAX_0_FRONT_CONST), spec_limit_min()), Preceded(Tag::spec_new(U8, LIMITSMAX_0_FRONT_CONST), spec_limit_min_max())), mapper: LimitsMapper })
}

                
pub fn limits() -> (o: LimitsCombinator)
    ensures o@ == spec_limits(),
{
    LimitsCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, LIMITSNOMAX_0_FRONT_CONST), limit_min()), Preceded(Tag::new(U8, LIMITSMAX_0_FRONT_CONST), limit_min_max())), mapper: LimitsMapper })
}

                

pub struct SpecTabletype {
    pub elemtype: SpecReftype,
    pub limits: SpecLimits,
}

pub type SpecTabletypeInner = (SpecReftype, SpecLimits);


impl SpecFrom<SpecTabletype> for SpecTabletypeInner {
    open spec fn spec_from(m: SpecTabletype) -> SpecTabletypeInner {
        (m.elemtype, m.limits)
    }
}

impl SpecFrom<SpecTabletypeInner> for SpecTabletype {
    open spec fn spec_from(m: SpecTabletypeInner) -> SpecTabletype {
        let (elemtype, limits) = m;
        SpecTabletype { elemtype, limits }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tabletype {
    pub elemtype: Reftype,
    pub limits: Limits,
}

impl View for Tabletype {
    type V = SpecTabletype;

    open spec fn view(&self) -> Self::V {
        SpecTabletype {
            elemtype: self.elemtype@,
            limits: self.limits@,
        }
    }
}
pub type TabletypeInner = (Reftype, Limits);

pub type TabletypeInnerRef<'a> = (&'a Reftype, &'a Limits);
impl<'a> From<&'a Tabletype> for TabletypeInnerRef<'a> {
    fn ex_from(m: &'a Tabletype) -> TabletypeInnerRef<'a> {
        (&m.elemtype, &m.limits)
    }
}

impl From<TabletypeInner> for Tabletype {
    fn ex_from(m: TabletypeInner) -> Tabletype {
        let (elemtype, limits) = m;
        Tabletype { elemtype, limits }
    }
}

pub struct TabletypeMapper;
impl View for TabletypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TabletypeMapper {
    type Src = SpecTabletypeInner;
    type Dst = SpecTabletype;
}
impl SpecIsoProof for TabletypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TabletypeMapper {
    type Src = TabletypeInner;
    type Dst = Tabletype;
    type RefSrc = TabletypeInnerRef<'a>;
}

pub struct SpecTabletypeCombinator(SpecTabletypeCombinatorAlias);

impl SpecCombinator for SpecTabletypeCombinator {
    type Type = SpecTabletype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTabletypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTabletypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecTabletypeCombinatorAlias = Mapped<(SpecReftypeCombinator, SpecLimitsCombinator), TabletypeMapper>;

pub struct TabletypeCombinator(TabletypeCombinatorAlias);

impl View for TabletypeCombinator {
    type V = SpecTabletypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecTabletypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TabletypeCombinator {
    type Type = Tabletype;
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
pub type TabletypeCombinatorAlias = Mapped<(ReftypeCombinator, LimitsCombinator), TabletypeMapper>;


pub closed spec fn spec_tabletype() -> SpecTabletypeCombinator {
    SpecTabletypeCombinator(
    Mapped {
        inner: (spec_reftype(), spec_limits()),
        mapper: TabletypeMapper,
    })
}

                
pub fn tabletype() -> (o: TabletypeCombinator)
    ensures o@ == spec_tabletype(),
{
    TabletypeCombinator(
    Mapped {
        inner: (reftype(), limits()),
        mapper: TabletypeMapper,
    })
}

                

pub struct SpecTable {
    pub ty: SpecTabletype,
}

pub type SpecTableInner = SpecTabletype;


impl SpecFrom<SpecTable> for SpecTableInner {
    open spec fn spec_from(m: SpecTable) -> SpecTableInner {
        m.ty
    }
}

impl SpecFrom<SpecTableInner> for SpecTable {
    open spec fn spec_from(m: SpecTableInner) -> SpecTable {
        let ty = m;
        SpecTable { ty }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Table {
    pub ty: Tabletype,
}

impl View for Table {
    type V = SpecTable;

    open spec fn view(&self) -> Self::V {
        SpecTable {
            ty: self.ty@,
        }
    }
}
pub type TableInner = Tabletype;

pub type TableInnerRef<'a> = &'a Tabletype;
impl<'a> From<&'a Table> for TableInnerRef<'a> {
    fn ex_from(m: &'a Table) -> TableInnerRef<'a> {
        &m.ty
    }
}

impl From<TableInner> for Table {
    fn ex_from(m: TableInner) -> Table {
        let ty = m;
        Table { ty }
    }
}

pub struct TableMapper;
impl View for TableMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TableMapper {
    type Src = SpecTableInner;
    type Dst = SpecTable;
}
impl SpecIsoProof for TableMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TableMapper {
    type Src = TableInner;
    type Dst = Table;
    type RefSrc = TableInnerRef<'a>;
}

pub struct SpecTableCombinator(SpecTableCombinatorAlias);

impl SpecCombinator for SpecTableCombinator {
    type Type = SpecTable;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTableCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTableCombinatorAlias::is_prefix_secure() }
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
pub type SpecTableCombinatorAlias = Mapped<SpecTabletypeCombinator, TableMapper>;

pub struct TableCombinator(TableCombinatorAlias);

impl View for TableCombinator {
    type V = SpecTableCombinator;
    closed spec fn view(&self) -> Self::V { SpecTableCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TableCombinator {
    type Type = Table;
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
pub type TableCombinatorAlias = Mapped<TabletypeCombinator, TableMapper>;


pub closed spec fn spec_table() -> SpecTableCombinator {
    SpecTableCombinator(
    Mapped {
        inner: spec_tabletype(),
        mapper: TableMapper,
    })
}

                
pub fn table() -> (o: TableCombinator)
    ensures o@ == spec_table(),
{
    TableCombinator(
    Mapped {
        inner: tabletype(),
        mapper: TableMapper,
    })
}

                

pub struct SpecTablesecContent {
    pub l: u64,
    pub v: Seq<SpecTable>,
}

pub type SpecTablesecContentInner = (u64, Seq<SpecTable>);


impl SpecFrom<SpecTablesecContent> for SpecTablesecContentInner {
    open spec fn spec_from(m: SpecTablesecContent) -> SpecTablesecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecTablesecContentInner> for SpecTablesecContent {
    open spec fn spec_from(m: SpecTablesecContentInner) -> SpecTablesecContent {
        let (l, v) = m;
        SpecTablesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TablesecContent {
    pub l: u64,
    pub v: RepeatResult<Table>,
}

impl View for TablesecContent {
    type V = SpecTablesecContent;

    open spec fn view(&self) -> Self::V {
        SpecTablesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type TablesecContentInner = (u64, RepeatResult<Table>);

pub type TablesecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Table>);
impl<'a> From<&'a TablesecContent> for TablesecContentInnerRef<'a> {
    fn ex_from(m: &'a TablesecContent) -> TablesecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<TablesecContentInner> for TablesecContent {
    fn ex_from(m: TablesecContentInner) -> TablesecContent {
        let (l, v) = m;
        TablesecContent { l, v }
    }
}

pub struct TablesecContentMapper;
impl View for TablesecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TablesecContentMapper {
    type Src = SpecTablesecContentInner;
    type Dst = SpecTablesecContent;
}
impl SpecIsoProof for TablesecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TablesecContentMapper {
    type Src = TablesecContentInner;
    type Dst = TablesecContent;
    type RefSrc = TablesecContentInnerRef<'a>;
}

pub struct SpecTablesecContentCombinator(SpecTablesecContentCombinatorAlias);

impl SpecCombinator for SpecTablesecContentCombinator {
    type Type = SpecTablesecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTablesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTablesecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecTablesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecTableCombinator>>, TablesecContentMapper>;

pub struct TablesecContentCombinator(TablesecContentCombinatorAlias);

impl View for TablesecContentCombinator {
    type V = SpecTablesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecTablesecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TablesecContentCombinator {
    type Type = TablesecContent;
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
pub type TablesecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<TableCombinator>, TablesecContentCont0>, TablesecContentMapper>;


pub closed spec fn spec_tablesec_content() -> SpecTablesecContentCombinator {
    SpecTablesecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_tablesec_content_cont0(deps)),
        mapper: TablesecContentMapper,
    })
}

pub open spec fn spec_tablesec_content_cont0(deps: u64) -> RepeatN<SpecTableCombinator> {
    let l = deps;
    RepeatN(spec_table(), l.spec_into())
}

impl View for TablesecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecTableCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_tablesec_content_cont0(deps)
        }
    }
}

                
pub fn tablesec_content() -> (o: TablesecContentCombinator)
    ensures o@ == spec_tablesec_content(),
{
    TablesecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, TablesecContentCont0),
        mapper: TablesecContentMapper,
    })
}

pub struct TablesecContentCont0;
type TablesecContentCont0Type<'a, 'b> = &'b u64;
type TablesecContentCont0SType<'a, 'x> = &'x u64;
type TablesecContentCont0Input<'a, 'b, 'x> = POrSType<TablesecContentCont0Type<'a, 'b>, TablesecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TablesecContentCont0Input<'a, 'b, 'x>> for TablesecContentCont0 {
    type Output = RepeatN<TableCombinator>;

    open spec fn requires(&self, deps: TablesecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TablesecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tablesec_content_cont0(deps@)
    }

    fn apply(&self, deps: TablesecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(table(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(table(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecLocalCompressed {
    pub count: u64,
    pub vt: SpecValtype,
}

pub type SpecLocalCompressedInner = (u64, SpecValtype);


impl SpecFrom<SpecLocalCompressed> for SpecLocalCompressedInner {
    open spec fn spec_from(m: SpecLocalCompressed) -> SpecLocalCompressedInner {
        (m.count, m.vt)
    }
}

impl SpecFrom<SpecLocalCompressedInner> for SpecLocalCompressed {
    open spec fn spec_from(m: SpecLocalCompressedInner) -> SpecLocalCompressed {
        let (count, vt) = m;
        SpecLocalCompressed { count, vt }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct LocalCompressed {
    pub count: u64,
    pub vt: Valtype,
}

impl View for LocalCompressed {
    type V = SpecLocalCompressed;

    open spec fn view(&self) -> Self::V {
        SpecLocalCompressed {
            count: self.count@,
            vt: self.vt@,
        }
    }
}
pub type LocalCompressedInner = (u64, Valtype);

pub type LocalCompressedInnerRef<'a> = (&'a u64, &'a Valtype);
impl<'a> From<&'a LocalCompressed> for LocalCompressedInnerRef<'a> {
    fn ex_from(m: &'a LocalCompressed) -> LocalCompressedInnerRef<'a> {
        (&m.count, &m.vt)
    }
}

impl From<LocalCompressedInner> for LocalCompressed {
    fn ex_from(m: LocalCompressedInner) -> LocalCompressed {
        let (count, vt) = m;
        LocalCompressed { count, vt }
    }
}

pub struct LocalCompressedMapper;
impl View for LocalCompressedMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LocalCompressedMapper {
    type Src = SpecLocalCompressedInner;
    type Dst = SpecLocalCompressed;
}
impl SpecIsoProof for LocalCompressedMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LocalCompressedMapper {
    type Src = LocalCompressedInner;
    type Dst = LocalCompressed;
    type RefSrc = LocalCompressedInnerRef<'a>;
}

pub struct SpecLocalCompressedCombinator(SpecLocalCompressedCombinatorAlias);

impl SpecCombinator for SpecLocalCompressedCombinator {
    type Type = SpecLocalCompressed;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalCompressedCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalCompressedCombinatorAlias::is_prefix_secure() }
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
pub type SpecLocalCompressedCombinatorAlias = Mapped<(UnsignedLEB128, SpecValtypeCombinator), LocalCompressedMapper>;

pub struct LocalCompressedCombinator(LocalCompressedCombinatorAlias);

impl View for LocalCompressedCombinator {
    type V = SpecLocalCompressedCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalCompressedCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LocalCompressedCombinator {
    type Type = LocalCompressed;
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
pub type LocalCompressedCombinatorAlias = Mapped<(UnsignedLEB128, ValtypeCombinator), LocalCompressedMapper>;


pub closed spec fn spec_local_compressed() -> SpecLocalCompressedCombinator {
    SpecLocalCompressedCombinator(
    Mapped {
        inner: (UnsignedLEB128, spec_valtype()),
        mapper: LocalCompressedMapper,
    })
}

                
pub fn local_compressed() -> (o: LocalCompressedCombinator)
    ensures o@ == spec_local_compressed(),
{
    LocalCompressedCombinator(
    Mapped {
        inner: (UnsignedLEB128, valtype()),
        mapper: LocalCompressedMapper,
    })
}

                

pub struct SpecLocals {
    pub l: u64,
    pub v: Seq<SpecLocalCompressed>,
}

pub type SpecLocalsInner = (u64, Seq<SpecLocalCompressed>);


impl SpecFrom<SpecLocals> for SpecLocalsInner {
    open spec fn spec_from(m: SpecLocals) -> SpecLocalsInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecLocalsInner> for SpecLocals {
    open spec fn spec_from(m: SpecLocalsInner) -> SpecLocals {
        let (l, v) = m;
        SpecLocals { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Locals {
    pub l: u64,
    pub v: RepeatResult<LocalCompressed>,
}

impl View for Locals {
    type V = SpecLocals;

    open spec fn view(&self) -> Self::V {
        SpecLocals {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type LocalsInner = (u64, RepeatResult<LocalCompressed>);

pub type LocalsInnerRef<'a> = (&'a u64, &'a RepeatResult<LocalCompressed>);
impl<'a> From<&'a Locals> for LocalsInnerRef<'a> {
    fn ex_from(m: &'a Locals) -> LocalsInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<LocalsInner> for Locals {
    fn ex_from(m: LocalsInner) -> Locals {
        let (l, v) = m;
        Locals { l, v }
    }
}

pub struct LocalsMapper;
impl View for LocalsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for LocalsMapper {
    type Src = SpecLocalsInner;
    type Dst = SpecLocals;
}
impl SpecIsoProof for LocalsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for LocalsMapper {
    type Src = LocalsInner;
    type Dst = Locals;
    type RefSrc = LocalsInnerRef<'a>;
}

pub struct SpecLocalsCombinator(SpecLocalsCombinatorAlias);

impl SpecCombinator for SpecLocalsCombinator {
    type Type = SpecLocals;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecLocalsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecLocalsCombinatorAlias::is_prefix_secure() }
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
pub type SpecLocalsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecLocalCompressedCombinator>>, LocalsMapper>;

pub struct LocalsCombinator(LocalsCombinatorAlias);

impl View for LocalsCombinator {
    type V = SpecLocalsCombinator;
    closed spec fn view(&self) -> Self::V { SpecLocalsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for LocalsCombinator {
    type Type = Locals;
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
pub type LocalsCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<LocalCompressedCombinator>, LocalsCont0>, LocalsMapper>;


pub closed spec fn spec_locals() -> SpecLocalsCombinator {
    SpecLocalsCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_locals_cont0(deps)),
        mapper: LocalsMapper,
    })
}

pub open spec fn spec_locals_cont0(deps: u64) -> RepeatN<SpecLocalCompressedCombinator> {
    let l = deps;
    RepeatN(spec_local_compressed(), l.spec_into())
}

impl View for LocalsCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecLocalCompressedCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_locals_cont0(deps)
        }
    }
}

                
pub fn locals() -> (o: LocalsCombinator)
    ensures o@ == spec_locals(),
{
    LocalsCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, LocalsCont0),
        mapper: LocalsMapper,
    })
}

pub struct LocalsCont0;
type LocalsCont0Type<'a, 'b> = &'b u64;
type LocalsCont0SType<'a, 'x> = &'x u64;
type LocalsCont0Input<'a, 'b, 'x> = POrSType<LocalsCont0Type<'a, 'b>, LocalsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<LocalsCont0Input<'a, 'b, 'x>> for LocalsCont0 {
    type Output = RepeatN<LocalCompressedCombinator>;

    open spec fn requires(&self, deps: LocalsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: LocalsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_locals_cont0(deps@)
    }

    fn apply(&self, deps: LocalsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(local_compressed(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(local_compressed(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecFunc {
    pub locals: SpecLocals,
    pub body: SpecExpr,
}

pub type SpecFuncInner = (SpecLocals, SpecExpr);


impl SpecFrom<SpecFunc> for SpecFuncInner {
    open spec fn spec_from(m: SpecFunc) -> SpecFuncInner {
        (m.locals, m.body)
    }
}

impl SpecFrom<SpecFuncInner> for SpecFunc {
    open spec fn spec_from(m: SpecFuncInner) -> SpecFunc {
        let (locals, body) = m;
        SpecFunc { locals, body }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Func<'a> {
    pub locals: Locals,
    pub body: Expr<'a>,
}

impl View for Func<'_> {
    type V = SpecFunc;

    open spec fn view(&self) -> Self::V {
        SpecFunc {
            locals: self.locals@,
            body: self.body@,
        }
    }
}
pub type FuncInner<'a> = (Locals, Expr<'a>);

pub type FuncInnerRef<'a> = (&'a Locals, &'a Expr<'a>);
impl<'a> From<&'a Func<'a>> for FuncInnerRef<'a> {
    fn ex_from(m: &'a Func) -> FuncInnerRef<'a> {
        (&m.locals, &m.body)
    }
}

impl<'a> From<FuncInner<'a>> for Func<'a> {
    fn ex_from(m: FuncInner) -> Func {
        let (locals, body) = m;
        Func { locals, body }
    }
}

pub struct FuncMapper;
impl View for FuncMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncMapper {
    type Src = SpecFuncInner;
    type Dst = SpecFunc;
}
impl SpecIsoProof for FuncMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FuncMapper {
    type Src = FuncInner<'a>;
    type Dst = Func<'a>;
    type RefSrc = FuncInnerRef<'a>;
}

pub struct SpecFuncCombinator(SpecFuncCombinatorAlias);

impl SpecCombinator for SpecFuncCombinator {
    type Type = SpecFunc;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncCombinatorAlias::is_prefix_secure() }
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
pub type SpecFuncCombinatorAlias = Mapped<(SpecLocalsCombinator, SpecExprCombinator), FuncMapper>;

pub struct FuncCombinator(FuncCombinatorAlias);

impl View for FuncCombinator {
    type V = SpecFuncCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FuncCombinator {
    type Type = Func<'a>;
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
pub type FuncCombinatorAlias = Mapped<(LocalsCombinator, ExprCombinator), FuncMapper>;


pub closed spec fn spec_func() -> SpecFuncCombinator {
    SpecFuncCombinator(
    Mapped {
        inner: (spec_locals(), spec_expr()),
        mapper: FuncMapper,
    })
}

                
pub fn func() -> (o: FuncCombinator)
    ensures o@ == spec_func(),
{
    FuncCombinator(
    Mapped {
        inner: (locals(), expr()),
        mapper: FuncMapper,
    })
}

                

pub struct SpecByteVec {
    pub l: u64,
    pub v: Seq<u8>,
}

pub type SpecByteVecInner = (u64, Seq<u8>);


impl SpecFrom<SpecByteVec> for SpecByteVecInner {
    open spec fn spec_from(m: SpecByteVec) -> SpecByteVecInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecByteVecInner> for SpecByteVec {
    open spec fn spec_from(m: SpecByteVecInner) -> SpecByteVec {
        let (l, v) = m;
        SpecByteVec { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ByteVec {
    pub l: u64,
    pub v: RepeatResult<u8>,
}

impl View for ByteVec {
    type V = SpecByteVec;

    open spec fn view(&self) -> Self::V {
        SpecByteVec {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ByteVecInner = (u64, RepeatResult<u8>);

pub type ByteVecInnerRef<'a> = (&'a u64, &'a RepeatResult<u8>);
impl<'a> From<&'a ByteVec> for ByteVecInnerRef<'a> {
    fn ex_from(m: &'a ByteVec) -> ByteVecInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<ByteVecInner> for ByteVec {
    fn ex_from(m: ByteVecInner) -> ByteVec {
        let (l, v) = m;
        ByteVec { l, v }
    }
}

pub struct ByteVecMapper;
impl View for ByteVecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ByteVecMapper {
    type Src = SpecByteVecInner;
    type Dst = SpecByteVec;
}
impl SpecIsoProof for ByteVecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ByteVecMapper {
    type Src = ByteVecInner;
    type Dst = ByteVec;
    type RefSrc = ByteVecInnerRef<'a>;
}

pub struct SpecByteVecCombinator(SpecByteVecCombinatorAlias);

impl SpecCombinator for SpecByteVecCombinator {
    type Type = SpecByteVec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecByteVecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecByteVecCombinatorAlias::is_prefix_secure() }
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
pub type SpecByteVecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<U8>>, ByteVecMapper>;

pub struct ByteVecCombinator(ByteVecCombinatorAlias);

impl View for ByteVecCombinator {
    type V = SpecByteVecCombinator;
    closed spec fn view(&self) -> Self::V { SpecByteVecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ByteVecCombinator {
    type Type = ByteVec;
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
pub type ByteVecCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<U8>, ByteVecCont0>, ByteVecMapper>;


pub closed spec fn spec_byte_vec() -> SpecByteVecCombinator {
    SpecByteVecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_byte_vec_cont0(deps)),
        mapper: ByteVecMapper,
    })
}

pub open spec fn spec_byte_vec_cont0(deps: u64) -> RepeatN<U8> {
    let l = deps;
    RepeatN(U8, l.spec_into())
}

impl View for ByteVecCont0 {
    type V = spec_fn(u64) -> RepeatN<U8>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_byte_vec_cont0(deps)
        }
    }
}

                
pub fn byte_vec() -> (o: ByteVecCombinator)
    ensures o@ == spec_byte_vec(),
{
    ByteVecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ByteVecCont0),
        mapper: ByteVecMapper,
    })
}

pub struct ByteVecCont0;
type ByteVecCont0Type<'a, 'b> = &'b u64;
type ByteVecCont0SType<'a, 'x> = &'x u64;
type ByteVecCont0Input<'a, 'b, 'x> = POrSType<ByteVecCont0Type<'a, 'b>, ByteVecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ByteVecCont0Input<'a, 'b, 'x>> for ByteVecCont0 {
    type Output = RepeatN<U8>;

    open spec fn requires(&self, deps: ByteVecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ByteVecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_byte_vec_cont0(deps@)
    }

    fn apply(&self, deps: ByteVecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(U8, l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(U8, l.ex_into())
            }
        }
    }
}
                

pub struct SpecFuncsecContent {
    pub l: u64,
    pub v: Seq<SpecTypeidx>,
}

pub type SpecFuncsecContentInner = (u64, Seq<SpecTypeidx>);


impl SpecFrom<SpecFuncsecContent> for SpecFuncsecContentInner {
    open spec fn spec_from(m: SpecFuncsecContent) -> SpecFuncsecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecFuncsecContentInner> for SpecFuncsecContent {
    open spec fn spec_from(m: SpecFuncsecContentInner) -> SpecFuncsecContent {
        let (l, v) = m;
        SpecFuncsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct FuncsecContent {
    pub l: u64,
    pub v: RepeatResult<Typeidx>,
}

impl View for FuncsecContent {
    type V = SpecFuncsecContent;

    open spec fn view(&self) -> Self::V {
        SpecFuncsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type FuncsecContentInner = (u64, RepeatResult<Typeidx>);

pub type FuncsecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Typeidx>);
impl<'a> From<&'a FuncsecContent> for FuncsecContentInnerRef<'a> {
    fn ex_from(m: &'a FuncsecContent) -> FuncsecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<FuncsecContentInner> for FuncsecContent {
    fn ex_from(m: FuncsecContentInner) -> FuncsecContent {
        let (l, v) = m;
        FuncsecContent { l, v }
    }
}

pub struct FuncsecContentMapper;
impl View for FuncsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncsecContentMapper {
    type Src = SpecFuncsecContentInner;
    type Dst = SpecFuncsecContent;
}
impl SpecIsoProof for FuncsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FuncsecContentMapper {
    type Src = FuncsecContentInner;
    type Dst = FuncsecContent;
    type RefSrc = FuncsecContentInnerRef<'a>;
}

pub struct SpecFuncsecContentCombinator(SpecFuncsecContentCombinatorAlias);

impl SpecCombinator for SpecFuncsecContentCombinator {
    type Type = SpecFuncsecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncsecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecFuncsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecTypeidxCombinator>>, FuncsecContentMapper>;

pub struct FuncsecContentCombinator(FuncsecContentCombinatorAlias);

impl View for FuncsecContentCombinator {
    type V = SpecFuncsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncsecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FuncsecContentCombinator {
    type Type = FuncsecContent;
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
pub type FuncsecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<TypeidxCombinator>, FuncsecContentCont0>, FuncsecContentMapper>;


pub closed spec fn spec_funcsec_content() -> SpecFuncsecContentCombinator {
    SpecFuncsecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_funcsec_content_cont0(deps)),
        mapper: FuncsecContentMapper,
    })
}

pub open spec fn spec_funcsec_content_cont0(deps: u64) -> RepeatN<SpecTypeidxCombinator> {
    let l = deps;
    RepeatN(spec_typeidx(), l.spec_into())
}

impl View for FuncsecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecTypeidxCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_funcsec_content_cont0(deps)
        }
    }
}

                
pub fn funcsec_content() -> (o: FuncsecContentCombinator)
    ensures o@ == spec_funcsec_content(),
{
    FuncsecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, FuncsecContentCont0),
        mapper: FuncsecContentMapper,
    })
}

pub struct FuncsecContentCont0;
type FuncsecContentCont0Type<'a, 'b> = &'b u64;
type FuncsecContentCont0SType<'a, 'x> = &'x u64;
type FuncsecContentCont0Input<'a, 'b, 'x> = POrSType<FuncsecContentCont0Type<'a, 'b>, FuncsecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<FuncsecContentCont0Input<'a, 'b, 'x>> for FuncsecContentCont0 {
    type Output = RepeatN<TypeidxCombinator>;

    open spec fn requires(&self, deps: FuncsecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: FuncsecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_funcsec_content_cont0(deps@)
    }

    fn apply(&self, deps: FuncsecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(typeidx(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(typeidx(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecFuncsec {
    pub size: u64,
    pub cont: SpecFuncsecContent,
}

pub type SpecFuncsecInner = (u64, SpecFuncsecContent);


impl SpecFrom<SpecFuncsec> for SpecFuncsecInner {
    open spec fn spec_from(m: SpecFuncsec) -> SpecFuncsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecFuncsecInner> for SpecFuncsec {
    open spec fn spec_from(m: SpecFuncsecInner) -> SpecFuncsec {
        let (size, cont) = m;
        SpecFuncsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Funcsec {
    pub size: u64,
    pub cont: FuncsecContent,
}

impl View for Funcsec {
    type V = SpecFuncsec;

    open spec fn view(&self) -> Self::V {
        SpecFuncsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type FuncsecInner = (u64, FuncsecContent);

pub type FuncsecInnerRef<'a> = (&'a u64, &'a FuncsecContent);
impl<'a> From<&'a Funcsec> for FuncsecInnerRef<'a> {
    fn ex_from(m: &'a Funcsec) -> FuncsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<FuncsecInner> for Funcsec {
    fn ex_from(m: FuncsecInner) -> Funcsec {
        let (size, cont) = m;
        Funcsec { size, cont }
    }
}

pub struct FuncsecMapper;
impl View for FuncsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FuncsecMapper {
    type Src = SpecFuncsecInner;
    type Dst = SpecFuncsec;
}
impl SpecIsoProof for FuncsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FuncsecMapper {
    type Src = FuncsecInner;
    type Dst = Funcsec;
    type RefSrc = FuncsecInnerRef<'a>;
}

pub struct SpecFuncsecCombinator(SpecFuncsecCombinatorAlias);

impl SpecCombinator for SpecFuncsecCombinator {
    type Type = SpecFuncsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFuncsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFuncsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecFuncsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecFuncsecContentCombinator>>, FuncsecMapper>;

pub struct FuncsecCombinator(FuncsecCombinatorAlias);

impl View for FuncsecCombinator {
    type V = SpecFuncsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecFuncsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FuncsecCombinator {
    type Type = Funcsec;
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
pub type FuncsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, FuncsecContentCombinator>, FuncsecCont0>, FuncsecMapper>;


pub closed spec fn spec_funcsec() -> SpecFuncsecCombinator {
    SpecFuncsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_funcsec_cont0(deps)),
        mapper: FuncsecMapper,
    })
}

pub open spec fn spec_funcsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecFuncsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_funcsec_content())
}

impl View for FuncsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecFuncsecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_funcsec_cont0(deps)
        }
    }
}

                
pub fn funcsec() -> (o: FuncsecCombinator)
    ensures o@ == spec_funcsec(),
{
    FuncsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, FuncsecCont0),
        mapper: FuncsecMapper,
    })
}

pub struct FuncsecCont0;
type FuncsecCont0Type<'a, 'b> = &'b u64;
type FuncsecCont0SType<'a, 'x> = &'x u64;
type FuncsecCont0Input<'a, 'b, 'x> = POrSType<FuncsecCont0Type<'a, 'b>, FuncsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<FuncsecCont0Input<'a, 'b, 'x>> for FuncsecCont0 {
    type Output = AndThen<bytes::Variable, FuncsecContentCombinator>;

    open spec fn requires(&self, deps: FuncsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: FuncsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_funcsec_cont0(deps@)
    }

    fn apply(&self, deps: FuncsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), funcsec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), funcsec_content())
            }
        }
    }
}
                

pub struct SpecStart {
    pub func: SpecFuncidx,
}

pub type SpecStartInner = SpecFuncidx;


impl SpecFrom<SpecStart> for SpecStartInner {
    open spec fn spec_from(m: SpecStart) -> SpecStartInner {
        m.func
    }
}

impl SpecFrom<SpecStartInner> for SpecStart {
    open spec fn spec_from(m: SpecStartInner) -> SpecStart {
        let func = m;
        SpecStart { func }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Start {
    pub func: Funcidx,
}

impl View for Start {
    type V = SpecStart;

    open spec fn view(&self) -> Self::V {
        SpecStart {
            func: self.func@,
        }
    }
}
pub type StartInner = Funcidx;

pub type StartInnerRef<'a> = &'a Funcidx;
impl<'a> From<&'a Start> for StartInnerRef<'a> {
    fn ex_from(m: &'a Start) -> StartInnerRef<'a> {
        &m.func
    }
}

impl From<StartInner> for Start {
    fn ex_from(m: StartInner) -> Start {
        let func = m;
        Start { func }
    }
}

pub struct StartMapper;
impl View for StartMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StartMapper {
    type Src = SpecStartInner;
    type Dst = SpecStart;
}
impl SpecIsoProof for StartMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StartMapper {
    type Src = StartInner;
    type Dst = Start;
    type RefSrc = StartInnerRef<'a>;
}

pub struct SpecStartCombinator(SpecStartCombinatorAlias);

impl SpecCombinator for SpecStartCombinator {
    type Type = SpecStart;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStartCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecStartCombinatorAlias::is_prefix_secure() }
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
pub type SpecStartCombinatorAlias = Mapped<SpecFuncidxCombinator, StartMapper>;

pub struct StartCombinator(StartCombinatorAlias);

impl View for StartCombinator {
    type V = SpecStartCombinator;
    closed spec fn view(&self) -> Self::V { SpecStartCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StartCombinator {
    type Type = Start;
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
pub type StartCombinatorAlias = Mapped<FuncidxCombinator, StartMapper>;


pub closed spec fn spec_start() -> SpecStartCombinator {
    SpecStartCombinator(
    Mapped {
        inner: spec_funcidx(),
        mapper: StartMapper,
    })
}

                
pub fn start() -> (o: StartCombinator)
    ensures o@ == spec_start(),
{
    StartCombinator(
    Mapped {
        inner: funcidx(),
        mapper: StartMapper,
    })
}

                

pub struct SpecResulttype {
    pub l: u64,
    pub v: Seq<SpecValtype>,
}

pub type SpecResulttypeInner = (u64, Seq<SpecValtype>);


impl SpecFrom<SpecResulttype> for SpecResulttypeInner {
    open spec fn spec_from(m: SpecResulttype) -> SpecResulttypeInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecResulttypeInner> for SpecResulttype {
    open spec fn spec_from(m: SpecResulttypeInner) -> SpecResulttype {
        let (l, v) = m;
        SpecResulttype { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Resulttype {
    pub l: u64,
    pub v: RepeatResult<Valtype>,
}

impl View for Resulttype {
    type V = SpecResulttype;

    open spec fn view(&self) -> Self::V {
        SpecResulttype {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ResulttypeInner = (u64, RepeatResult<Valtype>);

pub type ResulttypeInnerRef<'a> = (&'a u64, &'a RepeatResult<Valtype>);
impl<'a> From<&'a Resulttype> for ResulttypeInnerRef<'a> {
    fn ex_from(m: &'a Resulttype) -> ResulttypeInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<ResulttypeInner> for Resulttype {
    fn ex_from(m: ResulttypeInner) -> Resulttype {
        let (l, v) = m;
        Resulttype { l, v }
    }
}

pub struct ResulttypeMapper;
impl View for ResulttypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResulttypeMapper {
    type Src = SpecResulttypeInner;
    type Dst = SpecResulttype;
}
impl SpecIsoProof for ResulttypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ResulttypeMapper {
    type Src = ResulttypeInner;
    type Dst = Resulttype;
    type RefSrc = ResulttypeInnerRef<'a>;
}

pub struct SpecResulttypeCombinator(SpecResulttypeCombinatorAlias);

impl SpecCombinator for SpecResulttypeCombinator {
    type Type = SpecResulttype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecResulttypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResulttypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecResulttypeCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecValtypeCombinator>>, ResulttypeMapper>;

pub struct ResulttypeCombinator(ResulttypeCombinatorAlias);

impl View for ResulttypeCombinator {
    type V = SpecResulttypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecResulttypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ResulttypeCombinator {
    type Type = Resulttype;
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
pub type ResulttypeCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ValtypeCombinator>, ResulttypeCont0>, ResulttypeMapper>;


pub closed spec fn spec_resulttype() -> SpecResulttypeCombinator {
    SpecResulttypeCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_resulttype_cont0(deps)),
        mapper: ResulttypeMapper,
    })
}

pub open spec fn spec_resulttype_cont0(deps: u64) -> RepeatN<SpecValtypeCombinator> {
    let l = deps;
    RepeatN(spec_valtype(), l.spec_into())
}

impl View for ResulttypeCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecValtypeCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_resulttype_cont0(deps)
        }
    }
}

                
pub fn resulttype() -> (o: ResulttypeCombinator)
    ensures o@ == spec_resulttype(),
{
    ResulttypeCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ResulttypeCont0),
        mapper: ResulttypeMapper,
    })
}

pub struct ResulttypeCont0;
type ResulttypeCont0Type<'a, 'b> = &'b u64;
type ResulttypeCont0SType<'a, 'x> = &'x u64;
type ResulttypeCont0Input<'a, 'b, 'x> = POrSType<ResulttypeCont0Type<'a, 'b>, ResulttypeCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ResulttypeCont0Input<'a, 'b, 'x>> for ResulttypeCont0 {
    type Output = RepeatN<ValtypeCombinator>;

    open spec fn requires(&self, deps: ResulttypeCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ResulttypeCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_resulttype_cont0(deps@)
    }

    fn apply(&self, deps: ResulttypeCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(valtype(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(valtype(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecActiveData0 {
    pub offset: SpecExpr,
    pub init: SpecByteVec,
}

pub type SpecActiveData0Inner = (SpecExpr, SpecByteVec);


impl SpecFrom<SpecActiveData0> for SpecActiveData0Inner {
    open spec fn spec_from(m: SpecActiveData0) -> SpecActiveData0Inner {
        (m.offset, m.init)
    }
}

impl SpecFrom<SpecActiveData0Inner> for SpecActiveData0 {
    open spec fn spec_from(m: SpecActiveData0Inner) -> SpecActiveData0 {
        let (offset, init) = m;
        SpecActiveData0 { offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ActiveData0<'a> {
    pub offset: Expr<'a>,
    pub init: ByteVec,
}

impl View for ActiveData0<'_> {
    type V = SpecActiveData0;

    open spec fn view(&self) -> Self::V {
        SpecActiveData0 {
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ActiveData0Inner<'a> = (Expr<'a>, ByteVec);

pub type ActiveData0InnerRef<'a> = (&'a Expr<'a>, &'a ByteVec);
impl<'a> From<&'a ActiveData0<'a>> for ActiveData0InnerRef<'a> {
    fn ex_from(m: &'a ActiveData0) -> ActiveData0InnerRef<'a> {
        (&m.offset, &m.init)
    }
}

impl<'a> From<ActiveData0Inner<'a>> for ActiveData0<'a> {
    fn ex_from(m: ActiveData0Inner) -> ActiveData0 {
        let (offset, init) = m;
        ActiveData0 { offset, init }
    }
}

pub struct ActiveData0Mapper;
impl View for ActiveData0Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ActiveData0Mapper {
    type Src = SpecActiveData0Inner;
    type Dst = SpecActiveData0;
}
impl SpecIsoProof for ActiveData0Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ActiveData0Mapper {
    type Src = ActiveData0Inner<'a>;
    type Dst = ActiveData0<'a>;
    type RefSrc = ActiveData0InnerRef<'a>;
}

pub struct SpecActiveData0Combinator(SpecActiveData0CombinatorAlias);

impl SpecCombinator for SpecActiveData0Combinator {
    type Type = SpecActiveData0;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecActiveData0Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecActiveData0CombinatorAlias::is_prefix_secure() }
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
pub type SpecActiveData0CombinatorAlias = Mapped<(SpecExprCombinator, SpecByteVecCombinator), ActiveData0Mapper>;

pub struct ActiveData0Combinator(ActiveData0CombinatorAlias);

impl View for ActiveData0Combinator {
    type V = SpecActiveData0Combinator;
    closed spec fn view(&self) -> Self::V { SpecActiveData0Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ActiveData0Combinator {
    type Type = ActiveData0<'a>;
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
pub type ActiveData0CombinatorAlias = Mapped<(ExprCombinator, ByteVecCombinator), ActiveData0Mapper>;


pub closed spec fn spec_active_data0() -> SpecActiveData0Combinator {
    SpecActiveData0Combinator(
    Mapped {
        inner: (spec_expr(), spec_byte_vec()),
        mapper: ActiveData0Mapper,
    })
}

                
pub fn active_data0() -> (o: ActiveData0Combinator)
    ensures o@ == spec_active_data0(),
{
    ActiveData0Combinator(
    Mapped {
        inner: (expr(), byte_vec()),
        mapper: ActiveData0Mapper,
    })
}

                
pub type SpecPassiveData = SpecByteVec;
pub type PassiveData = ByteVec;
pub type PassiveDataRef<'a> = &'a ByteVec;


pub struct SpecPassiveDataCombinator(SpecPassiveDataCombinatorAlias);

impl SpecCombinator for SpecPassiveDataCombinator {
    type Type = SpecPassiveData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecPassiveDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPassiveDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecPassiveDataCombinatorAlias = SpecByteVecCombinator;

pub struct PassiveDataCombinator(PassiveDataCombinatorAlias);

impl View for PassiveDataCombinator {
    type V = SpecPassiveDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecPassiveDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for PassiveDataCombinator {
    type Type = PassiveData;
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
pub type PassiveDataCombinatorAlias = ByteVecCombinator;


pub closed spec fn spec_passive_data() -> SpecPassiveDataCombinator {
    SpecPassiveDataCombinator(spec_byte_vec())
}

                
pub fn passive_data() -> (o: PassiveDataCombinator)
    ensures o@ == spec_passive_data(),
{
    PassiveDataCombinator(byte_vec())
}

                
pub type SpecMemidx = u64;
pub type Memidx = u64;
pub type MemidxRef<'a> = &'a u64;


pub struct SpecMemidxCombinator(SpecMemidxCombinatorAlias);

impl SpecCombinator for SpecMemidxCombinator {
    type Type = SpecMemidx;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemidxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemidxCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemidxCombinatorAlias = UnsignedLEB128;

pub struct MemidxCombinator(MemidxCombinatorAlias);

impl View for MemidxCombinator {
    type V = SpecMemidxCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemidxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemidxCombinator {
    type Type = Memidx;
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
pub type MemidxCombinatorAlias = UnsignedLEB128;


pub closed spec fn spec_memidx() -> SpecMemidxCombinator {
    SpecMemidxCombinator(UnsignedLEB128)
}

                
pub fn memidx() -> (o: MemidxCombinator)
    ensures o@ == spec_memidx(),
{
    MemidxCombinator(UnsignedLEB128)
}

                

pub struct SpecActiveDatax {
    pub memory: SpecMemidx,
    pub offset: SpecExpr,
    pub init: SpecByteVec,
}

pub type SpecActiveDataxInner = (SpecMemidx, (SpecExpr, SpecByteVec));


impl SpecFrom<SpecActiveDatax> for SpecActiveDataxInner {
    open spec fn spec_from(m: SpecActiveDatax) -> SpecActiveDataxInner {
        (m.memory, (m.offset, m.init))
    }
}

impl SpecFrom<SpecActiveDataxInner> for SpecActiveDatax {
    open spec fn spec_from(m: SpecActiveDataxInner) -> SpecActiveDatax {
        let (memory, (offset, init)) = m;
        SpecActiveDatax { memory, offset, init }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ActiveDatax<'a> {
    pub memory: Memidx,
    pub offset: Expr<'a>,
    pub init: ByteVec,
}

impl View for ActiveDatax<'_> {
    type V = SpecActiveDatax;

    open spec fn view(&self) -> Self::V {
        SpecActiveDatax {
            memory: self.memory@,
            offset: self.offset@,
            init: self.init@,
        }
    }
}
pub type ActiveDataxInner<'a> = (Memidx, (Expr<'a>, ByteVec));

pub type ActiveDataxInnerRef<'a> = (&'a Memidx, (&'a Expr<'a>, &'a ByteVec));
impl<'a> From<&'a ActiveDatax<'a>> for ActiveDataxInnerRef<'a> {
    fn ex_from(m: &'a ActiveDatax) -> ActiveDataxInnerRef<'a> {
        (&m.memory, (&m.offset, &m.init))
    }
}

impl<'a> From<ActiveDataxInner<'a>> for ActiveDatax<'a> {
    fn ex_from(m: ActiveDataxInner) -> ActiveDatax {
        let (memory, (offset, init)) = m;
        ActiveDatax { memory, offset, init }
    }
}

pub struct ActiveDataxMapper;
impl View for ActiveDataxMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ActiveDataxMapper {
    type Src = SpecActiveDataxInner;
    type Dst = SpecActiveDatax;
}
impl SpecIsoProof for ActiveDataxMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ActiveDataxMapper {
    type Src = ActiveDataxInner<'a>;
    type Dst = ActiveDatax<'a>;
    type RefSrc = ActiveDataxInnerRef<'a>;
}

pub struct SpecActiveDataxCombinator(SpecActiveDataxCombinatorAlias);

impl SpecCombinator for SpecActiveDataxCombinator {
    type Type = SpecActiveDatax;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecActiveDataxCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecActiveDataxCombinatorAlias::is_prefix_secure() }
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
pub type SpecActiveDataxCombinatorAlias = Mapped<(SpecMemidxCombinator, (SpecExprCombinator, SpecByteVecCombinator)), ActiveDataxMapper>;

pub struct ActiveDataxCombinator(ActiveDataxCombinatorAlias);

impl View for ActiveDataxCombinator {
    type V = SpecActiveDataxCombinator;
    closed spec fn view(&self) -> Self::V { SpecActiveDataxCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ActiveDataxCombinator {
    type Type = ActiveDatax<'a>;
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
pub type ActiveDataxCombinatorAlias = Mapped<(MemidxCombinator, (ExprCombinator, ByteVecCombinator)), ActiveDataxMapper>;


pub closed spec fn spec_active_datax() -> SpecActiveDataxCombinator {
    SpecActiveDataxCombinator(
    Mapped {
        inner: (spec_memidx(), (spec_expr(), spec_byte_vec())),
        mapper: ActiveDataxMapper,
    })
}

                
pub fn active_datax() -> (o: ActiveDataxCombinator)
    ensures o@ == spec_active_datax(),
{
    ActiveDataxCombinator(
    Mapped {
        inner: (memidx(), (expr(), byte_vec())),
        mapper: ActiveDataxMapper,
    })
}

                

pub enum SpecData {
    ActiveData0(SpecActiveData0),
    PassiveData(SpecPassiveData),
    ActiveDataX(SpecActiveDatax),
}

pub type SpecDataInner = Either<SpecActiveData0, Either<SpecPassiveData, SpecActiveDatax>>;

impl SpecFrom<SpecData> for SpecDataInner {
    open spec fn spec_from(m: SpecData) -> SpecDataInner {
        match m {
            SpecData::ActiveData0(m) => Either::Left(m),
            SpecData::PassiveData(m) => Either::Right(Either::Left(m)),
            SpecData::ActiveDataX(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecDataInner> for SpecData {
    open spec fn spec_from(m: SpecDataInner) -> SpecData {
        match m {
            Either::Left(m) => SpecData::ActiveData0(m),
            Either::Right(Either::Left(m)) => SpecData::PassiveData(m),
            Either::Right(Either::Right(m)) => SpecData::ActiveDataX(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Data<'a> {
    ActiveData0(ActiveData0<'a>),
    PassiveData(PassiveData),
    ActiveDataX(ActiveDatax<'a>),
}

pub type DataInner<'a> = Either<ActiveData0<'a>, Either<PassiveData, ActiveDatax<'a>>>;

pub type DataInnerRef<'a> = Either<&'a ActiveData0<'a>, Either<&'a PassiveData, &'a ActiveDatax<'a>>>;


impl<'a> View for Data<'a> {
    type V = SpecData;
    open spec fn view(&self) -> Self::V {
        match self {
            Data::ActiveData0(m) => SpecData::ActiveData0(m@),
            Data::PassiveData(m) => SpecData::PassiveData(m@),
            Data::ActiveDataX(m) => SpecData::ActiveDataX(m@),
        }
    }
}


impl<'a> From<&'a Data<'a>> for DataInnerRef<'a> {
    fn ex_from(m: &'a Data<'a>) -> DataInnerRef<'a> {
        match m {
            Data::ActiveData0(m) => Either::Left(m),
            Data::PassiveData(m) => Either::Right(Either::Left(m)),
            Data::ActiveDataX(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl<'a> From<DataInner<'a>> for Data<'a> {
    fn ex_from(m: DataInner<'a>) -> Data<'a> {
        match m {
            Either::Left(m) => Data::ActiveData0(m),
            Either::Right(Either::Left(m)) => Data::PassiveData(m),
            Either::Right(Either::Right(m)) => Data::ActiveDataX(m),
        }
    }
    
}


pub struct DataMapper;
impl View for DataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DataMapper {
    type Src = SpecDataInner;
    type Dst = SpecData;
}
impl SpecIsoProof for DataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DataMapper {
    type Src = DataInner<'a>;
    type Dst = Data<'a>;
    type RefSrc = DataInnerRef<'a>;
}

pub const DATAACTIVEDATA0_0_FRONT_CONST: u64 = 0;

pub const DATAPASSIVEDATA_0_FRONT_CONST: u64 = 1;

pub const DATAACTIVEDATAX_0_FRONT_CONST: u64 = 2;


pub struct SpecDataCombinator(SpecDataCombinatorAlias);

impl SpecCombinator for SpecDataCombinator {
    type Type = SpecData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecDataCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecActiveData0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, SpecPassiveDataCombinator>, Preceded<Tag<UnsignedLEB128, u64>, SpecActiveDataxCombinator>>>, DataMapper>;




pub struct DataCombinator(DataCombinatorAlias);

impl View for DataCombinator {
    type V = SpecDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DataCombinator {
    type Type = Data<'a>;
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
pub type DataCombinatorAlias = Mapped<Choice<Preceded<Tag<UnsignedLEB128, u64>, ActiveData0Combinator>, Choice<Preceded<Tag<UnsignedLEB128, u64>, PassiveDataCombinator>, Preceded<Tag<UnsignedLEB128, u64>, ActiveDataxCombinator>>>, DataMapper>;


pub closed spec fn spec_data() -> SpecDataCombinator {
    SpecDataCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(UnsignedLEB128, DATAACTIVEDATA0_0_FRONT_CONST), spec_active_data0()), Choice(Preceded(Tag::spec_new(UnsignedLEB128, DATAPASSIVEDATA_0_FRONT_CONST), spec_passive_data()), Preceded(Tag::spec_new(UnsignedLEB128, DATAACTIVEDATAX_0_FRONT_CONST), spec_active_datax()))), mapper: DataMapper })
}

                
pub fn data() -> (o: DataCombinator)
    ensures o@ == spec_data(),
{
    DataCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(UnsignedLEB128, DATAACTIVEDATA0_0_FRONT_CONST), active_data0()), Choice::new(Preceded(Tag::new(UnsignedLEB128, DATAPASSIVEDATA_0_FRONT_CONST), passive_data()), Preceded(Tag::new(UnsignedLEB128, DATAACTIVEDATAX_0_FRONT_CONST), active_datax()))), mapper: DataMapper })
}

                

pub struct SpecDatasecContent {
    pub l: u64,
    pub v: Seq<SpecData>,
}

pub type SpecDatasecContentInner = (u64, Seq<SpecData>);


impl SpecFrom<SpecDatasecContent> for SpecDatasecContentInner {
    open spec fn spec_from(m: SpecDatasecContent) -> SpecDatasecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecDatasecContentInner> for SpecDatasecContent {
    open spec fn spec_from(m: SpecDatasecContentInner) -> SpecDatasecContent {
        let (l, v) = m;
        SpecDatasecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct DatasecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Data<'a>>,
}

impl View for DatasecContent<'_> {
    type V = SpecDatasecContent;

    open spec fn view(&self) -> Self::V {
        SpecDatasecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type DatasecContentInner<'a> = (u64, RepeatResult<Data<'a>>);

pub type DatasecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Data<'a>>);
impl<'a> From<&'a DatasecContent<'a>> for DatasecContentInnerRef<'a> {
    fn ex_from(m: &'a DatasecContent) -> DatasecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<DatasecContentInner<'a>> for DatasecContent<'a> {
    fn ex_from(m: DatasecContentInner) -> DatasecContent {
        let (l, v) = m;
        DatasecContent { l, v }
    }
}

pub struct DatasecContentMapper;
impl View for DatasecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatasecContentMapper {
    type Src = SpecDatasecContentInner;
    type Dst = SpecDatasecContent;
}
impl SpecIsoProof for DatasecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DatasecContentMapper {
    type Src = DatasecContentInner<'a>;
    type Dst = DatasecContent<'a>;
    type RefSrc = DatasecContentInnerRef<'a>;
}

pub struct SpecDatasecContentCombinator(SpecDatasecContentCombinatorAlias);

impl SpecCombinator for SpecDatasecContentCombinator {
    type Type = SpecDatasecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatasecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatasecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecDatasecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecDataCombinator>>, DatasecContentMapper>;

pub struct DatasecContentCombinator(DatasecContentCombinatorAlias);

impl View for DatasecContentCombinator {
    type V = SpecDatasecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatasecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DatasecContentCombinator {
    type Type = DatasecContent<'a>;
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
pub type DatasecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<DataCombinator>, DatasecContentCont0>, DatasecContentMapper>;


pub closed spec fn spec_datasec_content() -> SpecDatasecContentCombinator {
    SpecDatasecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_datasec_content_cont0(deps)),
        mapper: DatasecContentMapper,
    })
}

pub open spec fn spec_datasec_content_cont0(deps: u64) -> RepeatN<SpecDataCombinator> {
    let l = deps;
    RepeatN(spec_data(), l.spec_into())
}

impl View for DatasecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecDataCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_datasec_content_cont0(deps)
        }
    }
}

                
pub fn datasec_content() -> (o: DatasecContentCombinator)
    ensures o@ == spec_datasec_content(),
{
    DatasecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, DatasecContentCont0),
        mapper: DatasecContentMapper,
    })
}

pub struct DatasecContentCont0;
type DatasecContentCont0Type<'a, 'b> = &'b u64;
type DatasecContentCont0SType<'a, 'x> = &'x u64;
type DatasecContentCont0Input<'a, 'b, 'x> = POrSType<DatasecContentCont0Type<'a, 'b>, DatasecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DatasecContentCont0Input<'a, 'b, 'x>> for DatasecContentCont0 {
    type Output = RepeatN<DataCombinator>;

    open spec fn requires(&self, deps: DatasecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: DatasecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_datasec_content_cont0(deps@)
    }

    fn apply(&self, deps: DatasecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(data(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(data(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecDatasec {
    pub size: u64,
    pub cont: SpecDatasecContent,
}

pub type SpecDatasecInner = (u64, SpecDatasecContent);


impl SpecFrom<SpecDatasec> for SpecDatasecInner {
    open spec fn spec_from(m: SpecDatasec) -> SpecDatasecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecDatasecInner> for SpecDatasec {
    open spec fn spec_from(m: SpecDatasecInner) -> SpecDatasec {
        let (size, cont) = m;
        SpecDatasec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Datasec<'a> {
    pub size: u64,
    pub cont: DatasecContent<'a>,
}

impl View for Datasec<'_> {
    type V = SpecDatasec;

    open spec fn view(&self) -> Self::V {
        SpecDatasec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type DatasecInner<'a> = (u64, DatasecContent<'a>);

pub type DatasecInnerRef<'a> = (&'a u64, &'a DatasecContent<'a>);
impl<'a> From<&'a Datasec<'a>> for DatasecInnerRef<'a> {
    fn ex_from(m: &'a Datasec) -> DatasecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl<'a> From<DatasecInner<'a>> for Datasec<'a> {
    fn ex_from(m: DatasecInner) -> Datasec {
        let (size, cont) = m;
        Datasec { size, cont }
    }
}

pub struct DatasecMapper;
impl View for DatasecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatasecMapper {
    type Src = SpecDatasecInner;
    type Dst = SpecDatasec;
}
impl SpecIsoProof for DatasecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DatasecMapper {
    type Src = DatasecInner<'a>;
    type Dst = Datasec<'a>;
    type RefSrc = DatasecInnerRef<'a>;
}

pub struct SpecDatasecCombinator(SpecDatasecCombinatorAlias);

impl SpecCombinator for SpecDatasecCombinator {
    type Type = SpecDatasec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatasecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatasecCombinatorAlias::is_prefix_secure() }
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
pub type SpecDatasecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecDatasecContentCombinator>>, DatasecMapper>;

pub struct DatasecCombinator(DatasecCombinatorAlias);

impl View for DatasecCombinator {
    type V = SpecDatasecCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatasecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DatasecCombinator {
    type Type = Datasec<'a>;
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
pub type DatasecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, DatasecContentCombinator>, DatasecCont0>, DatasecMapper>;


pub closed spec fn spec_datasec() -> SpecDatasecCombinator {
    SpecDatasecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_datasec_cont0(deps)),
        mapper: DatasecMapper,
    })
}

pub open spec fn spec_datasec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecDatasecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_datasec_content())
}

impl View for DatasecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecDatasecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_datasec_cont0(deps)
        }
    }
}

                
pub fn datasec() -> (o: DatasecCombinator)
    ensures o@ == spec_datasec(),
{
    DatasecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, DatasecCont0),
        mapper: DatasecMapper,
    })
}

pub struct DatasecCont0;
type DatasecCont0Type<'a, 'b> = &'b u64;
type DatasecCont0SType<'a, 'x> = &'x u64;
type DatasecCont0Input<'a, 'b, 'x> = POrSType<DatasecCont0Type<'a, 'b>, DatasecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DatasecCont0Input<'a, 'b, 'x>> for DatasecCont0 {
    type Output = AndThen<bytes::Variable, DatasecContentCombinator>;

    open spec fn requires(&self, deps: DatasecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: DatasecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_datasec_cont0(deps@)
    }

    fn apply(&self, deps: DatasecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), datasec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), datasec_content())
            }
        }
    }
}
                
pub type SpecSigned32 = Seq<u8>;
pub type Signed32<'a> = &'a [u8];
pub type Signed32Ref<'a> = &'a &'a [u8];


pub struct SpecSigned32Combinator(SpecSigned32CombinatorAlias);

impl SpecCombinator for SpecSigned32Combinator {
    type Type = SpecSigned32;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSigned32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSigned32CombinatorAlias::is_prefix_secure() }
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
pub type SpecSigned32CombinatorAlias = bytes::Fixed<4>;

pub struct Signed32Combinator(Signed32CombinatorAlias);

impl View for Signed32Combinator {
    type V = SpecSigned32Combinator;
    closed spec fn view(&self) -> Self::V { SpecSigned32Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Signed32Combinator {
    type Type = Signed32<'a>;
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
pub type Signed32CombinatorAlias = bytes::Fixed<4>;


pub closed spec fn spec_signed_32() -> SpecSigned32Combinator {
    SpecSigned32Combinator(bytes::Fixed::<4>)
}

                
pub fn signed_32() -> (o: Signed32Combinator)
    ensures o@ == spec_signed_32(),
{
    Signed32Combinator(bytes::Fixed::<4>)
}

                

pub struct SpecElemsec {
    pub size: u64,
    pub cont: SpecElemsecContent,
}

pub type SpecElemsecInner = (u64, SpecElemsecContent);


impl SpecFrom<SpecElemsec> for SpecElemsecInner {
    open spec fn spec_from(m: SpecElemsec) -> SpecElemsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecElemsecInner> for SpecElemsec {
    open spec fn spec_from(m: SpecElemsecInner) -> SpecElemsec {
        let (size, cont) = m;
        SpecElemsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Elemsec<'a> {
    pub size: u64,
    pub cont: ElemsecContent<'a>,
}

impl View for Elemsec<'_> {
    type V = SpecElemsec;

    open spec fn view(&self) -> Self::V {
        SpecElemsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ElemsecInner<'a> = (u64, ElemsecContent<'a>);

pub type ElemsecInnerRef<'a> = (&'a u64, &'a ElemsecContent<'a>);
impl<'a> From<&'a Elemsec<'a>> for ElemsecInnerRef<'a> {
    fn ex_from(m: &'a Elemsec) -> ElemsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl<'a> From<ElemsecInner<'a>> for Elemsec<'a> {
    fn ex_from(m: ElemsecInner) -> Elemsec {
        let (size, cont) = m;
        Elemsec { size, cont }
    }
}

pub struct ElemsecMapper;
impl View for ElemsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemsecMapper {
    type Src = SpecElemsecInner;
    type Dst = SpecElemsec;
}
impl SpecIsoProof for ElemsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ElemsecMapper {
    type Src = ElemsecInner<'a>;
    type Dst = Elemsec<'a>;
    type RefSrc = ElemsecInnerRef<'a>;
}

pub struct SpecElemsecCombinator(SpecElemsecCombinatorAlias);

impl SpecCombinator for SpecElemsecCombinator {
    type Type = SpecElemsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecElemsecContentCombinator>>, ElemsecMapper>;

pub struct ElemsecCombinator(ElemsecCombinatorAlias);

impl View for ElemsecCombinator {
    type V = SpecElemsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemsecCombinator {
    type Type = Elemsec<'a>;
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
pub type ElemsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, ElemsecContentCombinator>, ElemsecCont0>, ElemsecMapper>;


pub closed spec fn spec_elemsec() -> SpecElemsecCombinator {
    SpecElemsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_elemsec_cont0(deps)),
        mapper: ElemsecMapper,
    })
}

pub open spec fn spec_elemsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecElemsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_elemsec_content())
}

impl View for ElemsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecElemsecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_elemsec_cont0(deps)
        }
    }
}

                
pub fn elemsec() -> (o: ElemsecCombinator)
    ensures o@ == spec_elemsec(),
{
    ElemsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ElemsecCont0),
        mapper: ElemsecMapper,
    })
}

pub struct ElemsecCont0;
type ElemsecCont0Type<'a, 'b> = &'b u64;
type ElemsecCont0SType<'a, 'x> = &'x u64;
type ElemsecCont0Input<'a, 'b, 'x> = POrSType<ElemsecCont0Type<'a, 'b>, ElemsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ElemsecCont0Input<'a, 'b, 'x>> for ElemsecCont0 {
    type Output = AndThen<bytes::Variable, ElemsecContentCombinator>;

    open spec fn requires(&self, deps: ElemsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ElemsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_elemsec_cont0(deps@)
    }

    fn apply(&self, deps: ElemsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), elemsec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), elemsec_content())
            }
        }
    }
}
                
pub type SpecMemtype = SpecLimits;
pub type Memtype = Limits;
pub type MemtypeRef<'a> = &'a Limits;


pub struct SpecMemtypeCombinator(SpecMemtypeCombinatorAlias);

impl SpecCombinator for SpecMemtypeCombinator {
    type Type = SpecMemtype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemtypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemtypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemtypeCombinatorAlias = SpecLimitsCombinator;

pub struct MemtypeCombinator(MemtypeCombinatorAlias);

impl View for MemtypeCombinator {
    type V = SpecMemtypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemtypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemtypeCombinator {
    type Type = Memtype;
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
pub type MemtypeCombinatorAlias = LimitsCombinator;


pub closed spec fn spec_memtype() -> SpecMemtypeCombinator {
    SpecMemtypeCombinator(spec_limits())
}

                
pub fn memtype() -> (o: MemtypeCombinator)
    ensures o@ == spec_memtype(),
{
    MemtypeCombinator(limits())
}

                

pub enum SpecImportdesc {
    Func(SpecTypeidx),
    Table(SpecTabletype),
    Mem(SpecMemtype),
    Global(SpecGlobaltype),
}

pub type SpecImportdescInner = Either<SpecTypeidx, Either<SpecTabletype, Either<SpecMemtype, SpecGlobaltype>>>;

impl SpecFrom<SpecImportdesc> for SpecImportdescInner {
    open spec fn spec_from(m: SpecImportdesc) -> SpecImportdescInner {
        match m {
            SpecImportdesc::Func(m) => Either::Left(m),
            SpecImportdesc::Table(m) => Either::Right(Either::Left(m)),
            SpecImportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecImportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecImportdescInner> for SpecImportdesc {
    open spec fn spec_from(m: SpecImportdescInner) -> SpecImportdesc {
        match m {
            Either::Left(m) => SpecImportdesc::Func(m),
            Either::Right(Either::Left(m)) => SpecImportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecImportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecImportdesc::Global(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Importdesc {
    Func(Typeidx),
    Table(Tabletype),
    Mem(Memtype),
    Global(Globaltype),
}

pub type ImportdescInner = Either<Typeidx, Either<Tabletype, Either<Memtype, Globaltype>>>;

pub type ImportdescInnerRef<'a> = Either<&'a Typeidx, Either<&'a Tabletype, Either<&'a Memtype, &'a Globaltype>>>;


impl View for Importdesc {
    type V = SpecImportdesc;
    open spec fn view(&self) -> Self::V {
        match self {
            Importdesc::Func(m) => SpecImportdesc::Func(m@),
            Importdesc::Table(m) => SpecImportdesc::Table(m@),
            Importdesc::Mem(m) => SpecImportdesc::Mem(m@),
            Importdesc::Global(m) => SpecImportdesc::Global(m@),
        }
    }
}


impl<'a> From<&'a Importdesc> for ImportdescInnerRef<'a> {
    fn ex_from(m: &'a Importdesc) -> ImportdescInnerRef<'a> {
        match m {
            Importdesc::Func(m) => Either::Left(m),
            Importdesc::Table(m) => Either::Right(Either::Left(m)),
            Importdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            Importdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl From<ImportdescInner> for Importdesc {
    fn ex_from(m: ImportdescInner) -> Importdesc {
        match m {
            Either::Left(m) => Importdesc::Func(m),
            Either::Right(Either::Left(m)) => Importdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => Importdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => Importdesc::Global(m),
        }
    }
    
}


pub struct ImportdescMapper;
impl View for ImportdescMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportdescMapper {
    type Src = SpecImportdescInner;
    type Dst = SpecImportdesc;
}
impl SpecIsoProof for ImportdescMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ImportdescMapper {
    type Src = ImportdescInner;
    type Dst = Importdesc;
    type RefSrc = ImportdescInnerRef<'a>;
}

pub const IMPORTDESCFUNC_0_FRONT_CONST: u8 = 0;

pub const IMPORTDESCTABLE_0_FRONT_CONST: u8 = 1;

pub const IMPORTDESCMEM_0_FRONT_CONST: u8 = 2;

pub const IMPORTDESCGLOBAL_0_FRONT_CONST: u8 = 3;


pub struct SpecImportdescCombinator(SpecImportdescCombinatorAlias);

impl SpecCombinator for SpecImportdescCombinator {
    type Type = SpecImportdesc;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportdescCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportdescCombinatorAlias::is_prefix_secure() }
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
pub type SpecImportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecTypeidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecTabletypeCombinator>, Choice<Preceded<Tag<U8, u8>, SpecMemtypeCombinator>, Preceded<Tag<U8, u8>, SpecGlobaltypeCombinator>>>>, ImportdescMapper>;





pub struct ImportdescCombinator(ImportdescCombinatorAlias);

impl View for ImportdescCombinator {
    type V = SpecImportdescCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportdescCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ImportdescCombinator {
    type Type = Importdesc;
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
pub type ImportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, TypeidxCombinator>, Choice<Preceded<Tag<U8, u8>, TabletypeCombinator>, Choice<Preceded<Tag<U8, u8>, MemtypeCombinator>, Preceded<Tag<U8, u8>, GlobaltypeCombinator>>>>, ImportdescMapper>;


pub closed spec fn spec_importdesc() -> SpecImportdescCombinator {
    SpecImportdescCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, IMPORTDESCFUNC_0_FRONT_CONST), spec_typeidx()), Choice(Preceded(Tag::spec_new(U8, IMPORTDESCTABLE_0_FRONT_CONST), spec_tabletype()), Choice(Preceded(Tag::spec_new(U8, IMPORTDESCMEM_0_FRONT_CONST), spec_memtype()), Preceded(Tag::spec_new(U8, IMPORTDESCGLOBAL_0_FRONT_CONST), spec_globaltype())))), mapper: ImportdescMapper })
}

                
pub fn importdesc() -> (o: ImportdescCombinator)
    ensures o@ == spec_importdesc(),
{
    ImportdescCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, IMPORTDESCFUNC_0_FRONT_CONST), typeidx()), Choice::new(Preceded(Tag::new(U8, IMPORTDESCTABLE_0_FRONT_CONST), tabletype()), Choice::new(Preceded(Tag::new(U8, IMPORTDESCMEM_0_FRONT_CONST), memtype()), Preceded(Tag::new(U8, IMPORTDESCGLOBAL_0_FRONT_CONST), globaltype())))), mapper: ImportdescMapper })
}

                

pub struct SpecFunctype {
    pub tag: u8,
    pub params: SpecResulttype,
    pub results: SpecResulttype,
}

pub type SpecFunctypeInner = (u8, (SpecResulttype, SpecResulttype));


impl SpecFrom<SpecFunctype> for SpecFunctypeInner {
    open spec fn spec_from(m: SpecFunctype) -> SpecFunctypeInner {
        (m.tag, (m.params, m.results))
    }
}

impl SpecFrom<SpecFunctypeInner> for SpecFunctype {
    open spec fn spec_from(m: SpecFunctypeInner) -> SpecFunctype {
        let (tag, (params, results)) = m;
        SpecFunctype { tag, params, results }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Functype {
    pub tag: u8,
    pub params: Resulttype,
    pub results: Resulttype,
}

impl View for Functype {
    type V = SpecFunctype;

    open spec fn view(&self) -> Self::V {
        SpecFunctype {
            tag: self.tag@,
            params: self.params@,
            results: self.results@,
        }
    }
}
pub type FunctypeInner = (u8, (Resulttype, Resulttype));

pub type FunctypeInnerRef<'a> = (&'a u8, (&'a Resulttype, &'a Resulttype));
impl<'a> From<&'a Functype> for FunctypeInnerRef<'a> {
    fn ex_from(m: &'a Functype) -> FunctypeInnerRef<'a> {
        (&m.tag, (&m.params, &m.results))
    }
}

impl From<FunctypeInner> for Functype {
    fn ex_from(m: FunctypeInner) -> Functype {
        let (tag, (params, results)) = m;
        Functype { tag, params, results }
    }
}

pub struct FunctypeMapper;
impl View for FunctypeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for FunctypeMapper {
    type Src = SpecFunctypeInner;
    type Dst = SpecFunctype;
}
impl SpecIsoProof for FunctypeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for FunctypeMapper {
    type Src = FunctypeInner;
    type Dst = Functype;
    type RefSrc = FunctypeInnerRef<'a>;
}
pub const FUNCTYPETAG_CONST: u8 = 96;

pub struct SpecFunctypeCombinator(SpecFunctypeCombinatorAlias);

impl SpecCombinator for SpecFunctypeCombinator {
    type Type = SpecFunctype;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecFunctypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFunctypeCombinatorAlias::is_prefix_secure() }
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
pub type SpecFunctypeCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (SpecResulttypeCombinator, SpecResulttypeCombinator)), FunctypeMapper>;

pub struct FunctypeCombinator(FunctypeCombinatorAlias);

impl View for FunctypeCombinator {
    type V = SpecFunctypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecFunctypeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for FunctypeCombinator {
    type Type = Functype;
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
pub type FunctypeCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (ResulttypeCombinator, ResulttypeCombinator)), FunctypeMapper>;


pub closed spec fn spec_functype() -> SpecFunctypeCombinator {
    SpecFunctypeCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(FUNCTYPETAG_CONST) }, (spec_resulttype(), spec_resulttype())),
        mapper: FunctypeMapper,
    })
}

                
pub fn functype() -> (o: FunctypeCombinator)
    ensures o@ == spec_functype(),
{
    FunctypeCombinator(
    Mapped {
        inner: (Refined { inner: U8, predicate: TagPred(FUNCTYPETAG_CONST) }, (resulttype(), resulttype())),
        mapper: FunctypeMapper,
    })
}

                

pub struct SpecTypesecContent {
    pub l: u64,
    pub v: Seq<SpecFunctype>,
}

pub type SpecTypesecContentInner = (u64, Seq<SpecFunctype>);


impl SpecFrom<SpecTypesecContent> for SpecTypesecContentInner {
    open spec fn spec_from(m: SpecTypesecContent) -> SpecTypesecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecTypesecContentInner> for SpecTypesecContent {
    open spec fn spec_from(m: SpecTypesecContentInner) -> SpecTypesecContent {
        let (l, v) = m;
        SpecTypesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct TypesecContent {
    pub l: u64,
    pub v: RepeatResult<Functype>,
}

impl View for TypesecContent {
    type V = SpecTypesecContent;

    open spec fn view(&self) -> Self::V {
        SpecTypesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type TypesecContentInner = (u64, RepeatResult<Functype>);

pub type TypesecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Functype>);
impl<'a> From<&'a TypesecContent> for TypesecContentInnerRef<'a> {
    fn ex_from(m: &'a TypesecContent) -> TypesecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<TypesecContentInner> for TypesecContent {
    fn ex_from(m: TypesecContentInner) -> TypesecContent {
        let (l, v) = m;
        TypesecContent { l, v }
    }
}

pub struct TypesecContentMapper;
impl View for TypesecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypesecContentMapper {
    type Src = SpecTypesecContentInner;
    type Dst = SpecTypesecContent;
}
impl SpecIsoProof for TypesecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TypesecContentMapper {
    type Src = TypesecContentInner;
    type Dst = TypesecContent;
    type RefSrc = TypesecContentInnerRef<'a>;
}

pub struct SpecTypesecContentCombinator(SpecTypesecContentCombinatorAlias);

impl SpecCombinator for SpecTypesecContentCombinator {
    type Type = SpecTypesecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypesecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecTypesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecFunctypeCombinator>>, TypesecContentMapper>;

pub struct TypesecContentCombinator(TypesecContentCombinatorAlias);

impl View for TypesecContentCombinator {
    type V = SpecTypesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypesecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TypesecContentCombinator {
    type Type = TypesecContent;
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
pub type TypesecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<FunctypeCombinator>, TypesecContentCont0>, TypesecContentMapper>;


pub closed spec fn spec_typesec_content() -> SpecTypesecContentCombinator {
    SpecTypesecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_typesec_content_cont0(deps)),
        mapper: TypesecContentMapper,
    })
}

pub open spec fn spec_typesec_content_cont0(deps: u64) -> RepeatN<SpecFunctypeCombinator> {
    let l = deps;
    RepeatN(spec_functype(), l.spec_into())
}

impl View for TypesecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecFunctypeCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_typesec_content_cont0(deps)
        }
    }
}

                
pub fn typesec_content() -> (o: TypesecContentCombinator)
    ensures o@ == spec_typesec_content(),
{
    TypesecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, TypesecContentCont0),
        mapper: TypesecContentMapper,
    })
}

pub struct TypesecContentCont0;
type TypesecContentCont0Type<'a, 'b> = &'b u64;
type TypesecContentCont0SType<'a, 'x> = &'x u64;
type TypesecContentCont0Input<'a, 'b, 'x> = POrSType<TypesecContentCont0Type<'a, 'b>, TypesecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TypesecContentCont0Input<'a, 'b, 'x>> for TypesecContentCont0 {
    type Output = RepeatN<FunctypeCombinator>;

    open spec fn requires(&self, deps: TypesecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TypesecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_typesec_content_cont0(deps@)
    }

    fn apply(&self, deps: TypesecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(functype(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(functype(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecTypesec {
    pub size: u64,
    pub cont: SpecTypesecContent,
}

pub type SpecTypesecInner = (u64, SpecTypesecContent);


impl SpecFrom<SpecTypesec> for SpecTypesecInner {
    open spec fn spec_from(m: SpecTypesec) -> SpecTypesecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecTypesecInner> for SpecTypesec {
    open spec fn spec_from(m: SpecTypesecInner) -> SpecTypesec {
        let (size, cont) = m;
        SpecTypesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Typesec {
    pub size: u64,
    pub cont: TypesecContent,
}

impl View for Typesec {
    type V = SpecTypesec;

    open spec fn view(&self) -> Self::V {
        SpecTypesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type TypesecInner = (u64, TypesecContent);

pub type TypesecInnerRef<'a> = (&'a u64, &'a TypesecContent);
impl<'a> From<&'a Typesec> for TypesecInnerRef<'a> {
    fn ex_from(m: &'a Typesec) -> TypesecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<TypesecInner> for Typesec {
    fn ex_from(m: TypesecInner) -> Typesec {
        let (size, cont) = m;
        Typesec { size, cont }
    }
}

pub struct TypesecMapper;
impl View for TypesecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TypesecMapper {
    type Src = SpecTypesecInner;
    type Dst = SpecTypesec;
}
impl SpecIsoProof for TypesecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TypesecMapper {
    type Src = TypesecInner;
    type Dst = Typesec;
    type RefSrc = TypesecInnerRef<'a>;
}

pub struct SpecTypesecCombinator(SpecTypesecCombinatorAlias);

impl SpecCombinator for SpecTypesecCombinator {
    type Type = SpecTypesec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTypesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTypesecCombinatorAlias::is_prefix_secure() }
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
pub type SpecTypesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecTypesecContentCombinator>>, TypesecMapper>;

pub struct TypesecCombinator(TypesecCombinatorAlias);

impl View for TypesecCombinator {
    type V = SpecTypesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecTypesecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TypesecCombinator {
    type Type = Typesec;
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
pub type TypesecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, TypesecContentCombinator>, TypesecCont0>, TypesecMapper>;


pub closed spec fn spec_typesec() -> SpecTypesecCombinator {
    SpecTypesecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_typesec_cont0(deps)),
        mapper: TypesecMapper,
    })
}

pub open spec fn spec_typesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecTypesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_typesec_content())
}

impl View for TypesecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecTypesecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_typesec_cont0(deps)
        }
    }
}

                
pub fn typesec() -> (o: TypesecCombinator)
    ensures o@ == spec_typesec(),
{
    TypesecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, TypesecCont0),
        mapper: TypesecMapper,
    })
}

pub struct TypesecCont0;
type TypesecCont0Type<'a, 'b> = &'b u64;
type TypesecCont0SType<'a, 'x> = &'x u64;
type TypesecCont0Input<'a, 'b, 'x> = POrSType<TypesecCont0Type<'a, 'b>, TypesecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TypesecCont0Input<'a, 'b, 'x>> for TypesecCont0 {
    type Output = AndThen<bytes::Variable, TypesecContentCombinator>;

    open spec fn requires(&self, deps: TypesecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TypesecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_typesec_cont0(deps@)
    }

    fn apply(&self, deps: TypesecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), typesec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), typesec_content())
            }
        }
    }
}
                

pub struct SpecMem {
    pub ty: SpecMemtype,
}

pub type SpecMemInner = SpecMemtype;


impl SpecFrom<SpecMem> for SpecMemInner {
    open spec fn spec_from(m: SpecMem) -> SpecMemInner {
        m.ty
    }
}

impl SpecFrom<SpecMemInner> for SpecMem {
    open spec fn spec_from(m: SpecMemInner) -> SpecMem {
        let ty = m;
        SpecMem { ty }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Mem {
    pub ty: Memtype,
}

impl View for Mem {
    type V = SpecMem;

    open spec fn view(&self) -> Self::V {
        SpecMem {
            ty: self.ty@,
        }
    }
}
pub type MemInner = Memtype;

pub type MemInnerRef<'a> = &'a Memtype;
impl<'a> From<&'a Mem> for MemInnerRef<'a> {
    fn ex_from(m: &'a Mem) -> MemInnerRef<'a> {
        &m.ty
    }
}

impl From<MemInner> for Mem {
    fn ex_from(m: MemInner) -> Mem {
        let ty = m;
        Mem { ty }
    }
}

pub struct MemMapper;
impl View for MemMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemMapper {
    type Src = SpecMemInner;
    type Dst = SpecMem;
}
impl SpecIsoProof for MemMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemMapper {
    type Src = MemInner;
    type Dst = Mem;
    type RefSrc = MemInnerRef<'a>;
}

pub struct SpecMemCombinator(SpecMemCombinatorAlias);

impl SpecCombinator for SpecMemCombinator {
    type Type = SpecMem;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemCombinatorAlias = Mapped<SpecMemtypeCombinator, MemMapper>;

pub struct MemCombinator(MemCombinatorAlias);

impl View for MemCombinator {
    type V = SpecMemCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemCombinator {
    type Type = Mem;
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
pub type MemCombinatorAlias = Mapped<MemtypeCombinator, MemMapper>;


pub closed spec fn spec_mem() -> SpecMemCombinator {
    SpecMemCombinator(
    Mapped {
        inner: spec_memtype(),
        mapper: MemMapper,
    })
}

                
pub fn mem() -> (o: MemCombinator)
    ensures o@ == spec_mem(),
{
    MemCombinator(
    Mapped {
        inner: memtype(),
        mapper: MemMapper,
    })
}

                

pub struct SpecMemsecContent {
    pub l: u64,
    pub v: Seq<SpecMem>,
}

pub type SpecMemsecContentInner = (u64, Seq<SpecMem>);


impl SpecFrom<SpecMemsecContent> for SpecMemsecContentInner {
    open spec fn spec_from(m: SpecMemsecContent) -> SpecMemsecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecMemsecContentInner> for SpecMemsecContent {
    open spec fn spec_from(m: SpecMemsecContentInner) -> SpecMemsecContent {
        let (l, v) = m;
        SpecMemsecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct MemsecContent {
    pub l: u64,
    pub v: RepeatResult<Mem>,
}

impl View for MemsecContent {
    type V = SpecMemsecContent;

    open spec fn view(&self) -> Self::V {
        SpecMemsecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type MemsecContentInner = (u64, RepeatResult<Mem>);

pub type MemsecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Mem>);
impl<'a> From<&'a MemsecContent> for MemsecContentInnerRef<'a> {
    fn ex_from(m: &'a MemsecContent) -> MemsecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<MemsecContentInner> for MemsecContent {
    fn ex_from(m: MemsecContentInner) -> MemsecContent {
        let (l, v) = m;
        MemsecContent { l, v }
    }
}

pub struct MemsecContentMapper;
impl View for MemsecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemsecContentMapper {
    type Src = SpecMemsecContentInner;
    type Dst = SpecMemsecContent;
}
impl SpecIsoProof for MemsecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemsecContentMapper {
    type Src = MemsecContentInner;
    type Dst = MemsecContent;
    type RefSrc = MemsecContentInnerRef<'a>;
}

pub struct SpecMemsecContentCombinator(SpecMemsecContentCombinatorAlias);

impl SpecCombinator for SpecMemsecContentCombinator {
    type Type = SpecMemsecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemsecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemsecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemsecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecMemCombinator>>, MemsecContentMapper>;

pub struct MemsecContentCombinator(MemsecContentCombinatorAlias);

impl View for MemsecContentCombinator {
    type V = SpecMemsecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemsecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemsecContentCombinator {
    type Type = MemsecContent;
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
pub type MemsecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<MemCombinator>, MemsecContentCont0>, MemsecContentMapper>;


pub closed spec fn spec_memsec_content() -> SpecMemsecContentCombinator {
    SpecMemsecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_memsec_content_cont0(deps)),
        mapper: MemsecContentMapper,
    })
}

pub open spec fn spec_memsec_content_cont0(deps: u64) -> RepeatN<SpecMemCombinator> {
    let l = deps;
    RepeatN(spec_mem(), l.spec_into())
}

impl View for MemsecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecMemCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_memsec_content_cont0(deps)
        }
    }
}

                
pub fn memsec_content() -> (o: MemsecContentCombinator)
    ensures o@ == spec_memsec_content(),
{
    MemsecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, MemsecContentCont0),
        mapper: MemsecContentMapper,
    })
}

pub struct MemsecContentCont0;
type MemsecContentCont0Type<'a, 'b> = &'b u64;
type MemsecContentCont0SType<'a, 'x> = &'x u64;
type MemsecContentCont0Input<'a, 'b, 'x> = POrSType<MemsecContentCont0Type<'a, 'b>, MemsecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MemsecContentCont0Input<'a, 'b, 'x>> for MemsecContentCont0 {
    type Output = RepeatN<MemCombinator>;

    open spec fn requires(&self, deps: MemsecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MemsecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_memsec_content_cont0(deps@)
    }

    fn apply(&self, deps: MemsecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(mem(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(mem(), l.ex_into())
            }
        }
    }
}
                
pub type SpecName = SpecByteVec;
pub type Name = ByteVec;
pub type NameRef<'a> = &'a ByteVec;


pub struct SpecNameCombinator(SpecNameCombinatorAlias);

impl SpecCombinator for SpecNameCombinator {
    type Type = SpecName;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNameCombinatorAlias::is_prefix_secure() }
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
pub type SpecNameCombinatorAlias = SpecByteVecCombinator;

pub struct NameCombinator(NameCombinatorAlias);

impl View for NameCombinator {
    type V = SpecNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecNameCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for NameCombinator {
    type Type = Name;
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
pub type NameCombinatorAlias = ByteVecCombinator;


pub closed spec fn spec_name() -> SpecNameCombinator {
    SpecNameCombinator(spec_byte_vec())
}

                
pub fn name() -> (o: NameCombinator)
    ensures o@ == spec_name(),
{
    NameCombinator(byte_vec())
}

                

pub enum SpecExportdesc {
    Func(SpecFuncidx),
    Table(SpecTableidx),
    Mem(SpecMemidx),
    Global(SpecGlobalidx),
}

pub type SpecExportdescInner = Either<SpecFuncidx, Either<SpecTableidx, Either<SpecMemidx, SpecGlobalidx>>>;

impl SpecFrom<SpecExportdesc> for SpecExportdescInner {
    open spec fn spec_from(m: SpecExportdesc) -> SpecExportdescInner {
        match m {
            SpecExportdesc::Func(m) => Either::Left(m),
            SpecExportdesc::Table(m) => Either::Right(Either::Left(m)),
            SpecExportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecExportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecExportdescInner> for SpecExportdesc {
    open spec fn spec_from(m: SpecExportdescInner) -> SpecExportdesc {
        match m {
            Either::Left(m) => SpecExportdesc::Func(m),
            Either::Right(Either::Left(m)) => SpecExportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecExportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecExportdesc::Global(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exportdesc {
    Func(Funcidx),
    Table(Tableidx),
    Mem(Memidx),
    Global(Globalidx),
}

pub type ExportdescInner = Either<Funcidx, Either<Tableidx, Either<Memidx, Globalidx>>>;

pub type ExportdescInnerRef<'a> = Either<&'a Funcidx, Either<&'a Tableidx, Either<&'a Memidx, &'a Globalidx>>>;


impl View for Exportdesc {
    type V = SpecExportdesc;
    open spec fn view(&self) -> Self::V {
        match self {
            Exportdesc::Func(m) => SpecExportdesc::Func(m@),
            Exportdesc::Table(m) => SpecExportdesc::Table(m@),
            Exportdesc::Mem(m) => SpecExportdesc::Mem(m@),
            Exportdesc::Global(m) => SpecExportdesc::Global(m@),
        }
    }
}


impl<'a> From<&'a Exportdesc> for ExportdescInnerRef<'a> {
    fn ex_from(m: &'a Exportdesc) -> ExportdescInnerRef<'a> {
        match m {
            Exportdesc::Func(m) => Either::Left(m),
            Exportdesc::Table(m) => Either::Right(Either::Left(m)),
            Exportdesc::Mem(m) => Either::Right(Either::Right(Either::Left(m))),
            Exportdesc::Global(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl From<ExportdescInner> for Exportdesc {
    fn ex_from(m: ExportdescInner) -> Exportdesc {
        match m {
            Either::Left(m) => Exportdesc::Func(m),
            Either::Right(Either::Left(m)) => Exportdesc::Table(m),
            Either::Right(Either::Right(Either::Left(m))) => Exportdesc::Mem(m),
            Either::Right(Either::Right(Either::Right(m))) => Exportdesc::Global(m),
        }
    }
    
}


pub struct ExportdescMapper;
impl View for ExportdescMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportdescMapper {
    type Src = SpecExportdescInner;
    type Dst = SpecExportdesc;
}
impl SpecIsoProof for ExportdescMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExportdescMapper {
    type Src = ExportdescInner;
    type Dst = Exportdesc;
    type RefSrc = ExportdescInnerRef<'a>;
}

pub const EXPORTDESCFUNC_0_FRONT_CONST: u8 = 0;

pub const EXPORTDESCTABLE_0_FRONT_CONST: u8 = 1;

pub const EXPORTDESCMEM_0_FRONT_CONST: u8 = 2;

pub const EXPORTDESCGLOBAL_0_FRONT_CONST: u8 = 3;


pub struct SpecExportdescCombinator(SpecExportdescCombinatorAlias);

impl SpecCombinator for SpecExportdescCombinator {
    type Type = SpecExportdesc;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportdescCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportdescCombinatorAlias::is_prefix_secure() }
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
pub type SpecExportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, SpecFuncidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecTableidxCombinator>, Choice<Preceded<Tag<U8, u8>, SpecMemidxCombinator>, Preceded<Tag<U8, u8>, SpecGlobalidxCombinator>>>>, ExportdescMapper>;





pub struct ExportdescCombinator(ExportdescCombinatorAlias);

impl View for ExportdescCombinator {
    type V = SpecExportdescCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportdescCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExportdescCombinator {
    type Type = Exportdesc;
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
pub type ExportdescCombinatorAlias = Mapped<Choice<Preceded<Tag<U8, u8>, FuncidxCombinator>, Choice<Preceded<Tag<U8, u8>, TableidxCombinator>, Choice<Preceded<Tag<U8, u8>, MemidxCombinator>, Preceded<Tag<U8, u8>, GlobalidxCombinator>>>>, ExportdescMapper>;


pub closed spec fn spec_exportdesc() -> SpecExportdescCombinator {
    SpecExportdescCombinator(Mapped { inner: Choice(Preceded(Tag::spec_new(U8, EXPORTDESCFUNC_0_FRONT_CONST), spec_funcidx()), Choice(Preceded(Tag::spec_new(U8, EXPORTDESCTABLE_0_FRONT_CONST), spec_tableidx()), Choice(Preceded(Tag::spec_new(U8, EXPORTDESCMEM_0_FRONT_CONST), spec_memidx()), Preceded(Tag::spec_new(U8, EXPORTDESCGLOBAL_0_FRONT_CONST), spec_globalidx())))), mapper: ExportdescMapper })
}

                
pub fn exportdesc() -> (o: ExportdescCombinator)
    ensures o@ == spec_exportdesc(),
{
    ExportdescCombinator(Mapped { inner: Choice::new(Preceded(Tag::new(U8, EXPORTDESCFUNC_0_FRONT_CONST), funcidx()), Choice::new(Preceded(Tag::new(U8, EXPORTDESCTABLE_0_FRONT_CONST), tableidx()), Choice::new(Preceded(Tag::new(U8, EXPORTDESCMEM_0_FRONT_CONST), memidx()), Preceded(Tag::new(U8, EXPORTDESCGLOBAL_0_FRONT_CONST), globalidx())))), mapper: ExportdescMapper })
}

                

pub struct SpecExport {
    pub nm: SpecName,
    pub d: SpecExportdesc,
}

pub type SpecExportInner = (SpecName, SpecExportdesc);


impl SpecFrom<SpecExport> for SpecExportInner {
    open spec fn spec_from(m: SpecExport) -> SpecExportInner {
        (m.nm, m.d)
    }
}

impl SpecFrom<SpecExportInner> for SpecExport {
    open spec fn spec_from(m: SpecExportInner) -> SpecExport {
        let (nm, d) = m;
        SpecExport { nm, d }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Export {
    pub nm: Name,
    pub d: Exportdesc,
}

impl View for Export {
    type V = SpecExport;

    open spec fn view(&self) -> Self::V {
        SpecExport {
            nm: self.nm@,
            d: self.d@,
        }
    }
}
pub type ExportInner = (Name, Exportdesc);

pub type ExportInnerRef<'a> = (&'a Name, &'a Exportdesc);
impl<'a> From<&'a Export> for ExportInnerRef<'a> {
    fn ex_from(m: &'a Export) -> ExportInnerRef<'a> {
        (&m.nm, &m.d)
    }
}

impl From<ExportInner> for Export {
    fn ex_from(m: ExportInner) -> Export {
        let (nm, d) = m;
        Export { nm, d }
    }
}

pub struct ExportMapper;
impl View for ExportMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportMapper {
    type Src = SpecExportInner;
    type Dst = SpecExport;
}
impl SpecIsoProof for ExportMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExportMapper {
    type Src = ExportInner;
    type Dst = Export;
    type RefSrc = ExportInnerRef<'a>;
}

pub struct SpecExportCombinator(SpecExportCombinatorAlias);

impl SpecCombinator for SpecExportCombinator {
    type Type = SpecExport;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportCombinatorAlias::is_prefix_secure() }
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
pub type SpecExportCombinatorAlias = Mapped<(SpecNameCombinator, SpecExportdescCombinator), ExportMapper>;

pub struct ExportCombinator(ExportCombinatorAlias);

impl View for ExportCombinator {
    type V = SpecExportCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExportCombinator {
    type Type = Export;
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
pub type ExportCombinatorAlias = Mapped<(NameCombinator, ExportdescCombinator), ExportMapper>;


pub closed spec fn spec_export() -> SpecExportCombinator {
    SpecExportCombinator(
    Mapped {
        inner: (spec_name(), spec_exportdesc()),
        mapper: ExportMapper,
    })
}

                
pub fn export() -> (o: ExportCombinator)
    ensures o@ == spec_export(),
{
    ExportCombinator(
    Mapped {
        inner: (name(), exportdesc()),
        mapper: ExportMapper,
    })
}

                
pub type SpecELEMKIND = u8;
pub type ELEMKIND = u8;
pub type ELEMKINDRef<'a> = &'a u8;

pub const ELEMKIND_CONST: u8 = 0;
pub type SpecELEMKINDCombinator = Refined<U8, TagPred<u8>>;
pub type ELEMKINDCombinator = Refined<U8, TagPred<u8>>;


pub closed spec fn spec_ELEMKIND() -> SpecELEMKINDCombinator {
    Refined { inner: U8, predicate: TagPred(ELEMKIND_CONST) }
}

pub fn ELEMKIND() -> (o: ELEMKINDCombinator)
    ensures o@ == spec_ELEMKIND(),
{
    Refined { inner: U8, predicate: TagPred(ELEMKIND_CONST) }
}


pub struct SpecCode {
    pub size: u64,
    pub code: SpecFunc,
}

pub type SpecCodeInner = (u64, SpecFunc);


impl SpecFrom<SpecCode> for SpecCodeInner {
    open spec fn spec_from(m: SpecCode) -> SpecCodeInner {
        (m.size, m.code)
    }
}

impl SpecFrom<SpecCodeInner> for SpecCode {
    open spec fn spec_from(m: SpecCodeInner) -> SpecCode {
        let (size, code) = m;
        SpecCode { size, code }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Code<'a> {
    pub size: u64,
    pub code: Func<'a>,
}

impl View for Code<'_> {
    type V = SpecCode;

    open spec fn view(&self) -> Self::V {
        SpecCode {
            size: self.size@,
            code: self.code@,
        }
    }
}
pub type CodeInner<'a> = (u64, Func<'a>);

pub type CodeInnerRef<'a> = (&'a u64, &'a Func<'a>);
impl<'a> From<&'a Code<'a>> for CodeInnerRef<'a> {
    fn ex_from(m: &'a Code) -> CodeInnerRef<'a> {
        (&m.size, &m.code)
    }
}

impl<'a> From<CodeInner<'a>> for Code<'a> {
    fn ex_from(m: CodeInner) -> Code {
        let (size, code) = m;
        Code { size, code }
    }
}

pub struct CodeMapper;
impl View for CodeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodeMapper {
    type Src = SpecCodeInner;
    type Dst = SpecCode;
}
impl SpecIsoProof for CodeMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CodeMapper {
    type Src = CodeInner<'a>;
    type Dst = Code<'a>;
    type RefSrc = CodeInnerRef<'a>;
}

pub struct SpecCodeCombinator(SpecCodeCombinatorAlias);

impl SpecCombinator for SpecCodeCombinator {
    type Type = SpecCode;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodeCombinatorAlias::is_prefix_secure() }
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
pub type SpecCodeCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecFuncCombinator>>, CodeMapper>;

pub struct CodeCombinator(CodeCombinatorAlias);

impl View for CodeCombinator {
    type V = SpecCodeCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodeCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CodeCombinator {
    type Type = Code<'a>;
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
pub type CodeCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, FuncCombinator>, CodeCont0>, CodeMapper>;


pub closed spec fn spec_code() -> SpecCodeCombinator {
    SpecCodeCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_code_cont0(deps)),
        mapper: CodeMapper,
    })
}

pub open spec fn spec_code_cont0(deps: u64) -> AndThen<bytes::Variable, SpecFuncCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_func())
}

impl View for CodeCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecFuncCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_code_cont0(deps)
        }
    }
}

                
pub fn code() -> (o: CodeCombinator)
    ensures o@ == spec_code(),
{
    CodeCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, CodeCont0),
        mapper: CodeMapper,
    })
}

pub struct CodeCont0;
type CodeCont0Type<'a, 'b> = &'b u64;
type CodeCont0SType<'a, 'x> = &'x u64;
type CodeCont0Input<'a, 'b, 'x> = POrSType<CodeCont0Type<'a, 'b>, CodeCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CodeCont0Input<'a, 'b, 'x>> for CodeCont0 {
    type Output = AndThen<bytes::Variable, FuncCombinator>;

    open spec fn requires(&self, deps: CodeCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CodeCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_code_cont0(deps@)
    }

    fn apply(&self, deps: CodeCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), func())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), func())
            }
        }
    }
}
                

pub struct SpecCodesecContent {
    pub l: u64,
    pub v: Seq<SpecCode>,
}

pub type SpecCodesecContentInner = (u64, Seq<SpecCode>);


impl SpecFrom<SpecCodesecContent> for SpecCodesecContentInner {
    open spec fn spec_from(m: SpecCodesecContent) -> SpecCodesecContentInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecCodesecContentInner> for SpecCodesecContent {
    open spec fn spec_from(m: SpecCodesecContentInner) -> SpecCodesecContent {
        let (l, v) = m;
        SpecCodesecContent { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct CodesecContent<'a> {
    pub l: u64,
    pub v: RepeatResult<Code<'a>>,
}

impl View for CodesecContent<'_> {
    type V = SpecCodesecContent;

    open spec fn view(&self) -> Self::V {
        SpecCodesecContent {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type CodesecContentInner<'a> = (u64, RepeatResult<Code<'a>>);

pub type CodesecContentInnerRef<'a> = (&'a u64, &'a RepeatResult<Code<'a>>);
impl<'a> From<&'a CodesecContent<'a>> for CodesecContentInnerRef<'a> {
    fn ex_from(m: &'a CodesecContent) -> CodesecContentInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl<'a> From<CodesecContentInner<'a>> for CodesecContent<'a> {
    fn ex_from(m: CodesecContentInner) -> CodesecContent {
        let (l, v) = m;
        CodesecContent { l, v }
    }
}

pub struct CodesecContentMapper;
impl View for CodesecContentMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodesecContentMapper {
    type Src = SpecCodesecContentInner;
    type Dst = SpecCodesecContent;
}
impl SpecIsoProof for CodesecContentMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CodesecContentMapper {
    type Src = CodesecContentInner<'a>;
    type Dst = CodesecContent<'a>;
    type RefSrc = CodesecContentInnerRef<'a>;
}

pub struct SpecCodesecContentCombinator(SpecCodesecContentCombinatorAlias);

impl SpecCombinator for SpecCodesecContentCombinator {
    type Type = SpecCodesecContent;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodesecContentCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodesecContentCombinatorAlias::is_prefix_secure() }
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
pub type SpecCodesecContentCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecCodeCombinator>>, CodesecContentMapper>;

pub struct CodesecContentCombinator(CodesecContentCombinatorAlias);

impl View for CodesecContentCombinator {
    type V = SpecCodesecContentCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodesecContentCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CodesecContentCombinator {
    type Type = CodesecContent<'a>;
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
pub type CodesecContentCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<CodeCombinator>, CodesecContentCont0>, CodesecContentMapper>;


pub closed spec fn spec_codesec_content() -> SpecCodesecContentCombinator {
    SpecCodesecContentCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_codesec_content_cont0(deps)),
        mapper: CodesecContentMapper,
    })
}

pub open spec fn spec_codesec_content_cont0(deps: u64) -> RepeatN<SpecCodeCombinator> {
    let l = deps;
    RepeatN(spec_code(), l.spec_into())
}

impl View for CodesecContentCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecCodeCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_codesec_content_cont0(deps)
        }
    }
}

                
pub fn codesec_content() -> (o: CodesecContentCombinator)
    ensures o@ == spec_codesec_content(),
{
    CodesecContentCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, CodesecContentCont0),
        mapper: CodesecContentMapper,
    })
}

pub struct CodesecContentCont0;
type CodesecContentCont0Type<'a, 'b> = &'b u64;
type CodesecContentCont0SType<'a, 'x> = &'x u64;
type CodesecContentCont0Input<'a, 'b, 'x> = POrSType<CodesecContentCont0Type<'a, 'b>, CodesecContentCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CodesecContentCont0Input<'a, 'b, 'x>> for CodesecContentCont0 {
    type Output = RepeatN<CodeCombinator>;

    open spec fn requires(&self, deps: CodesecContentCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CodesecContentCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_codesec_content_cont0(deps@)
    }

    fn apply(&self, deps: CodesecContentCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(code(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(code(), l.ex_into())
            }
        }
    }
}
                
pub type SpecMyCustomSection = SpecByteVec;
pub type MyCustomSection = ByteVec;
pub type MyCustomSectionRef<'a> = &'a ByteVec;


pub struct SpecMyCustomSectionCombinator(SpecMyCustomSectionCombinatorAlias);

impl SpecCombinator for SpecMyCustomSectionCombinator {
    type Type = SpecMyCustomSection;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMyCustomSectionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMyCustomSectionCombinatorAlias::is_prefix_secure() }
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
pub type SpecMyCustomSectionCombinatorAlias = SpecByteVecCombinator;

pub struct MyCustomSectionCombinator(MyCustomSectionCombinatorAlias);

impl View for MyCustomSectionCombinator {
    type V = SpecMyCustomSectionCombinator;
    closed spec fn view(&self) -> Self::V { SpecMyCustomSectionCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MyCustomSectionCombinator {
    type Type = MyCustomSection;
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
pub type MyCustomSectionCombinatorAlias = ByteVecCombinator;


pub closed spec fn spec_my_custom_section() -> SpecMyCustomSectionCombinator {
    SpecMyCustomSectionCombinator(spec_byte_vec())
}

                
pub fn my_custom_section() -> (o: MyCustomSectionCombinator)
    ensures o@ == spec_my_custom_section(),
{
    MyCustomSectionCombinator(byte_vec())
}

                

pub struct SpecCustom {
    pub name: SpecName,
    pub data: SpecMyCustomSection,
}

pub type SpecCustomInner = (SpecName, SpecMyCustomSection);


impl SpecFrom<SpecCustom> for SpecCustomInner {
    open spec fn spec_from(m: SpecCustom) -> SpecCustomInner {
        (m.name, m.data)
    }
}

impl SpecFrom<SpecCustomInner> for SpecCustom {
    open spec fn spec_from(m: SpecCustomInner) -> SpecCustom {
        let (name, data) = m;
        SpecCustom { name, data }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Custom {
    pub name: Name,
    pub data: MyCustomSection,
}

impl View for Custom {
    type V = SpecCustom;

    open spec fn view(&self) -> Self::V {
        SpecCustom {
            name: self.name@,
            data: self.data@,
        }
    }
}
pub type CustomInner = (Name, MyCustomSection);

pub type CustomInnerRef<'a> = (&'a Name, &'a MyCustomSection);
impl<'a> From<&'a Custom> for CustomInnerRef<'a> {
    fn ex_from(m: &'a Custom) -> CustomInnerRef<'a> {
        (&m.name, &m.data)
    }
}

impl From<CustomInner> for Custom {
    fn ex_from(m: CustomInner) -> Custom {
        let (name, data) = m;
        Custom { name, data }
    }
}

pub struct CustomMapper;
impl View for CustomMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CustomMapper {
    type Src = SpecCustomInner;
    type Dst = SpecCustom;
}
impl SpecIsoProof for CustomMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CustomMapper {
    type Src = CustomInner;
    type Dst = Custom;
    type RefSrc = CustomInnerRef<'a>;
}

pub struct SpecCustomCombinator(SpecCustomCombinatorAlias);

impl SpecCombinator for SpecCustomCombinator {
    type Type = SpecCustom;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCustomCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCustomCombinatorAlias::is_prefix_secure() }
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
pub type SpecCustomCombinatorAlias = Mapped<(SpecNameCombinator, SpecMyCustomSectionCombinator), CustomMapper>;

pub struct CustomCombinator(CustomCombinatorAlias);

impl View for CustomCombinator {
    type V = SpecCustomCombinator;
    closed spec fn view(&self) -> Self::V { SpecCustomCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CustomCombinator {
    type Type = Custom;
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
pub type CustomCombinatorAlias = Mapped<(NameCombinator, MyCustomSectionCombinator), CustomMapper>;


pub closed spec fn spec_custom() -> SpecCustomCombinator {
    SpecCustomCombinator(
    Mapped {
        inner: (spec_name(), spec_my_custom_section()),
        mapper: CustomMapper,
    })
}

                
pub fn custom() -> (o: CustomCombinator)
    ensures o@ == spec_custom(),
{
    CustomCombinator(
    Mapped {
        inner: (name(), my_custom_section()),
        mapper: CustomMapper,
    })
}

                

pub struct SpecCustomsec {
    pub size: u64,
    pub cont: SpecCustom,
}

pub type SpecCustomsecInner = (u64, SpecCustom);


impl SpecFrom<SpecCustomsec> for SpecCustomsecInner {
    open spec fn spec_from(m: SpecCustomsec) -> SpecCustomsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecCustomsecInner> for SpecCustomsec {
    open spec fn spec_from(m: SpecCustomsecInner) -> SpecCustomsec {
        let (size, cont) = m;
        SpecCustomsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Customsec {
    pub size: u64,
    pub cont: Custom,
}

impl View for Customsec {
    type V = SpecCustomsec;

    open spec fn view(&self) -> Self::V {
        SpecCustomsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type CustomsecInner = (u64, Custom);

pub type CustomsecInnerRef<'a> = (&'a u64, &'a Custom);
impl<'a> From<&'a Customsec> for CustomsecInnerRef<'a> {
    fn ex_from(m: &'a Customsec) -> CustomsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<CustomsecInner> for Customsec {
    fn ex_from(m: CustomsecInner) -> Customsec {
        let (size, cont) = m;
        Customsec { size, cont }
    }
}

pub struct CustomsecMapper;
impl View for CustomsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CustomsecMapper {
    type Src = SpecCustomsecInner;
    type Dst = SpecCustomsec;
}
impl SpecIsoProof for CustomsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CustomsecMapper {
    type Src = CustomsecInner;
    type Dst = Customsec;
    type RefSrc = CustomsecInnerRef<'a>;
}

pub struct SpecCustomsecCombinator(SpecCustomsecCombinatorAlias);

impl SpecCombinator for SpecCustomsecCombinator {
    type Type = SpecCustomsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCustomsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCustomsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecCustomsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecCustomCombinator>>, CustomsecMapper>;

pub struct CustomsecCombinator(CustomsecCombinatorAlias);

impl View for CustomsecCombinator {
    type V = SpecCustomsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecCustomsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CustomsecCombinator {
    type Type = Customsec;
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
pub type CustomsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, CustomCombinator>, CustomsecCont0>, CustomsecMapper>;


pub closed spec fn spec_customsec() -> SpecCustomsecCombinator {
    SpecCustomsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_customsec_cont0(deps)),
        mapper: CustomsecMapper,
    })
}

pub open spec fn spec_customsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecCustomCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_custom())
}

impl View for CustomsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecCustomCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_customsec_cont0(deps)
        }
    }
}

                
pub fn customsec() -> (o: CustomsecCombinator)
    ensures o@ == spec_customsec(),
{
    CustomsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, CustomsecCont0),
        mapper: CustomsecMapper,
    })
}

pub struct CustomsecCont0;
type CustomsecCont0Type<'a, 'b> = &'b u64;
type CustomsecCont0SType<'a, 'x> = &'x u64;
type CustomsecCont0Input<'a, 'b, 'x> = POrSType<CustomsecCont0Type<'a, 'b>, CustomsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CustomsecCont0Input<'a, 'b, 'x>> for CustomsecCont0 {
    type Output = AndThen<bytes::Variable, CustomCombinator>;

    open spec fn requires(&self, deps: CustomsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CustomsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_customsec_cont0(deps@)
    }

    fn apply(&self, deps: CustomsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), custom())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), custom())
            }
        }
    }
}
                

pub struct SpecExports {
    pub l: u64,
    pub v: Seq<SpecExport>,
}

pub type SpecExportsInner = (u64, Seq<SpecExport>);


impl SpecFrom<SpecExports> for SpecExportsInner {
    open spec fn spec_from(m: SpecExports) -> SpecExportsInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecExportsInner> for SpecExports {
    open spec fn spec_from(m: SpecExportsInner) -> SpecExports {
        let (l, v) = m;
        SpecExports { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exports {
    pub l: u64,
    pub v: RepeatResult<Export>,
}

impl View for Exports {
    type V = SpecExports;

    open spec fn view(&self) -> Self::V {
        SpecExports {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ExportsInner = (u64, RepeatResult<Export>);

pub type ExportsInnerRef<'a> = (&'a u64, &'a RepeatResult<Export>);
impl<'a> From<&'a Exports> for ExportsInnerRef<'a> {
    fn ex_from(m: &'a Exports) -> ExportsInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<ExportsInner> for Exports {
    fn ex_from(m: ExportsInner) -> Exports {
        let (l, v) = m;
        Exports { l, v }
    }
}

pub struct ExportsMapper;
impl View for ExportsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportsMapper {
    type Src = SpecExportsInner;
    type Dst = SpecExports;
}
impl SpecIsoProof for ExportsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExportsMapper {
    type Src = ExportsInner;
    type Dst = Exports;
    type RefSrc = ExportsInnerRef<'a>;
}

pub struct SpecExportsCombinator(SpecExportsCombinatorAlias);

impl SpecCombinator for SpecExportsCombinator {
    type Type = SpecExports;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportsCombinatorAlias::is_prefix_secure() }
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
pub type SpecExportsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecExportCombinator>>, ExportsMapper>;

pub struct ExportsCombinator(ExportsCombinatorAlias);

impl View for ExportsCombinator {
    type V = SpecExportsCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExportsCombinator {
    type Type = Exports;
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
pub type ExportsCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ExportCombinator>, ExportsCont0>, ExportsMapper>;


pub closed spec fn spec_exports() -> SpecExportsCombinator {
    SpecExportsCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_exports_cont0(deps)),
        mapper: ExportsMapper,
    })
}

pub open spec fn spec_exports_cont0(deps: u64) -> RepeatN<SpecExportCombinator> {
    let l = deps;
    RepeatN(spec_export(), l.spec_into())
}

impl View for ExportsCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecExportCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_exports_cont0(deps)
        }
    }
}

                
pub fn exports() -> (o: ExportsCombinator)
    ensures o@ == spec_exports(),
{
    ExportsCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ExportsCont0),
        mapper: ExportsMapper,
    })
}

pub struct ExportsCont0;
type ExportsCont0Type<'a, 'b> = &'b u64;
type ExportsCont0SType<'a, 'x> = &'x u64;
type ExportsCont0Input<'a, 'b, 'x> = POrSType<ExportsCont0Type<'a, 'b>, ExportsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ExportsCont0Input<'a, 'b, 'x>> for ExportsCont0 {
    type Output = RepeatN<ExportCombinator>;

    open spec fn requires(&self, deps: ExportsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ExportsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_exports_cont0(deps@)
    }

    fn apply(&self, deps: ExportsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(export(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(export(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecDatacountsec {
    pub size: u64,
    pub cont: u64,
}

pub type SpecDatacountsecInner = (u64, u64);


impl SpecFrom<SpecDatacountsec> for SpecDatacountsecInner {
    open spec fn spec_from(m: SpecDatacountsec) -> SpecDatacountsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecDatacountsecInner> for SpecDatacountsec {
    open spec fn spec_from(m: SpecDatacountsecInner) -> SpecDatacountsec {
        let (size, cont) = m;
        SpecDatacountsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Datacountsec {
    pub size: u64,
    pub cont: u64,
}

impl View for Datacountsec {
    type V = SpecDatacountsec;

    open spec fn view(&self) -> Self::V {
        SpecDatacountsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type DatacountsecInner = (u64, u64);

pub type DatacountsecInnerRef<'a> = (&'a u64, &'a u64);
impl<'a> From<&'a Datacountsec> for DatacountsecInnerRef<'a> {
    fn ex_from(m: &'a Datacountsec) -> DatacountsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<DatacountsecInner> for Datacountsec {
    fn ex_from(m: DatacountsecInner) -> Datacountsec {
        let (size, cont) = m;
        Datacountsec { size, cont }
    }
}

pub struct DatacountsecMapper;
impl View for DatacountsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for DatacountsecMapper {
    type Src = SpecDatacountsecInner;
    type Dst = SpecDatacountsec;
}
impl SpecIsoProof for DatacountsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for DatacountsecMapper {
    type Src = DatacountsecInner;
    type Dst = Datacountsec;
    type RefSrc = DatacountsecInnerRef<'a>;
}

pub struct SpecDatacountsecCombinator(SpecDatacountsecCombinatorAlias);

impl SpecCombinator for SpecDatacountsecCombinator {
    type Type = SpecDatacountsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecDatacountsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDatacountsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecDatacountsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, UnsignedLEB128>>, DatacountsecMapper>;

pub struct DatacountsecCombinator(DatacountsecCombinatorAlias);

impl View for DatacountsecCombinator {
    type V = SpecDatacountsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecDatacountsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for DatacountsecCombinator {
    type Type = Datacountsec;
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
pub type DatacountsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, UnsignedLEB128>, DatacountsecCont0>, DatacountsecMapper>;


pub closed spec fn spec_datacountsec() -> SpecDatacountsecCombinator {
    SpecDatacountsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_datacountsec_cont0(deps)),
        mapper: DatacountsecMapper,
    })
}

pub open spec fn spec_datacountsec_cont0(deps: u64) -> AndThen<bytes::Variable, UnsignedLEB128> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), UnsignedLEB128)
}

impl View for DatacountsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, UnsignedLEB128>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_datacountsec_cont0(deps)
        }
    }
}

                
pub fn datacountsec() -> (o: DatacountsecCombinator)
    ensures o@ == spec_datacountsec(),
{
    DatacountsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, DatacountsecCont0),
        mapper: DatacountsecMapper,
    })
}

pub struct DatacountsecCont0;
type DatacountsecCont0Type<'a, 'b> = &'b u64;
type DatacountsecCont0SType<'a, 'x> = &'x u64;
type DatacountsecCont0Input<'a, 'b, 'x> = POrSType<DatacountsecCont0Type<'a, 'b>, DatacountsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<DatacountsecCont0Input<'a, 'b, 'x>> for DatacountsecCont0 {
    type Output = AndThen<bytes::Variable, UnsignedLEB128>;

    open spec fn requires(&self, deps: DatacountsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: DatacountsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_datacountsec_cont0(deps@)
    }

    fn apply(&self, deps: DatacountsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), UnsignedLEB128)
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), UnsignedLEB128)
            }
        }
    }
}
                

pub struct SpecCodesec {
    pub size: u64,
    pub cont: SpecCodesecContent,
}

pub type SpecCodesecInner = (u64, SpecCodesecContent);


impl SpecFrom<SpecCodesec> for SpecCodesecInner {
    open spec fn spec_from(m: SpecCodesec) -> SpecCodesecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecCodesecInner> for SpecCodesec {
    open spec fn spec_from(m: SpecCodesecInner) -> SpecCodesec {
        let (size, cont) = m;
        SpecCodesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Codesec<'a> {
    pub size: u64,
    pub cont: CodesecContent<'a>,
}

impl View for Codesec<'_> {
    type V = SpecCodesec;

    open spec fn view(&self) -> Self::V {
        SpecCodesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type CodesecInner<'a> = (u64, CodesecContent<'a>);

pub type CodesecInnerRef<'a> = (&'a u64, &'a CodesecContent<'a>);
impl<'a> From<&'a Codesec<'a>> for CodesecInnerRef<'a> {
    fn ex_from(m: &'a Codesec) -> CodesecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl<'a> From<CodesecInner<'a>> for Codesec<'a> {
    fn ex_from(m: CodesecInner) -> Codesec {
        let (size, cont) = m;
        Codesec { size, cont }
    }
}

pub struct CodesecMapper;
impl View for CodesecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CodesecMapper {
    type Src = SpecCodesecInner;
    type Dst = SpecCodesec;
}
impl SpecIsoProof for CodesecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for CodesecMapper {
    type Src = CodesecInner<'a>;
    type Dst = Codesec<'a>;
    type RefSrc = CodesecInnerRef<'a>;
}

pub struct SpecCodesecCombinator(SpecCodesecCombinatorAlias);

impl SpecCombinator for SpecCodesecCombinator {
    type Type = SpecCodesec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecCodesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCodesecCombinatorAlias::is_prefix_secure() }
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
pub type SpecCodesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecCodesecContentCombinator>>, CodesecMapper>;

pub struct CodesecCombinator(CodesecCombinatorAlias);

impl View for CodesecCombinator {
    type V = SpecCodesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecCodesecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for CodesecCombinator {
    type Type = Codesec<'a>;
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
pub type CodesecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, CodesecContentCombinator>, CodesecCont0>, CodesecMapper>;


pub closed spec fn spec_codesec() -> SpecCodesecCombinator {
    SpecCodesecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_codesec_cont0(deps)),
        mapper: CodesecMapper,
    })
}

pub open spec fn spec_codesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecCodesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_codesec_content())
}

impl View for CodesecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecCodesecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_codesec_cont0(deps)
        }
    }
}

                
pub fn codesec() -> (o: CodesecCombinator)
    ensures o@ == spec_codesec(),
{
    CodesecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, CodesecCont0),
        mapper: CodesecMapper,
    })
}

pub struct CodesecCont0;
type CodesecCont0Type<'a, 'b> = &'b u64;
type CodesecCont0SType<'a, 'x> = &'x u64;
type CodesecCont0Input<'a, 'b, 'x> = POrSType<CodesecCont0Type<'a, 'b>, CodesecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<CodesecCont0Input<'a, 'b, 'x>> for CodesecCont0 {
    type Output = AndThen<bytes::Variable, CodesecContentCombinator>;

    open spec fn requires(&self, deps: CodesecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: CodesecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_codesec_cont0(deps@)
    }

    fn apply(&self, deps: CodesecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), codesec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), codesec_content())
            }
        }
    }
}
                

pub struct SpecElemCodeData {
    pub elems: Option<SpecElemsec>,
    pub datacount: Option<SpecDatacountsec>,
    pub codes: Option<SpecCodesec>,
    pub datas: Option<SpecDatasec>,
}

pub type SpecElemCodeDataInner = (Option<SpecElemsec>, (Option<SpecDatacountsec>, (Option<SpecCodesec>, Option<SpecDatasec>)));


impl SpecFrom<SpecElemCodeData> for SpecElemCodeDataInner {
    open spec fn spec_from(m: SpecElemCodeData) -> SpecElemCodeDataInner {
        (m.elems, (m.datacount, (m.codes, m.datas)))
    }
}

impl SpecFrom<SpecElemCodeDataInner> for SpecElemCodeData {
    open spec fn spec_from(m: SpecElemCodeDataInner) -> SpecElemCodeData {
        let (elems, (datacount, (codes, datas))) = m;
        SpecElemCodeData { elems, datacount, codes, datas }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ElemCodeData<'a> {
    pub elems: Optional<Elemsec<'a>>,
    pub datacount: Optional<Datacountsec>,
    pub codes: Optional<Codesec<'a>>,
    pub datas: Optional<Datasec<'a>>,
}

impl View for ElemCodeData<'_> {
    type V = SpecElemCodeData;

    open spec fn view(&self) -> Self::V {
        SpecElemCodeData {
            elems: self.elems@,
            datacount: self.datacount@,
            codes: self.codes@,
            datas: self.datas@,
        }
    }
}
pub type ElemCodeDataInner<'a> = (Optional<Elemsec<'a>>, (Optional<Datacountsec>, (Optional<Codesec<'a>>, Optional<Datasec<'a>>)));

pub type ElemCodeDataInnerRef<'a> = (&'a Optional<Elemsec<'a>>, (&'a Optional<Datacountsec>, (&'a Optional<Codesec<'a>>, &'a Optional<Datasec<'a>>)));
impl<'a> From<&'a ElemCodeData<'a>> for ElemCodeDataInnerRef<'a> {
    fn ex_from(m: &'a ElemCodeData) -> ElemCodeDataInnerRef<'a> {
        (&m.elems, (&m.datacount, (&m.codes, &m.datas)))
    }
}

impl<'a> From<ElemCodeDataInner<'a>> for ElemCodeData<'a> {
    fn ex_from(m: ElemCodeDataInner) -> ElemCodeData {
        let (elems, (datacount, (codes, datas))) = m;
        ElemCodeData { elems, datacount, codes, datas }
    }
}

pub struct ElemCodeDataMapper;
impl View for ElemCodeDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ElemCodeDataMapper {
    type Src = SpecElemCodeDataInner;
    type Dst = SpecElemCodeData;
}
impl SpecIsoProof for ElemCodeDataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ElemCodeDataMapper {
    type Src = ElemCodeDataInner<'a>;
    type Dst = ElemCodeData<'a>;
    type RefSrc = ElemCodeDataInnerRef<'a>;
}
pub const ELEMCODEDATAELEMS_0_FRONT_CONST: u8 = 9;

pub const ELEMCODEDATADATACOUNT_0_FRONT_CONST: u8 = 12;

pub const ELEMCODEDATACODES_0_FRONT_CONST: u8 = 10;

pub const ELEMCODEDATADATAS_0_FRONT_CONST: u8 = 11;


pub struct SpecElemCodeDataCombinator(SpecElemCodeDataCombinatorAlias);

impl SpecCombinator for SpecElemCodeDataCombinator {
    type Type = SpecElemCodeData;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecElemCodeDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecElemCodeDataCombinatorAlias::is_prefix_secure() }
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
pub type SpecElemCodeDataCombinatorAlias = Mapped<(Opt<Preceded<Tag<U8, u8>, SpecElemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecDatacountsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecCodesecCombinator>>, Opt<Preceded<Tag<U8, u8>, SpecDatasecCombinator>>))), ElemCodeDataMapper>;





pub struct ElemCodeDataCombinator(ElemCodeDataCombinatorAlias);

impl View for ElemCodeDataCombinator {
    type V = SpecElemCodeDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecElemCodeDataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ElemCodeDataCombinator {
    type Type = ElemCodeData<'a>;
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
pub type ElemCodeDataCombinatorAlias = Mapped<(Opt<Preceded<Tag<U8, u8>, ElemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, DatacountsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, CodesecCombinator>>, Opt<Preceded<Tag<U8, u8>, DatasecCombinator>>))), ElemCodeDataMapper>;


pub closed spec fn spec_elem_code_data() -> SpecElemCodeDataCombinator {
    SpecElemCodeDataCombinator(
    Mapped {
        inner: (Opt(Preceded(Tag::spec_new(U8, ELEMCODEDATAELEMS_0_FRONT_CONST), spec_elemsec())), (Opt(Preceded(Tag::spec_new(U8, ELEMCODEDATADATACOUNT_0_FRONT_CONST), spec_datacountsec())), (Opt(Preceded(Tag::spec_new(U8, ELEMCODEDATACODES_0_FRONT_CONST), spec_codesec())), Opt(Preceded(Tag::spec_new(U8, ELEMCODEDATADATAS_0_FRONT_CONST), spec_datasec()))))),
        mapper: ElemCodeDataMapper,
    })
}

                
pub fn elem_code_data() -> (o: ElemCodeDataCombinator)
    ensures o@ == spec_elem_code_data(),
{
    ElemCodeDataCombinator(
    Mapped {
        inner: (Opt::new(Preceded(Tag::new(U8, ELEMCODEDATAELEMS_0_FRONT_CONST), elemsec())), (Opt::new(Preceded(Tag::new(U8, ELEMCODEDATADATACOUNT_0_FRONT_CONST), datacountsec())), (Opt::new(Preceded(Tag::new(U8, ELEMCODEDATACODES_0_FRONT_CONST), codesec())), Opt::new(Preceded(Tag::new(U8, ELEMCODEDATADATAS_0_FRONT_CONST), datasec()))))),
        mapper: ElemCodeDataMapper,
    })
}

                

pub struct SpecExportsec {
    pub size: u64,
    pub cont: SpecExports,
}

pub type SpecExportsecInner = (u64, SpecExports);


impl SpecFrom<SpecExportsec> for SpecExportsecInner {
    open spec fn spec_from(m: SpecExportsec) -> SpecExportsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecExportsecInner> for SpecExportsec {
    open spec fn spec_from(m: SpecExportsecInner) -> SpecExportsec {
        let (size, cont) = m;
        SpecExportsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Exportsec {
    pub size: u64,
    pub cont: Exports,
}

impl View for Exportsec {
    type V = SpecExportsec;

    open spec fn view(&self) -> Self::V {
        SpecExportsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ExportsecInner = (u64, Exports);

pub type ExportsecInnerRef<'a> = (&'a u64, &'a Exports);
impl<'a> From<&'a Exportsec> for ExportsecInnerRef<'a> {
    fn ex_from(m: &'a Exportsec) -> ExportsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<ExportsecInner> for Exportsec {
    fn ex_from(m: ExportsecInner) -> Exportsec {
        let (size, cont) = m;
        Exportsec { size, cont }
    }
}

pub struct ExportsecMapper;
impl View for ExportsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExportsecMapper {
    type Src = SpecExportsecInner;
    type Dst = SpecExportsec;
}
impl SpecIsoProof for ExportsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ExportsecMapper {
    type Src = ExportsecInner;
    type Dst = Exportsec;
    type RefSrc = ExportsecInnerRef<'a>;
}

pub struct SpecExportsecCombinator(SpecExportsecCombinatorAlias);

impl SpecCombinator for SpecExportsecCombinator {
    type Type = SpecExportsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecExportsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExportsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecExportsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecExportsCombinator>>, ExportsecMapper>;

pub struct ExportsecCombinator(ExportsecCombinatorAlias);

impl View for ExportsecCombinator {
    type V = SpecExportsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecExportsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ExportsecCombinator {
    type Type = Exportsec;
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
pub type ExportsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, ExportsCombinator>, ExportsecCont0>, ExportsecMapper>;


pub closed spec fn spec_exportsec() -> SpecExportsecCombinator {
    SpecExportsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_exportsec_cont0(deps)),
        mapper: ExportsecMapper,
    })
}

pub open spec fn spec_exportsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecExportsCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_exports())
}

impl View for ExportsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecExportsCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_exportsec_cont0(deps)
        }
    }
}

                
pub fn exportsec() -> (o: ExportsecCombinator)
    ensures o@ == spec_exportsec(),
{
    ExportsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ExportsecCont0),
        mapper: ExportsecMapper,
    })
}

pub struct ExportsecCont0;
type ExportsecCont0Type<'a, 'b> = &'b u64;
type ExportsecCont0SType<'a, 'x> = &'x u64;
type ExportsecCont0Input<'a, 'b, 'x> = POrSType<ExportsecCont0Type<'a, 'b>, ExportsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ExportsecCont0Input<'a, 'b, 'x>> for ExportsecCont0 {
    type Output = AndThen<bytes::Variable, ExportsCombinator>;

    open spec fn requires(&self, deps: ExportsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ExportsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_exportsec_cont0(deps@)
    }

    fn apply(&self, deps: ExportsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), exports())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), exports())
            }
        }
    }
}
                
pub type SpecSigned64 = Seq<u8>;
pub type Signed64<'a> = &'a [u8];
pub type Signed64Ref<'a> = &'a &'a [u8];


pub struct SpecSigned64Combinator(SpecSigned64CombinatorAlias);

impl SpecCombinator for SpecSigned64Combinator {
    type Type = SpecSigned64;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecSigned64Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSigned64CombinatorAlias::is_prefix_secure() }
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
pub type SpecSigned64CombinatorAlias = bytes::Fixed<8>;

pub struct Signed64Combinator(Signed64CombinatorAlias);

impl View for Signed64Combinator {
    type V = SpecSigned64Combinator;
    closed spec fn view(&self) -> Self::V { SpecSigned64Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for Signed64Combinator {
    type Type = Signed64<'a>;
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
pub type Signed64CombinatorAlias = bytes::Fixed<8>;


pub closed spec fn spec_signed_64() -> SpecSigned64Combinator {
    SpecSigned64Combinator(bytes::Fixed::<8>)
}

                
pub fn signed_64() -> (o: Signed64Combinator)
    ensures o@ == spec_signed_64(),
{
    Signed64Combinator(bytes::Fixed::<8>)
}

                

pub struct SpecImport {
    pub module: SpecName,
    pub name: SpecName,
    pub desc: SpecImportdesc,
}

pub type SpecImportInner = (SpecName, (SpecName, SpecImportdesc));


impl SpecFrom<SpecImport> for SpecImportInner {
    open spec fn spec_from(m: SpecImport) -> SpecImportInner {
        (m.module, (m.name, m.desc))
    }
}

impl SpecFrom<SpecImportInner> for SpecImport {
    open spec fn spec_from(m: SpecImportInner) -> SpecImport {
        let (module, (name, desc)) = m;
        SpecImport { module, name, desc }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Import {
    pub module: Name,
    pub name: Name,
    pub desc: Importdesc,
}

impl View for Import {
    type V = SpecImport;

    open spec fn view(&self) -> Self::V {
        SpecImport {
            module: self.module@,
            name: self.name@,
            desc: self.desc@,
        }
    }
}
pub type ImportInner = (Name, (Name, Importdesc));

pub type ImportInnerRef<'a> = (&'a Name, (&'a Name, &'a Importdesc));
impl<'a> From<&'a Import> for ImportInnerRef<'a> {
    fn ex_from(m: &'a Import) -> ImportInnerRef<'a> {
        (&m.module, (&m.name, &m.desc))
    }
}

impl From<ImportInner> for Import {
    fn ex_from(m: ImportInner) -> Import {
        let (module, (name, desc)) = m;
        Import { module, name, desc }
    }
}

pub struct ImportMapper;
impl View for ImportMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportMapper {
    type Src = SpecImportInner;
    type Dst = SpecImport;
}
impl SpecIsoProof for ImportMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ImportMapper {
    type Src = ImportInner;
    type Dst = Import;
    type RefSrc = ImportInnerRef<'a>;
}

pub struct SpecImportCombinator(SpecImportCombinatorAlias);

impl SpecCombinator for SpecImportCombinator {
    type Type = SpecImport;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportCombinatorAlias::is_prefix_secure() }
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
pub type SpecImportCombinatorAlias = Mapped<(SpecNameCombinator, (SpecNameCombinator, SpecImportdescCombinator)), ImportMapper>;

pub struct ImportCombinator(ImportCombinatorAlias);

impl View for ImportCombinator {
    type V = SpecImportCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ImportCombinator {
    type Type = Import;
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
pub type ImportCombinatorAlias = Mapped<(NameCombinator, (NameCombinator, ImportdescCombinator)), ImportMapper>;


pub closed spec fn spec_import() -> SpecImportCombinator {
    SpecImportCombinator(
    Mapped {
        inner: (spec_name(), (spec_name(), spec_importdesc())),
        mapper: ImportMapper,
    })
}

                
pub fn import() -> (o: ImportCombinator)
    ensures o@ == spec_import(),
{
    ImportCombinator(
    Mapped {
        inner: (name(), (name(), importdesc())),
        mapper: ImportMapper,
    })
}

                

pub struct SpecImports {
    pub l: u64,
    pub v: Seq<SpecImport>,
}

pub type SpecImportsInner = (u64, Seq<SpecImport>);


impl SpecFrom<SpecImports> for SpecImportsInner {
    open spec fn spec_from(m: SpecImports) -> SpecImportsInner {
        (m.l, m.v)
    }
}

impl SpecFrom<SpecImportsInner> for SpecImports {
    open spec fn spec_from(m: SpecImportsInner) -> SpecImports {
        let (l, v) = m;
        SpecImports { l, v }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Imports {
    pub l: u64,
    pub v: RepeatResult<Import>,
}

impl View for Imports {
    type V = SpecImports;

    open spec fn view(&self) -> Self::V {
        SpecImports {
            l: self.l@,
            v: self.v@,
        }
    }
}
pub type ImportsInner = (u64, RepeatResult<Import>);

pub type ImportsInnerRef<'a> = (&'a u64, &'a RepeatResult<Import>);
impl<'a> From<&'a Imports> for ImportsInnerRef<'a> {
    fn ex_from(m: &'a Imports) -> ImportsInnerRef<'a> {
        (&m.l, &m.v)
    }
}

impl From<ImportsInner> for Imports {
    fn ex_from(m: ImportsInner) -> Imports {
        let (l, v) = m;
        Imports { l, v }
    }
}

pub struct ImportsMapper;
impl View for ImportsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportsMapper {
    type Src = SpecImportsInner;
    type Dst = SpecImports;
}
impl SpecIsoProof for ImportsMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ImportsMapper {
    type Src = ImportsInner;
    type Dst = Imports;
    type RefSrc = ImportsInnerRef<'a>;
}

pub struct SpecImportsCombinator(SpecImportsCombinatorAlias);

impl SpecCombinator for SpecImportsCombinator {
    type Type = SpecImports;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportsCombinatorAlias::is_prefix_secure() }
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
pub type SpecImportsCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, RepeatN<SpecImportCombinator>>, ImportsMapper>;

pub struct ImportsCombinator(ImportsCombinatorAlias);

impl View for ImportsCombinator {
    type V = SpecImportsCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportsCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ImportsCombinator {
    type Type = Imports;
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
pub type ImportsCombinatorAlias = Mapped<Pair<UnsignedLEB128, RepeatN<ImportCombinator>, ImportsCont0>, ImportsMapper>;


pub closed spec fn spec_imports() -> SpecImportsCombinator {
    SpecImportsCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_imports_cont0(deps)),
        mapper: ImportsMapper,
    })
}

pub open spec fn spec_imports_cont0(deps: u64) -> RepeatN<SpecImportCombinator> {
    let l = deps;
    RepeatN(spec_import(), l.spec_into())
}

impl View for ImportsCont0 {
    type V = spec_fn(u64) -> RepeatN<SpecImportCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_imports_cont0(deps)
        }
    }
}

                
pub fn imports() -> (o: ImportsCombinator)
    ensures o@ == spec_imports(),
{
    ImportsCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ImportsCont0),
        mapper: ImportsMapper,
    })
}

pub struct ImportsCont0;
type ImportsCont0Type<'a, 'b> = &'b u64;
type ImportsCont0SType<'a, 'x> = &'x u64;
type ImportsCont0Input<'a, 'b, 'x> = POrSType<ImportsCont0Type<'a, 'b>, ImportsCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ImportsCont0Input<'a, 'b, 'x>> for ImportsCont0 {
    type Output = RepeatN<ImportCombinator>;

    open spec fn requires(&self, deps: ImportsCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ImportsCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_imports_cont0(deps@)
    }

    fn apply(&self, deps: ImportsCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let l = *deps;
                RepeatN(import(), l.ex_into())
            }
            POrSType::S(deps) => {
                let l = deps;
                let l = *l;
                RepeatN(import(), l.ex_into())
            }
        }
    }
}
                

pub struct SpecModuleHeader {
    pub magic: Seq<u8>,
    pub version: Seq<u8>,
}

pub type SpecModuleHeaderInner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecModuleHeader> for SpecModuleHeaderInner {
    open spec fn spec_from(m: SpecModuleHeader) -> SpecModuleHeaderInner {
        (m.magic, m.version)
    }
}

impl SpecFrom<SpecModuleHeaderInner> for SpecModuleHeader {
    open spec fn spec_from(m: SpecModuleHeaderInner) -> SpecModuleHeader {
        let (magic, version) = m;
        SpecModuleHeader { magic, version }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct ModuleHeader<'a> {
    pub magic: &'a [u8],
    pub version: &'a [u8],
}

impl View for ModuleHeader<'_> {
    type V = SpecModuleHeader;

    open spec fn view(&self) -> Self::V {
        SpecModuleHeader {
            magic: self.magic@,
            version: self.version@,
        }
    }
}
pub type ModuleHeaderInner<'a> = (&'a [u8], &'a [u8]);

pub type ModuleHeaderInnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a ModuleHeader<'a>> for ModuleHeaderInnerRef<'a> {
    fn ex_from(m: &'a ModuleHeader) -> ModuleHeaderInnerRef<'a> {
        (&m.magic, &m.version)
    }
}

impl<'a> From<ModuleHeaderInner<'a>> for ModuleHeader<'a> {
    fn ex_from(m: ModuleHeaderInner) -> ModuleHeader {
        let (magic, version) = m;
        ModuleHeader { magic, version }
    }
}

pub struct ModuleHeaderMapper;
impl View for ModuleHeaderMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ModuleHeaderMapper {
    type Src = SpecModuleHeaderInner;
    type Dst = SpecModuleHeader;
}
impl SpecIsoProof for ModuleHeaderMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ModuleHeaderMapper {
    type Src = ModuleHeaderInner<'a>;
    type Dst = ModuleHeader<'a>;
    type RefSrc = ModuleHeaderInnerRef<'a>;
}
pub spec const SPEC_MODULEHEADERMAGIC_CONST: Seq<u8> = seq![0, 97, 115, 109];pub spec const SPEC_MODULEHEADERVERSION_CONST: Seq<u8> = seq![1, 0, 0, 0];
pub struct SpecModuleHeaderCombinator(SpecModuleHeaderCombinatorAlias);

impl SpecCombinator for SpecModuleHeaderCombinator {
    type Type = SpecModuleHeader;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecModuleHeaderCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecModuleHeaderCombinatorAlias::is_prefix_secure() }
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
pub type SpecModuleHeaderCombinatorAlias = Mapped<(Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>, Refined<bytes::Fixed<4>, TagPred<Seq<u8>>>), ModuleHeaderMapper>;
pub exec static MODULEHEADERMAGIC_CONST: [u8; 4]
    ensures MODULEHEADERMAGIC_CONST@ == SPEC_MODULEHEADERMAGIC_CONST,
{
    let arr: [u8; 4] = [0, 97, 115, 109];
    assert(arr@ == SPEC_MODULEHEADERMAGIC_CONST);
    arr
}
pub exec static MODULEHEADERVERSION_CONST: [u8; 4]
    ensures MODULEHEADERVERSION_CONST@ == SPEC_MODULEHEADERVERSION_CONST,
{
    let arr: [u8; 4] = [1, 0, 0, 0];
    assert(arr@ == SPEC_MODULEHEADERVERSION_CONST);
    arr
}

pub struct ModuleHeaderCombinator(ModuleHeaderCombinatorAlias);

impl View for ModuleHeaderCombinator {
    type V = SpecModuleHeaderCombinator;
    closed spec fn view(&self) -> Self::V { SpecModuleHeaderCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ModuleHeaderCombinator {
    type Type = ModuleHeader<'a>;
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
pub type ModuleHeaderCombinatorAlias = Mapped<(Refined<bytes::Fixed<4>, TagPred<[u8; 4]>>, Refined<bytes::Fixed<4>, TagPred<[u8; 4]>>), ModuleHeaderMapper>;


pub closed spec fn spec_module_header() -> SpecModuleHeaderCombinator {
    SpecModuleHeaderCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MODULEHEADERMAGIC_CONST) }, Refined { inner: bytes::Fixed::<4>, predicate: TagPred(SPEC_MODULEHEADERVERSION_CONST) }),
        mapper: ModuleHeaderMapper,
    })
}

                
pub fn module_header() -> (o: ModuleHeaderCombinator)
    ensures o@ == spec_module_header(),
{
    ModuleHeaderCombinator(
    Mapped {
        inner: (Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MODULEHEADERMAGIC_CONST) }, Refined { inner: bytes::Fixed::<4>, predicate: TagPred(MODULEHEADERVERSION_CONST) }),
        mapper: ModuleHeaderMapper,
    })
}

                

pub struct SpecImportsec {
    pub size: u64,
    pub cont: SpecImports,
}

pub type SpecImportsecInner = (u64, SpecImports);


impl SpecFrom<SpecImportsec> for SpecImportsecInner {
    open spec fn spec_from(m: SpecImportsec) -> SpecImportsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecImportsecInner> for SpecImportsec {
    open spec fn spec_from(m: SpecImportsecInner) -> SpecImportsec {
        let (size, cont) = m;
        SpecImportsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Importsec {
    pub size: u64,
    pub cont: Imports,
}

impl View for Importsec {
    type V = SpecImportsec;

    open spec fn view(&self) -> Self::V {
        SpecImportsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type ImportsecInner = (u64, Imports);

pub type ImportsecInnerRef<'a> = (&'a u64, &'a Imports);
impl<'a> From<&'a Importsec> for ImportsecInnerRef<'a> {
    fn ex_from(m: &'a Importsec) -> ImportsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<ImportsecInner> for Importsec {
    fn ex_from(m: ImportsecInner) -> Importsec {
        let (size, cont) = m;
        Importsec { size, cont }
    }
}

pub struct ImportsecMapper;
impl View for ImportsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ImportsecMapper {
    type Src = SpecImportsecInner;
    type Dst = SpecImportsec;
}
impl SpecIsoProof for ImportsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ImportsecMapper {
    type Src = ImportsecInner;
    type Dst = Importsec;
    type RefSrc = ImportsecInnerRef<'a>;
}

pub struct SpecImportsecCombinator(SpecImportsecCombinatorAlias);

impl SpecCombinator for SpecImportsecCombinator {
    type Type = SpecImportsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecImportsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecImportsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecImportsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecImportsCombinator>>, ImportsecMapper>;

pub struct ImportsecCombinator(ImportsecCombinatorAlias);

impl View for ImportsecCombinator {
    type V = SpecImportsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecImportsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ImportsecCombinator {
    type Type = Importsec;
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
pub type ImportsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, ImportsCombinator>, ImportsecCont0>, ImportsecMapper>;


pub closed spec fn spec_importsec() -> SpecImportsecCombinator {
    SpecImportsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_importsec_cont0(deps)),
        mapper: ImportsecMapper,
    })
}

pub open spec fn spec_importsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecImportsCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_imports())
}

impl View for ImportsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecImportsCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_importsec_cont0(deps)
        }
    }
}

                
pub fn importsec() -> (o: ImportsecCombinator)
    ensures o@ == spec_importsec(),
{
    ImportsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, ImportsecCont0),
        mapper: ImportsecMapper,
    })
}

pub struct ImportsecCont0;
type ImportsecCont0Type<'a, 'b> = &'b u64;
type ImportsecCont0SType<'a, 'x> = &'x u64;
type ImportsecCont0Input<'a, 'b, 'x> = POrSType<ImportsecCont0Type<'a, 'b>, ImportsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<ImportsecCont0Input<'a, 'b, 'x>> for ImportsecCont0 {
    type Output = AndThen<bytes::Variable, ImportsCombinator>;

    open spec fn requires(&self, deps: ImportsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: ImportsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_importsec_cont0(deps@)
    }

    fn apply(&self, deps: ImportsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), imports())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), imports())
            }
        }
    }
}
                

pub struct SpecTablesec {
    pub size: u64,
    pub cont: SpecTablesecContent,
}

pub type SpecTablesecInner = (u64, SpecTablesecContent);


impl SpecFrom<SpecTablesec> for SpecTablesecInner {
    open spec fn spec_from(m: SpecTablesec) -> SpecTablesecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecTablesecInner> for SpecTablesec {
    open spec fn spec_from(m: SpecTablesecInner) -> SpecTablesec {
        let (size, cont) = m;
        SpecTablesec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tablesec {
    pub size: u64,
    pub cont: TablesecContent,
}

impl View for Tablesec {
    type V = SpecTablesec;

    open spec fn view(&self) -> Self::V {
        SpecTablesec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type TablesecInner = (u64, TablesecContent);

pub type TablesecInnerRef<'a> = (&'a u64, &'a TablesecContent);
impl<'a> From<&'a Tablesec> for TablesecInnerRef<'a> {
    fn ex_from(m: &'a Tablesec) -> TablesecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<TablesecInner> for Tablesec {
    fn ex_from(m: TablesecInner) -> Tablesec {
        let (size, cont) = m;
        Tablesec { size, cont }
    }
}

pub struct TablesecMapper;
impl View for TablesecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TablesecMapper {
    type Src = SpecTablesecInner;
    type Dst = SpecTablesec;
}
impl SpecIsoProof for TablesecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TablesecMapper {
    type Src = TablesecInner;
    type Dst = Tablesec;
    type RefSrc = TablesecInnerRef<'a>;
}

pub struct SpecTablesecCombinator(SpecTablesecCombinatorAlias);

impl SpecCombinator for SpecTablesecCombinator {
    type Type = SpecTablesec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTablesecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTablesecCombinatorAlias::is_prefix_secure() }
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
pub type SpecTablesecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecTablesecContentCombinator>>, TablesecMapper>;

pub struct TablesecCombinator(TablesecCombinatorAlias);

impl View for TablesecCombinator {
    type V = SpecTablesecCombinator;
    closed spec fn view(&self) -> Self::V { SpecTablesecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TablesecCombinator {
    type Type = Tablesec;
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
pub type TablesecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, TablesecContentCombinator>, TablesecCont0>, TablesecMapper>;


pub closed spec fn spec_tablesec() -> SpecTablesecCombinator {
    SpecTablesecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_tablesec_cont0(deps)),
        mapper: TablesecMapper,
    })
}

pub open spec fn spec_tablesec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecTablesecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_tablesec_content())
}

impl View for TablesecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecTablesecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_tablesec_cont0(deps)
        }
    }
}

                
pub fn tablesec() -> (o: TablesecCombinator)
    ensures o@ == spec_tablesec(),
{
    TablesecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, TablesecCont0),
        mapper: TablesecMapper,
    })
}

pub struct TablesecCont0;
type TablesecCont0Type<'a, 'b> = &'b u64;
type TablesecCont0SType<'a, 'x> = &'x u64;
type TablesecCont0Input<'a, 'b, 'x> = POrSType<TablesecCont0Type<'a, 'b>, TablesecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TablesecCont0Input<'a, 'b, 'x>> for TablesecCont0 {
    type Output = AndThen<bytes::Variable, TablesecContentCombinator>;

    open spec fn requires(&self, deps: TablesecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TablesecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tablesec_cont0(deps@)
    }

    fn apply(&self, deps: TablesecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), tablesec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), tablesec_content())
            }
        }
    }
}
                

pub struct SpecMemsec {
    pub size: u64,
    pub cont: SpecMemsecContent,
}

pub type SpecMemsecInner = (u64, SpecMemsecContent);


impl SpecFrom<SpecMemsec> for SpecMemsecInner {
    open spec fn spec_from(m: SpecMemsec) -> SpecMemsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecMemsecInner> for SpecMemsec {
    open spec fn spec_from(m: SpecMemsecInner) -> SpecMemsec {
        let (size, cont) = m;
        SpecMemsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Memsec {
    pub size: u64,
    pub cont: MemsecContent,
}

impl View for Memsec {
    type V = SpecMemsec;

    open spec fn view(&self) -> Self::V {
        SpecMemsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type MemsecInner = (u64, MemsecContent);

pub type MemsecInnerRef<'a> = (&'a u64, &'a MemsecContent);
impl<'a> From<&'a Memsec> for MemsecInnerRef<'a> {
    fn ex_from(m: &'a Memsec) -> MemsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<MemsecInner> for Memsec {
    fn ex_from(m: MemsecInner) -> Memsec {
        let (size, cont) = m;
        Memsec { size, cont }
    }
}

pub struct MemsecMapper;
impl View for MemsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MemsecMapper {
    type Src = SpecMemsecInner;
    type Dst = SpecMemsec;
}
impl SpecIsoProof for MemsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MemsecMapper {
    type Src = MemsecInner;
    type Dst = Memsec;
    type RefSrc = MemsecInnerRef<'a>;
}

pub struct SpecMemsecCombinator(SpecMemsecCombinatorAlias);

impl SpecCombinator for SpecMemsecCombinator {
    type Type = SpecMemsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMemsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMemsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecMemsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecMemsecContentCombinator>>, MemsecMapper>;

pub struct MemsecCombinator(MemsecCombinatorAlias);

impl View for MemsecCombinator {
    type V = SpecMemsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecMemsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MemsecCombinator {
    type Type = Memsec;
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
pub type MemsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, MemsecContentCombinator>, MemsecCont0>, MemsecMapper>;


pub closed spec fn spec_memsec() -> SpecMemsecCombinator {
    SpecMemsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_memsec_cont0(deps)),
        mapper: MemsecMapper,
    })
}

pub open spec fn spec_memsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecMemsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_memsec_content())
}

impl View for MemsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecMemsecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_memsec_cont0(deps)
        }
    }
}

                
pub fn memsec() -> (o: MemsecCombinator)
    ensures o@ == spec_memsec(),
{
    MemsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, MemsecCont0),
        mapper: MemsecMapper,
    })
}

pub struct MemsecCont0;
type MemsecCont0Type<'a, 'b> = &'b u64;
type MemsecCont0SType<'a, 'x> = &'x u64;
type MemsecCont0Input<'a, 'b, 'x> = POrSType<MemsecCont0Type<'a, 'b>, MemsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<MemsecCont0Input<'a, 'b, 'x>> for MemsecCont0 {
    type Output = AndThen<bytes::Variable, MemsecContentCombinator>;

    open spec fn requires(&self, deps: MemsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: MemsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_memsec_cont0(deps@)
    }

    fn apply(&self, deps: MemsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), memsec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), memsec_content())
            }
        }
    }
}
                

pub struct SpecGlobalsec {
    pub size: u64,
    pub cont: SpecGlobalsecContent,
}

pub type SpecGlobalsecInner = (u64, SpecGlobalsecContent);


impl SpecFrom<SpecGlobalsec> for SpecGlobalsecInner {
    open spec fn spec_from(m: SpecGlobalsec) -> SpecGlobalsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecGlobalsecInner> for SpecGlobalsec {
    open spec fn spec_from(m: SpecGlobalsecInner) -> SpecGlobalsec {
        let (size, cont) = m;
        SpecGlobalsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Globalsec<'a> {
    pub size: u64,
    pub cont: GlobalsecContent<'a>,
}

impl View for Globalsec<'_> {
    type V = SpecGlobalsec;

    open spec fn view(&self) -> Self::V {
        SpecGlobalsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type GlobalsecInner<'a> = (u64, GlobalsecContent<'a>);

pub type GlobalsecInnerRef<'a> = (&'a u64, &'a GlobalsecContent<'a>);
impl<'a> From<&'a Globalsec<'a>> for GlobalsecInnerRef<'a> {
    fn ex_from(m: &'a Globalsec) -> GlobalsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl<'a> From<GlobalsecInner<'a>> for Globalsec<'a> {
    fn ex_from(m: GlobalsecInner) -> Globalsec {
        let (size, cont) = m;
        Globalsec { size, cont }
    }
}

pub struct GlobalsecMapper;
impl View for GlobalsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for GlobalsecMapper {
    type Src = SpecGlobalsecInner;
    type Dst = SpecGlobalsec;
}
impl SpecIsoProof for GlobalsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for GlobalsecMapper {
    type Src = GlobalsecInner<'a>;
    type Dst = Globalsec<'a>;
    type RefSrc = GlobalsecInnerRef<'a>;
}

pub struct SpecGlobalsecCombinator(SpecGlobalsecCombinatorAlias);

impl SpecCombinator for SpecGlobalsecCombinator {
    type Type = SpecGlobalsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecGlobalsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecGlobalsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecGlobalsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecGlobalsecContentCombinator>>, GlobalsecMapper>;

pub struct GlobalsecCombinator(GlobalsecCombinatorAlias);

impl View for GlobalsecCombinator {
    type V = SpecGlobalsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecGlobalsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for GlobalsecCombinator {
    type Type = Globalsec<'a>;
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
pub type GlobalsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, GlobalsecContentCombinator>, GlobalsecCont0>, GlobalsecMapper>;


pub closed spec fn spec_globalsec() -> SpecGlobalsecCombinator {
    SpecGlobalsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_globalsec_cont0(deps)),
        mapper: GlobalsecMapper,
    })
}

pub open spec fn spec_globalsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecGlobalsecContentCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_globalsec_content())
}

impl View for GlobalsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecGlobalsecContentCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_globalsec_cont0(deps)
        }
    }
}

                
pub fn globalsec() -> (o: GlobalsecCombinator)
    ensures o@ == spec_globalsec(),
{
    GlobalsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, GlobalsecCont0),
        mapper: GlobalsecMapper,
    })
}

pub struct GlobalsecCont0;
type GlobalsecCont0Type<'a, 'b> = &'b u64;
type GlobalsecCont0SType<'a, 'x> = &'x u64;
type GlobalsecCont0Input<'a, 'b, 'x> = POrSType<GlobalsecCont0Type<'a, 'b>, GlobalsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<GlobalsecCont0Input<'a, 'b, 'x>> for GlobalsecCont0 {
    type Output = AndThen<bytes::Variable, GlobalsecContentCombinator>;

    open spec fn requires(&self, deps: GlobalsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: GlobalsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_globalsec_cont0(deps@)
    }

    fn apply(&self, deps: GlobalsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), globalsec_content())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), globalsec_content())
            }
        }
    }
}
                

pub struct SpecStartsec {
    pub size: u64,
    pub cont: SpecStart,
}

pub type SpecStartsecInner = (u64, SpecStart);


impl SpecFrom<SpecStartsec> for SpecStartsecInner {
    open spec fn spec_from(m: SpecStartsec) -> SpecStartsecInner {
        (m.size, m.cont)
    }
}

impl SpecFrom<SpecStartsecInner> for SpecStartsec {
    open spec fn spec_from(m: SpecStartsecInner) -> SpecStartsec {
        let (size, cont) = m;
        SpecStartsec { size, cont }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Startsec {
    pub size: u64,
    pub cont: Start,
}

impl View for Startsec {
    type V = SpecStartsec;

    open spec fn view(&self) -> Self::V {
        SpecStartsec {
            size: self.size@,
            cont: self.cont@,
        }
    }
}
pub type StartsecInner = (u64, Start);

pub type StartsecInnerRef<'a> = (&'a u64, &'a Start);
impl<'a> From<&'a Startsec> for StartsecInnerRef<'a> {
    fn ex_from(m: &'a Startsec) -> StartsecInnerRef<'a> {
        (&m.size, &m.cont)
    }
}

impl From<StartsecInner> for Startsec {
    fn ex_from(m: StartsecInner) -> Startsec {
        let (size, cont) = m;
        Startsec { size, cont }
    }
}

pub struct StartsecMapper;
impl View for StartsecMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for StartsecMapper {
    type Src = SpecStartsecInner;
    type Dst = SpecStartsec;
}
impl SpecIsoProof for StartsecMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for StartsecMapper {
    type Src = StartsecInner;
    type Dst = Startsec;
    type RefSrc = StartsecInnerRef<'a>;
}

pub struct SpecStartsecCombinator(SpecStartsecCombinatorAlias);

impl SpecCombinator for SpecStartsecCombinator {
    type Type = SpecStartsec;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecStartsecCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecStartsecCombinatorAlias::is_prefix_secure() }
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
pub type SpecStartsecCombinatorAlias = Mapped<SpecPair<UnsignedLEB128, AndThen<bytes::Variable, SpecStartCombinator>>, StartsecMapper>;

pub struct StartsecCombinator(StartsecCombinatorAlias);

impl View for StartsecCombinator {
    type V = SpecStartsecCombinator;
    closed spec fn view(&self) -> Self::V { SpecStartsecCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for StartsecCombinator {
    type Type = Startsec;
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
pub type StartsecCombinatorAlias = Mapped<Pair<UnsignedLEB128, AndThen<bytes::Variable, StartCombinator>, StartsecCont0>, StartsecMapper>;


pub closed spec fn spec_startsec() -> SpecStartsecCombinator {
    SpecStartsecCombinator(
    Mapped {
        inner: Pair::spec_new(UnsignedLEB128, |deps| spec_startsec_cont0(deps)),
        mapper: StartsecMapper,
    })
}

pub open spec fn spec_startsec_cont0(deps: u64) -> AndThen<bytes::Variable, SpecStartCombinator> {
    let size = deps;
    AndThen(bytes::Variable(size.spec_into()), spec_start())
}

impl View for StartsecCont0 {
    type V = spec_fn(u64) -> AndThen<bytes::Variable, SpecStartCombinator>;

    open spec fn view(&self) -> Self::V {
        |deps: u64| {
            spec_startsec_cont0(deps)
        }
    }
}

                
pub fn startsec() -> (o: StartsecCombinator)
    ensures o@ == spec_startsec(),
{
    StartsecCombinator(
    Mapped {
        inner: Pair::new(UnsignedLEB128, StartsecCont0),
        mapper: StartsecMapper,
    })
}

pub struct StartsecCont0;
type StartsecCont0Type<'a, 'b> = &'b u64;
type StartsecCont0SType<'a, 'x> = &'x u64;
type StartsecCont0Input<'a, 'b, 'x> = POrSType<StartsecCont0Type<'a, 'b>, StartsecCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<StartsecCont0Input<'a, 'b, 'x>> for StartsecCont0 {
    type Output = AndThen<bytes::Variable, StartCombinator>;

    open spec fn requires(&self, deps: StartsecCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: StartsecCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_startsec_cont0(deps@)
    }

    fn apply(&self, deps: StartsecCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let size = *deps;
                AndThen(bytes::Variable(size.ex_into()), start())
            }
            POrSType::S(deps) => {
                let size = deps;
                let size = *size;
                AndThen(bytes::Variable(size.ex_into()), start())
            }
        }
    }
}
                

pub struct SpecModule {
    pub header: SpecModuleHeader,
    pub types: Option<SpecTypesec>,
    pub imports: Option<SpecImportsec>,
    pub typeidxs: Option<SpecFuncsec>,
    pub tables: Option<SpecTablesec>,
    pub mems: Option<SpecMemsec>,
    pub globals: Option<SpecGlobalsec>,
    pub exports: Option<SpecExportsec>,
    pub start: Option<SpecStartsec>,
    pub rest_secs: SpecElemCodeData,
}

pub type SpecModuleInner = (SpecModuleHeader, (Option<SpecTypesec>, (Option<SpecImportsec>, (Option<SpecFuncsec>, (Option<SpecTablesec>, (Option<SpecMemsec>, (Option<SpecGlobalsec>, (Option<SpecExportsec>, (Option<SpecStartsec>, SpecElemCodeData)))))))));


impl SpecFrom<SpecModule> for SpecModuleInner {
    open spec fn spec_from(m: SpecModule) -> SpecModuleInner {
        (m.header, (m.types, (m.imports, (m.typeidxs, (m.tables, (m.mems, (m.globals, (m.exports, (m.start, m.rest_secs)))))))))
    }
}

impl SpecFrom<SpecModuleInner> for SpecModule {
    open spec fn spec_from(m: SpecModuleInner) -> SpecModule {
        let (header, (types, (imports, (typeidxs, (tables, (mems, (globals, (exports, (start, rest_secs))))))))) = m;
        SpecModule { header, types, imports, typeidxs, tables, mems, globals, exports, start, rest_secs }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Module<'a> {
    pub header: ModuleHeader<'a>,
    pub types: Optional<Typesec>,
    pub imports: Optional<Importsec>,
    pub typeidxs: Optional<Funcsec>,
    pub tables: Optional<Tablesec>,
    pub mems: Optional<Memsec>,
    pub globals: Optional<Globalsec<'a>>,
    pub exports: Optional<Exportsec>,
    pub start: Optional<Startsec>,
    pub rest_secs: ElemCodeData<'a>,
}

impl View for Module<'_> {
    type V = SpecModule;

    open spec fn view(&self) -> Self::V {
        SpecModule {
            header: self.header@,
            types: self.types@,
            imports: self.imports@,
            typeidxs: self.typeidxs@,
            tables: self.tables@,
            mems: self.mems@,
            globals: self.globals@,
            exports: self.exports@,
            start: self.start@,
            rest_secs: self.rest_secs@,
        }
    }
}
pub type ModuleInner<'a> = (ModuleHeader<'a>, (Optional<Typesec>, (Optional<Importsec>, (Optional<Funcsec>, (Optional<Tablesec>, (Optional<Memsec>, (Optional<Globalsec<'a>>, (Optional<Exportsec>, (Optional<Startsec>, ElemCodeData<'a>)))))))));

pub type ModuleInnerRef<'a> = (&'a ModuleHeader<'a>, (&'a Optional<Typesec>, (&'a Optional<Importsec>, (&'a Optional<Funcsec>, (&'a Optional<Tablesec>, (&'a Optional<Memsec>, (&'a Optional<Globalsec<'a>>, (&'a Optional<Exportsec>, (&'a Optional<Startsec>, &'a ElemCodeData<'a>)))))))));
impl<'a> From<&'a Module<'a>> for ModuleInnerRef<'a> {
    fn ex_from(m: &'a Module) -> ModuleInnerRef<'a> {
        (&m.header, (&m.types, (&m.imports, (&m.typeidxs, (&m.tables, (&m.mems, (&m.globals, (&m.exports, (&m.start, &m.rest_secs)))))))))
    }
}

impl<'a> From<ModuleInner<'a>> for Module<'a> {
    fn ex_from(m: ModuleInner) -> Module {
        let (header, (types, (imports, (typeidxs, (tables, (mems, (globals, (exports, (start, rest_secs))))))))) = m;
        Module { header, types, imports, typeidxs, tables, mems, globals, exports, start, rest_secs }
    }
}

pub struct ModuleMapper;
impl View for ModuleMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ModuleMapper {
    type Src = SpecModuleInner;
    type Dst = SpecModule;
}
impl SpecIsoProof for ModuleMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ModuleMapper {
    type Src = ModuleInner<'a>;
    type Dst = Module<'a>;
    type RefSrc = ModuleInnerRef<'a>;
}
pub const MODULETYPES_0_FRONT_CONST: u8 = 1;

pub const MODULEIMPORTS_0_FRONT_CONST: u8 = 2;

pub const MODULETYPEIDXS_0_FRONT_CONST: u8 = 3;

pub const MODULETABLES_0_FRONT_CONST: u8 = 4;

pub const MODULEMEMS_0_FRONT_CONST: u8 = 5;

pub const MODULEGLOBALS_0_FRONT_CONST: u8 = 6;

pub const MODULEEXPORTS_0_FRONT_CONST: u8 = 7;

pub const MODULESTART_0_FRONT_CONST: u8 = 8;


pub struct SpecModuleCombinator(SpecModuleCombinatorAlias);

impl SpecCombinator for SpecModuleCombinator {
    type Type = SpecModule;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecModuleCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecModuleCombinatorAlias::is_prefix_secure() }
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
pub type SpecModuleCombinatorAlias = Mapped<(SpecModuleHeaderCombinator, (Opt<Preceded<Tag<U8, u8>, SpecTypesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecImportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecFuncsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecTablesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecMemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecGlobalsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecExportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, SpecStartsecCombinator>>, SpecElemCodeDataCombinator))))))))), ModuleMapper>;









pub struct ModuleCombinator(ModuleCombinatorAlias);

impl View for ModuleCombinator {
    type V = SpecModuleCombinator;
    closed spec fn view(&self) -> Self::V { SpecModuleCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ModuleCombinator {
    type Type = Module<'a>;
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
pub type ModuleCombinatorAlias = Mapped<(ModuleHeaderCombinator, (Opt<Preceded<Tag<U8, u8>, TypesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, ImportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, FuncsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, TablesecCombinator>>, (Opt<Preceded<Tag<U8, u8>, MemsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, GlobalsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, ExportsecCombinator>>, (Opt<Preceded<Tag<U8, u8>, StartsecCombinator>>, ElemCodeDataCombinator))))))))), ModuleMapper>;


pub closed spec fn spec_module() -> SpecModuleCombinator {
    SpecModuleCombinator(
    Mapped {
        inner: (spec_module_header(), (Opt(Preceded(Tag::spec_new(U8, MODULETYPES_0_FRONT_CONST), spec_typesec())), (Opt(Preceded(Tag::spec_new(U8, MODULEIMPORTS_0_FRONT_CONST), spec_importsec())), (Opt(Preceded(Tag::spec_new(U8, MODULETYPEIDXS_0_FRONT_CONST), spec_funcsec())), (Opt(Preceded(Tag::spec_new(U8, MODULETABLES_0_FRONT_CONST), spec_tablesec())), (Opt(Preceded(Tag::spec_new(U8, MODULEMEMS_0_FRONT_CONST), spec_memsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEGLOBALS_0_FRONT_CONST), spec_globalsec())), (Opt(Preceded(Tag::spec_new(U8, MODULEEXPORTS_0_FRONT_CONST), spec_exportsec())), (Opt(Preceded(Tag::spec_new(U8, MODULESTART_0_FRONT_CONST), spec_startsec())), spec_elem_code_data()))))))))),
        mapper: ModuleMapper,
    })
}

                
pub fn module() -> (o: ModuleCombinator)
    ensures o@ == spec_module(),
{
    ModuleCombinator(
    Mapped {
        inner: (module_header(), (Opt::new(Preceded(Tag::new(U8, MODULETYPES_0_FRONT_CONST), typesec())), (Opt::new(Preceded(Tag::new(U8, MODULEIMPORTS_0_FRONT_CONST), importsec())), (Opt::new(Preceded(Tag::new(U8, MODULETYPEIDXS_0_FRONT_CONST), funcsec())), (Opt::new(Preceded(Tag::new(U8, MODULETABLES_0_FRONT_CONST), tablesec())), (Opt::new(Preceded(Tag::new(U8, MODULEMEMS_0_FRONT_CONST), memsec())), (Opt::new(Preceded(Tag::new(U8, MODULEGLOBALS_0_FRONT_CONST), globalsec())), (Opt::new(Preceded(Tag::new(U8, MODULEEXPORTS_0_FRONT_CONST), exportsec())), (Opt::new(Preceded(Tag::new(U8, MODULESTART_0_FRONT_CONST), startsec())), elem_code_data()))))))))),
        mapper: ModuleMapper,
    })
}

                

}
