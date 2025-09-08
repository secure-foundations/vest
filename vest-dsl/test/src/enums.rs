
#![allow(warnings)]
#![allow(unused)]
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

macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::vstd::prelude::verus! {
            impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for $combinator {
                type Type = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::Type;
                type SType = <$combinator_alias as Combinator<'a, &'a [u8], Vec<u8>>>::SType;
                fn length(&self, v: Self::SType) -> usize
                { <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&self.0, v) }
                closed spec fn ex_requires(&self) -> bool
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

pub enum SpecAChooseWithDefault {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecAChooseWithDefaultInner = Either<u8, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecAChooseWithDefault> for SpecAChooseWithDefaultInner {
    open spec fn spec_from(m: SpecAChooseWithDefault) -> SpecAChooseWithDefaultInner {
        match m {
            SpecAChooseWithDefault::A(m) => Either::Left(m),
            SpecAChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            SpecAChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecAChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

                
impl SpecFrom<SpecAChooseWithDefaultInner> for SpecAChooseWithDefault {
    open spec fn spec_from(m: SpecAChooseWithDefaultInner) -> SpecAChooseWithDefault {
        match m {
            Either::Left(m) => SpecAChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => SpecAChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecAChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecAChooseWithDefault::Unrecognized(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AChooseWithDefault<'a> {
    A(u8),
    B(u16),
    C(u32),
    Unrecognized(&'a [u8]),
}

pub type AChooseWithDefaultInner<'a> = Either<u8, Either<u16, Either<u32, &'a [u8]>>>;

pub type AChooseWithDefaultInnerRef<'a> = Either<&'a u8, Either<&'a u16, Either<&'a u32, &'a &'a [u8]>>>;


impl<'a> View for AChooseWithDefault<'a> {
    type V = SpecAChooseWithDefault;
    open spec fn view(&self) -> Self::V {
        match self {
            AChooseWithDefault::A(m) => SpecAChooseWithDefault::A(m@),
            AChooseWithDefault::B(m) => SpecAChooseWithDefault::B(m@),
            AChooseWithDefault::C(m) => SpecAChooseWithDefault::C(m@),
            AChooseWithDefault::Unrecognized(m) => SpecAChooseWithDefault::Unrecognized(m@),
        }
    }
}


impl<'a> From<&'a AChooseWithDefault<'a>> for AChooseWithDefaultInnerRef<'a> {
    fn ex_from(m: &'a AChooseWithDefault<'a>) -> AChooseWithDefaultInnerRef<'a> {
        match m {
            AChooseWithDefault::A(m) => Either::Left(m),
            AChooseWithDefault::B(m) => Either::Right(Either::Left(m)),
            AChooseWithDefault::C(m) => Either::Right(Either::Right(Either::Left(m))),
            AChooseWithDefault::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }

}

impl<'a> From<AChooseWithDefaultInner<'a>> for AChooseWithDefault<'a> {
    fn ex_from(m: AChooseWithDefaultInner<'a>) -> AChooseWithDefault<'a> {
        match m {
            Either::Left(m) => AChooseWithDefault::A(m),
            Either::Right(Either::Left(m)) => AChooseWithDefault::B(m),
            Either::Right(Either::Right(Either::Left(m))) => AChooseWithDefault::C(m),
            Either::Right(Either::Right(Either::Right(m))) => AChooseWithDefault::Unrecognized(m),
        }
    }
    
}


pub struct AChooseWithDefaultMapper;
impl View for AChooseWithDefaultMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AChooseWithDefaultMapper {
    type Src = SpecAChooseWithDefaultInner;
    type Dst = SpecAChooseWithDefault;
}
impl SpecIsoProof for AChooseWithDefaultMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for AChooseWithDefaultMapper {
    type Src = AChooseWithDefaultInner<'a>;
    type Dst = AChooseWithDefault<'a>;
    type RefSrc = AChooseWithDefaultInnerRef<'a>;
}

type SpecAChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type SpecAChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, SpecAChooseWithDefaultCombinatorAlias1>;
type SpecAChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, SpecAChooseWithDefaultCombinatorAlias2>;
pub struct SpecAChooseWithDefaultCombinator(SpecAChooseWithDefaultCombinatorAlias);

impl SpecCombinator for SpecAChooseWithDefaultCombinator {
    type Type = SpecAChooseWithDefault;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAChooseWithDefaultCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAChooseWithDefaultCombinatorAlias::is_prefix_secure() }
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
pub type SpecAChooseWithDefaultCombinatorAlias = Mapped<SpecAChooseWithDefaultCombinatorAlias3, AChooseWithDefaultMapper>;
type AChooseWithDefaultCombinatorAlias1 = Choice<Cond<U32Le>, Cond<bytes::Tail>>;
type AChooseWithDefaultCombinatorAlias2 = Choice<Cond<U16Le>, AChooseWithDefaultCombinator1>;
type AChooseWithDefaultCombinatorAlias3 = Choice<Cond<U8>, AChooseWithDefaultCombinator2>;
struct AChooseWithDefaultCombinator1(AChooseWithDefaultCombinatorAlias1);
impl View for AChooseWithDefaultCombinator1 {
    type V = SpecAChooseWithDefaultCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator1, AChooseWithDefaultCombinatorAlias1);

struct AChooseWithDefaultCombinator2(AChooseWithDefaultCombinatorAlias2);
impl View for AChooseWithDefaultCombinator2 {
    type V = SpecAChooseWithDefaultCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator2, AChooseWithDefaultCombinatorAlias2);

struct AChooseWithDefaultCombinator3(AChooseWithDefaultCombinatorAlias3);
impl View for AChooseWithDefaultCombinator3 {
    type V = SpecAChooseWithDefaultCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(AChooseWithDefaultCombinator3, AChooseWithDefaultCombinatorAlias3);

pub struct AChooseWithDefaultCombinator(AChooseWithDefaultCombinatorAlias);

impl View for AChooseWithDefaultCombinator {
    type V = SpecAChooseWithDefaultCombinator;
    closed spec fn view(&self) -> Self::V { SpecAChooseWithDefaultCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AChooseWithDefaultCombinator {
    type Type = AChooseWithDefault<'a>;
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
pub type AChooseWithDefaultCombinatorAlias = Mapped<AChooseWithDefaultCombinator3, AChooseWithDefaultMapper>;


pub closed spec fn spec_a_choose_with_default(e: SpecAnOpenEnum) -> SpecAChooseWithDefaultCombinator {
    SpecAChooseWithDefaultCombinator(Mapped { inner: Choice(Cond { cond: e == 0, inner: U8 }, Choice(Cond { cond: e == 1, inner: U16Le }, Choice(Cond { cond: e == 2, inner: U32Le }, Cond { cond: !(e == 0 || e == 1 || e == 2), inner: bytes::Tail }))), mapper: AChooseWithDefaultMapper })
}

pub fn a_choose_with_default<'a>(e: AnOpenEnum) -> (o: AChooseWithDefaultCombinator)
    ensures o@ == spec_a_choose_with_default(e@),
{
    AChooseWithDefaultCombinator(Mapped { inner: AChooseWithDefaultCombinator3(Choice::new(Cond { cond: e == 0, inner: U8 }, AChooseWithDefaultCombinator2(Choice::new(Cond { cond: e == 1, inner: U16Le }, AChooseWithDefaultCombinator1(Choice::new(Cond { cond: e == 2, inner: U32Le }, Cond { cond: !(e == 0 || e == 1 || e == 2), inner: bytes::Tail })))))), mapper: AChooseWithDefaultMapper })
}


pub enum SpecANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type SpecANonDependentChooseInner = Either<u8, Either<u8, u8>>;

impl SpecFrom<SpecANonDependentChoose> for SpecANonDependentChooseInner {
    open spec fn spec_from(m: SpecANonDependentChoose) -> SpecANonDependentChooseInner {
        match m {
            SpecANonDependentChoose::Variant1(m) => Either::Left(m),
            SpecANonDependentChoose::Variant2(m) => Either::Right(Either::Left(m)),
            SpecANonDependentChoose::Variant3(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecANonDependentChooseInner> for SpecANonDependentChoose {
    open spec fn spec_from(m: SpecANonDependentChooseInner) -> SpecANonDependentChoose {
        match m {
            Either::Left(m) => SpecANonDependentChoose::Variant1(m),
            Either::Right(Either::Left(m)) => SpecANonDependentChoose::Variant2(m),
            Either::Right(Either::Right(m)) => SpecANonDependentChoose::Variant3(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ANonDependentChoose {
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
}

pub type ANonDependentChooseInner = Either<u8, Either<u8, u8>>;

pub type ANonDependentChooseInnerRef<'a> = Either<&'a u8, Either<&'a u8, &'a u8>>;


impl View for ANonDependentChoose {
    type V = SpecANonDependentChoose;
    open spec fn view(&self) -> Self::V {
        match self {
            ANonDependentChoose::Variant1(m) => SpecANonDependentChoose::Variant1(m@),
            ANonDependentChoose::Variant2(m) => SpecANonDependentChoose::Variant2(m@),
            ANonDependentChoose::Variant3(m) => SpecANonDependentChoose::Variant3(m@),
        }
    }
}


impl<'a> From<&'a ANonDependentChoose> for ANonDependentChooseInnerRef<'a> {
    fn ex_from(m: &'a ANonDependentChoose) -> ANonDependentChooseInnerRef<'a> {
        match m {
            ANonDependentChoose::Variant1(m) => Either::Left(m),
            ANonDependentChoose::Variant2(m) => Either::Right(Either::Left(m)),
            ANonDependentChoose::Variant3(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ANonDependentChooseInner> for ANonDependentChoose {
    fn ex_from(m: ANonDependentChooseInner) -> ANonDependentChoose {
        match m {
            Either::Left(m) => ANonDependentChoose::Variant1(m),
            Either::Right(Either::Left(m)) => ANonDependentChoose::Variant2(m),
            Either::Right(Either::Right(m)) => ANonDependentChoose::Variant3(m),
        }
    }
    
}


pub struct ANonDependentChooseMapper;
impl View for ANonDependentChooseMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ANonDependentChooseMapper {
    type Src = SpecANonDependentChooseInner;
    type Dst = SpecANonDependentChoose;
}
impl SpecIsoProof for ANonDependentChooseMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ANonDependentChooseMapper {
    type Src = ANonDependentChooseInner;
    type Dst = ANonDependentChoose;
    type RefSrc = ANonDependentChooseInnerRef<'a>;
}

type SpecANonDependentChooseCombinatorAlias1 = Choice<Refined<U8, Predicate3779459584691363859>, Refined<U8, Predicate16013864750610309580>>;
type SpecANonDependentChooseCombinatorAlias2 = Choice<Refined<U8, Predicate8434700403445569729>, SpecANonDependentChooseCombinatorAlias1>;
pub struct SpecANonDependentChooseCombinator(SpecANonDependentChooseCombinatorAlias);

impl SpecCombinator for SpecANonDependentChooseCombinator {
    type Type = SpecANonDependentChoose;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecANonDependentChooseCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecANonDependentChooseCombinatorAlias::is_prefix_secure() }
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
pub type SpecANonDependentChooseCombinatorAlias = Mapped<SpecANonDependentChooseCombinatorAlias2, ANonDependentChooseMapper>;
pub struct Predicate8434700403445569729;
impl View for Predicate8434700403445569729 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8434700403445569729 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10)
    }
}
impl SpecPred<u8> for Predicate8434700403445569729 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10)
    }
}
pub struct Predicate3779459584691363859;
impl View for Predicate3779459584691363859 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3779459584691363859 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 11 && i <= 20)
    }
}
impl SpecPred<u8> for Predicate3779459584691363859 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 11 && i <= 20)
    }
}
pub struct Predicate16013864750610309580;
impl View for Predicate16013864750610309580 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16013864750610309580 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 21)
    }
}
impl SpecPred<u8> for Predicate16013864750610309580 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 21)
    }
}
type ANonDependentChooseCombinatorAlias1 = Choice<Refined<U8, Predicate3779459584691363859>, Refined<U8, Predicate16013864750610309580>>;
type ANonDependentChooseCombinatorAlias2 = Choice<Refined<U8, Predicate8434700403445569729>, ANonDependentChooseCombinator1>;
struct ANonDependentChooseCombinator1(ANonDependentChooseCombinatorAlias1);
impl View for ANonDependentChooseCombinator1 {
    type V = SpecANonDependentChooseCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ANonDependentChooseCombinator1, ANonDependentChooseCombinatorAlias1);

struct ANonDependentChooseCombinator2(ANonDependentChooseCombinatorAlias2);
impl View for ANonDependentChooseCombinator2 {
    type V = SpecANonDependentChooseCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ANonDependentChooseCombinator2, ANonDependentChooseCombinatorAlias2);

pub struct ANonDependentChooseCombinator(ANonDependentChooseCombinatorAlias);

impl View for ANonDependentChooseCombinator {
    type V = SpecANonDependentChooseCombinator;
    closed spec fn view(&self) -> Self::V { SpecANonDependentChooseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ANonDependentChooseCombinator {
    type Type = ANonDependentChoose;
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
pub type ANonDependentChooseCombinatorAlias = Mapped<ANonDependentChooseCombinator2, ANonDependentChooseMapper>;


pub closed spec fn spec_a_non_dependent_choose() -> SpecANonDependentChooseCombinator {
    SpecANonDependentChooseCombinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate8434700403445569729 }, Choice(Refined { inner: U8, predicate: Predicate3779459584691363859 }, Refined { inner: U8, predicate: Predicate16013864750610309580 })), mapper: ANonDependentChooseMapper })
}

                
pub fn a_non_dependent_choose() -> (o: ANonDependentChooseCombinator)
    ensures o@ == spec_a_non_dependent_choose(),
{
    ANonDependentChooseCombinator(Mapped { inner: ANonDependentChooseCombinator2(Choice::new(Refined { inner: U8, predicate: Predicate8434700403445569729 }, ANonDependentChooseCombinator1(Choice::new(Refined { inner: U8, predicate: Predicate3779459584691363859 }, Refined { inner: U8, predicate: Predicate16013864750610309580 })))), mapper: ANonDependentChooseMapper })
}

                

pub spec const SPEC_AClosedEnum_A: u8 = 0;
pub spec const SPEC_AClosedEnum_B: u8 = 1;
pub spec const SPEC_AClosedEnum_C: u8 = 2;
pub exec static EXEC_AClosedEnum_A: u8 ensures EXEC_AClosedEnum_A == SPEC_AClosedEnum_A { 0 }
pub exec static EXEC_AClosedEnum_B: u8 ensures EXEC_AClosedEnum_B == SPEC_AClosedEnum_B { 1 }
pub exec static EXEC_AClosedEnum_C: u8 ensures EXEC_AClosedEnum_C == SPEC_AClosedEnum_C { 2 }

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AClosedEnum {
    A = 0,
B = 1,
C = 2
}
pub type SpecAClosedEnum = AClosedEnum;

pub type AClosedEnumInner = u8;

pub type AClosedEnumInnerRef<'a> = &'a u8;

impl View for AClosedEnum {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AClosedEnum> for AClosedEnumInner {
    type Error = ();

    open spec fn spec_try_from(v: AClosedEnum) -> Result<AClosedEnumInner, ()> {
        match v {
            AClosedEnum::A => Ok(SPEC_AClosedEnum_A),
            AClosedEnum::B => Ok(SPEC_AClosedEnum_B),
            AClosedEnum::C => Ok(SPEC_AClosedEnum_C),
        }
    }
}

impl TryFrom<AClosedEnumInner> for AClosedEnum {
    type Error = ();

    fn ex_try_from(v: AClosedEnumInner) -> Result<AClosedEnum, ()> {
        match v {
            0u8 => Ok(AClosedEnum::A),
            1u8 => Ok(AClosedEnum::B),
            2u8 => Ok(AClosedEnum::C),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a AClosedEnum> for AClosedEnumInnerRef<'a> {
    type Error = ();

    fn ex_try_from(v: &'a AClosedEnum) -> Result<AClosedEnumInnerRef<'a>, ()> {
        match v {
            AClosedEnum::A => Ok(&EXEC_AClosedEnum_A),
            AClosedEnum::B => Ok(&EXEC_AClosedEnum_B),
            AClosedEnum::C => Ok(&EXEC_AClosedEnum_C),
        }
    }
}

pub struct AClosedEnumMapper;

impl View for AClosedEnumMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPartialIso for AClosedEnumMapper {
    type Src = AClosedEnumInner;
    type Dst = AClosedEnum;
}

impl SpecPartialIsoProof for AClosedEnumMapper {
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

impl<'a> PartialIso<'a> for AClosedEnumMapper {
    type Src = AClosedEnumInner;
    type Dst = AClosedEnum;
    type RefSrc = AClosedEnumInnerRef<'a>;
}


pub struct SpecAClosedEnumCombinator(SpecAClosedEnumCombinatorAlias);

impl SpecCombinator for SpecAClosedEnumCombinator {
    type Type = SpecAClosedEnum;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAClosedEnumCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAClosedEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecAClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;

pub struct AClosedEnumCombinator(AClosedEnumCombinatorAlias);

impl View for AClosedEnumCombinator {
    type V = SpecAClosedEnumCombinator;
    closed spec fn view(&self) -> Self::V { SpecAClosedEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AClosedEnumCombinator {
    type Type = AClosedEnum;
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
pub type AClosedEnumCombinatorAlias = TryMap<U8, AClosedEnumMapper>;


pub closed spec fn spec_a_closed_enum() -> SpecAClosedEnumCombinator {
    SpecAClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

                
pub fn a_closed_enum() -> (o: AClosedEnumCombinator)
    ensures o@ == spec_a_closed_enum(),
{
    AClosedEnumCombinator(TryMap { inner: U8, mapper: AClosedEnumMapper })
}

                
pub type SpecAnOpenEnum = u8;
pub type AnOpenEnum = u8;
pub type AnOpenEnumRef<'a> = &'a u8;


pub struct SpecAnOpenEnumCombinator(SpecAnOpenEnumCombinatorAlias);

impl SpecCombinator for SpecAnOpenEnumCombinator {
    type Type = SpecAnOpenEnum;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecAnOpenEnumCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAnOpenEnumCombinatorAlias::is_prefix_secure() }
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
pub type SpecAnOpenEnumCombinatorAlias = U8;

pub struct AnOpenEnumCombinator(AnOpenEnumCombinatorAlias);

impl View for AnOpenEnumCombinator {
    type V = SpecAnOpenEnumCombinator;
    closed spec fn view(&self) -> Self::V { SpecAnOpenEnumCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for AnOpenEnumCombinator {
    type Type = AnOpenEnum;
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
pub type AnOpenEnumCombinatorAlias = U8;


pub closed spec fn spec_an_open_enum() -> SpecAnOpenEnumCombinator {
    SpecAnOpenEnumCombinator(U8)
}

                
pub fn an_open_enum() -> (o: AnOpenEnumCombinator)
    ensures o@ == spec_an_open_enum(),
{
    AnOpenEnumCombinator(U8)
}

                

pub enum SpecARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type SpecARegularChooseInner = Either<u8, Either<u16, u32>>;

impl SpecFrom<SpecARegularChoose> for SpecARegularChooseInner {
    open spec fn spec_from(m: SpecARegularChoose) -> SpecARegularChooseInner {
        match m {
            SpecARegularChoose::A(m) => Either::Left(m),
            SpecARegularChoose::B(m) => Either::Right(Either::Left(m)),
            SpecARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

                
impl SpecFrom<SpecARegularChooseInner> for SpecARegularChoose {
    open spec fn spec_from(m: SpecARegularChooseInner) -> SpecARegularChoose {
        match m {
            Either::Left(m) => SpecARegularChoose::A(m),
            Either::Right(Either::Left(m)) => SpecARegularChoose::B(m),
            Either::Right(Either::Right(m)) => SpecARegularChoose::C(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ARegularChoose {
    A(u8),
    B(u16),
    C(u32),
}

pub type ARegularChooseInner = Either<u8, Either<u16, u32>>;

pub type ARegularChooseInnerRef<'a> = Either<&'a u8, Either<&'a u16, &'a u32>>;


impl View for ARegularChoose {
    type V = SpecARegularChoose;
    open spec fn view(&self) -> Self::V {
        match self {
            ARegularChoose::A(m) => SpecARegularChoose::A(m@),
            ARegularChoose::B(m) => SpecARegularChoose::B(m@),
            ARegularChoose::C(m) => SpecARegularChoose::C(m@),
        }
    }
}


impl<'a> From<&'a ARegularChoose> for ARegularChooseInnerRef<'a> {
    fn ex_from(m: &'a ARegularChoose) -> ARegularChooseInnerRef<'a> {
        match m {
            ARegularChoose::A(m) => Either::Left(m),
            ARegularChoose::B(m) => Either::Right(Either::Left(m)),
            ARegularChoose::C(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ARegularChooseInner> for ARegularChoose {
    fn ex_from(m: ARegularChooseInner) -> ARegularChoose {
        match m {
            Either::Left(m) => ARegularChoose::A(m),
            Either::Right(Either::Left(m)) => ARegularChoose::B(m),
            Either::Right(Either::Right(m)) => ARegularChoose::C(m),
        }
    }
    
}


pub struct ARegularChooseMapper;
impl View for ARegularChooseMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ARegularChooseMapper {
    type Src = SpecARegularChooseInner;
    type Dst = SpecARegularChoose;
}
impl SpecIsoProof for ARegularChooseMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ARegularChooseMapper {
    type Src = ARegularChooseInner;
    type Dst = ARegularChoose;
    type RefSrc = ARegularChooseInnerRef<'a>;
}

type SpecARegularChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type SpecARegularChooseCombinatorAlias2 = Choice<Cond<U8>, SpecARegularChooseCombinatorAlias1>;
pub struct SpecARegularChooseCombinator(SpecARegularChooseCombinatorAlias);

impl SpecCombinator for SpecARegularChooseCombinator {
    type Type = SpecARegularChoose;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecARegularChooseCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecARegularChooseCombinatorAlias::is_prefix_secure() }
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
pub type SpecARegularChooseCombinatorAlias = Mapped<SpecARegularChooseCombinatorAlias2, ARegularChooseMapper>;
type ARegularChooseCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U32Le>>;
type ARegularChooseCombinatorAlias2 = Choice<Cond<U8>, ARegularChooseCombinator1>;
struct ARegularChooseCombinator1(ARegularChooseCombinatorAlias1);
impl View for ARegularChooseCombinator1 {
    type V = SpecARegularChooseCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ARegularChooseCombinator1, ARegularChooseCombinatorAlias1);

struct ARegularChooseCombinator2(ARegularChooseCombinatorAlias2);
impl View for ARegularChooseCombinator2 {
    type V = SpecARegularChooseCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ARegularChooseCombinator2, ARegularChooseCombinatorAlias2);

pub struct ARegularChooseCombinator(ARegularChooseCombinatorAlias);

impl View for ARegularChooseCombinator {
    type V = SpecARegularChooseCombinator;
    closed spec fn view(&self) -> Self::V { SpecARegularChooseCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ARegularChooseCombinator {
    type Type = ARegularChoose;
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
pub type ARegularChooseCombinatorAlias = Mapped<ARegularChooseCombinator2, ARegularChooseMapper>;


pub closed spec fn spec_a_regular_choose(e: SpecAClosedEnum) -> SpecARegularChooseCombinator {
    SpecARegularChooseCombinator(Mapped { inner: Choice(Cond { cond: e == AClosedEnum::A, inner: U8 }, Choice(Cond { cond: e == AClosedEnum::B, inner: U16Le }, Cond { cond: e == AClosedEnum::C, inner: U32Le })), mapper: ARegularChooseMapper })
}

pub fn a_regular_choose<'a>(e: AClosedEnum) -> (o: ARegularChooseCombinator)
    ensures o@ == spec_a_regular_choose(e@),
{
    ARegularChooseCombinator(Mapped { inner: ARegularChooseCombinator2(Choice::new(Cond { cond: e == AClosedEnum::A, inner: U8 }, ARegularChooseCombinator1(Choice::new(Cond { cond: e == AClosedEnum::B, inner: U16Le }, Cond { cond: e == AClosedEnum::C, inner: U32Le })))), mapper: ARegularChooseMapper })
}


}
