
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

pub enum SpecChoiceWidth16 {
    Variant0(u8),
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
    Variant4(u8),
    Variant5(u8),
    Variant6(u8),
    Variant7(u8),
    Variant8(u8),
    Variant9(u8),
    Variant10(u8),
    Variant11(u8),
    Variant12(u8),
    Variant13(u8),
    Variant14(u8),
    Variant15(u8),
}

pub type SpecChoiceWidth16Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>;

impl SpecFrom<SpecChoiceWidth16> for SpecChoiceWidth16Inner {
    open spec fn spec_from(m: SpecChoiceWidth16) -> SpecChoiceWidth16Inner {
        match m {
            SpecChoiceWidth16::Variant0(m) => Either::Left(m),
            SpecChoiceWidth16::Variant1(m) => Either::Right(Either::Left(m)),
            SpecChoiceWidth16::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecChoiceWidth16::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecChoiceWidth16::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecChoiceWidth16::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecChoiceWidth16::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecChoiceWidth16::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecChoiceWidth16::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecChoiceWidth16::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecChoiceWidth16::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecChoiceWidth16::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecChoiceWidth16::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecChoiceWidth16::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecChoiceWidth16::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecChoiceWidth16::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecChoiceWidth16Inner> for SpecChoiceWidth16 {
    open spec fn spec_from(m: SpecChoiceWidth16Inner) -> SpecChoiceWidth16 {
        match m {
            Either::Left(m) => SpecChoiceWidth16::Variant0(m),
            Either::Right(Either::Left(m)) => SpecChoiceWidth16::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecChoiceWidth16::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecChoiceWidth16::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecChoiceWidth16::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecChoiceWidth16::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecChoiceWidth16::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecChoiceWidth16::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecChoiceWidth16::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecChoiceWidth16::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecChoiceWidth16::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecChoiceWidth16::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecChoiceWidth16::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecChoiceWidth16::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecChoiceWidth16::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))) => SpecChoiceWidth16::Variant15(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceWidth16 {
    Variant0(u8),
    Variant1(u8),
    Variant2(u8),
    Variant3(u8),
    Variant4(u8),
    Variant5(u8),
    Variant6(u8),
    Variant7(u8),
    Variant8(u8),
    Variant9(u8),
    Variant10(u8),
    Variant11(u8),
    Variant12(u8),
    Variant13(u8),
    Variant14(u8),
    Variant15(u8),
}

pub type ChoiceWidth16Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>;

pub type ChoiceWidth16InnerRef<'a> = Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, &'a u8>>>>>>>>>>>>>>>;


impl View for ChoiceWidth16 {
    type V = SpecChoiceWidth16;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceWidth16::Variant0(m) => SpecChoiceWidth16::Variant0(m@),
            ChoiceWidth16::Variant1(m) => SpecChoiceWidth16::Variant1(m@),
            ChoiceWidth16::Variant2(m) => SpecChoiceWidth16::Variant2(m@),
            ChoiceWidth16::Variant3(m) => SpecChoiceWidth16::Variant3(m@),
            ChoiceWidth16::Variant4(m) => SpecChoiceWidth16::Variant4(m@),
            ChoiceWidth16::Variant5(m) => SpecChoiceWidth16::Variant5(m@),
            ChoiceWidth16::Variant6(m) => SpecChoiceWidth16::Variant6(m@),
            ChoiceWidth16::Variant7(m) => SpecChoiceWidth16::Variant7(m@),
            ChoiceWidth16::Variant8(m) => SpecChoiceWidth16::Variant8(m@),
            ChoiceWidth16::Variant9(m) => SpecChoiceWidth16::Variant9(m@),
            ChoiceWidth16::Variant10(m) => SpecChoiceWidth16::Variant10(m@),
            ChoiceWidth16::Variant11(m) => SpecChoiceWidth16::Variant11(m@),
            ChoiceWidth16::Variant12(m) => SpecChoiceWidth16::Variant12(m@),
            ChoiceWidth16::Variant13(m) => SpecChoiceWidth16::Variant13(m@),
            ChoiceWidth16::Variant14(m) => SpecChoiceWidth16::Variant14(m@),
            ChoiceWidth16::Variant15(m) => SpecChoiceWidth16::Variant15(m@),
        }
    }
}


impl<'a> From<&'a ChoiceWidth16> for ChoiceWidth16InnerRef<'a> {
    fn ex_from(m: &'a ChoiceWidth16) -> ChoiceWidth16InnerRef<'a> {
        match m {
            ChoiceWidth16::Variant0(m) => Either::Left(m),
            ChoiceWidth16::Variant1(m) => Either::Right(Either::Left(m)),
            ChoiceWidth16::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            ChoiceWidth16::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ChoiceWidth16::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ChoiceWidth16::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ChoiceWidth16::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ChoiceWidth16::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ChoiceWidth16::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ChoiceWidth16::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ChoiceWidth16::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ChoiceWidth16::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ChoiceWidth16::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ChoiceWidth16::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ChoiceWidth16::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ChoiceWidth16::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))),
        }
    }

}

impl From<ChoiceWidth16Inner> for ChoiceWidth16 {
    fn ex_from(m: ChoiceWidth16Inner) -> ChoiceWidth16 {
        match m {
            Either::Left(m) => ChoiceWidth16::Variant0(m),
            Either::Right(Either::Left(m)) => ChoiceWidth16::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => ChoiceWidth16::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ChoiceWidth16::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ChoiceWidth16::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ChoiceWidth16::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ChoiceWidth16::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ChoiceWidth16::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ChoiceWidth16::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ChoiceWidth16::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ChoiceWidth16::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ChoiceWidth16::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ChoiceWidth16::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ChoiceWidth16::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ChoiceWidth16::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))) => ChoiceWidth16::Variant15(m),
        }
    }
    
}


pub struct ChoiceWidth16Mapper;
impl View for ChoiceWidth16Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceWidth16Mapper {
    type Src = SpecChoiceWidth16Inner;
    type Dst = SpecChoiceWidth16;
}
impl SpecIsoProof for ChoiceWidth16Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceWidth16Mapper {
    type Src = ChoiceWidth16Inner;
    type Dst = ChoiceWidth16;
    type RefSrc = ChoiceWidth16InnerRef<'a>;
}

type SpecChoiceWidth16CombinatorAlias1 = Choice<Refined<U8, Predicate3258795957419340618>, Refined<U8, Predicate17779166221338240295>>;
type SpecChoiceWidth16CombinatorAlias2 = Choice<Refined<U8, Predicate4672853435886844331>, SpecChoiceWidth16CombinatorAlias1>;
type SpecChoiceWidth16CombinatorAlias3 = Choice<Refined<U8, Predicate9731316588179370935>, SpecChoiceWidth16CombinatorAlias2>;
type SpecChoiceWidth16CombinatorAlias4 = Choice<Refined<U8, Predicate13393337139612027911>, SpecChoiceWidth16CombinatorAlias3>;
type SpecChoiceWidth16CombinatorAlias5 = Choice<Refined<U8, Predicate1670200719151657759>, SpecChoiceWidth16CombinatorAlias4>;
type SpecChoiceWidth16CombinatorAlias6 = Choice<Refined<U8, Predicate2286677770329837199>, SpecChoiceWidth16CombinatorAlias5>;
type SpecChoiceWidth16CombinatorAlias7 = Choice<Refined<U8, Predicate11758281649694429187>, SpecChoiceWidth16CombinatorAlias6>;
type SpecChoiceWidth16CombinatorAlias8 = Choice<Refined<U8, Predicate9770172291787044034>, SpecChoiceWidth16CombinatorAlias7>;
type SpecChoiceWidth16CombinatorAlias9 = Choice<Refined<U8, Predicate4214186895105241400>, SpecChoiceWidth16CombinatorAlias8>;
type SpecChoiceWidth16CombinatorAlias10 = Choice<Refined<U8, Predicate9186325526105272194>, SpecChoiceWidth16CombinatorAlias9>;
type SpecChoiceWidth16CombinatorAlias11 = Choice<Refined<U8, Predicate4589101901519479956>, SpecChoiceWidth16CombinatorAlias10>;
type SpecChoiceWidth16CombinatorAlias12 = Choice<Refined<U8, Predicate2671570727481267254>, SpecChoiceWidth16CombinatorAlias11>;
type SpecChoiceWidth16CombinatorAlias13 = Choice<Refined<U8, Predicate6170912057263668010>, SpecChoiceWidth16CombinatorAlias12>;
type SpecChoiceWidth16CombinatorAlias14 = Choice<Refined<U8, Predicate13385608959756530935>, SpecChoiceWidth16CombinatorAlias13>;
type SpecChoiceWidth16CombinatorAlias15 = Choice<Refined<U8, Predicate2576612288366319398>, SpecChoiceWidth16CombinatorAlias14>;
pub struct SpecChoiceWidth16Combinator(pub SpecChoiceWidth16CombinatorAlias);

impl SpecCombinator for SpecChoiceWidth16Combinator {
    type Type = SpecChoiceWidth16;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceWidth16Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceWidth16CombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceWidth16CombinatorAlias = Mapped<SpecChoiceWidth16CombinatorAlias15, ChoiceWidth16Mapper>;
pub struct Predicate2576612288366319398;
impl View for Predicate2576612288366319398 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2576612288366319398 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
impl SpecPred<u8> for Predicate2576612288366319398 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 0)
    }
}
pub struct Predicate13385608959756530935;
impl View for Predicate13385608959756530935 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13385608959756530935 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 1)
    }
}
impl SpecPred<u8> for Predicate13385608959756530935 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 1)
    }
}
pub struct Predicate6170912057263668010;
impl View for Predicate6170912057263668010 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate6170912057263668010 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 2)
    }
}
impl SpecPred<u8> for Predicate6170912057263668010 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 2)
    }
}
pub struct Predicate2671570727481267254;
impl View for Predicate2671570727481267254 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2671570727481267254 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 3)
    }
}
impl SpecPred<u8> for Predicate2671570727481267254 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 3)
    }
}
pub struct Predicate4589101901519479956;
impl View for Predicate4589101901519479956 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4589101901519479956 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 4)
    }
}
impl SpecPred<u8> for Predicate4589101901519479956 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 4)
    }
}
pub struct Predicate9186325526105272194;
impl View for Predicate9186325526105272194 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate9186325526105272194 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 5)
    }
}
impl SpecPred<u8> for Predicate9186325526105272194 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 5)
    }
}
pub struct Predicate4214186895105241400;
impl View for Predicate4214186895105241400 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4214186895105241400 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 6)
    }
}
impl SpecPred<u8> for Predicate4214186895105241400 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 6)
    }
}
pub struct Predicate9770172291787044034;
impl View for Predicate9770172291787044034 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate9770172291787044034 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 7)
    }
}
impl SpecPred<u8> for Predicate9770172291787044034 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 7)
    }
}
pub struct Predicate11758281649694429187;
impl View for Predicate11758281649694429187 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate11758281649694429187 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 8)
    }
}
impl SpecPred<u8> for Predicate11758281649694429187 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 8)
    }
}
pub struct Predicate2286677770329837199;
impl View for Predicate2286677770329837199 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2286677770329837199 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 9)
    }
}
impl SpecPred<u8> for Predicate2286677770329837199 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 9)
    }
}
pub struct Predicate1670200719151657759;
impl View for Predicate1670200719151657759 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1670200719151657759 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 10)
    }
}
impl SpecPred<u8> for Predicate1670200719151657759 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 10)
    }
}
pub struct Predicate13393337139612027911;
impl View for Predicate13393337139612027911 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13393337139612027911 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 11)
    }
}
impl SpecPred<u8> for Predicate13393337139612027911 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 11)
    }
}
pub struct Predicate9731316588179370935;
impl View for Predicate9731316588179370935 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate9731316588179370935 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 12)
    }
}
impl SpecPred<u8> for Predicate9731316588179370935 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 12)
    }
}
pub struct Predicate4672853435886844331;
impl View for Predicate4672853435886844331 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4672853435886844331 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 13)
    }
}
impl SpecPred<u8> for Predicate4672853435886844331 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 13)
    }
}
pub struct Predicate3258795957419340618;
impl View for Predicate3258795957419340618 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3258795957419340618 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 14)
    }
}
impl SpecPred<u8> for Predicate3258795957419340618 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 14)
    }
}
pub struct Predicate17779166221338240295;
impl View for Predicate17779166221338240295 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate17779166221338240295 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 15)
    }
}
impl SpecPred<u8> for Predicate17779166221338240295 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 15)
    }
}
type ChoiceWidth16CombinatorAlias1 = Choice<Refined<U8, Predicate3258795957419340618>, Refined<U8, Predicate17779166221338240295>>;
type ChoiceWidth16CombinatorAlias2 = Choice<Refined<U8, Predicate4672853435886844331>, ChoiceWidth16Combinator1>;
type ChoiceWidth16CombinatorAlias3 = Choice<Refined<U8, Predicate9731316588179370935>, ChoiceWidth16Combinator2>;
type ChoiceWidth16CombinatorAlias4 = Choice<Refined<U8, Predicate13393337139612027911>, ChoiceWidth16Combinator3>;
type ChoiceWidth16CombinatorAlias5 = Choice<Refined<U8, Predicate1670200719151657759>, ChoiceWidth16Combinator4>;
type ChoiceWidth16CombinatorAlias6 = Choice<Refined<U8, Predicate2286677770329837199>, ChoiceWidth16Combinator5>;
type ChoiceWidth16CombinatorAlias7 = Choice<Refined<U8, Predicate11758281649694429187>, ChoiceWidth16Combinator6>;
type ChoiceWidth16CombinatorAlias8 = Choice<Refined<U8, Predicate9770172291787044034>, ChoiceWidth16Combinator7>;
type ChoiceWidth16CombinatorAlias9 = Choice<Refined<U8, Predicate4214186895105241400>, ChoiceWidth16Combinator8>;
type ChoiceWidth16CombinatorAlias10 = Choice<Refined<U8, Predicate9186325526105272194>, ChoiceWidth16Combinator9>;
type ChoiceWidth16CombinatorAlias11 = Choice<Refined<U8, Predicate4589101901519479956>, ChoiceWidth16Combinator10>;
type ChoiceWidth16CombinatorAlias12 = Choice<Refined<U8, Predicate2671570727481267254>, ChoiceWidth16Combinator11>;
type ChoiceWidth16CombinatorAlias13 = Choice<Refined<U8, Predicate6170912057263668010>, ChoiceWidth16Combinator12>;
type ChoiceWidth16CombinatorAlias14 = Choice<Refined<U8, Predicate13385608959756530935>, ChoiceWidth16Combinator13>;
type ChoiceWidth16CombinatorAlias15 = Choice<Refined<U8, Predicate2576612288366319398>, ChoiceWidth16Combinator14>;
pub struct ChoiceWidth16Combinator1(pub ChoiceWidth16CombinatorAlias1);
impl View for ChoiceWidth16Combinator1 {
    type V = SpecChoiceWidth16CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator1, ChoiceWidth16CombinatorAlias1);

pub struct ChoiceWidth16Combinator2(pub ChoiceWidth16CombinatorAlias2);
impl View for ChoiceWidth16Combinator2 {
    type V = SpecChoiceWidth16CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator2, ChoiceWidth16CombinatorAlias2);

pub struct ChoiceWidth16Combinator3(pub ChoiceWidth16CombinatorAlias3);
impl View for ChoiceWidth16Combinator3 {
    type V = SpecChoiceWidth16CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator3, ChoiceWidth16CombinatorAlias3);

pub struct ChoiceWidth16Combinator4(pub ChoiceWidth16CombinatorAlias4);
impl View for ChoiceWidth16Combinator4 {
    type V = SpecChoiceWidth16CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator4, ChoiceWidth16CombinatorAlias4);

pub struct ChoiceWidth16Combinator5(pub ChoiceWidth16CombinatorAlias5);
impl View for ChoiceWidth16Combinator5 {
    type V = SpecChoiceWidth16CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator5, ChoiceWidth16CombinatorAlias5);

pub struct ChoiceWidth16Combinator6(pub ChoiceWidth16CombinatorAlias6);
impl View for ChoiceWidth16Combinator6 {
    type V = SpecChoiceWidth16CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator6, ChoiceWidth16CombinatorAlias6);

pub struct ChoiceWidth16Combinator7(pub ChoiceWidth16CombinatorAlias7);
impl View for ChoiceWidth16Combinator7 {
    type V = SpecChoiceWidth16CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator7, ChoiceWidth16CombinatorAlias7);

pub struct ChoiceWidth16Combinator8(pub ChoiceWidth16CombinatorAlias8);
impl View for ChoiceWidth16Combinator8 {
    type V = SpecChoiceWidth16CombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator8, ChoiceWidth16CombinatorAlias8);

pub struct ChoiceWidth16Combinator9(pub ChoiceWidth16CombinatorAlias9);
impl View for ChoiceWidth16Combinator9 {
    type V = SpecChoiceWidth16CombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator9, ChoiceWidth16CombinatorAlias9);

pub struct ChoiceWidth16Combinator10(pub ChoiceWidth16CombinatorAlias10);
impl View for ChoiceWidth16Combinator10 {
    type V = SpecChoiceWidth16CombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator10, ChoiceWidth16CombinatorAlias10);

pub struct ChoiceWidth16Combinator11(pub ChoiceWidth16CombinatorAlias11);
impl View for ChoiceWidth16Combinator11 {
    type V = SpecChoiceWidth16CombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator11, ChoiceWidth16CombinatorAlias11);

pub struct ChoiceWidth16Combinator12(pub ChoiceWidth16CombinatorAlias12);
impl View for ChoiceWidth16Combinator12 {
    type V = SpecChoiceWidth16CombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator12, ChoiceWidth16CombinatorAlias12);

pub struct ChoiceWidth16Combinator13(pub ChoiceWidth16CombinatorAlias13);
impl View for ChoiceWidth16Combinator13 {
    type V = SpecChoiceWidth16CombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator13, ChoiceWidth16CombinatorAlias13);

pub struct ChoiceWidth16Combinator14(pub ChoiceWidth16CombinatorAlias14);
impl View for ChoiceWidth16Combinator14 {
    type V = SpecChoiceWidth16CombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator14, ChoiceWidth16CombinatorAlias14);

pub struct ChoiceWidth16Combinator15(pub ChoiceWidth16CombinatorAlias15);
impl View for ChoiceWidth16Combinator15 {
    type V = SpecChoiceWidth16CombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth16Combinator15, ChoiceWidth16CombinatorAlias15);

pub struct ChoiceWidth16Combinator(pub ChoiceWidth16CombinatorAlias);

impl View for ChoiceWidth16Combinator {
    type V = SpecChoiceWidth16Combinator;
    open spec fn view(&self) -> Self::V { SpecChoiceWidth16Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceWidth16Combinator {
    type Type = ChoiceWidth16;
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
pub type ChoiceWidth16CombinatorAlias = Mapped<ChoiceWidth16Combinator15, ChoiceWidth16Mapper>;


pub open spec fn spec_choice_width16() -> SpecChoiceWidth16Combinator {
    SpecChoiceWidth16Combinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Choice(Refined { inner: U8, predicate: Predicate13385608959756530935 }, Choice(Refined { inner: U8, predicate: Predicate6170912057263668010 }, Choice(Refined { inner: U8, predicate: Predicate2671570727481267254 }, Choice(Refined { inner: U8, predicate: Predicate4589101901519479956 }, Choice(Refined { inner: U8, predicate: Predicate9186325526105272194 }, Choice(Refined { inner: U8, predicate: Predicate4214186895105241400 }, Choice(Refined { inner: U8, predicate: Predicate9770172291787044034 }, Choice(Refined { inner: U8, predicate: Predicate11758281649694429187 }, Choice(Refined { inner: U8, predicate: Predicate2286677770329837199 }, Choice(Refined { inner: U8, predicate: Predicate1670200719151657759 }, Choice(Refined { inner: U8, predicate: Predicate13393337139612027911 }, Choice(Refined { inner: U8, predicate: Predicate9731316588179370935 }, Choice(Refined { inner: U8, predicate: Predicate4672853435886844331 }, Choice(Refined { inner: U8, predicate: Predicate3258795957419340618 }, Refined { inner: U8, predicate: Predicate17779166221338240295 }))))))))))))))), mapper: ChoiceWidth16Mapper })
}

                
pub fn choice_width16<'a>() -> (o: ChoiceWidth16Combinator)
    ensures o@ == spec_choice_width16(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceWidth16Combinator(Mapped { inner: ChoiceWidth16Combinator15(Choice::new(Refined { inner: U8, predicate: Predicate2576612288366319398 }, ChoiceWidth16Combinator14(Choice::new(Refined { inner: U8, predicate: Predicate13385608959756530935 }, ChoiceWidth16Combinator13(Choice::new(Refined { inner: U8, predicate: Predicate6170912057263668010 }, ChoiceWidth16Combinator12(Choice::new(Refined { inner: U8, predicate: Predicate2671570727481267254 }, ChoiceWidth16Combinator11(Choice::new(Refined { inner: U8, predicate: Predicate4589101901519479956 }, ChoiceWidth16Combinator10(Choice::new(Refined { inner: U8, predicate: Predicate9186325526105272194 }, ChoiceWidth16Combinator9(Choice::new(Refined { inner: U8, predicate: Predicate4214186895105241400 }, ChoiceWidth16Combinator8(Choice::new(Refined { inner: U8, predicate: Predicate9770172291787044034 }, ChoiceWidth16Combinator7(Choice::new(Refined { inner: U8, predicate: Predicate11758281649694429187 }, ChoiceWidth16Combinator6(Choice::new(Refined { inner: U8, predicate: Predicate2286677770329837199 }, ChoiceWidth16Combinator5(Choice::new(Refined { inner: U8, predicate: Predicate1670200719151657759 }, ChoiceWidth16Combinator4(Choice::new(Refined { inner: U8, predicate: Predicate13393337139612027911 }, ChoiceWidth16Combinator3(Choice::new(Refined { inner: U8, predicate: Predicate9731316588179370935 }, ChoiceWidth16Combinator2(Choice::new(Refined { inner: U8, predicate: Predicate4672853435886844331 }, ChoiceWidth16Combinator1(Choice::new(Refined { inner: U8, predicate: Predicate3258795957419340618 }, Refined { inner: U8, predicate: Predicate17779166221338240295 })))))))))))))))))))))))))))))), mapper: ChoiceWidth16Mapper });
    // assert({
    //     &&& combinator@ == spec_choice_width16()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_width16<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_width16().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_width16().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_width16().spec_parse(input@) is None,
        spec_choice_width16().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_width16<'a>(v: <ChoiceWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_width16().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_choice_width16().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_choice_width16().spec_serialize(v@))
        },
{
    let combinator = choice_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn choice_width16_len<'a>(v: <ChoiceWidth16Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_width16().wf(v@),
        spec_choice_width16().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_width16().spec_serialize(v@).len(),
{
    let combinator = choice_width16();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
