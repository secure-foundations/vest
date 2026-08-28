
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

pub enum SpecChoiceWidth32 {
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
    Variant16(u8),
    Variant17(u8),
    Variant18(u8),
    Variant19(u8),
    Variant20(u8),
    Variant21(u8),
    Variant22(u8),
    Variant23(u8),
    Variant24(u8),
    Variant25(u8),
    Variant26(u8),
    Variant27(u8),
    Variant28(u8),
    Variant29(u8),
    Variant30(u8),
    Variant31(u8),
}

pub type SpecChoiceWidth32Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

impl SpecFrom<SpecChoiceWidth32> for SpecChoiceWidth32Inner {
    open spec fn spec_from(m: SpecChoiceWidth32) -> SpecChoiceWidth32Inner {
        match m {
            SpecChoiceWidth32::Variant0(m) => Either::Left(m),
            SpecChoiceWidth32::Variant1(m) => Either::Right(Either::Left(m)),
            SpecChoiceWidth32::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecChoiceWidth32::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecChoiceWidth32::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecChoiceWidth32::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecChoiceWidth32::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecChoiceWidth32::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecChoiceWidth32::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecChoiceWidth32::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecChoiceWidth32::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecChoiceWidth32::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecChoiceWidth32::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecChoiceWidth32::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecChoiceWidth32::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecChoiceWidth32::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecChoiceWidth32::Variant16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecChoiceWidth32::Variant17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecChoiceWidth32::Variant18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecChoiceWidth32::Variant19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecChoiceWidth32::Variant20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecChoiceWidth32::Variant21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecChoiceWidth32::Variant22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecChoiceWidth32::Variant23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecChoiceWidth32::Variant24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            SpecChoiceWidth32::Variant31(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecChoiceWidth32Inner> for SpecChoiceWidth32 {
    open spec fn spec_from(m: SpecChoiceWidth32Inner) -> SpecChoiceWidth32 {
        match m {
            Either::Left(m) => SpecChoiceWidth32::Variant0(m),
            Either::Right(Either::Left(m)) => SpecChoiceWidth32::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecChoiceWidth32::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecChoiceWidth32::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecChoiceWidth32::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecChoiceWidth32::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecChoiceWidth32::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecChoiceWidth32::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecChoiceWidth32::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecChoiceWidth32::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecChoiceWidth32::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecChoiceWidth32::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecChoiceWidth32::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecChoiceWidth32::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecChoiceWidth32::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecChoiceWidth32::Variant15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecChoiceWidth32::Variant16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecChoiceWidth32::Variant17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecChoiceWidth32::Variant18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecChoiceWidth32::Variant19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecChoiceWidth32::Variant20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecChoiceWidth32::Variant21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecChoiceWidth32::Variant22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecChoiceWidth32::Variant23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecChoiceWidth32::Variant24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecChoiceWidth32::Variant25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant30(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))) => SpecChoiceWidth32::Variant31(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceWidth32 {
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
    Variant16(u8),
    Variant17(u8),
    Variant18(u8),
    Variant19(u8),
    Variant20(u8),
    Variant21(u8),
    Variant22(u8),
    Variant23(u8),
    Variant24(u8),
    Variant25(u8),
    Variant26(u8),
    Variant27(u8),
    Variant28(u8),
    Variant29(u8),
    Variant30(u8),
    Variant31(u8),
}

pub type ChoiceWidth32Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

pub type ChoiceWidth32InnerRef<'a> = Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, &'a u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;


impl View for ChoiceWidth32 {
    type V = SpecChoiceWidth32;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceWidth32::Variant0(m) => SpecChoiceWidth32::Variant0(m@),
            ChoiceWidth32::Variant1(m) => SpecChoiceWidth32::Variant1(m@),
            ChoiceWidth32::Variant2(m) => SpecChoiceWidth32::Variant2(m@),
            ChoiceWidth32::Variant3(m) => SpecChoiceWidth32::Variant3(m@),
            ChoiceWidth32::Variant4(m) => SpecChoiceWidth32::Variant4(m@),
            ChoiceWidth32::Variant5(m) => SpecChoiceWidth32::Variant5(m@),
            ChoiceWidth32::Variant6(m) => SpecChoiceWidth32::Variant6(m@),
            ChoiceWidth32::Variant7(m) => SpecChoiceWidth32::Variant7(m@),
            ChoiceWidth32::Variant8(m) => SpecChoiceWidth32::Variant8(m@),
            ChoiceWidth32::Variant9(m) => SpecChoiceWidth32::Variant9(m@),
            ChoiceWidth32::Variant10(m) => SpecChoiceWidth32::Variant10(m@),
            ChoiceWidth32::Variant11(m) => SpecChoiceWidth32::Variant11(m@),
            ChoiceWidth32::Variant12(m) => SpecChoiceWidth32::Variant12(m@),
            ChoiceWidth32::Variant13(m) => SpecChoiceWidth32::Variant13(m@),
            ChoiceWidth32::Variant14(m) => SpecChoiceWidth32::Variant14(m@),
            ChoiceWidth32::Variant15(m) => SpecChoiceWidth32::Variant15(m@),
            ChoiceWidth32::Variant16(m) => SpecChoiceWidth32::Variant16(m@),
            ChoiceWidth32::Variant17(m) => SpecChoiceWidth32::Variant17(m@),
            ChoiceWidth32::Variant18(m) => SpecChoiceWidth32::Variant18(m@),
            ChoiceWidth32::Variant19(m) => SpecChoiceWidth32::Variant19(m@),
            ChoiceWidth32::Variant20(m) => SpecChoiceWidth32::Variant20(m@),
            ChoiceWidth32::Variant21(m) => SpecChoiceWidth32::Variant21(m@),
            ChoiceWidth32::Variant22(m) => SpecChoiceWidth32::Variant22(m@),
            ChoiceWidth32::Variant23(m) => SpecChoiceWidth32::Variant23(m@),
            ChoiceWidth32::Variant24(m) => SpecChoiceWidth32::Variant24(m@),
            ChoiceWidth32::Variant25(m) => SpecChoiceWidth32::Variant25(m@),
            ChoiceWidth32::Variant26(m) => SpecChoiceWidth32::Variant26(m@),
            ChoiceWidth32::Variant27(m) => SpecChoiceWidth32::Variant27(m@),
            ChoiceWidth32::Variant28(m) => SpecChoiceWidth32::Variant28(m@),
            ChoiceWidth32::Variant29(m) => SpecChoiceWidth32::Variant29(m@),
            ChoiceWidth32::Variant30(m) => SpecChoiceWidth32::Variant30(m@),
            ChoiceWidth32::Variant31(m) => SpecChoiceWidth32::Variant31(m@),
        }
    }
}


impl<'a> From<&'a ChoiceWidth32> for ChoiceWidth32InnerRef<'a> {
    fn ex_from(m: &'a ChoiceWidth32) -> ChoiceWidth32InnerRef<'a> {
        match m {
            ChoiceWidth32::Variant0(m) => Either::Left(m),
            ChoiceWidth32::Variant1(m) => Either::Right(Either::Left(m)),
            ChoiceWidth32::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            ChoiceWidth32::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ChoiceWidth32::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ChoiceWidth32::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ChoiceWidth32::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ChoiceWidth32::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ChoiceWidth32::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ChoiceWidth32::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ChoiceWidth32::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ChoiceWidth32::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ChoiceWidth32::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ChoiceWidth32::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ChoiceWidth32::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ChoiceWidth32::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ChoiceWidth32::Variant16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ChoiceWidth32::Variant17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ChoiceWidth32::Variant18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ChoiceWidth32::Variant19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ChoiceWidth32::Variant20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ChoiceWidth32::Variant21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ChoiceWidth32::Variant22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ChoiceWidth32::Variant23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ChoiceWidth32::Variant24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            ChoiceWidth32::Variant25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            ChoiceWidth32::Variant26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            ChoiceWidth32::Variant27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            ChoiceWidth32::Variant28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            ChoiceWidth32::Variant29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            ChoiceWidth32::Variant30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            ChoiceWidth32::Variant31(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))),
        }
    }

}

impl From<ChoiceWidth32Inner> for ChoiceWidth32 {
    fn ex_from(m: ChoiceWidth32Inner) -> ChoiceWidth32 {
        match m {
            Either::Left(m) => ChoiceWidth32::Variant0(m),
            Either::Right(Either::Left(m)) => ChoiceWidth32::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => ChoiceWidth32::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ChoiceWidth32::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ChoiceWidth32::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ChoiceWidth32::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ChoiceWidth32::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ChoiceWidth32::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ChoiceWidth32::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ChoiceWidth32::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ChoiceWidth32::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ChoiceWidth32::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ChoiceWidth32::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ChoiceWidth32::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ChoiceWidth32::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ChoiceWidth32::Variant15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ChoiceWidth32::Variant16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ChoiceWidth32::Variant17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ChoiceWidth32::Variant18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ChoiceWidth32::Variant19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ChoiceWidth32::Variant20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ChoiceWidth32::Variant21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ChoiceWidth32::Variant22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ChoiceWidth32::Variant23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => ChoiceWidth32::Variant24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => ChoiceWidth32::Variant25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => ChoiceWidth32::Variant26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => ChoiceWidth32::Variant27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => ChoiceWidth32::Variant28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => ChoiceWidth32::Variant29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => ChoiceWidth32::Variant30(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))) => ChoiceWidth32::Variant31(m),
        }
    }
    
}


pub struct ChoiceWidth32Mapper;
impl View for ChoiceWidth32Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceWidth32Mapper {
    type Src = SpecChoiceWidth32Inner;
    type Dst = SpecChoiceWidth32;
}
impl SpecIsoProof for ChoiceWidth32Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceWidth32Mapper {
    type Src = ChoiceWidth32Inner;
    type Dst = ChoiceWidth32;
    type RefSrc = ChoiceWidth32InnerRef<'a>;
}

type SpecChoiceWidth32CombinatorAlias1 = Choice<Refined<U8, Predicate1385328176252848081>, Refined<U8, Predicate14757914070657982036>>;
type SpecChoiceWidth32CombinatorAlias2 = Choice<Refined<U8, Predicate17516429898706644594>, SpecChoiceWidth32CombinatorAlias1>;
type SpecChoiceWidth32CombinatorAlias3 = Choice<Refined<U8, Predicate11809820865766219170>, SpecChoiceWidth32CombinatorAlias2>;
type SpecChoiceWidth32CombinatorAlias4 = Choice<Refined<U8, Predicate14700689986523383325>, SpecChoiceWidth32CombinatorAlias3>;
type SpecChoiceWidth32CombinatorAlias5 = Choice<Refined<U8, Predicate3285282901849553415>, SpecChoiceWidth32CombinatorAlias4>;
type SpecChoiceWidth32CombinatorAlias6 = Choice<Refined<U8, Predicate2213030098669005785>, SpecChoiceWidth32CombinatorAlias5>;
type SpecChoiceWidth32CombinatorAlias7 = Choice<Refined<U8, Predicate14174989844364464752>, SpecChoiceWidth32CombinatorAlias6>;
type SpecChoiceWidth32CombinatorAlias8 = Choice<Refined<U8, Predicate1304083776951938903>, SpecChoiceWidth32CombinatorAlias7>;
type SpecChoiceWidth32CombinatorAlias9 = Choice<Refined<U8, Predicate4869308575099852777>, SpecChoiceWidth32CombinatorAlias8>;
type SpecChoiceWidth32CombinatorAlias10 = Choice<Refined<U8, Predicate16333054977080421469>, SpecChoiceWidth32CombinatorAlias9>;
type SpecChoiceWidth32CombinatorAlias11 = Choice<Refined<U8, Predicate1445610904132711222>, SpecChoiceWidth32CombinatorAlias10>;
type SpecChoiceWidth32CombinatorAlias12 = Choice<Refined<U8, Predicate4072810196653762843>, SpecChoiceWidth32CombinatorAlias11>;
type SpecChoiceWidth32CombinatorAlias13 = Choice<Refined<U8, Predicate14707428835277590315>, SpecChoiceWidth32CombinatorAlias12>;
type SpecChoiceWidth32CombinatorAlias14 = Choice<Refined<U8, Predicate8251779752648547376>, SpecChoiceWidth32CombinatorAlias13>;
type SpecChoiceWidth32CombinatorAlias15 = Choice<Refined<U8, Predicate15291213704223769698>, SpecChoiceWidth32CombinatorAlias14>;
type SpecChoiceWidth32CombinatorAlias16 = Choice<Refined<U8, Predicate6037550869214390311>, SpecChoiceWidth32CombinatorAlias15>;
type SpecChoiceWidth32CombinatorAlias17 = Choice<Refined<U8, Predicate3258795957419340618>, SpecChoiceWidth32CombinatorAlias16>;
type SpecChoiceWidth32CombinatorAlias18 = Choice<Refined<U8, Predicate4672853435886844331>, SpecChoiceWidth32CombinatorAlias17>;
type SpecChoiceWidth32CombinatorAlias19 = Choice<Refined<U8, Predicate9731316588179370935>, SpecChoiceWidth32CombinatorAlias18>;
type SpecChoiceWidth32CombinatorAlias20 = Choice<Refined<U8, Predicate13393337139612027911>, SpecChoiceWidth32CombinatorAlias19>;
type SpecChoiceWidth32CombinatorAlias21 = Choice<Refined<U8, Predicate1670200719151657759>, SpecChoiceWidth32CombinatorAlias20>;
type SpecChoiceWidth32CombinatorAlias22 = Choice<Refined<U8, Predicate2286677770329837199>, SpecChoiceWidth32CombinatorAlias21>;
type SpecChoiceWidth32CombinatorAlias23 = Choice<Refined<U8, Predicate11758281649694429187>, SpecChoiceWidth32CombinatorAlias22>;
type SpecChoiceWidth32CombinatorAlias24 = Choice<Refined<U8, Predicate9770172291787044034>, SpecChoiceWidth32CombinatorAlias23>;
type SpecChoiceWidth32CombinatorAlias25 = Choice<Refined<U8, Predicate4214186895105241400>, SpecChoiceWidth32CombinatorAlias24>;
type SpecChoiceWidth32CombinatorAlias26 = Choice<Refined<U8, Predicate9186325526105272194>, SpecChoiceWidth32CombinatorAlias25>;
type SpecChoiceWidth32CombinatorAlias27 = Choice<Refined<U8, Predicate4589101901519479956>, SpecChoiceWidth32CombinatorAlias26>;
type SpecChoiceWidth32CombinatorAlias28 = Choice<Refined<U8, Predicate2671570727481267254>, SpecChoiceWidth32CombinatorAlias27>;
type SpecChoiceWidth32CombinatorAlias29 = Choice<Refined<U8, Predicate6170912057263668010>, SpecChoiceWidth32CombinatorAlias28>;
type SpecChoiceWidth32CombinatorAlias30 = Choice<Refined<U8, Predicate13385608959756530935>, SpecChoiceWidth32CombinatorAlias29>;
type SpecChoiceWidth32CombinatorAlias31 = Choice<Refined<U8, Predicate2576612288366319398>, SpecChoiceWidth32CombinatorAlias30>;
pub struct SpecChoiceWidth32Combinator(pub SpecChoiceWidth32CombinatorAlias);

impl SpecCombinator for SpecChoiceWidth32Combinator {
    type Type = SpecChoiceWidth32;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceWidth32Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceWidth32CombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceWidth32CombinatorAlias = Mapped<SpecChoiceWidth32CombinatorAlias31, ChoiceWidth32Mapper>;
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
pub struct Predicate6037550869214390311;
impl View for Predicate6037550869214390311 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate6037550869214390311 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 15)
    }
}
impl SpecPred<u8> for Predicate6037550869214390311 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 15)
    }
}
pub struct Predicate15291213704223769698;
impl View for Predicate15291213704223769698 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15291213704223769698 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 16)
    }
}
impl SpecPred<u8> for Predicate15291213704223769698 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 16)
    }
}
pub struct Predicate8251779752648547376;
impl View for Predicate8251779752648547376 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8251779752648547376 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 17)
    }
}
impl SpecPred<u8> for Predicate8251779752648547376 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 17)
    }
}
pub struct Predicate14707428835277590315;
impl View for Predicate14707428835277590315 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14707428835277590315 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 18)
    }
}
impl SpecPred<u8> for Predicate14707428835277590315 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 18)
    }
}
pub struct Predicate4072810196653762843;
impl View for Predicate4072810196653762843 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4072810196653762843 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 19)
    }
}
impl SpecPred<u8> for Predicate4072810196653762843 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 19)
    }
}
pub struct Predicate1445610904132711222;
impl View for Predicate1445610904132711222 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1445610904132711222 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 20)
    }
}
impl SpecPred<u8> for Predicate1445610904132711222 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 20)
    }
}
pub struct Predicate16333054977080421469;
impl View for Predicate16333054977080421469 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16333054977080421469 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 21)
    }
}
impl SpecPred<u8> for Predicate16333054977080421469 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 21)
    }
}
pub struct Predicate4869308575099852777;
impl View for Predicate4869308575099852777 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4869308575099852777 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 22)
    }
}
impl SpecPred<u8> for Predicate4869308575099852777 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 22)
    }
}
pub struct Predicate1304083776951938903;
impl View for Predicate1304083776951938903 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1304083776951938903 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 23)
    }
}
impl SpecPred<u8> for Predicate1304083776951938903 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 23)
    }
}
pub struct Predicate14174989844364464752;
impl View for Predicate14174989844364464752 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14174989844364464752 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 24)
    }
}
impl SpecPred<u8> for Predicate14174989844364464752 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 24)
    }
}
pub struct Predicate2213030098669005785;
impl View for Predicate2213030098669005785 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2213030098669005785 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 25)
    }
}
impl SpecPred<u8> for Predicate2213030098669005785 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 25)
    }
}
pub struct Predicate3285282901849553415;
impl View for Predicate3285282901849553415 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3285282901849553415 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 26)
    }
}
impl SpecPred<u8> for Predicate3285282901849553415 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 26)
    }
}
pub struct Predicate14700689986523383325;
impl View for Predicate14700689986523383325 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14700689986523383325 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 27)
    }
}
impl SpecPred<u8> for Predicate14700689986523383325 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 27)
    }
}
pub struct Predicate11809820865766219170;
impl View for Predicate11809820865766219170 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate11809820865766219170 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 28)
    }
}
impl SpecPred<u8> for Predicate11809820865766219170 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 28)
    }
}
pub struct Predicate17516429898706644594;
impl View for Predicate17516429898706644594 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate17516429898706644594 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 29)
    }
}
impl SpecPred<u8> for Predicate17516429898706644594 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 29)
    }
}
pub struct Predicate1385328176252848081;
impl View for Predicate1385328176252848081 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1385328176252848081 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 30)
    }
}
impl SpecPred<u8> for Predicate1385328176252848081 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 30)
    }
}
pub struct Predicate14757914070657982036;
impl View for Predicate14757914070657982036 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14757914070657982036 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 31)
    }
}
impl SpecPred<u8> for Predicate14757914070657982036 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 31)
    }
}
type ChoiceWidth32CombinatorAlias1 = Choice<Refined<U8, Predicate1385328176252848081>, Refined<U8, Predicate14757914070657982036>>;
type ChoiceWidth32CombinatorAlias2 = Choice<Refined<U8, Predicate17516429898706644594>, ChoiceWidth32Combinator1>;
type ChoiceWidth32CombinatorAlias3 = Choice<Refined<U8, Predicate11809820865766219170>, ChoiceWidth32Combinator2>;
type ChoiceWidth32CombinatorAlias4 = Choice<Refined<U8, Predicate14700689986523383325>, ChoiceWidth32Combinator3>;
type ChoiceWidth32CombinatorAlias5 = Choice<Refined<U8, Predicate3285282901849553415>, ChoiceWidth32Combinator4>;
type ChoiceWidth32CombinatorAlias6 = Choice<Refined<U8, Predicate2213030098669005785>, ChoiceWidth32Combinator5>;
type ChoiceWidth32CombinatorAlias7 = Choice<Refined<U8, Predicate14174989844364464752>, ChoiceWidth32Combinator6>;
type ChoiceWidth32CombinatorAlias8 = Choice<Refined<U8, Predicate1304083776951938903>, ChoiceWidth32Combinator7>;
type ChoiceWidth32CombinatorAlias9 = Choice<Refined<U8, Predicate4869308575099852777>, ChoiceWidth32Combinator8>;
type ChoiceWidth32CombinatorAlias10 = Choice<Refined<U8, Predicate16333054977080421469>, ChoiceWidth32Combinator9>;
type ChoiceWidth32CombinatorAlias11 = Choice<Refined<U8, Predicate1445610904132711222>, ChoiceWidth32Combinator10>;
type ChoiceWidth32CombinatorAlias12 = Choice<Refined<U8, Predicate4072810196653762843>, ChoiceWidth32Combinator11>;
type ChoiceWidth32CombinatorAlias13 = Choice<Refined<U8, Predicate14707428835277590315>, ChoiceWidth32Combinator12>;
type ChoiceWidth32CombinatorAlias14 = Choice<Refined<U8, Predicate8251779752648547376>, ChoiceWidth32Combinator13>;
type ChoiceWidth32CombinatorAlias15 = Choice<Refined<U8, Predicate15291213704223769698>, ChoiceWidth32Combinator14>;
type ChoiceWidth32CombinatorAlias16 = Choice<Refined<U8, Predicate6037550869214390311>, ChoiceWidth32Combinator15>;
type ChoiceWidth32CombinatorAlias17 = Choice<Refined<U8, Predicate3258795957419340618>, ChoiceWidth32Combinator16>;
type ChoiceWidth32CombinatorAlias18 = Choice<Refined<U8, Predicate4672853435886844331>, ChoiceWidth32Combinator17>;
type ChoiceWidth32CombinatorAlias19 = Choice<Refined<U8, Predicate9731316588179370935>, ChoiceWidth32Combinator18>;
type ChoiceWidth32CombinatorAlias20 = Choice<Refined<U8, Predicate13393337139612027911>, ChoiceWidth32Combinator19>;
type ChoiceWidth32CombinatorAlias21 = Choice<Refined<U8, Predicate1670200719151657759>, ChoiceWidth32Combinator20>;
type ChoiceWidth32CombinatorAlias22 = Choice<Refined<U8, Predicate2286677770329837199>, ChoiceWidth32Combinator21>;
type ChoiceWidth32CombinatorAlias23 = Choice<Refined<U8, Predicate11758281649694429187>, ChoiceWidth32Combinator22>;
type ChoiceWidth32CombinatorAlias24 = Choice<Refined<U8, Predicate9770172291787044034>, ChoiceWidth32Combinator23>;
type ChoiceWidth32CombinatorAlias25 = Choice<Refined<U8, Predicate4214186895105241400>, ChoiceWidth32Combinator24>;
type ChoiceWidth32CombinatorAlias26 = Choice<Refined<U8, Predicate9186325526105272194>, ChoiceWidth32Combinator25>;
type ChoiceWidth32CombinatorAlias27 = Choice<Refined<U8, Predicate4589101901519479956>, ChoiceWidth32Combinator26>;
type ChoiceWidth32CombinatorAlias28 = Choice<Refined<U8, Predicate2671570727481267254>, ChoiceWidth32Combinator27>;
type ChoiceWidth32CombinatorAlias29 = Choice<Refined<U8, Predicate6170912057263668010>, ChoiceWidth32Combinator28>;
type ChoiceWidth32CombinatorAlias30 = Choice<Refined<U8, Predicate13385608959756530935>, ChoiceWidth32Combinator29>;
type ChoiceWidth32CombinatorAlias31 = Choice<Refined<U8, Predicate2576612288366319398>, ChoiceWidth32Combinator30>;
pub struct ChoiceWidth32Combinator1(pub ChoiceWidth32CombinatorAlias1);
impl View for ChoiceWidth32Combinator1 {
    type V = SpecChoiceWidth32CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator1, ChoiceWidth32CombinatorAlias1);

pub struct ChoiceWidth32Combinator2(pub ChoiceWidth32CombinatorAlias2);
impl View for ChoiceWidth32Combinator2 {
    type V = SpecChoiceWidth32CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator2, ChoiceWidth32CombinatorAlias2);

pub struct ChoiceWidth32Combinator3(pub ChoiceWidth32CombinatorAlias3);
impl View for ChoiceWidth32Combinator3 {
    type V = SpecChoiceWidth32CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator3, ChoiceWidth32CombinatorAlias3);

pub struct ChoiceWidth32Combinator4(pub ChoiceWidth32CombinatorAlias4);
impl View for ChoiceWidth32Combinator4 {
    type V = SpecChoiceWidth32CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator4, ChoiceWidth32CombinatorAlias4);

pub struct ChoiceWidth32Combinator5(pub ChoiceWidth32CombinatorAlias5);
impl View for ChoiceWidth32Combinator5 {
    type V = SpecChoiceWidth32CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator5, ChoiceWidth32CombinatorAlias5);

pub struct ChoiceWidth32Combinator6(pub ChoiceWidth32CombinatorAlias6);
impl View for ChoiceWidth32Combinator6 {
    type V = SpecChoiceWidth32CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator6, ChoiceWidth32CombinatorAlias6);

pub struct ChoiceWidth32Combinator7(pub ChoiceWidth32CombinatorAlias7);
impl View for ChoiceWidth32Combinator7 {
    type V = SpecChoiceWidth32CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator7, ChoiceWidth32CombinatorAlias7);

pub struct ChoiceWidth32Combinator8(pub ChoiceWidth32CombinatorAlias8);
impl View for ChoiceWidth32Combinator8 {
    type V = SpecChoiceWidth32CombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator8, ChoiceWidth32CombinatorAlias8);

pub struct ChoiceWidth32Combinator9(pub ChoiceWidth32CombinatorAlias9);
impl View for ChoiceWidth32Combinator9 {
    type V = SpecChoiceWidth32CombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator9, ChoiceWidth32CombinatorAlias9);

pub struct ChoiceWidth32Combinator10(pub ChoiceWidth32CombinatorAlias10);
impl View for ChoiceWidth32Combinator10 {
    type V = SpecChoiceWidth32CombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator10, ChoiceWidth32CombinatorAlias10);

pub struct ChoiceWidth32Combinator11(pub ChoiceWidth32CombinatorAlias11);
impl View for ChoiceWidth32Combinator11 {
    type V = SpecChoiceWidth32CombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator11, ChoiceWidth32CombinatorAlias11);

pub struct ChoiceWidth32Combinator12(pub ChoiceWidth32CombinatorAlias12);
impl View for ChoiceWidth32Combinator12 {
    type V = SpecChoiceWidth32CombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator12, ChoiceWidth32CombinatorAlias12);

pub struct ChoiceWidth32Combinator13(pub ChoiceWidth32CombinatorAlias13);
impl View for ChoiceWidth32Combinator13 {
    type V = SpecChoiceWidth32CombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator13, ChoiceWidth32CombinatorAlias13);

pub struct ChoiceWidth32Combinator14(pub ChoiceWidth32CombinatorAlias14);
impl View for ChoiceWidth32Combinator14 {
    type V = SpecChoiceWidth32CombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator14, ChoiceWidth32CombinatorAlias14);

pub struct ChoiceWidth32Combinator15(pub ChoiceWidth32CombinatorAlias15);
impl View for ChoiceWidth32Combinator15 {
    type V = SpecChoiceWidth32CombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator15, ChoiceWidth32CombinatorAlias15);

pub struct ChoiceWidth32Combinator16(pub ChoiceWidth32CombinatorAlias16);
impl View for ChoiceWidth32Combinator16 {
    type V = SpecChoiceWidth32CombinatorAlias16;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator16, ChoiceWidth32CombinatorAlias16);

pub struct ChoiceWidth32Combinator17(pub ChoiceWidth32CombinatorAlias17);
impl View for ChoiceWidth32Combinator17 {
    type V = SpecChoiceWidth32CombinatorAlias17;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator17, ChoiceWidth32CombinatorAlias17);

pub struct ChoiceWidth32Combinator18(pub ChoiceWidth32CombinatorAlias18);
impl View for ChoiceWidth32Combinator18 {
    type V = SpecChoiceWidth32CombinatorAlias18;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator18, ChoiceWidth32CombinatorAlias18);

pub struct ChoiceWidth32Combinator19(pub ChoiceWidth32CombinatorAlias19);
impl View for ChoiceWidth32Combinator19 {
    type V = SpecChoiceWidth32CombinatorAlias19;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator19, ChoiceWidth32CombinatorAlias19);

pub struct ChoiceWidth32Combinator20(pub ChoiceWidth32CombinatorAlias20);
impl View for ChoiceWidth32Combinator20 {
    type V = SpecChoiceWidth32CombinatorAlias20;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator20, ChoiceWidth32CombinatorAlias20);

pub struct ChoiceWidth32Combinator21(pub ChoiceWidth32CombinatorAlias21);
impl View for ChoiceWidth32Combinator21 {
    type V = SpecChoiceWidth32CombinatorAlias21;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator21, ChoiceWidth32CombinatorAlias21);

pub struct ChoiceWidth32Combinator22(pub ChoiceWidth32CombinatorAlias22);
impl View for ChoiceWidth32Combinator22 {
    type V = SpecChoiceWidth32CombinatorAlias22;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator22, ChoiceWidth32CombinatorAlias22);

pub struct ChoiceWidth32Combinator23(pub ChoiceWidth32CombinatorAlias23);
impl View for ChoiceWidth32Combinator23 {
    type V = SpecChoiceWidth32CombinatorAlias23;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator23, ChoiceWidth32CombinatorAlias23);

pub struct ChoiceWidth32Combinator24(pub ChoiceWidth32CombinatorAlias24);
impl View for ChoiceWidth32Combinator24 {
    type V = SpecChoiceWidth32CombinatorAlias24;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator24, ChoiceWidth32CombinatorAlias24);

pub struct ChoiceWidth32Combinator25(pub ChoiceWidth32CombinatorAlias25);
impl View for ChoiceWidth32Combinator25 {
    type V = SpecChoiceWidth32CombinatorAlias25;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator25, ChoiceWidth32CombinatorAlias25);

pub struct ChoiceWidth32Combinator26(pub ChoiceWidth32CombinatorAlias26);
impl View for ChoiceWidth32Combinator26 {
    type V = SpecChoiceWidth32CombinatorAlias26;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator26, ChoiceWidth32CombinatorAlias26);

pub struct ChoiceWidth32Combinator27(pub ChoiceWidth32CombinatorAlias27);
impl View for ChoiceWidth32Combinator27 {
    type V = SpecChoiceWidth32CombinatorAlias27;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator27, ChoiceWidth32CombinatorAlias27);

pub struct ChoiceWidth32Combinator28(pub ChoiceWidth32CombinatorAlias28);
impl View for ChoiceWidth32Combinator28 {
    type V = SpecChoiceWidth32CombinatorAlias28;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator28, ChoiceWidth32CombinatorAlias28);

pub struct ChoiceWidth32Combinator29(pub ChoiceWidth32CombinatorAlias29);
impl View for ChoiceWidth32Combinator29 {
    type V = SpecChoiceWidth32CombinatorAlias29;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator29, ChoiceWidth32CombinatorAlias29);

pub struct ChoiceWidth32Combinator30(pub ChoiceWidth32CombinatorAlias30);
impl View for ChoiceWidth32Combinator30 {
    type V = SpecChoiceWidth32CombinatorAlias30;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator30, ChoiceWidth32CombinatorAlias30);

pub struct ChoiceWidth32Combinator31(pub ChoiceWidth32CombinatorAlias31);
impl View for ChoiceWidth32Combinator31 {
    type V = SpecChoiceWidth32CombinatorAlias31;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth32Combinator31, ChoiceWidth32CombinatorAlias31);

pub struct ChoiceWidth32Combinator(pub ChoiceWidth32CombinatorAlias);

impl View for ChoiceWidth32Combinator {
    type V = SpecChoiceWidth32Combinator;
    open spec fn view(&self) -> Self::V { SpecChoiceWidth32Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceWidth32Combinator {
    type Type = ChoiceWidth32;
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
pub type ChoiceWidth32CombinatorAlias = Mapped<ChoiceWidth32Combinator31, ChoiceWidth32Mapper>;


pub open spec fn spec_choice_width32() -> SpecChoiceWidth32Combinator {
    SpecChoiceWidth32Combinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Choice(Refined { inner: U8, predicate: Predicate13385608959756530935 }, Choice(Refined { inner: U8, predicate: Predicate6170912057263668010 }, Choice(Refined { inner: U8, predicate: Predicate2671570727481267254 }, Choice(Refined { inner: U8, predicate: Predicate4589101901519479956 }, Choice(Refined { inner: U8, predicate: Predicate9186325526105272194 }, Choice(Refined { inner: U8, predicate: Predicate4214186895105241400 }, Choice(Refined { inner: U8, predicate: Predicate9770172291787044034 }, Choice(Refined { inner: U8, predicate: Predicate11758281649694429187 }, Choice(Refined { inner: U8, predicate: Predicate2286677770329837199 }, Choice(Refined { inner: U8, predicate: Predicate1670200719151657759 }, Choice(Refined { inner: U8, predicate: Predicate13393337139612027911 }, Choice(Refined { inner: U8, predicate: Predicate9731316588179370935 }, Choice(Refined { inner: U8, predicate: Predicate4672853435886844331 }, Choice(Refined { inner: U8, predicate: Predicate3258795957419340618 }, Choice(Refined { inner: U8, predicate: Predicate6037550869214390311 }, Choice(Refined { inner: U8, predicate: Predicate15291213704223769698 }, Choice(Refined { inner: U8, predicate: Predicate8251779752648547376 }, Choice(Refined { inner: U8, predicate: Predicate14707428835277590315 }, Choice(Refined { inner: U8, predicate: Predicate4072810196653762843 }, Choice(Refined { inner: U8, predicate: Predicate1445610904132711222 }, Choice(Refined { inner: U8, predicate: Predicate16333054977080421469 }, Choice(Refined { inner: U8, predicate: Predicate4869308575099852777 }, Choice(Refined { inner: U8, predicate: Predicate1304083776951938903 }, Choice(Refined { inner: U8, predicate: Predicate14174989844364464752 }, Choice(Refined { inner: U8, predicate: Predicate2213030098669005785 }, Choice(Refined { inner: U8, predicate: Predicate3285282901849553415 }, Choice(Refined { inner: U8, predicate: Predicate14700689986523383325 }, Choice(Refined { inner: U8, predicate: Predicate11809820865766219170 }, Choice(Refined { inner: U8, predicate: Predicate17516429898706644594 }, Choice(Refined { inner: U8, predicate: Predicate1385328176252848081 }, Refined { inner: U8, predicate: Predicate14757914070657982036 }))))))))))))))))))))))))))))))), mapper: ChoiceWidth32Mapper })
}

                
pub fn choice_width32<'a>() -> (o: ChoiceWidth32Combinator)
    ensures o@ == spec_choice_width32(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceWidth32Combinator(Mapped { inner: ChoiceWidth32Combinator31(Choice::new(Refined { inner: U8, predicate: Predicate2576612288366319398 }, ChoiceWidth32Combinator30(Choice::new(Refined { inner: U8, predicate: Predicate13385608959756530935 }, ChoiceWidth32Combinator29(Choice::new(Refined { inner: U8, predicate: Predicate6170912057263668010 }, ChoiceWidth32Combinator28(Choice::new(Refined { inner: U8, predicate: Predicate2671570727481267254 }, ChoiceWidth32Combinator27(Choice::new(Refined { inner: U8, predicate: Predicate4589101901519479956 }, ChoiceWidth32Combinator26(Choice::new(Refined { inner: U8, predicate: Predicate9186325526105272194 }, ChoiceWidth32Combinator25(Choice::new(Refined { inner: U8, predicate: Predicate4214186895105241400 }, ChoiceWidth32Combinator24(Choice::new(Refined { inner: U8, predicate: Predicate9770172291787044034 }, ChoiceWidth32Combinator23(Choice::new(Refined { inner: U8, predicate: Predicate11758281649694429187 }, ChoiceWidth32Combinator22(Choice::new(Refined { inner: U8, predicate: Predicate2286677770329837199 }, ChoiceWidth32Combinator21(Choice::new(Refined { inner: U8, predicate: Predicate1670200719151657759 }, ChoiceWidth32Combinator20(Choice::new(Refined { inner: U8, predicate: Predicate13393337139612027911 }, ChoiceWidth32Combinator19(Choice::new(Refined { inner: U8, predicate: Predicate9731316588179370935 }, ChoiceWidth32Combinator18(Choice::new(Refined { inner: U8, predicate: Predicate4672853435886844331 }, ChoiceWidth32Combinator17(Choice::new(Refined { inner: U8, predicate: Predicate3258795957419340618 }, ChoiceWidth32Combinator16(Choice::new(Refined { inner: U8, predicate: Predicate6037550869214390311 }, ChoiceWidth32Combinator15(Choice::new(Refined { inner: U8, predicate: Predicate15291213704223769698 }, ChoiceWidth32Combinator14(Choice::new(Refined { inner: U8, predicate: Predicate8251779752648547376 }, ChoiceWidth32Combinator13(Choice::new(Refined { inner: U8, predicate: Predicate14707428835277590315 }, ChoiceWidth32Combinator12(Choice::new(Refined { inner: U8, predicate: Predicate4072810196653762843 }, ChoiceWidth32Combinator11(Choice::new(Refined { inner: U8, predicate: Predicate1445610904132711222 }, ChoiceWidth32Combinator10(Choice::new(Refined { inner: U8, predicate: Predicate16333054977080421469 }, ChoiceWidth32Combinator9(Choice::new(Refined { inner: U8, predicate: Predicate4869308575099852777 }, ChoiceWidth32Combinator8(Choice::new(Refined { inner: U8, predicate: Predicate1304083776951938903 }, ChoiceWidth32Combinator7(Choice::new(Refined { inner: U8, predicate: Predicate14174989844364464752 }, ChoiceWidth32Combinator6(Choice::new(Refined { inner: U8, predicate: Predicate2213030098669005785 }, ChoiceWidth32Combinator5(Choice::new(Refined { inner: U8, predicate: Predicate3285282901849553415 }, ChoiceWidth32Combinator4(Choice::new(Refined { inner: U8, predicate: Predicate14700689986523383325 }, ChoiceWidth32Combinator3(Choice::new(Refined { inner: U8, predicate: Predicate11809820865766219170 }, ChoiceWidth32Combinator2(Choice::new(Refined { inner: U8, predicate: Predicate17516429898706644594 }, ChoiceWidth32Combinator1(Choice::new(Refined { inner: U8, predicate: Predicate1385328176252848081 }, Refined { inner: U8, predicate: Predicate14757914070657982036 })))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: ChoiceWidth32Mapper });
    // assert({
    //     &&& combinator@ == spec_choice_width32()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_width32<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceWidth32Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_width32().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_width32().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_width32().spec_parse(input@) is None,
        spec_choice_width32().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_width32();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_width32<'a>(v: <ChoiceWidth32Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_width32().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_choice_width32().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_choice_width32().spec_serialize(v@))
        },
{
    let combinator = choice_width32();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn choice_width32_len<'a>(v: <ChoiceWidth32Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_width32().wf(v@),
        spec_choice_width32().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_width32().spec_serialize(v@).len(),
{
    let combinator = choice_width32();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
