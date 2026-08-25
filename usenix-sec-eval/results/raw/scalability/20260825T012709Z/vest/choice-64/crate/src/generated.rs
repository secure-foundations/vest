
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

pub enum SpecChoiceWidth64 {
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
    Variant32(u8),
    Variant33(u8),
    Variant34(u8),
    Variant35(u8),
    Variant36(u8),
    Variant37(u8),
    Variant38(u8),
    Variant39(u8),
    Variant40(u8),
    Variant41(u8),
    Variant42(u8),
    Variant43(u8),
    Variant44(u8),
    Variant45(u8),
    Variant46(u8),
    Variant47(u8),
    Variant48(u8),
    Variant49(u8),
    Variant50(u8),
    Variant51(u8),
    Variant52(u8),
    Variant53(u8),
    Variant54(u8),
    Variant55(u8),
    Variant56(u8),
    Variant57(u8),
    Variant58(u8),
    Variant59(u8),
    Variant60(u8),
    Variant61(u8),
    Variant62(u8),
    Variant63(u8),
}

pub type SpecChoiceWidth64Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

impl SpecFrom<SpecChoiceWidth64> for SpecChoiceWidth64Inner {
    open spec fn spec_from(m: SpecChoiceWidth64) -> SpecChoiceWidth64Inner {
        match m {
            SpecChoiceWidth64::Variant0(m) => Either::Left(m),
            SpecChoiceWidth64::Variant1(m) => Either::Right(Either::Left(m)),
            SpecChoiceWidth64::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecChoiceWidth64::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecChoiceWidth64::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecChoiceWidth64::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecChoiceWidth64::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecChoiceWidth64::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecChoiceWidth64::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecChoiceWidth64::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecChoiceWidth64::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecChoiceWidth64::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecChoiceWidth64::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecChoiceWidth64::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecChoiceWidth64::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecChoiceWidth64::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecChoiceWidth64::Variant16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecChoiceWidth64::Variant17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecChoiceWidth64::Variant18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecChoiceWidth64::Variant19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecChoiceWidth64::Variant20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecChoiceWidth64::Variant21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecChoiceWidth64::Variant22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecChoiceWidth64::Variant23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecChoiceWidth64::Variant24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant31(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant32(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant33(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant34(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant35(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant36(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant37(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant38(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant39(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant40(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant41(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant42(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant43(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant44(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant45(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant46(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant47(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant48(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant49(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant50(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant51(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant52(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant53(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant54(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant55(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant56(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant57(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant58(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant59(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant60(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant61(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant62(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            SpecChoiceWidth64::Variant63(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecChoiceWidth64Inner> for SpecChoiceWidth64 {
    open spec fn spec_from(m: SpecChoiceWidth64Inner) -> SpecChoiceWidth64 {
        match m {
            Either::Left(m) => SpecChoiceWidth64::Variant0(m),
            Either::Right(Either::Left(m)) => SpecChoiceWidth64::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecChoiceWidth64::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecChoiceWidth64::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecChoiceWidth64::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecChoiceWidth64::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecChoiceWidth64::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecChoiceWidth64::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecChoiceWidth64::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecChoiceWidth64::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecChoiceWidth64::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecChoiceWidth64::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecChoiceWidth64::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecChoiceWidth64::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecChoiceWidth64::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecChoiceWidth64::Variant15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecChoiceWidth64::Variant16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecChoiceWidth64::Variant17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecChoiceWidth64::Variant18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecChoiceWidth64::Variant19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecChoiceWidth64::Variant20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecChoiceWidth64::Variant21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecChoiceWidth64::Variant22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecChoiceWidth64::Variant23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecChoiceWidth64::Variant24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecChoiceWidth64::Variant25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant30(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant31(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant32(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant33(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant34(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant35(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant36(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant37(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant38(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant39(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant40(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant41(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant42(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant43(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant44(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant45(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant46(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant47(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant48(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant49(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant50(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant51(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant52(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant53(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant54(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant55(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant56(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant57(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant58(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant59(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant60(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant61(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant62(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => SpecChoiceWidth64::Variant63(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChoiceWidth64 {
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
    Variant32(u8),
    Variant33(u8),
    Variant34(u8),
    Variant35(u8),
    Variant36(u8),
    Variant37(u8),
    Variant38(u8),
    Variant39(u8),
    Variant40(u8),
    Variant41(u8),
    Variant42(u8),
    Variant43(u8),
    Variant44(u8),
    Variant45(u8),
    Variant46(u8),
    Variant47(u8),
    Variant48(u8),
    Variant49(u8),
    Variant50(u8),
    Variant51(u8),
    Variant52(u8),
    Variant53(u8),
    Variant54(u8),
    Variant55(u8),
    Variant56(u8),
    Variant57(u8),
    Variant58(u8),
    Variant59(u8),
    Variant60(u8),
    Variant61(u8),
    Variant62(u8),
    Variant63(u8),
}

pub type ChoiceWidth64Inner = Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, Either<u8, u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

pub type ChoiceWidth64InnerRef<'a> = Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, Either<&'a u8, &'a u8>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;


impl View for ChoiceWidth64 {
    type V = SpecChoiceWidth64;
    open spec fn view(&self) -> Self::V {
        match self {
            ChoiceWidth64::Variant0(m) => SpecChoiceWidth64::Variant0(m@),
            ChoiceWidth64::Variant1(m) => SpecChoiceWidth64::Variant1(m@),
            ChoiceWidth64::Variant2(m) => SpecChoiceWidth64::Variant2(m@),
            ChoiceWidth64::Variant3(m) => SpecChoiceWidth64::Variant3(m@),
            ChoiceWidth64::Variant4(m) => SpecChoiceWidth64::Variant4(m@),
            ChoiceWidth64::Variant5(m) => SpecChoiceWidth64::Variant5(m@),
            ChoiceWidth64::Variant6(m) => SpecChoiceWidth64::Variant6(m@),
            ChoiceWidth64::Variant7(m) => SpecChoiceWidth64::Variant7(m@),
            ChoiceWidth64::Variant8(m) => SpecChoiceWidth64::Variant8(m@),
            ChoiceWidth64::Variant9(m) => SpecChoiceWidth64::Variant9(m@),
            ChoiceWidth64::Variant10(m) => SpecChoiceWidth64::Variant10(m@),
            ChoiceWidth64::Variant11(m) => SpecChoiceWidth64::Variant11(m@),
            ChoiceWidth64::Variant12(m) => SpecChoiceWidth64::Variant12(m@),
            ChoiceWidth64::Variant13(m) => SpecChoiceWidth64::Variant13(m@),
            ChoiceWidth64::Variant14(m) => SpecChoiceWidth64::Variant14(m@),
            ChoiceWidth64::Variant15(m) => SpecChoiceWidth64::Variant15(m@),
            ChoiceWidth64::Variant16(m) => SpecChoiceWidth64::Variant16(m@),
            ChoiceWidth64::Variant17(m) => SpecChoiceWidth64::Variant17(m@),
            ChoiceWidth64::Variant18(m) => SpecChoiceWidth64::Variant18(m@),
            ChoiceWidth64::Variant19(m) => SpecChoiceWidth64::Variant19(m@),
            ChoiceWidth64::Variant20(m) => SpecChoiceWidth64::Variant20(m@),
            ChoiceWidth64::Variant21(m) => SpecChoiceWidth64::Variant21(m@),
            ChoiceWidth64::Variant22(m) => SpecChoiceWidth64::Variant22(m@),
            ChoiceWidth64::Variant23(m) => SpecChoiceWidth64::Variant23(m@),
            ChoiceWidth64::Variant24(m) => SpecChoiceWidth64::Variant24(m@),
            ChoiceWidth64::Variant25(m) => SpecChoiceWidth64::Variant25(m@),
            ChoiceWidth64::Variant26(m) => SpecChoiceWidth64::Variant26(m@),
            ChoiceWidth64::Variant27(m) => SpecChoiceWidth64::Variant27(m@),
            ChoiceWidth64::Variant28(m) => SpecChoiceWidth64::Variant28(m@),
            ChoiceWidth64::Variant29(m) => SpecChoiceWidth64::Variant29(m@),
            ChoiceWidth64::Variant30(m) => SpecChoiceWidth64::Variant30(m@),
            ChoiceWidth64::Variant31(m) => SpecChoiceWidth64::Variant31(m@),
            ChoiceWidth64::Variant32(m) => SpecChoiceWidth64::Variant32(m@),
            ChoiceWidth64::Variant33(m) => SpecChoiceWidth64::Variant33(m@),
            ChoiceWidth64::Variant34(m) => SpecChoiceWidth64::Variant34(m@),
            ChoiceWidth64::Variant35(m) => SpecChoiceWidth64::Variant35(m@),
            ChoiceWidth64::Variant36(m) => SpecChoiceWidth64::Variant36(m@),
            ChoiceWidth64::Variant37(m) => SpecChoiceWidth64::Variant37(m@),
            ChoiceWidth64::Variant38(m) => SpecChoiceWidth64::Variant38(m@),
            ChoiceWidth64::Variant39(m) => SpecChoiceWidth64::Variant39(m@),
            ChoiceWidth64::Variant40(m) => SpecChoiceWidth64::Variant40(m@),
            ChoiceWidth64::Variant41(m) => SpecChoiceWidth64::Variant41(m@),
            ChoiceWidth64::Variant42(m) => SpecChoiceWidth64::Variant42(m@),
            ChoiceWidth64::Variant43(m) => SpecChoiceWidth64::Variant43(m@),
            ChoiceWidth64::Variant44(m) => SpecChoiceWidth64::Variant44(m@),
            ChoiceWidth64::Variant45(m) => SpecChoiceWidth64::Variant45(m@),
            ChoiceWidth64::Variant46(m) => SpecChoiceWidth64::Variant46(m@),
            ChoiceWidth64::Variant47(m) => SpecChoiceWidth64::Variant47(m@),
            ChoiceWidth64::Variant48(m) => SpecChoiceWidth64::Variant48(m@),
            ChoiceWidth64::Variant49(m) => SpecChoiceWidth64::Variant49(m@),
            ChoiceWidth64::Variant50(m) => SpecChoiceWidth64::Variant50(m@),
            ChoiceWidth64::Variant51(m) => SpecChoiceWidth64::Variant51(m@),
            ChoiceWidth64::Variant52(m) => SpecChoiceWidth64::Variant52(m@),
            ChoiceWidth64::Variant53(m) => SpecChoiceWidth64::Variant53(m@),
            ChoiceWidth64::Variant54(m) => SpecChoiceWidth64::Variant54(m@),
            ChoiceWidth64::Variant55(m) => SpecChoiceWidth64::Variant55(m@),
            ChoiceWidth64::Variant56(m) => SpecChoiceWidth64::Variant56(m@),
            ChoiceWidth64::Variant57(m) => SpecChoiceWidth64::Variant57(m@),
            ChoiceWidth64::Variant58(m) => SpecChoiceWidth64::Variant58(m@),
            ChoiceWidth64::Variant59(m) => SpecChoiceWidth64::Variant59(m@),
            ChoiceWidth64::Variant60(m) => SpecChoiceWidth64::Variant60(m@),
            ChoiceWidth64::Variant61(m) => SpecChoiceWidth64::Variant61(m@),
            ChoiceWidth64::Variant62(m) => SpecChoiceWidth64::Variant62(m@),
            ChoiceWidth64::Variant63(m) => SpecChoiceWidth64::Variant63(m@),
        }
    }
}


impl<'a> From<&'a ChoiceWidth64> for ChoiceWidth64InnerRef<'a> {
    fn ex_from(m: &'a ChoiceWidth64) -> ChoiceWidth64InnerRef<'a> {
        match m {
            ChoiceWidth64::Variant0(m) => Either::Left(m),
            ChoiceWidth64::Variant1(m) => Either::Right(Either::Left(m)),
            ChoiceWidth64::Variant2(m) => Either::Right(Either::Right(Either::Left(m))),
            ChoiceWidth64::Variant3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ChoiceWidth64::Variant4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ChoiceWidth64::Variant5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ChoiceWidth64::Variant6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ChoiceWidth64::Variant7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ChoiceWidth64::Variant8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ChoiceWidth64::Variant9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ChoiceWidth64::Variant10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ChoiceWidth64::Variant11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ChoiceWidth64::Variant12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ChoiceWidth64::Variant13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ChoiceWidth64::Variant14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ChoiceWidth64::Variant15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ChoiceWidth64::Variant16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ChoiceWidth64::Variant17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ChoiceWidth64::Variant18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ChoiceWidth64::Variant19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ChoiceWidth64::Variant20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ChoiceWidth64::Variant21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ChoiceWidth64::Variant22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ChoiceWidth64::Variant23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ChoiceWidth64::Variant24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            ChoiceWidth64::Variant25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            ChoiceWidth64::Variant26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            ChoiceWidth64::Variant27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            ChoiceWidth64::Variant28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant31(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant32(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant33(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant34(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant35(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant36(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant37(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant38(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant39(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant40(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant41(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant42(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant43(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant44(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant45(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant46(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant47(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant48(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant49(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant50(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant51(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant52(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant53(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant54(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant55(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant56(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant57(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant58(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant59(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant60(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant61(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant62(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
            ChoiceWidth64::Variant63(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        }
    }

}

impl From<ChoiceWidth64Inner> for ChoiceWidth64 {
    fn ex_from(m: ChoiceWidth64Inner) -> ChoiceWidth64 {
        match m {
            Either::Left(m) => ChoiceWidth64::Variant0(m),
            Either::Right(Either::Left(m)) => ChoiceWidth64::Variant1(m),
            Either::Right(Either::Right(Either::Left(m))) => ChoiceWidth64::Variant2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ChoiceWidth64::Variant3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ChoiceWidth64::Variant4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ChoiceWidth64::Variant5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ChoiceWidth64::Variant6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ChoiceWidth64::Variant7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ChoiceWidth64::Variant8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ChoiceWidth64::Variant9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ChoiceWidth64::Variant10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ChoiceWidth64::Variant11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ChoiceWidth64::Variant12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ChoiceWidth64::Variant13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ChoiceWidth64::Variant14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ChoiceWidth64::Variant15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ChoiceWidth64::Variant16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ChoiceWidth64::Variant17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ChoiceWidth64::Variant18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ChoiceWidth64::Variant19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ChoiceWidth64::Variant20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ChoiceWidth64::Variant21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ChoiceWidth64::Variant22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ChoiceWidth64::Variant23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => ChoiceWidth64::Variant24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => ChoiceWidth64::Variant25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => ChoiceWidth64::Variant26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => ChoiceWidth64::Variant27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => ChoiceWidth64::Variant28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => ChoiceWidth64::Variant29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant30(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant31(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant32(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant33(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant34(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant35(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant36(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant37(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant38(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant39(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant40(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant41(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant42(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant43(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant44(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant45(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant46(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant47(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant48(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant49(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant50(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant51(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant52(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant53(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant54(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant55(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant56(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant57(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant58(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant59(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant60(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant61(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant62(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) => ChoiceWidth64::Variant63(m),
        }
    }
    
}


pub struct ChoiceWidth64Mapper;
impl View for ChoiceWidth64Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChoiceWidth64Mapper {
    type Src = SpecChoiceWidth64Inner;
    type Dst = SpecChoiceWidth64;
}
impl SpecIsoProof for ChoiceWidth64Mapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChoiceWidth64Mapper {
    type Src = ChoiceWidth64Inner;
    type Dst = ChoiceWidth64;
    type RefSrc = ChoiceWidth64InnerRef<'a>;
}

type SpecChoiceWidth64CombinatorAlias1 = Choice<Refined<U8, Predicate3507748065990518294>, Refined<U8, Predicate7060793718683294274>>;
type SpecChoiceWidth64CombinatorAlias2 = Choice<Refined<U8, Predicate16525731073934049962>, SpecChoiceWidth64CombinatorAlias1>;
type SpecChoiceWidth64CombinatorAlias3 = Choice<Refined<U8, Predicate16096414308557702779>, SpecChoiceWidth64CombinatorAlias2>;
type SpecChoiceWidth64CombinatorAlias4 = Choice<Refined<U8, Predicate523614933806454484>, SpecChoiceWidth64CombinatorAlias3>;
type SpecChoiceWidth64CombinatorAlias5 = Choice<Refined<U8, Predicate16310795002558583531>, SpecChoiceWidth64CombinatorAlias4>;
type SpecChoiceWidth64CombinatorAlias6 = Choice<Refined<U8, Predicate17887014877089214959>, SpecChoiceWidth64CombinatorAlias5>;
type SpecChoiceWidth64CombinatorAlias7 = Choice<Refined<U8, Predicate7061727330754004306>, SpecChoiceWidth64CombinatorAlias6>;
type SpecChoiceWidth64CombinatorAlias8 = Choice<Refined<U8, Predicate2601603138918071977>, SpecChoiceWidth64CombinatorAlias7>;
type SpecChoiceWidth64CombinatorAlias9 = Choice<Refined<U8, Predicate16056970709915507831>, SpecChoiceWidth64CombinatorAlias8>;
type SpecChoiceWidth64CombinatorAlias10 = Choice<Refined<U8, Predicate4585217353424408452>, SpecChoiceWidth64CombinatorAlias9>;
type SpecChoiceWidth64CombinatorAlias11 = Choice<Refined<U8, Predicate13280578818964598340>, SpecChoiceWidth64CombinatorAlias10>;
type SpecChoiceWidth64CombinatorAlias12 = Choice<Refined<U8, Predicate2548737043788673441>, SpecChoiceWidth64CombinatorAlias11>;
type SpecChoiceWidth64CombinatorAlias13 = Choice<Refined<U8, Predicate7168319075050448275>, SpecChoiceWidth64CombinatorAlias12>;
type SpecChoiceWidth64CombinatorAlias14 = Choice<Refined<U8, Predicate5708320620815040592>, SpecChoiceWidth64CombinatorAlias13>;
type SpecChoiceWidth64CombinatorAlias15 = Choice<Refined<U8, Predicate13353397467677316255>, SpecChoiceWidth64CombinatorAlias14>;
type SpecChoiceWidth64CombinatorAlias16 = Choice<Refined<U8, Predicate8132005230405764957>, SpecChoiceWidth64CombinatorAlias15>;
type SpecChoiceWidth64CombinatorAlias17 = Choice<Refined<U8, Predicate14940225619408692556>, SpecChoiceWidth64CombinatorAlias16>;
type SpecChoiceWidth64CombinatorAlias18 = Choice<Refined<U8, Predicate2033264211231655736>, SpecChoiceWidth64CombinatorAlias17>;
type SpecChoiceWidth64CombinatorAlias19 = Choice<Refined<U8, Predicate1713587495682179202>, SpecChoiceWidth64CombinatorAlias18>;
type SpecChoiceWidth64CombinatorAlias20 = Choice<Refined<U8, Predicate11749655642528703983>, SpecChoiceWidth64CombinatorAlias19>;
type SpecChoiceWidth64CombinatorAlias21 = Choice<Refined<U8, Predicate12936565273184922672>, SpecChoiceWidth64CombinatorAlias20>;
type SpecChoiceWidth64CombinatorAlias22 = Choice<Refined<U8, Predicate1470905948243798090>, SpecChoiceWidth64CombinatorAlias21>;
type SpecChoiceWidth64CombinatorAlias23 = Choice<Refined<U8, Predicate15352586006205863074>, SpecChoiceWidth64CombinatorAlias22>;
type SpecChoiceWidth64CombinatorAlias24 = Choice<Refined<U8, Predicate17318782312207542369>, SpecChoiceWidth64CombinatorAlias23>;
type SpecChoiceWidth64CombinatorAlias25 = Choice<Refined<U8, Predicate528137220236479490>, SpecChoiceWidth64CombinatorAlias24>;
type SpecChoiceWidth64CombinatorAlias26 = Choice<Refined<U8, Predicate15502240502801463573>, SpecChoiceWidth64CombinatorAlias25>;
type SpecChoiceWidth64CombinatorAlias27 = Choice<Refined<U8, Predicate15872893073119229437>, SpecChoiceWidth64CombinatorAlias26>;
type SpecChoiceWidth64CombinatorAlias28 = Choice<Refined<U8, Predicate8880797979392678721>, SpecChoiceWidth64CombinatorAlias27>;
type SpecChoiceWidth64CombinatorAlias29 = Choice<Refined<U8, Predicate14945695403078815867>, SpecChoiceWidth64CombinatorAlias28>;
type SpecChoiceWidth64CombinatorAlias30 = Choice<Refined<U8, Predicate364580195256496202>, SpecChoiceWidth64CombinatorAlias29>;
type SpecChoiceWidth64CombinatorAlias31 = Choice<Refined<U8, Predicate4262279460611959614>, SpecChoiceWidth64CombinatorAlias30>;
type SpecChoiceWidth64CombinatorAlias32 = Choice<Refined<U8, Predicate4772354365252939758>, SpecChoiceWidth64CombinatorAlias31>;
type SpecChoiceWidth64CombinatorAlias33 = Choice<Refined<U8, Predicate1385328176252848081>, SpecChoiceWidth64CombinatorAlias32>;
type SpecChoiceWidth64CombinatorAlias34 = Choice<Refined<U8, Predicate17516429898706644594>, SpecChoiceWidth64CombinatorAlias33>;
type SpecChoiceWidth64CombinatorAlias35 = Choice<Refined<U8, Predicate11809820865766219170>, SpecChoiceWidth64CombinatorAlias34>;
type SpecChoiceWidth64CombinatorAlias36 = Choice<Refined<U8, Predicate14700689986523383325>, SpecChoiceWidth64CombinatorAlias35>;
type SpecChoiceWidth64CombinatorAlias37 = Choice<Refined<U8, Predicate3285282901849553415>, SpecChoiceWidth64CombinatorAlias36>;
type SpecChoiceWidth64CombinatorAlias38 = Choice<Refined<U8, Predicate2213030098669005785>, SpecChoiceWidth64CombinatorAlias37>;
type SpecChoiceWidth64CombinatorAlias39 = Choice<Refined<U8, Predicate14174989844364464752>, SpecChoiceWidth64CombinatorAlias38>;
type SpecChoiceWidth64CombinatorAlias40 = Choice<Refined<U8, Predicate1304083776951938903>, SpecChoiceWidth64CombinatorAlias39>;
type SpecChoiceWidth64CombinatorAlias41 = Choice<Refined<U8, Predicate4869308575099852777>, SpecChoiceWidth64CombinatorAlias40>;
type SpecChoiceWidth64CombinatorAlias42 = Choice<Refined<U8, Predicate16333054977080421469>, SpecChoiceWidth64CombinatorAlias41>;
type SpecChoiceWidth64CombinatorAlias43 = Choice<Refined<U8, Predicate1445610904132711222>, SpecChoiceWidth64CombinatorAlias42>;
type SpecChoiceWidth64CombinatorAlias44 = Choice<Refined<U8, Predicate4072810196653762843>, SpecChoiceWidth64CombinatorAlias43>;
type SpecChoiceWidth64CombinatorAlias45 = Choice<Refined<U8, Predicate14707428835277590315>, SpecChoiceWidth64CombinatorAlias44>;
type SpecChoiceWidth64CombinatorAlias46 = Choice<Refined<U8, Predicate8251779752648547376>, SpecChoiceWidth64CombinatorAlias45>;
type SpecChoiceWidth64CombinatorAlias47 = Choice<Refined<U8, Predicate15291213704223769698>, SpecChoiceWidth64CombinatorAlias46>;
type SpecChoiceWidth64CombinatorAlias48 = Choice<Refined<U8, Predicate6037550869214390311>, SpecChoiceWidth64CombinatorAlias47>;
type SpecChoiceWidth64CombinatorAlias49 = Choice<Refined<U8, Predicate3258795957419340618>, SpecChoiceWidth64CombinatorAlias48>;
type SpecChoiceWidth64CombinatorAlias50 = Choice<Refined<U8, Predicate4672853435886844331>, SpecChoiceWidth64CombinatorAlias49>;
type SpecChoiceWidth64CombinatorAlias51 = Choice<Refined<U8, Predicate9731316588179370935>, SpecChoiceWidth64CombinatorAlias50>;
type SpecChoiceWidth64CombinatorAlias52 = Choice<Refined<U8, Predicate13393337139612027911>, SpecChoiceWidth64CombinatorAlias51>;
type SpecChoiceWidth64CombinatorAlias53 = Choice<Refined<U8, Predicate1670200719151657759>, SpecChoiceWidth64CombinatorAlias52>;
type SpecChoiceWidth64CombinatorAlias54 = Choice<Refined<U8, Predicate2286677770329837199>, SpecChoiceWidth64CombinatorAlias53>;
type SpecChoiceWidth64CombinatorAlias55 = Choice<Refined<U8, Predicate11758281649694429187>, SpecChoiceWidth64CombinatorAlias54>;
type SpecChoiceWidth64CombinatorAlias56 = Choice<Refined<U8, Predicate9770172291787044034>, SpecChoiceWidth64CombinatorAlias55>;
type SpecChoiceWidth64CombinatorAlias57 = Choice<Refined<U8, Predicate4214186895105241400>, SpecChoiceWidth64CombinatorAlias56>;
type SpecChoiceWidth64CombinatorAlias58 = Choice<Refined<U8, Predicate9186325526105272194>, SpecChoiceWidth64CombinatorAlias57>;
type SpecChoiceWidth64CombinatorAlias59 = Choice<Refined<U8, Predicate4589101901519479956>, SpecChoiceWidth64CombinatorAlias58>;
type SpecChoiceWidth64CombinatorAlias60 = Choice<Refined<U8, Predicate2671570727481267254>, SpecChoiceWidth64CombinatorAlias59>;
type SpecChoiceWidth64CombinatorAlias61 = Choice<Refined<U8, Predicate6170912057263668010>, SpecChoiceWidth64CombinatorAlias60>;
type SpecChoiceWidth64CombinatorAlias62 = Choice<Refined<U8, Predicate13385608959756530935>, SpecChoiceWidth64CombinatorAlias61>;
type SpecChoiceWidth64CombinatorAlias63 = Choice<Refined<U8, Predicate2576612288366319398>, SpecChoiceWidth64CombinatorAlias62>;
pub struct SpecChoiceWidth64Combinator(pub SpecChoiceWidth64CombinatorAlias);

impl SpecCombinator for SpecChoiceWidth64Combinator {
    type Type = SpecChoiceWidth64;
    open spec fn requires(&self) -> bool
    { self.0.requires() }
    open spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChoiceWidth64Combinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChoiceWidth64CombinatorAlias::is_prefix_secure() }
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
pub type SpecChoiceWidth64CombinatorAlias = Mapped<SpecChoiceWidth64CombinatorAlias63, ChoiceWidth64Mapper>;
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
pub struct Predicate4772354365252939758;
impl View for Predicate4772354365252939758 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4772354365252939758 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 31)
    }
}
impl SpecPred<u8> for Predicate4772354365252939758 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 31)
    }
}
pub struct Predicate4262279460611959614;
impl View for Predicate4262279460611959614 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4262279460611959614 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 32)
    }
}
impl SpecPred<u8> for Predicate4262279460611959614 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 32)
    }
}
pub struct Predicate364580195256496202;
impl View for Predicate364580195256496202 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate364580195256496202 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 33)
    }
}
impl SpecPred<u8> for Predicate364580195256496202 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 33)
    }
}
pub struct Predicate14945695403078815867;
impl View for Predicate14945695403078815867 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14945695403078815867 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 34)
    }
}
impl SpecPred<u8> for Predicate14945695403078815867 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 34)
    }
}
pub struct Predicate8880797979392678721;
impl View for Predicate8880797979392678721 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8880797979392678721 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 35)
    }
}
impl SpecPred<u8> for Predicate8880797979392678721 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 35)
    }
}
pub struct Predicate15872893073119229437;
impl View for Predicate15872893073119229437 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15872893073119229437 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 36)
    }
}
impl SpecPred<u8> for Predicate15872893073119229437 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 36)
    }
}
pub struct Predicate15502240502801463573;
impl View for Predicate15502240502801463573 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15502240502801463573 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 37)
    }
}
impl SpecPred<u8> for Predicate15502240502801463573 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 37)
    }
}
pub struct Predicate528137220236479490;
impl View for Predicate528137220236479490 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate528137220236479490 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 38)
    }
}
impl SpecPred<u8> for Predicate528137220236479490 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 38)
    }
}
pub struct Predicate17318782312207542369;
impl View for Predicate17318782312207542369 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate17318782312207542369 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 39)
    }
}
impl SpecPred<u8> for Predicate17318782312207542369 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 39)
    }
}
pub struct Predicate15352586006205863074;
impl View for Predicate15352586006205863074 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate15352586006205863074 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 40)
    }
}
impl SpecPred<u8> for Predicate15352586006205863074 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 40)
    }
}
pub struct Predicate1470905948243798090;
impl View for Predicate1470905948243798090 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1470905948243798090 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 41)
    }
}
impl SpecPred<u8> for Predicate1470905948243798090 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 41)
    }
}
pub struct Predicate12936565273184922672;
impl View for Predicate12936565273184922672 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate12936565273184922672 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 42)
    }
}
impl SpecPred<u8> for Predicate12936565273184922672 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 42)
    }
}
pub struct Predicate11749655642528703983;
impl View for Predicate11749655642528703983 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate11749655642528703983 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 43)
    }
}
impl SpecPred<u8> for Predicate11749655642528703983 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 43)
    }
}
pub struct Predicate1713587495682179202;
impl View for Predicate1713587495682179202 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate1713587495682179202 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 44)
    }
}
impl SpecPred<u8> for Predicate1713587495682179202 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 44)
    }
}
pub struct Predicate2033264211231655736;
impl View for Predicate2033264211231655736 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2033264211231655736 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 45)
    }
}
impl SpecPred<u8> for Predicate2033264211231655736 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 45)
    }
}
pub struct Predicate14940225619408692556;
impl View for Predicate14940225619408692556 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate14940225619408692556 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 46)
    }
}
impl SpecPred<u8> for Predicate14940225619408692556 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 46)
    }
}
pub struct Predicate8132005230405764957;
impl View for Predicate8132005230405764957 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate8132005230405764957 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 47)
    }
}
impl SpecPred<u8> for Predicate8132005230405764957 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 47)
    }
}
pub struct Predicate13353397467677316255;
impl View for Predicate13353397467677316255 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13353397467677316255 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 48)
    }
}
impl SpecPred<u8> for Predicate13353397467677316255 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 48)
    }
}
pub struct Predicate5708320620815040592;
impl View for Predicate5708320620815040592 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate5708320620815040592 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 49)
    }
}
impl SpecPred<u8> for Predicate5708320620815040592 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 49)
    }
}
pub struct Predicate7168319075050448275;
impl View for Predicate7168319075050448275 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7168319075050448275 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 50)
    }
}
impl SpecPred<u8> for Predicate7168319075050448275 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 50)
    }
}
pub struct Predicate2548737043788673441;
impl View for Predicate2548737043788673441 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2548737043788673441 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 51)
    }
}
impl SpecPred<u8> for Predicate2548737043788673441 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 51)
    }
}
pub struct Predicate13280578818964598340;
impl View for Predicate13280578818964598340 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate13280578818964598340 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 52)
    }
}
impl SpecPred<u8> for Predicate13280578818964598340 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 52)
    }
}
pub struct Predicate4585217353424408452;
impl View for Predicate4585217353424408452 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate4585217353424408452 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 53)
    }
}
impl SpecPred<u8> for Predicate4585217353424408452 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 53)
    }
}
pub struct Predicate16056970709915507831;
impl View for Predicate16056970709915507831 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16056970709915507831 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 54)
    }
}
impl SpecPred<u8> for Predicate16056970709915507831 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 54)
    }
}
pub struct Predicate2601603138918071977;
impl View for Predicate2601603138918071977 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate2601603138918071977 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 55)
    }
}
impl SpecPred<u8> for Predicate2601603138918071977 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 55)
    }
}
pub struct Predicate7061727330754004306;
impl View for Predicate7061727330754004306 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7061727330754004306 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 56)
    }
}
impl SpecPred<u8> for Predicate7061727330754004306 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 56)
    }
}
pub struct Predicate17887014877089214959;
impl View for Predicate17887014877089214959 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate17887014877089214959 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 57)
    }
}
impl SpecPred<u8> for Predicate17887014877089214959 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 57)
    }
}
pub struct Predicate16310795002558583531;
impl View for Predicate16310795002558583531 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16310795002558583531 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 58)
    }
}
impl SpecPred<u8> for Predicate16310795002558583531 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 58)
    }
}
pub struct Predicate523614933806454484;
impl View for Predicate523614933806454484 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate523614933806454484 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 59)
    }
}
impl SpecPred<u8> for Predicate523614933806454484 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 59)
    }
}
pub struct Predicate16096414308557702779;
impl View for Predicate16096414308557702779 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16096414308557702779 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 60)
    }
}
impl SpecPred<u8> for Predicate16096414308557702779 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 60)
    }
}
pub struct Predicate16525731073934049962;
impl View for Predicate16525731073934049962 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate16525731073934049962 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 61)
    }
}
impl SpecPred<u8> for Predicate16525731073934049962 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 61)
    }
}
pub struct Predicate3507748065990518294;
impl View for Predicate3507748065990518294 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate3507748065990518294 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 62)
    }
}
impl SpecPred<u8> for Predicate3507748065990518294 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i == 62)
    }
}
pub struct Predicate7060793718683294274;
impl View for Predicate7060793718683294274 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred<u8> for Predicate7060793718683294274 {
    fn apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 63)
    }
}
impl SpecPred<u8> for Predicate7060793718683294274 {
    open spec fn spec_apply(&self, i: &u8) -> bool {
        let i = (*i);
        (i >= 63)
    }
}
type ChoiceWidth64CombinatorAlias1 = Choice<Refined<U8, Predicate3507748065990518294>, Refined<U8, Predicate7060793718683294274>>;
type ChoiceWidth64CombinatorAlias2 = Choice<Refined<U8, Predicate16525731073934049962>, ChoiceWidth64Combinator1>;
type ChoiceWidth64CombinatorAlias3 = Choice<Refined<U8, Predicate16096414308557702779>, ChoiceWidth64Combinator2>;
type ChoiceWidth64CombinatorAlias4 = Choice<Refined<U8, Predicate523614933806454484>, ChoiceWidth64Combinator3>;
type ChoiceWidth64CombinatorAlias5 = Choice<Refined<U8, Predicate16310795002558583531>, ChoiceWidth64Combinator4>;
type ChoiceWidth64CombinatorAlias6 = Choice<Refined<U8, Predicate17887014877089214959>, ChoiceWidth64Combinator5>;
type ChoiceWidth64CombinatorAlias7 = Choice<Refined<U8, Predicate7061727330754004306>, ChoiceWidth64Combinator6>;
type ChoiceWidth64CombinatorAlias8 = Choice<Refined<U8, Predicate2601603138918071977>, ChoiceWidth64Combinator7>;
type ChoiceWidth64CombinatorAlias9 = Choice<Refined<U8, Predicate16056970709915507831>, ChoiceWidth64Combinator8>;
type ChoiceWidth64CombinatorAlias10 = Choice<Refined<U8, Predicate4585217353424408452>, ChoiceWidth64Combinator9>;
type ChoiceWidth64CombinatorAlias11 = Choice<Refined<U8, Predicate13280578818964598340>, ChoiceWidth64Combinator10>;
type ChoiceWidth64CombinatorAlias12 = Choice<Refined<U8, Predicate2548737043788673441>, ChoiceWidth64Combinator11>;
type ChoiceWidth64CombinatorAlias13 = Choice<Refined<U8, Predicate7168319075050448275>, ChoiceWidth64Combinator12>;
type ChoiceWidth64CombinatorAlias14 = Choice<Refined<U8, Predicate5708320620815040592>, ChoiceWidth64Combinator13>;
type ChoiceWidth64CombinatorAlias15 = Choice<Refined<U8, Predicate13353397467677316255>, ChoiceWidth64Combinator14>;
type ChoiceWidth64CombinatorAlias16 = Choice<Refined<U8, Predicate8132005230405764957>, ChoiceWidth64Combinator15>;
type ChoiceWidth64CombinatorAlias17 = Choice<Refined<U8, Predicate14940225619408692556>, ChoiceWidth64Combinator16>;
type ChoiceWidth64CombinatorAlias18 = Choice<Refined<U8, Predicate2033264211231655736>, ChoiceWidth64Combinator17>;
type ChoiceWidth64CombinatorAlias19 = Choice<Refined<U8, Predicate1713587495682179202>, ChoiceWidth64Combinator18>;
type ChoiceWidth64CombinatorAlias20 = Choice<Refined<U8, Predicate11749655642528703983>, ChoiceWidth64Combinator19>;
type ChoiceWidth64CombinatorAlias21 = Choice<Refined<U8, Predicate12936565273184922672>, ChoiceWidth64Combinator20>;
type ChoiceWidth64CombinatorAlias22 = Choice<Refined<U8, Predicate1470905948243798090>, ChoiceWidth64Combinator21>;
type ChoiceWidth64CombinatorAlias23 = Choice<Refined<U8, Predicate15352586006205863074>, ChoiceWidth64Combinator22>;
type ChoiceWidth64CombinatorAlias24 = Choice<Refined<U8, Predicate17318782312207542369>, ChoiceWidth64Combinator23>;
type ChoiceWidth64CombinatorAlias25 = Choice<Refined<U8, Predicate528137220236479490>, ChoiceWidth64Combinator24>;
type ChoiceWidth64CombinatorAlias26 = Choice<Refined<U8, Predicate15502240502801463573>, ChoiceWidth64Combinator25>;
type ChoiceWidth64CombinatorAlias27 = Choice<Refined<U8, Predicate15872893073119229437>, ChoiceWidth64Combinator26>;
type ChoiceWidth64CombinatorAlias28 = Choice<Refined<U8, Predicate8880797979392678721>, ChoiceWidth64Combinator27>;
type ChoiceWidth64CombinatorAlias29 = Choice<Refined<U8, Predicate14945695403078815867>, ChoiceWidth64Combinator28>;
type ChoiceWidth64CombinatorAlias30 = Choice<Refined<U8, Predicate364580195256496202>, ChoiceWidth64Combinator29>;
type ChoiceWidth64CombinatorAlias31 = Choice<Refined<U8, Predicate4262279460611959614>, ChoiceWidth64Combinator30>;
type ChoiceWidth64CombinatorAlias32 = Choice<Refined<U8, Predicate4772354365252939758>, ChoiceWidth64Combinator31>;
type ChoiceWidth64CombinatorAlias33 = Choice<Refined<U8, Predicate1385328176252848081>, ChoiceWidth64Combinator32>;
type ChoiceWidth64CombinatorAlias34 = Choice<Refined<U8, Predicate17516429898706644594>, ChoiceWidth64Combinator33>;
type ChoiceWidth64CombinatorAlias35 = Choice<Refined<U8, Predicate11809820865766219170>, ChoiceWidth64Combinator34>;
type ChoiceWidth64CombinatorAlias36 = Choice<Refined<U8, Predicate14700689986523383325>, ChoiceWidth64Combinator35>;
type ChoiceWidth64CombinatorAlias37 = Choice<Refined<U8, Predicate3285282901849553415>, ChoiceWidth64Combinator36>;
type ChoiceWidth64CombinatorAlias38 = Choice<Refined<U8, Predicate2213030098669005785>, ChoiceWidth64Combinator37>;
type ChoiceWidth64CombinatorAlias39 = Choice<Refined<U8, Predicate14174989844364464752>, ChoiceWidth64Combinator38>;
type ChoiceWidth64CombinatorAlias40 = Choice<Refined<U8, Predicate1304083776951938903>, ChoiceWidth64Combinator39>;
type ChoiceWidth64CombinatorAlias41 = Choice<Refined<U8, Predicate4869308575099852777>, ChoiceWidth64Combinator40>;
type ChoiceWidth64CombinatorAlias42 = Choice<Refined<U8, Predicate16333054977080421469>, ChoiceWidth64Combinator41>;
type ChoiceWidth64CombinatorAlias43 = Choice<Refined<U8, Predicate1445610904132711222>, ChoiceWidth64Combinator42>;
type ChoiceWidth64CombinatorAlias44 = Choice<Refined<U8, Predicate4072810196653762843>, ChoiceWidth64Combinator43>;
type ChoiceWidth64CombinatorAlias45 = Choice<Refined<U8, Predicate14707428835277590315>, ChoiceWidth64Combinator44>;
type ChoiceWidth64CombinatorAlias46 = Choice<Refined<U8, Predicate8251779752648547376>, ChoiceWidth64Combinator45>;
type ChoiceWidth64CombinatorAlias47 = Choice<Refined<U8, Predicate15291213704223769698>, ChoiceWidth64Combinator46>;
type ChoiceWidth64CombinatorAlias48 = Choice<Refined<U8, Predicate6037550869214390311>, ChoiceWidth64Combinator47>;
type ChoiceWidth64CombinatorAlias49 = Choice<Refined<U8, Predicate3258795957419340618>, ChoiceWidth64Combinator48>;
type ChoiceWidth64CombinatorAlias50 = Choice<Refined<U8, Predicate4672853435886844331>, ChoiceWidth64Combinator49>;
type ChoiceWidth64CombinatorAlias51 = Choice<Refined<U8, Predicate9731316588179370935>, ChoiceWidth64Combinator50>;
type ChoiceWidth64CombinatorAlias52 = Choice<Refined<U8, Predicate13393337139612027911>, ChoiceWidth64Combinator51>;
type ChoiceWidth64CombinatorAlias53 = Choice<Refined<U8, Predicate1670200719151657759>, ChoiceWidth64Combinator52>;
type ChoiceWidth64CombinatorAlias54 = Choice<Refined<U8, Predicate2286677770329837199>, ChoiceWidth64Combinator53>;
type ChoiceWidth64CombinatorAlias55 = Choice<Refined<U8, Predicate11758281649694429187>, ChoiceWidth64Combinator54>;
type ChoiceWidth64CombinatorAlias56 = Choice<Refined<U8, Predicate9770172291787044034>, ChoiceWidth64Combinator55>;
type ChoiceWidth64CombinatorAlias57 = Choice<Refined<U8, Predicate4214186895105241400>, ChoiceWidth64Combinator56>;
type ChoiceWidth64CombinatorAlias58 = Choice<Refined<U8, Predicate9186325526105272194>, ChoiceWidth64Combinator57>;
type ChoiceWidth64CombinatorAlias59 = Choice<Refined<U8, Predicate4589101901519479956>, ChoiceWidth64Combinator58>;
type ChoiceWidth64CombinatorAlias60 = Choice<Refined<U8, Predicate2671570727481267254>, ChoiceWidth64Combinator59>;
type ChoiceWidth64CombinatorAlias61 = Choice<Refined<U8, Predicate6170912057263668010>, ChoiceWidth64Combinator60>;
type ChoiceWidth64CombinatorAlias62 = Choice<Refined<U8, Predicate13385608959756530935>, ChoiceWidth64Combinator61>;
type ChoiceWidth64CombinatorAlias63 = Choice<Refined<U8, Predicate2576612288366319398>, ChoiceWidth64Combinator62>;
pub struct ChoiceWidth64Combinator1(pub ChoiceWidth64CombinatorAlias1);
impl View for ChoiceWidth64Combinator1 {
    type V = SpecChoiceWidth64CombinatorAlias1;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator1, ChoiceWidth64CombinatorAlias1);

pub struct ChoiceWidth64Combinator2(pub ChoiceWidth64CombinatorAlias2);
impl View for ChoiceWidth64Combinator2 {
    type V = SpecChoiceWidth64CombinatorAlias2;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator2, ChoiceWidth64CombinatorAlias2);

pub struct ChoiceWidth64Combinator3(pub ChoiceWidth64CombinatorAlias3);
impl View for ChoiceWidth64Combinator3 {
    type V = SpecChoiceWidth64CombinatorAlias3;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator3, ChoiceWidth64CombinatorAlias3);

pub struct ChoiceWidth64Combinator4(pub ChoiceWidth64CombinatorAlias4);
impl View for ChoiceWidth64Combinator4 {
    type V = SpecChoiceWidth64CombinatorAlias4;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator4, ChoiceWidth64CombinatorAlias4);

pub struct ChoiceWidth64Combinator5(pub ChoiceWidth64CombinatorAlias5);
impl View for ChoiceWidth64Combinator5 {
    type V = SpecChoiceWidth64CombinatorAlias5;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator5, ChoiceWidth64CombinatorAlias5);

pub struct ChoiceWidth64Combinator6(pub ChoiceWidth64CombinatorAlias6);
impl View for ChoiceWidth64Combinator6 {
    type V = SpecChoiceWidth64CombinatorAlias6;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator6, ChoiceWidth64CombinatorAlias6);

pub struct ChoiceWidth64Combinator7(pub ChoiceWidth64CombinatorAlias7);
impl View for ChoiceWidth64Combinator7 {
    type V = SpecChoiceWidth64CombinatorAlias7;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator7, ChoiceWidth64CombinatorAlias7);

pub struct ChoiceWidth64Combinator8(pub ChoiceWidth64CombinatorAlias8);
impl View for ChoiceWidth64Combinator8 {
    type V = SpecChoiceWidth64CombinatorAlias8;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator8, ChoiceWidth64CombinatorAlias8);

pub struct ChoiceWidth64Combinator9(pub ChoiceWidth64CombinatorAlias9);
impl View for ChoiceWidth64Combinator9 {
    type V = SpecChoiceWidth64CombinatorAlias9;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator9, ChoiceWidth64CombinatorAlias9);

pub struct ChoiceWidth64Combinator10(pub ChoiceWidth64CombinatorAlias10);
impl View for ChoiceWidth64Combinator10 {
    type V = SpecChoiceWidth64CombinatorAlias10;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator10, ChoiceWidth64CombinatorAlias10);

pub struct ChoiceWidth64Combinator11(pub ChoiceWidth64CombinatorAlias11);
impl View for ChoiceWidth64Combinator11 {
    type V = SpecChoiceWidth64CombinatorAlias11;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator11, ChoiceWidth64CombinatorAlias11);

pub struct ChoiceWidth64Combinator12(pub ChoiceWidth64CombinatorAlias12);
impl View for ChoiceWidth64Combinator12 {
    type V = SpecChoiceWidth64CombinatorAlias12;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator12, ChoiceWidth64CombinatorAlias12);

pub struct ChoiceWidth64Combinator13(pub ChoiceWidth64CombinatorAlias13);
impl View for ChoiceWidth64Combinator13 {
    type V = SpecChoiceWidth64CombinatorAlias13;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator13, ChoiceWidth64CombinatorAlias13);

pub struct ChoiceWidth64Combinator14(pub ChoiceWidth64CombinatorAlias14);
impl View for ChoiceWidth64Combinator14 {
    type V = SpecChoiceWidth64CombinatorAlias14;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator14, ChoiceWidth64CombinatorAlias14);

pub struct ChoiceWidth64Combinator15(pub ChoiceWidth64CombinatorAlias15);
impl View for ChoiceWidth64Combinator15 {
    type V = SpecChoiceWidth64CombinatorAlias15;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator15, ChoiceWidth64CombinatorAlias15);

pub struct ChoiceWidth64Combinator16(pub ChoiceWidth64CombinatorAlias16);
impl View for ChoiceWidth64Combinator16 {
    type V = SpecChoiceWidth64CombinatorAlias16;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator16, ChoiceWidth64CombinatorAlias16);

pub struct ChoiceWidth64Combinator17(pub ChoiceWidth64CombinatorAlias17);
impl View for ChoiceWidth64Combinator17 {
    type V = SpecChoiceWidth64CombinatorAlias17;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator17, ChoiceWidth64CombinatorAlias17);

pub struct ChoiceWidth64Combinator18(pub ChoiceWidth64CombinatorAlias18);
impl View for ChoiceWidth64Combinator18 {
    type V = SpecChoiceWidth64CombinatorAlias18;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator18, ChoiceWidth64CombinatorAlias18);

pub struct ChoiceWidth64Combinator19(pub ChoiceWidth64CombinatorAlias19);
impl View for ChoiceWidth64Combinator19 {
    type V = SpecChoiceWidth64CombinatorAlias19;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator19, ChoiceWidth64CombinatorAlias19);

pub struct ChoiceWidth64Combinator20(pub ChoiceWidth64CombinatorAlias20);
impl View for ChoiceWidth64Combinator20 {
    type V = SpecChoiceWidth64CombinatorAlias20;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator20, ChoiceWidth64CombinatorAlias20);

pub struct ChoiceWidth64Combinator21(pub ChoiceWidth64CombinatorAlias21);
impl View for ChoiceWidth64Combinator21 {
    type V = SpecChoiceWidth64CombinatorAlias21;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator21, ChoiceWidth64CombinatorAlias21);

pub struct ChoiceWidth64Combinator22(pub ChoiceWidth64CombinatorAlias22);
impl View for ChoiceWidth64Combinator22 {
    type V = SpecChoiceWidth64CombinatorAlias22;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator22, ChoiceWidth64CombinatorAlias22);

pub struct ChoiceWidth64Combinator23(pub ChoiceWidth64CombinatorAlias23);
impl View for ChoiceWidth64Combinator23 {
    type V = SpecChoiceWidth64CombinatorAlias23;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator23, ChoiceWidth64CombinatorAlias23);

pub struct ChoiceWidth64Combinator24(pub ChoiceWidth64CombinatorAlias24);
impl View for ChoiceWidth64Combinator24 {
    type V = SpecChoiceWidth64CombinatorAlias24;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator24, ChoiceWidth64CombinatorAlias24);

pub struct ChoiceWidth64Combinator25(pub ChoiceWidth64CombinatorAlias25);
impl View for ChoiceWidth64Combinator25 {
    type V = SpecChoiceWidth64CombinatorAlias25;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator25, ChoiceWidth64CombinatorAlias25);

pub struct ChoiceWidth64Combinator26(pub ChoiceWidth64CombinatorAlias26);
impl View for ChoiceWidth64Combinator26 {
    type V = SpecChoiceWidth64CombinatorAlias26;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator26, ChoiceWidth64CombinatorAlias26);

pub struct ChoiceWidth64Combinator27(pub ChoiceWidth64CombinatorAlias27);
impl View for ChoiceWidth64Combinator27 {
    type V = SpecChoiceWidth64CombinatorAlias27;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator27, ChoiceWidth64CombinatorAlias27);

pub struct ChoiceWidth64Combinator28(pub ChoiceWidth64CombinatorAlias28);
impl View for ChoiceWidth64Combinator28 {
    type V = SpecChoiceWidth64CombinatorAlias28;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator28, ChoiceWidth64CombinatorAlias28);

pub struct ChoiceWidth64Combinator29(pub ChoiceWidth64CombinatorAlias29);
impl View for ChoiceWidth64Combinator29 {
    type V = SpecChoiceWidth64CombinatorAlias29;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator29, ChoiceWidth64CombinatorAlias29);

pub struct ChoiceWidth64Combinator30(pub ChoiceWidth64CombinatorAlias30);
impl View for ChoiceWidth64Combinator30 {
    type V = SpecChoiceWidth64CombinatorAlias30;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator30, ChoiceWidth64CombinatorAlias30);

pub struct ChoiceWidth64Combinator31(pub ChoiceWidth64CombinatorAlias31);
impl View for ChoiceWidth64Combinator31 {
    type V = SpecChoiceWidth64CombinatorAlias31;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator31, ChoiceWidth64CombinatorAlias31);

pub struct ChoiceWidth64Combinator32(pub ChoiceWidth64CombinatorAlias32);
impl View for ChoiceWidth64Combinator32 {
    type V = SpecChoiceWidth64CombinatorAlias32;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator32, ChoiceWidth64CombinatorAlias32);

pub struct ChoiceWidth64Combinator33(pub ChoiceWidth64CombinatorAlias33);
impl View for ChoiceWidth64Combinator33 {
    type V = SpecChoiceWidth64CombinatorAlias33;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator33, ChoiceWidth64CombinatorAlias33);

pub struct ChoiceWidth64Combinator34(pub ChoiceWidth64CombinatorAlias34);
impl View for ChoiceWidth64Combinator34 {
    type V = SpecChoiceWidth64CombinatorAlias34;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator34, ChoiceWidth64CombinatorAlias34);

pub struct ChoiceWidth64Combinator35(pub ChoiceWidth64CombinatorAlias35);
impl View for ChoiceWidth64Combinator35 {
    type V = SpecChoiceWidth64CombinatorAlias35;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator35, ChoiceWidth64CombinatorAlias35);

pub struct ChoiceWidth64Combinator36(pub ChoiceWidth64CombinatorAlias36);
impl View for ChoiceWidth64Combinator36 {
    type V = SpecChoiceWidth64CombinatorAlias36;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator36, ChoiceWidth64CombinatorAlias36);

pub struct ChoiceWidth64Combinator37(pub ChoiceWidth64CombinatorAlias37);
impl View for ChoiceWidth64Combinator37 {
    type V = SpecChoiceWidth64CombinatorAlias37;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator37, ChoiceWidth64CombinatorAlias37);

pub struct ChoiceWidth64Combinator38(pub ChoiceWidth64CombinatorAlias38);
impl View for ChoiceWidth64Combinator38 {
    type V = SpecChoiceWidth64CombinatorAlias38;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator38, ChoiceWidth64CombinatorAlias38);

pub struct ChoiceWidth64Combinator39(pub ChoiceWidth64CombinatorAlias39);
impl View for ChoiceWidth64Combinator39 {
    type V = SpecChoiceWidth64CombinatorAlias39;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator39, ChoiceWidth64CombinatorAlias39);

pub struct ChoiceWidth64Combinator40(pub ChoiceWidth64CombinatorAlias40);
impl View for ChoiceWidth64Combinator40 {
    type V = SpecChoiceWidth64CombinatorAlias40;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator40, ChoiceWidth64CombinatorAlias40);

pub struct ChoiceWidth64Combinator41(pub ChoiceWidth64CombinatorAlias41);
impl View for ChoiceWidth64Combinator41 {
    type V = SpecChoiceWidth64CombinatorAlias41;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator41, ChoiceWidth64CombinatorAlias41);

pub struct ChoiceWidth64Combinator42(pub ChoiceWidth64CombinatorAlias42);
impl View for ChoiceWidth64Combinator42 {
    type V = SpecChoiceWidth64CombinatorAlias42;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator42, ChoiceWidth64CombinatorAlias42);

pub struct ChoiceWidth64Combinator43(pub ChoiceWidth64CombinatorAlias43);
impl View for ChoiceWidth64Combinator43 {
    type V = SpecChoiceWidth64CombinatorAlias43;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator43, ChoiceWidth64CombinatorAlias43);

pub struct ChoiceWidth64Combinator44(pub ChoiceWidth64CombinatorAlias44);
impl View for ChoiceWidth64Combinator44 {
    type V = SpecChoiceWidth64CombinatorAlias44;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator44, ChoiceWidth64CombinatorAlias44);

pub struct ChoiceWidth64Combinator45(pub ChoiceWidth64CombinatorAlias45);
impl View for ChoiceWidth64Combinator45 {
    type V = SpecChoiceWidth64CombinatorAlias45;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator45, ChoiceWidth64CombinatorAlias45);

pub struct ChoiceWidth64Combinator46(pub ChoiceWidth64CombinatorAlias46);
impl View for ChoiceWidth64Combinator46 {
    type V = SpecChoiceWidth64CombinatorAlias46;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator46, ChoiceWidth64CombinatorAlias46);

pub struct ChoiceWidth64Combinator47(pub ChoiceWidth64CombinatorAlias47);
impl View for ChoiceWidth64Combinator47 {
    type V = SpecChoiceWidth64CombinatorAlias47;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator47, ChoiceWidth64CombinatorAlias47);

pub struct ChoiceWidth64Combinator48(pub ChoiceWidth64CombinatorAlias48);
impl View for ChoiceWidth64Combinator48 {
    type V = SpecChoiceWidth64CombinatorAlias48;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator48, ChoiceWidth64CombinatorAlias48);

pub struct ChoiceWidth64Combinator49(pub ChoiceWidth64CombinatorAlias49);
impl View for ChoiceWidth64Combinator49 {
    type V = SpecChoiceWidth64CombinatorAlias49;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator49, ChoiceWidth64CombinatorAlias49);

pub struct ChoiceWidth64Combinator50(pub ChoiceWidth64CombinatorAlias50);
impl View for ChoiceWidth64Combinator50 {
    type V = SpecChoiceWidth64CombinatorAlias50;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator50, ChoiceWidth64CombinatorAlias50);

pub struct ChoiceWidth64Combinator51(pub ChoiceWidth64CombinatorAlias51);
impl View for ChoiceWidth64Combinator51 {
    type V = SpecChoiceWidth64CombinatorAlias51;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator51, ChoiceWidth64CombinatorAlias51);

pub struct ChoiceWidth64Combinator52(pub ChoiceWidth64CombinatorAlias52);
impl View for ChoiceWidth64Combinator52 {
    type V = SpecChoiceWidth64CombinatorAlias52;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator52, ChoiceWidth64CombinatorAlias52);

pub struct ChoiceWidth64Combinator53(pub ChoiceWidth64CombinatorAlias53);
impl View for ChoiceWidth64Combinator53 {
    type V = SpecChoiceWidth64CombinatorAlias53;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator53, ChoiceWidth64CombinatorAlias53);

pub struct ChoiceWidth64Combinator54(pub ChoiceWidth64CombinatorAlias54);
impl View for ChoiceWidth64Combinator54 {
    type V = SpecChoiceWidth64CombinatorAlias54;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator54, ChoiceWidth64CombinatorAlias54);

pub struct ChoiceWidth64Combinator55(pub ChoiceWidth64CombinatorAlias55);
impl View for ChoiceWidth64Combinator55 {
    type V = SpecChoiceWidth64CombinatorAlias55;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator55, ChoiceWidth64CombinatorAlias55);

pub struct ChoiceWidth64Combinator56(pub ChoiceWidth64CombinatorAlias56);
impl View for ChoiceWidth64Combinator56 {
    type V = SpecChoiceWidth64CombinatorAlias56;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator56, ChoiceWidth64CombinatorAlias56);

pub struct ChoiceWidth64Combinator57(pub ChoiceWidth64CombinatorAlias57);
impl View for ChoiceWidth64Combinator57 {
    type V = SpecChoiceWidth64CombinatorAlias57;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator57, ChoiceWidth64CombinatorAlias57);

pub struct ChoiceWidth64Combinator58(pub ChoiceWidth64CombinatorAlias58);
impl View for ChoiceWidth64Combinator58 {
    type V = SpecChoiceWidth64CombinatorAlias58;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator58, ChoiceWidth64CombinatorAlias58);

pub struct ChoiceWidth64Combinator59(pub ChoiceWidth64CombinatorAlias59);
impl View for ChoiceWidth64Combinator59 {
    type V = SpecChoiceWidth64CombinatorAlias59;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator59, ChoiceWidth64CombinatorAlias59);

pub struct ChoiceWidth64Combinator60(pub ChoiceWidth64CombinatorAlias60);
impl View for ChoiceWidth64Combinator60 {
    type V = SpecChoiceWidth64CombinatorAlias60;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator60, ChoiceWidth64CombinatorAlias60);

pub struct ChoiceWidth64Combinator61(pub ChoiceWidth64CombinatorAlias61);
impl View for ChoiceWidth64Combinator61 {
    type V = SpecChoiceWidth64CombinatorAlias61;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator61, ChoiceWidth64CombinatorAlias61);

pub struct ChoiceWidth64Combinator62(pub ChoiceWidth64CombinatorAlias62);
impl View for ChoiceWidth64Combinator62 {
    type V = SpecChoiceWidth64CombinatorAlias62;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator62, ChoiceWidth64CombinatorAlias62);

pub struct ChoiceWidth64Combinator63(pub ChoiceWidth64CombinatorAlias63);
impl View for ChoiceWidth64Combinator63 {
    type V = SpecChoiceWidth64CombinatorAlias63;
    open spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(ChoiceWidth64Combinator63, ChoiceWidth64CombinatorAlias63);

pub struct ChoiceWidth64Combinator(pub ChoiceWidth64CombinatorAlias);

impl View for ChoiceWidth64Combinator {
    type V = SpecChoiceWidth64Combinator;
    open spec fn view(&self) -> Self::V { SpecChoiceWidth64Combinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChoiceWidth64Combinator {
    type Type = ChoiceWidth64;
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
pub type ChoiceWidth64CombinatorAlias = Mapped<ChoiceWidth64Combinator63, ChoiceWidth64Mapper>;


pub open spec fn spec_choice_width64() -> SpecChoiceWidth64Combinator {
    SpecChoiceWidth64Combinator(Mapped { inner: Choice(Refined { inner: U8, predicate: Predicate2576612288366319398 }, Choice(Refined { inner: U8, predicate: Predicate13385608959756530935 }, Choice(Refined { inner: U8, predicate: Predicate6170912057263668010 }, Choice(Refined { inner: U8, predicate: Predicate2671570727481267254 }, Choice(Refined { inner: U8, predicate: Predicate4589101901519479956 }, Choice(Refined { inner: U8, predicate: Predicate9186325526105272194 }, Choice(Refined { inner: U8, predicate: Predicate4214186895105241400 }, Choice(Refined { inner: U8, predicate: Predicate9770172291787044034 }, Choice(Refined { inner: U8, predicate: Predicate11758281649694429187 }, Choice(Refined { inner: U8, predicate: Predicate2286677770329837199 }, Choice(Refined { inner: U8, predicate: Predicate1670200719151657759 }, Choice(Refined { inner: U8, predicate: Predicate13393337139612027911 }, Choice(Refined { inner: U8, predicate: Predicate9731316588179370935 }, Choice(Refined { inner: U8, predicate: Predicate4672853435886844331 }, Choice(Refined { inner: U8, predicate: Predicate3258795957419340618 }, Choice(Refined { inner: U8, predicate: Predicate6037550869214390311 }, Choice(Refined { inner: U8, predicate: Predicate15291213704223769698 }, Choice(Refined { inner: U8, predicate: Predicate8251779752648547376 }, Choice(Refined { inner: U8, predicate: Predicate14707428835277590315 }, Choice(Refined { inner: U8, predicate: Predicate4072810196653762843 }, Choice(Refined { inner: U8, predicate: Predicate1445610904132711222 }, Choice(Refined { inner: U8, predicate: Predicate16333054977080421469 }, Choice(Refined { inner: U8, predicate: Predicate4869308575099852777 }, Choice(Refined { inner: U8, predicate: Predicate1304083776951938903 }, Choice(Refined { inner: U8, predicate: Predicate14174989844364464752 }, Choice(Refined { inner: U8, predicate: Predicate2213030098669005785 }, Choice(Refined { inner: U8, predicate: Predicate3285282901849553415 }, Choice(Refined { inner: U8, predicate: Predicate14700689986523383325 }, Choice(Refined { inner: U8, predicate: Predicate11809820865766219170 }, Choice(Refined { inner: U8, predicate: Predicate17516429898706644594 }, Choice(Refined { inner: U8, predicate: Predicate1385328176252848081 }, Choice(Refined { inner: U8, predicate: Predicate4772354365252939758 }, Choice(Refined { inner: U8, predicate: Predicate4262279460611959614 }, Choice(Refined { inner: U8, predicate: Predicate364580195256496202 }, Choice(Refined { inner: U8, predicate: Predicate14945695403078815867 }, Choice(Refined { inner: U8, predicate: Predicate8880797979392678721 }, Choice(Refined { inner: U8, predicate: Predicate15872893073119229437 }, Choice(Refined { inner: U8, predicate: Predicate15502240502801463573 }, Choice(Refined { inner: U8, predicate: Predicate528137220236479490 }, Choice(Refined { inner: U8, predicate: Predicate17318782312207542369 }, Choice(Refined { inner: U8, predicate: Predicate15352586006205863074 }, Choice(Refined { inner: U8, predicate: Predicate1470905948243798090 }, Choice(Refined { inner: U8, predicate: Predicate12936565273184922672 }, Choice(Refined { inner: U8, predicate: Predicate11749655642528703983 }, Choice(Refined { inner: U8, predicate: Predicate1713587495682179202 }, Choice(Refined { inner: U8, predicate: Predicate2033264211231655736 }, Choice(Refined { inner: U8, predicate: Predicate14940225619408692556 }, Choice(Refined { inner: U8, predicate: Predicate8132005230405764957 }, Choice(Refined { inner: U8, predicate: Predicate13353397467677316255 }, Choice(Refined { inner: U8, predicate: Predicate5708320620815040592 }, Choice(Refined { inner: U8, predicate: Predicate7168319075050448275 }, Choice(Refined { inner: U8, predicate: Predicate2548737043788673441 }, Choice(Refined { inner: U8, predicate: Predicate13280578818964598340 }, Choice(Refined { inner: U8, predicate: Predicate4585217353424408452 }, Choice(Refined { inner: U8, predicate: Predicate16056970709915507831 }, Choice(Refined { inner: U8, predicate: Predicate2601603138918071977 }, Choice(Refined { inner: U8, predicate: Predicate7061727330754004306 }, Choice(Refined { inner: U8, predicate: Predicate17887014877089214959 }, Choice(Refined { inner: U8, predicate: Predicate16310795002558583531 }, Choice(Refined { inner: U8, predicate: Predicate523614933806454484 }, Choice(Refined { inner: U8, predicate: Predicate16096414308557702779 }, Choice(Refined { inner: U8, predicate: Predicate16525731073934049962 }, Choice(Refined { inner: U8, predicate: Predicate3507748065990518294 }, Refined { inner: U8, predicate: Predicate7060793718683294274 }))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: ChoiceWidth64Mapper })
}

                
pub fn choice_width64<'a>() -> (o: ChoiceWidth64Combinator)
    ensures o@ == spec_choice_width64(),
            o@.requires(),
            <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&o),
{
    let combinator = ChoiceWidth64Combinator(Mapped { inner: ChoiceWidth64Combinator63(Choice::new(Refined { inner: U8, predicate: Predicate2576612288366319398 }, ChoiceWidth64Combinator62(Choice::new(Refined { inner: U8, predicate: Predicate13385608959756530935 }, ChoiceWidth64Combinator61(Choice::new(Refined { inner: U8, predicate: Predicate6170912057263668010 }, ChoiceWidth64Combinator60(Choice::new(Refined { inner: U8, predicate: Predicate2671570727481267254 }, ChoiceWidth64Combinator59(Choice::new(Refined { inner: U8, predicate: Predicate4589101901519479956 }, ChoiceWidth64Combinator58(Choice::new(Refined { inner: U8, predicate: Predicate9186325526105272194 }, ChoiceWidth64Combinator57(Choice::new(Refined { inner: U8, predicate: Predicate4214186895105241400 }, ChoiceWidth64Combinator56(Choice::new(Refined { inner: U8, predicate: Predicate9770172291787044034 }, ChoiceWidth64Combinator55(Choice::new(Refined { inner: U8, predicate: Predicate11758281649694429187 }, ChoiceWidth64Combinator54(Choice::new(Refined { inner: U8, predicate: Predicate2286677770329837199 }, ChoiceWidth64Combinator53(Choice::new(Refined { inner: U8, predicate: Predicate1670200719151657759 }, ChoiceWidth64Combinator52(Choice::new(Refined { inner: U8, predicate: Predicate13393337139612027911 }, ChoiceWidth64Combinator51(Choice::new(Refined { inner: U8, predicate: Predicate9731316588179370935 }, ChoiceWidth64Combinator50(Choice::new(Refined { inner: U8, predicate: Predicate4672853435886844331 }, ChoiceWidth64Combinator49(Choice::new(Refined { inner: U8, predicate: Predicate3258795957419340618 }, ChoiceWidth64Combinator48(Choice::new(Refined { inner: U8, predicate: Predicate6037550869214390311 }, ChoiceWidth64Combinator47(Choice::new(Refined { inner: U8, predicate: Predicate15291213704223769698 }, ChoiceWidth64Combinator46(Choice::new(Refined { inner: U8, predicate: Predicate8251779752648547376 }, ChoiceWidth64Combinator45(Choice::new(Refined { inner: U8, predicate: Predicate14707428835277590315 }, ChoiceWidth64Combinator44(Choice::new(Refined { inner: U8, predicate: Predicate4072810196653762843 }, ChoiceWidth64Combinator43(Choice::new(Refined { inner: U8, predicate: Predicate1445610904132711222 }, ChoiceWidth64Combinator42(Choice::new(Refined { inner: U8, predicate: Predicate16333054977080421469 }, ChoiceWidth64Combinator41(Choice::new(Refined { inner: U8, predicate: Predicate4869308575099852777 }, ChoiceWidth64Combinator40(Choice::new(Refined { inner: U8, predicate: Predicate1304083776951938903 }, ChoiceWidth64Combinator39(Choice::new(Refined { inner: U8, predicate: Predicate14174989844364464752 }, ChoiceWidth64Combinator38(Choice::new(Refined { inner: U8, predicate: Predicate2213030098669005785 }, ChoiceWidth64Combinator37(Choice::new(Refined { inner: U8, predicate: Predicate3285282901849553415 }, ChoiceWidth64Combinator36(Choice::new(Refined { inner: U8, predicate: Predicate14700689986523383325 }, ChoiceWidth64Combinator35(Choice::new(Refined { inner: U8, predicate: Predicate11809820865766219170 }, ChoiceWidth64Combinator34(Choice::new(Refined { inner: U8, predicate: Predicate17516429898706644594 }, ChoiceWidth64Combinator33(Choice::new(Refined { inner: U8, predicate: Predicate1385328176252848081 }, ChoiceWidth64Combinator32(Choice::new(Refined { inner: U8, predicate: Predicate4772354365252939758 }, ChoiceWidth64Combinator31(Choice::new(Refined { inner: U8, predicate: Predicate4262279460611959614 }, ChoiceWidth64Combinator30(Choice::new(Refined { inner: U8, predicate: Predicate364580195256496202 }, ChoiceWidth64Combinator29(Choice::new(Refined { inner: U8, predicate: Predicate14945695403078815867 }, ChoiceWidth64Combinator28(Choice::new(Refined { inner: U8, predicate: Predicate8880797979392678721 }, ChoiceWidth64Combinator27(Choice::new(Refined { inner: U8, predicate: Predicate15872893073119229437 }, ChoiceWidth64Combinator26(Choice::new(Refined { inner: U8, predicate: Predicate15502240502801463573 }, ChoiceWidth64Combinator25(Choice::new(Refined { inner: U8, predicate: Predicate528137220236479490 }, ChoiceWidth64Combinator24(Choice::new(Refined { inner: U8, predicate: Predicate17318782312207542369 }, ChoiceWidth64Combinator23(Choice::new(Refined { inner: U8, predicate: Predicate15352586006205863074 }, ChoiceWidth64Combinator22(Choice::new(Refined { inner: U8, predicate: Predicate1470905948243798090 }, ChoiceWidth64Combinator21(Choice::new(Refined { inner: U8, predicate: Predicate12936565273184922672 }, ChoiceWidth64Combinator20(Choice::new(Refined { inner: U8, predicate: Predicate11749655642528703983 }, ChoiceWidth64Combinator19(Choice::new(Refined { inner: U8, predicate: Predicate1713587495682179202 }, ChoiceWidth64Combinator18(Choice::new(Refined { inner: U8, predicate: Predicate2033264211231655736 }, ChoiceWidth64Combinator17(Choice::new(Refined { inner: U8, predicate: Predicate14940225619408692556 }, ChoiceWidth64Combinator16(Choice::new(Refined { inner: U8, predicate: Predicate8132005230405764957 }, ChoiceWidth64Combinator15(Choice::new(Refined { inner: U8, predicate: Predicate13353397467677316255 }, ChoiceWidth64Combinator14(Choice::new(Refined { inner: U8, predicate: Predicate5708320620815040592 }, ChoiceWidth64Combinator13(Choice::new(Refined { inner: U8, predicate: Predicate7168319075050448275 }, ChoiceWidth64Combinator12(Choice::new(Refined { inner: U8, predicate: Predicate2548737043788673441 }, ChoiceWidth64Combinator11(Choice::new(Refined { inner: U8, predicate: Predicate13280578818964598340 }, ChoiceWidth64Combinator10(Choice::new(Refined { inner: U8, predicate: Predicate4585217353424408452 }, ChoiceWidth64Combinator9(Choice::new(Refined { inner: U8, predicate: Predicate16056970709915507831 }, ChoiceWidth64Combinator8(Choice::new(Refined { inner: U8, predicate: Predicate2601603138918071977 }, ChoiceWidth64Combinator7(Choice::new(Refined { inner: U8, predicate: Predicate7061727330754004306 }, ChoiceWidth64Combinator6(Choice::new(Refined { inner: U8, predicate: Predicate17887014877089214959 }, ChoiceWidth64Combinator5(Choice::new(Refined { inner: U8, predicate: Predicate16310795002558583531 }, ChoiceWidth64Combinator4(Choice::new(Refined { inner: U8, predicate: Predicate523614933806454484 }, ChoiceWidth64Combinator3(Choice::new(Refined { inner: U8, predicate: Predicate16096414308557702779 }, ChoiceWidth64Combinator2(Choice::new(Refined { inner: U8, predicate: Predicate16525731073934049962 }, ChoiceWidth64Combinator1(Choice::new(Refined { inner: U8, predicate: Predicate3507748065990518294 }, Refined { inner: U8, predicate: Predicate7060793718683294274 })))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: ChoiceWidth64Mapper });
    // assert({
    //     &&& combinator@ == spec_choice_width64()
    //     &&& combinator@.requires()
    //     &&& <_ as Combinator<'a, &'a [u8], Vec<u8>>>::ex_requires(&combinator)
    // });
    combinator
}

pub fn parse_choice_width64<'a>(input: &'a [u8]) -> (res: PResult<<ChoiceWidth64Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::Type, ParseError>)
    requires
        input.len() <= usize::MAX,
    ensures
        res matches Ok((n, v)) ==> spec_choice_width64().spec_parse(input@) == Some((n as int, v@)),
        spec_choice_width64().spec_parse(input@) matches Some((n, v))
            ==> res matches Ok((m, u)) && m == n && v == u@,
        res is Err ==> spec_choice_width64().spec_parse(input@) is None,
        spec_choice_width64().spec_parse(input@) is None ==> res is Err,
{
    let combinator = choice_width64();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::parse(&combinator, input)
}

pub fn serialize_choice_width64<'a>(v: <ChoiceWidth64Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType, data: &mut Vec<u8>, pos: usize) -> (o: SResult<usize, SerializeError>)
    requires
        pos <= old(data)@.len() <= usize::MAX,
        spec_choice_width64().wf(v@),
    ensures
        o matches Ok(n) ==> {
            &&& final(data)@.len() == old(data)@.len()
            &&& pos <= usize::MAX - n && pos + n <= final(data)@.len()
            &&& n == spec_choice_width64().spec_serialize(v@).len()
            &&& final(data)@ == seq_splice(old(data)@, pos, spec_choice_width64().spec_serialize(v@))
        },
{
    let combinator = choice_width64();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::serialize(&combinator, v, &mut *data, pos)
}

pub fn choice_width64_len<'a>(v: <ChoiceWidth64Combinator as Combinator<'a, &'a [u8], Vec<u8>>>::SType) -> (serialize_len: usize)
    requires
        spec_choice_width64().wf(v@),
        spec_choice_width64().spec_serialize(v@).len() <= usize::MAX,
    ensures
        serialize_len == spec_choice_width64().spec_serialize(v@).len(),
{
    let combinator = choice_width64();
    <_ as Combinator<'a, &'a [u8], Vec<u8>>>::length(&combinator, v)
}

                

}
