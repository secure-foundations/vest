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

pub enum SpecChooseFmt {
    Variant0(u8),
    Variant1(u16),
    Variant2(u64),
}

pub type SpecChooseFmtInner = Either<u8, Either<u16, u64>>;

impl SpecFrom<SpecChooseFmt> for SpecChooseFmtInner {
    open spec fn spec_from(m: SpecChooseFmt) -> SpecChooseFmtInner {
        match m {
            SpecChooseFmt::Variant0(m) => Either::Left(m),
            SpecChooseFmt::Variant1(m) => Either::Right(Either::Left(m)),
            SpecChooseFmt::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}


impl SpecFrom<SpecChooseFmtInner> for SpecChooseFmt {
    open spec fn spec_from(m: SpecChooseFmtInner) -> SpecChooseFmt {
        match m {
            Either::Left(m) => SpecChooseFmt::Variant0(m),
            Either::Right(Either::Left(m)) => SpecChooseFmt::Variant1(m),
            Either::Right(Either::Right(m)) => SpecChooseFmt::Variant2(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChooseFmt {
    Variant0(u8),
    Variant1(u16),
    Variant2(u64),
}

pub type ChooseFmtInner = Either<u8, Either<u16, u64>>;

pub type ChooseFmtInnerRef<'a> = Either<&'a u8, Either<&'a u16, &'a u64>>;


impl View for ChooseFmt {
    type V = SpecChooseFmt;
    open spec fn view(&self) -> Self::V {
        match self {
            ChooseFmt::Variant0(m) => SpecChooseFmt::Variant0(m@),
            ChooseFmt::Variant1(m) => SpecChooseFmt::Variant1(m@),
            ChooseFmt::Variant2(m) => SpecChooseFmt::Variant2(m@),
        }
    }
}


impl<'a> From<&'a ChooseFmt> for ChooseFmtInnerRef<'a> {
    fn ex_from(m: &'a ChooseFmt) -> ChooseFmtInnerRef<'a> {
        match m {
            ChooseFmt::Variant0(m) => Either::Left(m),
            ChooseFmt::Variant1(m) => Either::Right(Either::Left(m)),
            ChooseFmt::Variant2(m) => Either::Right(Either::Right(m)),
        }
    }

}

impl From<ChooseFmtInner> for ChooseFmt {
    fn ex_from(m: ChooseFmtInner) -> ChooseFmt {
        match m {
            Either::Left(m) => ChooseFmt::Variant0(m),
            Either::Right(Either::Left(m)) => ChooseFmt::Variant1(m),
            Either::Right(Either::Right(m)) => ChooseFmt::Variant2(m),
        }
    }

}


pub struct ChooseFmtMapper;
impl View for ChooseFmtMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ChooseFmtMapper {
    type Src = SpecChooseFmtInner;
    type Dst = SpecChooseFmt;
}
impl SpecIsoProof for ChooseFmtMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for ChooseFmtMapper {
    type Src = ChooseFmtInner;
    type Dst = ChooseFmt;
    type RefSrc = ChooseFmtInnerRef<'a>;
}


pub struct SpecChooseFmtCombinator(SpecChooseFmtCombinatorAlias);

type SpecChooseFmtCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U64Le>>;
type SpecChooseFmtCombinatorAlias2 = Choice<Cond<U8>, SpecChooseFmtCombinatorAlias1>;
pub type SpecChooseFmtCombinatorAlias = Mapped<SpecChooseFmtCombinatorAlias2, ChooseFmtMapper>;

impl SpecCombinator for SpecChooseFmtCombinator {
    type Type = SpecChooseFmt;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecChooseFmtCombinator {
    open spec fn is_prefix_secure() -> bool
    { SpecChooseFmtCombinatorAlias::is_prefix_secure() }
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

struct ChooseFmtCombinator1(ChooseFmtCombinatorAlias1);
struct ChooseFmtCombinator2(ChooseFmtCombinatorAlias2);
pub struct ChooseFmtCombinator(ChooseFmtCombinatorAlias);

type ChooseFmtCombinatorAlias1 = Choice<Cond<U16Le>, Cond<U64Le>>;
type ChooseFmtCombinatorAlias2 = Choice<Cond<U8>, ChooseFmtCombinator1>;
type ChooseFmtCombinatorAlias = Mapped<ChooseFmtCombinator2, ChooseFmtMapper>;

// pub type ChooseFmtCombinatorAlias = Mapped<Choice<Cond<U8>, Choice<Cond<U16Le>, Cond<U64Le>>>, ChooseFmtMapper>;

impl View for ChooseFmtCombinator1 {
    type V = SpecChooseFmtCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl View for ChooseFmtCombinator2 {
    type V = SpecChooseFmtCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl View for ChooseFmtCombinator {
    type V = SpecChooseFmtCombinator;
    closed spec fn view(&self) -> Self::V { SpecChooseFmtCombinator(self.0@) }
}


macro_rules! impl_wrapper_combinator {
    ($combinator:ty, $combinator_alias:ty) => {
        ::builtin_macros::verus! {
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

impl_wrapper_combinator!(ChooseFmtCombinator1, ChooseFmtCombinatorAlias1);
impl_wrapper_combinator!(ChooseFmtCombinator2, ChooseFmtCombinatorAlias2);

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ChooseFmtCombinator {
    type Type = ChooseFmt;
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


pub closed spec fn spec_choose_fmt(tag: u8) -> SpecChooseFmtCombinator {
    SpecChooseFmtCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: U8 }, Choice(Cond { cond: tag == 1, inner: U16Le }, Cond { cond: !(tag == 0 || tag == 1), inner: U64Le })), mapper: ChooseFmtMapper })
}

pub fn choose_fmt<'a>(tag: u8) -> (o: ChooseFmtCombinator)
    ensures o@ == spec_choose_fmt(tag@),
{
    ChooseFmtCombinator(Mapped { inner: ChooseFmtCombinator2(Choice::new(Cond { cond: tag == 0, inner: U8 }, ChooseFmtCombinator1(Choice::new(Cond { cond: tag == 1, inner: U16Le }, Cond { cond: !(tag == 0 || tag == 1), inner: U64Le })))), mapper: ChooseFmtMapper })
}


}
