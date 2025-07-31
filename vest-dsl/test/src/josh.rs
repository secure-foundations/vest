
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

pub struct SpecMydata {
    pub foo: Seq<u8>,
    pub bar: Seq<u8>,
}

pub type SpecMydataInner = (Seq<u8>, Seq<u8>);


impl SpecFrom<SpecMydata> for SpecMydataInner {
    open spec fn spec_from(m: SpecMydata) -> SpecMydataInner {
        (m.foo, m.bar)
    }
}

impl SpecFrom<SpecMydataInner> for SpecMydata {
    open spec fn spec_from(m: SpecMydataInner) -> SpecMydata {
        let (foo, bar) = m;
        SpecMydata { foo, bar }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Mydata<'a> {
    pub foo: &'a [u8],
    pub bar: &'a [u8],
}

impl View for Mydata<'_> {
    type V = SpecMydata;

    open spec fn view(&self) -> Self::V {
        SpecMydata {
            foo: self.foo@,
            bar: self.bar@,
        }
    }
}
pub type MydataInner<'a> = (&'a [u8], &'a [u8]);

pub type MydataInnerRef<'a> = (&'a &'a [u8], &'a &'a [u8]);
impl<'a> From<&'a Mydata<'a>> for MydataInnerRef<'a> {
    fn ex_from(m: &'a Mydata) -> MydataInnerRef<'a> {
        (&m.foo, &m.bar)
    }
}

impl<'a> From<MydataInner<'a>> for Mydata<'a> {
    fn ex_from(m: MydataInner) -> Mydata {
        let (foo, bar) = m;
        Mydata { foo, bar }
    }
}

pub struct MydataMapper;
impl View for MydataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for MydataMapper {
    type Src = SpecMydataInner;
    type Dst = SpecMydata;
}
impl SpecIsoProof for MydataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for MydataMapper {
    type Src = MydataInner<'a>;
    type Dst = Mydata<'a>;
    type RefSrc = MydataInnerRef<'a>;
}
type SpecMydataCombinatorAlias1 = (bytes::Fixed<2>, bytes::Fixed<2>);
pub struct SpecMydataCombinator(SpecMydataCombinatorAlias);

impl SpecCombinator for SpecMydataCombinator {
    type Type = SpecMydata;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecMydataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMydataCombinatorAlias::is_prefix_secure() }
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
pub type SpecMydataCombinatorAlias = Mapped<SpecMydataCombinatorAlias1, MydataMapper>;
type MydataCombinatorAlias1 = (bytes::Fixed<2>, bytes::Fixed<2>);
struct MydataCombinator1(MydataCombinatorAlias1);
impl View for MydataCombinator1 {
    type V = SpecMydataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(MydataCombinator1, MydataCombinatorAlias1);

pub struct MydataCombinator(MydataCombinatorAlias);

impl View for MydataCombinator {
    type V = SpecMydataCombinator;
    closed spec fn view(&self) -> Self::V { SpecMydataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for MydataCombinator {
    type Type = Mydata<'a>;
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
pub type MydataCombinatorAlias = Mapped<MydataCombinator1, MydataMapper>;


pub closed spec fn spec_mydata() -> SpecMydataCombinator {
    SpecMydataCombinator(
    Mapped {
        inner: (bytes::Fixed::<2>, bytes::Fixed::<2>),
        mapper: MydataMapper,
    })
}

                
pub fn mydata() -> (o: MydataCombinator)
    ensures o@ == spec_mydata(),
{
    MydataCombinator(
    Mapped {
        inner: MydataCombinator1((bytes::Fixed::<2>, bytes::Fixed::<2>)),
        mapper: MydataMapper,
    })
}

                

pub enum SpecTstMydata {
    C0(SpecMydata),
    C1(SpecMydata),
    C2(SpecMydata),
    C3(SpecMydata),
    C4(SpecMydata),
    C5(SpecMydata),
    C6(SpecMydata),
    C7(SpecMydata),
    C8(SpecMydata),
    C9(SpecMydata),
    C10(SpecMydata),
    C11(SpecMydata),
    C12(SpecMydata),
    C13(SpecMydata),
    C14(SpecMydata),
    C15(SpecMydata),
    C16(SpecMydata),
    C17(SpecMydata),
    C18(SpecMydata),
    C19(SpecMydata),
    C20(SpecMydata),
    C21(SpecMydata),
    C22(SpecMydata),
    C23(SpecMydata),
    C24(SpecMydata),
    C25(SpecMydata),
    C26(SpecMydata),
    C27(SpecMydata),
    C28(SpecMydata),
    C29(SpecMydata),
    C30(SpecMydata),
}

pub type SpecTstMydataInner = Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, SpecMydata>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

impl SpecFrom<SpecTstMydata> for SpecTstMydataInner {
    open spec fn spec_from(m: SpecTstMydata) -> SpecTstMydataInner {
        match m {
            SpecTstMydata::C0(m) => Either::Left(m),
            SpecTstMydata::C1(m) => Either::Right(Either::Left(m)),
            SpecTstMydata::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecTstMydata::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecTstMydata::C4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecTstMydata::C5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecTstMydata::C6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecTstMydata::C7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecTstMydata::C8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecTstMydata::C9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecTstMydata::C10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecTstMydata::C11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecTstMydata::C12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecTstMydata::C13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecTstMydata::C14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecTstMydata::C15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecTstMydata::C16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecTstMydata::C17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecTstMydata::C18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecTstMydata::C19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecTstMydata::C20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecTstMydata::C21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecTstMydata::C22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecTstMydata::C23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecTstMydata::C24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecTstMydata::C25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecTstMydata::C26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            SpecTstMydata::C27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            SpecTstMydata::C28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            SpecTstMydata::C29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            SpecTstMydata::C30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))),
        }
    }

}

                
impl SpecFrom<SpecTstMydataInner> for SpecTstMydata {
    open spec fn spec_from(m: SpecTstMydataInner) -> SpecTstMydata {
        match m {
            Either::Left(m) => SpecTstMydata::C0(m),
            Either::Right(Either::Left(m)) => SpecTstMydata::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecTstMydata::C2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecTstMydata::C3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecTstMydata::C4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecTstMydata::C5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecTstMydata::C6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecTstMydata::C7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecTstMydata::C8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecTstMydata::C9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecTstMydata::C10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecTstMydata::C11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecTstMydata::C12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecTstMydata::C13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecTstMydata::C14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecTstMydata::C15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecTstMydata::C16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecTstMydata::C17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecTstMydata::C18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecTstMydata::C19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecTstMydata::C20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecTstMydata::C21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecTstMydata::C22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecTstMydata::C23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecTstMydata::C24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecTstMydata::C25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => SpecTstMydata::C26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => SpecTstMydata::C27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => SpecTstMydata::C28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => SpecTstMydata::C29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))) => SpecTstMydata::C30(m),
        }
    }

}



#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TstMydata<'a> {
    C0(Mydata<'a>),
    C1(Mydata<'a>),
    C2(Mydata<'a>),
    C3(Mydata<'a>),
    C4(Mydata<'a>),
    C5(Mydata<'a>),
    C6(Mydata<'a>),
    C7(Mydata<'a>),
    C8(Mydata<'a>),
    C9(Mydata<'a>),
    C10(Mydata<'a>),
    C11(Mydata<'a>),
    C12(Mydata<'a>),
    C13(Mydata<'a>),
    C14(Mydata<'a>),
    C15(Mydata<'a>),
    C16(Mydata<'a>),
    C17(Mydata<'a>),
    C18(Mydata<'a>),
    C19(Mydata<'a>),
    C20(Mydata<'a>),
    C21(Mydata<'a>),
    C22(Mydata<'a>),
    C23(Mydata<'a>),
    C24(Mydata<'a>),
    C25(Mydata<'a>),
    C26(Mydata<'a>),
    C27(Mydata<'a>),
    C28(Mydata<'a>),
    C29(Mydata<'a>),
    C30(Mydata<'a>),
}

pub type TstMydataInner<'a> = Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Mydata<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;

pub type TstMydataInnerRef<'a> = Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, Either<&'a Mydata<'a>, &'a Mydata<'a>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;


impl<'a> View for TstMydata<'a> {
    type V = SpecTstMydata;
    open spec fn view(&self) -> Self::V {
        match self {
            TstMydata::C0(m) => SpecTstMydata::C0(m@),
            TstMydata::C1(m) => SpecTstMydata::C1(m@),
            TstMydata::C2(m) => SpecTstMydata::C2(m@),
            TstMydata::C3(m) => SpecTstMydata::C3(m@),
            TstMydata::C4(m) => SpecTstMydata::C4(m@),
            TstMydata::C5(m) => SpecTstMydata::C5(m@),
            TstMydata::C6(m) => SpecTstMydata::C6(m@),
            TstMydata::C7(m) => SpecTstMydata::C7(m@),
            TstMydata::C8(m) => SpecTstMydata::C8(m@),
            TstMydata::C9(m) => SpecTstMydata::C9(m@),
            TstMydata::C10(m) => SpecTstMydata::C10(m@),
            TstMydata::C11(m) => SpecTstMydata::C11(m@),
            TstMydata::C12(m) => SpecTstMydata::C12(m@),
            TstMydata::C13(m) => SpecTstMydata::C13(m@),
            TstMydata::C14(m) => SpecTstMydata::C14(m@),
            TstMydata::C15(m) => SpecTstMydata::C15(m@),
            TstMydata::C16(m) => SpecTstMydata::C16(m@),
            TstMydata::C17(m) => SpecTstMydata::C17(m@),
            TstMydata::C18(m) => SpecTstMydata::C18(m@),
            TstMydata::C19(m) => SpecTstMydata::C19(m@),
            TstMydata::C20(m) => SpecTstMydata::C20(m@),
            TstMydata::C21(m) => SpecTstMydata::C21(m@),
            TstMydata::C22(m) => SpecTstMydata::C22(m@),
            TstMydata::C23(m) => SpecTstMydata::C23(m@),
            TstMydata::C24(m) => SpecTstMydata::C24(m@),
            TstMydata::C25(m) => SpecTstMydata::C25(m@),
            TstMydata::C26(m) => SpecTstMydata::C26(m@),
            TstMydata::C27(m) => SpecTstMydata::C27(m@),
            TstMydata::C28(m) => SpecTstMydata::C28(m@),
            TstMydata::C29(m) => SpecTstMydata::C29(m@),
            TstMydata::C30(m) => SpecTstMydata::C30(m@),
        }
    }
}


impl<'a> From<&'a TstMydata<'a>> for TstMydataInnerRef<'a> {
    fn ex_from(m: &'a TstMydata<'a>) -> TstMydataInnerRef<'a> {
        match m {
            TstMydata::C0(m) => Either::Left(m),
            TstMydata::C1(m) => Either::Right(Either::Left(m)),
            TstMydata::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            TstMydata::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            TstMydata::C4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            TstMydata::C5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            TstMydata::C6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            TstMydata::C7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            TstMydata::C8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            TstMydata::C9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            TstMydata::C10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            TstMydata::C11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            TstMydata::C12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            TstMydata::C13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            TstMydata::C14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            TstMydata::C15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            TstMydata::C16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            TstMydata::C17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            TstMydata::C18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            TstMydata::C19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            TstMydata::C20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            TstMydata::C21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            TstMydata::C22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            TstMydata::C23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            TstMydata::C24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            TstMydata::C25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            TstMydata::C26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            TstMydata::C27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            TstMydata::C28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            TstMydata::C29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            TstMydata::C30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))),
        }
    }

}

impl<'a> From<TstMydataInner<'a>> for TstMydata<'a> {
    fn ex_from(m: TstMydataInner<'a>) -> TstMydata<'a> {
        match m {
            Either::Left(m) => TstMydata::C0(m),
            Either::Right(Either::Left(m)) => TstMydata::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => TstMydata::C2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => TstMydata::C3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => TstMydata::C4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => TstMydata::C5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => TstMydata::C6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => TstMydata::C7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => TstMydata::C8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => TstMydata::C9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => TstMydata::C10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => TstMydata::C11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => TstMydata::C12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => TstMydata::C13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => TstMydata::C14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => TstMydata::C15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => TstMydata::C16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => TstMydata::C17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => TstMydata::C18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => TstMydata::C19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => TstMydata::C20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => TstMydata::C21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => TstMydata::C22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => TstMydata::C23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => TstMydata::C24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => TstMydata::C25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => TstMydata::C26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => TstMydata::C27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => TstMydata::C28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => TstMydata::C29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))) => TstMydata::C30(m),
        }
    }
    
}


pub struct TstMydataMapper;
impl View for TstMydataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TstMydataMapper {
    type Src = SpecTstMydataInner;
    type Dst = SpecTstMydata;
}
impl SpecIsoProof for TstMydataMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TstMydataMapper {
    type Src = TstMydataInner<'a>;
    type Dst = TstMydata<'a>;
    type RefSrc = TstMydataInnerRef<'a>;
}

type SpecTstMydataCombinatorAlias1 = Choice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>;
type SpecTstMydataCombinatorAlias2 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias1>;
type SpecTstMydataCombinatorAlias3 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias2>;
type SpecTstMydataCombinatorAlias4 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias3>;
type SpecTstMydataCombinatorAlias5 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias4>;
type SpecTstMydataCombinatorAlias6 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias5>;
type SpecTstMydataCombinatorAlias7 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias6>;
type SpecTstMydataCombinatorAlias8 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias7>;
type SpecTstMydataCombinatorAlias9 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias8>;
type SpecTstMydataCombinatorAlias10 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias9>;
type SpecTstMydataCombinatorAlias11 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias10>;
type SpecTstMydataCombinatorAlias12 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias11>;
type SpecTstMydataCombinatorAlias13 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias12>;
type SpecTstMydataCombinatorAlias14 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias13>;
type SpecTstMydataCombinatorAlias15 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias14>;
type SpecTstMydataCombinatorAlias16 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias15>;
type SpecTstMydataCombinatorAlias17 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias16>;
type SpecTstMydataCombinatorAlias18 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias17>;
type SpecTstMydataCombinatorAlias19 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias18>;
type SpecTstMydataCombinatorAlias20 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias19>;
type SpecTstMydataCombinatorAlias21 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias20>;
type SpecTstMydataCombinatorAlias22 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias21>;
type SpecTstMydataCombinatorAlias23 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias22>;
type SpecTstMydataCombinatorAlias24 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias23>;
type SpecTstMydataCombinatorAlias25 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias24>;
type SpecTstMydataCombinatorAlias26 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias25>;
type SpecTstMydataCombinatorAlias27 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias26>;
type SpecTstMydataCombinatorAlias28 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias27>;
type SpecTstMydataCombinatorAlias29 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias28>;
type SpecTstMydataCombinatorAlias30 = Choice<Cond<SpecMydataCombinator>, SpecTstMydataCombinatorAlias29>;
pub struct SpecTstMydataCombinator(SpecTstMydataCombinatorAlias);

impl SpecCombinator for SpecTstMydataCombinator {
    type Type = SpecTstMydata;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstMydataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTstMydataCombinatorAlias::is_prefix_secure() }
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
pub type SpecTstMydataCombinatorAlias = Mapped<SpecTstMydataCombinatorAlias30, TstMydataMapper>;
type TstMydataCombinatorAlias1 = Choice<Cond<MydataCombinator>, Cond<MydataCombinator>>;
type TstMydataCombinatorAlias2 = Choice<Cond<MydataCombinator>, TstMydataCombinator1>;
type TstMydataCombinatorAlias3 = Choice<Cond<MydataCombinator>, TstMydataCombinator2>;
type TstMydataCombinatorAlias4 = Choice<Cond<MydataCombinator>, TstMydataCombinator3>;
type TstMydataCombinatorAlias5 = Choice<Cond<MydataCombinator>, TstMydataCombinator4>;
type TstMydataCombinatorAlias6 = Choice<Cond<MydataCombinator>, TstMydataCombinator5>;
type TstMydataCombinatorAlias7 = Choice<Cond<MydataCombinator>, TstMydataCombinator6>;
type TstMydataCombinatorAlias8 = Choice<Cond<MydataCombinator>, TstMydataCombinator7>;
type TstMydataCombinatorAlias9 = Choice<Cond<MydataCombinator>, TstMydataCombinator8>;
type TstMydataCombinatorAlias10 = Choice<Cond<MydataCombinator>, TstMydataCombinator9>;
type TstMydataCombinatorAlias11 = Choice<Cond<MydataCombinator>, TstMydataCombinator10>;
type TstMydataCombinatorAlias12 = Choice<Cond<MydataCombinator>, TstMydataCombinator11>;
type TstMydataCombinatorAlias13 = Choice<Cond<MydataCombinator>, TstMydataCombinator12>;
type TstMydataCombinatorAlias14 = Choice<Cond<MydataCombinator>, TstMydataCombinator13>;
type TstMydataCombinatorAlias15 = Choice<Cond<MydataCombinator>, TstMydataCombinator14>;
type TstMydataCombinatorAlias16 = Choice<Cond<MydataCombinator>, TstMydataCombinator15>;
type TstMydataCombinatorAlias17 = Choice<Cond<MydataCombinator>, TstMydataCombinator16>;
type TstMydataCombinatorAlias18 = Choice<Cond<MydataCombinator>, TstMydataCombinator17>;
type TstMydataCombinatorAlias19 = Choice<Cond<MydataCombinator>, TstMydataCombinator18>;
type TstMydataCombinatorAlias20 = Choice<Cond<MydataCombinator>, TstMydataCombinator19>;
type TstMydataCombinatorAlias21 = Choice<Cond<MydataCombinator>, TstMydataCombinator20>;
type TstMydataCombinatorAlias22 = Choice<Cond<MydataCombinator>, TstMydataCombinator21>;
type TstMydataCombinatorAlias23 = Choice<Cond<MydataCombinator>, TstMydataCombinator22>;
type TstMydataCombinatorAlias24 = Choice<Cond<MydataCombinator>, TstMydataCombinator23>;
type TstMydataCombinatorAlias25 = Choice<Cond<MydataCombinator>, TstMydataCombinator24>;
type TstMydataCombinatorAlias26 = Choice<Cond<MydataCombinator>, TstMydataCombinator25>;
type TstMydataCombinatorAlias27 = Choice<Cond<MydataCombinator>, TstMydataCombinator26>;
type TstMydataCombinatorAlias28 = Choice<Cond<MydataCombinator>, TstMydataCombinator27>;
type TstMydataCombinatorAlias29 = Choice<Cond<MydataCombinator>, TstMydataCombinator28>;
type TstMydataCombinatorAlias30 = Choice<Cond<MydataCombinator>, TstMydataCombinator29>;
struct TstMydataCombinator1(TstMydataCombinatorAlias1);
impl View for TstMydataCombinator1 {
    type V = SpecTstMydataCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator1, TstMydataCombinatorAlias1);

struct TstMydataCombinator2(TstMydataCombinatorAlias2);
impl View for TstMydataCombinator2 {
    type V = SpecTstMydataCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator2, TstMydataCombinatorAlias2);

struct TstMydataCombinator3(TstMydataCombinatorAlias3);
impl View for TstMydataCombinator3 {
    type V = SpecTstMydataCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator3, TstMydataCombinatorAlias3);

struct TstMydataCombinator4(TstMydataCombinatorAlias4);
impl View for TstMydataCombinator4 {
    type V = SpecTstMydataCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator4, TstMydataCombinatorAlias4);

struct TstMydataCombinator5(TstMydataCombinatorAlias5);
impl View for TstMydataCombinator5 {
    type V = SpecTstMydataCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator5, TstMydataCombinatorAlias5);

struct TstMydataCombinator6(TstMydataCombinatorAlias6);
impl View for TstMydataCombinator6 {
    type V = SpecTstMydataCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator6, TstMydataCombinatorAlias6);

struct TstMydataCombinator7(TstMydataCombinatorAlias7);
impl View for TstMydataCombinator7 {
    type V = SpecTstMydataCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator7, TstMydataCombinatorAlias7);

struct TstMydataCombinator8(TstMydataCombinatorAlias8);
impl View for TstMydataCombinator8 {
    type V = SpecTstMydataCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator8, TstMydataCombinatorAlias8);

struct TstMydataCombinator9(TstMydataCombinatorAlias9);
impl View for TstMydataCombinator9 {
    type V = SpecTstMydataCombinatorAlias9;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator9, TstMydataCombinatorAlias9);

struct TstMydataCombinator10(TstMydataCombinatorAlias10);
impl View for TstMydataCombinator10 {
    type V = SpecTstMydataCombinatorAlias10;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator10, TstMydataCombinatorAlias10);

struct TstMydataCombinator11(TstMydataCombinatorAlias11);
impl View for TstMydataCombinator11 {
    type V = SpecTstMydataCombinatorAlias11;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator11, TstMydataCombinatorAlias11);

struct TstMydataCombinator12(TstMydataCombinatorAlias12);
impl View for TstMydataCombinator12 {
    type V = SpecTstMydataCombinatorAlias12;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator12, TstMydataCombinatorAlias12);

struct TstMydataCombinator13(TstMydataCombinatorAlias13);
impl View for TstMydataCombinator13 {
    type V = SpecTstMydataCombinatorAlias13;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator13, TstMydataCombinatorAlias13);

struct TstMydataCombinator14(TstMydataCombinatorAlias14);
impl View for TstMydataCombinator14 {
    type V = SpecTstMydataCombinatorAlias14;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator14, TstMydataCombinatorAlias14);

struct TstMydataCombinator15(TstMydataCombinatorAlias15);
impl View for TstMydataCombinator15 {
    type V = SpecTstMydataCombinatorAlias15;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator15, TstMydataCombinatorAlias15);

struct TstMydataCombinator16(TstMydataCombinatorAlias16);
impl View for TstMydataCombinator16 {
    type V = SpecTstMydataCombinatorAlias16;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator16, TstMydataCombinatorAlias16);

struct TstMydataCombinator17(TstMydataCombinatorAlias17);
impl View for TstMydataCombinator17 {
    type V = SpecTstMydataCombinatorAlias17;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator17, TstMydataCombinatorAlias17);

struct TstMydataCombinator18(TstMydataCombinatorAlias18);
impl View for TstMydataCombinator18 {
    type V = SpecTstMydataCombinatorAlias18;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator18, TstMydataCombinatorAlias18);

struct TstMydataCombinator19(TstMydataCombinatorAlias19);
impl View for TstMydataCombinator19 {
    type V = SpecTstMydataCombinatorAlias19;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator19, TstMydataCombinatorAlias19);

struct TstMydataCombinator20(TstMydataCombinatorAlias20);
impl View for TstMydataCombinator20 {
    type V = SpecTstMydataCombinatorAlias20;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator20, TstMydataCombinatorAlias20);

struct TstMydataCombinator21(TstMydataCombinatorAlias21);
impl View for TstMydataCombinator21 {
    type V = SpecTstMydataCombinatorAlias21;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator21, TstMydataCombinatorAlias21);

struct TstMydataCombinator22(TstMydataCombinatorAlias22);
impl View for TstMydataCombinator22 {
    type V = SpecTstMydataCombinatorAlias22;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator22, TstMydataCombinatorAlias22);

struct TstMydataCombinator23(TstMydataCombinatorAlias23);
impl View for TstMydataCombinator23 {
    type V = SpecTstMydataCombinatorAlias23;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator23, TstMydataCombinatorAlias23);

struct TstMydataCombinator24(TstMydataCombinatorAlias24);
impl View for TstMydataCombinator24 {
    type V = SpecTstMydataCombinatorAlias24;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator24, TstMydataCombinatorAlias24);

struct TstMydataCombinator25(TstMydataCombinatorAlias25);
impl View for TstMydataCombinator25 {
    type V = SpecTstMydataCombinatorAlias25;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator25, TstMydataCombinatorAlias25);

struct TstMydataCombinator26(TstMydataCombinatorAlias26);
impl View for TstMydataCombinator26 {
    type V = SpecTstMydataCombinatorAlias26;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator26, TstMydataCombinatorAlias26);

struct TstMydataCombinator27(TstMydataCombinatorAlias27);
impl View for TstMydataCombinator27 {
    type V = SpecTstMydataCombinatorAlias27;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator27, TstMydataCombinatorAlias27);

struct TstMydataCombinator28(TstMydataCombinatorAlias28);
impl View for TstMydataCombinator28 {
    type V = SpecTstMydataCombinatorAlias28;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator28, TstMydataCombinatorAlias28);

struct TstMydataCombinator29(TstMydataCombinatorAlias29);
impl View for TstMydataCombinator29 {
    type V = SpecTstMydataCombinatorAlias29;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator29, TstMydataCombinatorAlias29);

struct TstMydataCombinator30(TstMydataCombinatorAlias30);
impl View for TstMydataCombinator30 {
    type V = SpecTstMydataCombinatorAlias30;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(TstMydataCombinator30, TstMydataCombinatorAlias30);

pub struct TstMydataCombinator(TstMydataCombinatorAlias);

impl View for TstMydataCombinator {
    type V = SpecTstMydataCombinator;
    closed spec fn view(&self) -> Self::V { SpecTstMydataCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstMydataCombinator {
    type Type = TstMydata<'a>;
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
pub type TstMydataCombinatorAlias = Mapped<TstMydataCombinator30, TstMydataMapper>;


pub closed spec fn spec_tst_mydata(tag: SpecTstTag) -> SpecTstMydataCombinator {
    SpecTstMydataCombinator(Mapped { inner: Choice(Cond { cond: tag == 0, inner: spec_mydata() }, Choice(Cond { cond: tag == 1, inner: spec_mydata() }, Choice(Cond { cond: tag == 2, inner: spec_mydata() }, Choice(Cond { cond: tag == 3, inner: spec_mydata() }, Choice(Cond { cond: tag == 4, inner: spec_mydata() }, Choice(Cond { cond: tag == 5, inner: spec_mydata() }, Choice(Cond { cond: tag == 6, inner: spec_mydata() }, Choice(Cond { cond: tag == 7, inner: spec_mydata() }, Choice(Cond { cond: tag == 8, inner: spec_mydata() }, Choice(Cond { cond: tag == 9, inner: spec_mydata() }, Choice(Cond { cond: tag == 10, inner: spec_mydata() }, Choice(Cond { cond: tag == 11, inner: spec_mydata() }, Choice(Cond { cond: tag == 12, inner: spec_mydata() }, Choice(Cond { cond: tag == 13, inner: spec_mydata() }, Choice(Cond { cond: tag == 14, inner: spec_mydata() }, Choice(Cond { cond: tag == 15, inner: spec_mydata() }, Choice(Cond { cond: tag == 16, inner: spec_mydata() }, Choice(Cond { cond: tag == 17, inner: spec_mydata() }, Choice(Cond { cond: tag == 18, inner: spec_mydata() }, Choice(Cond { cond: tag == 19, inner: spec_mydata() }, Choice(Cond { cond: tag == 20, inner: spec_mydata() }, Choice(Cond { cond: tag == 21, inner: spec_mydata() }, Choice(Cond { cond: tag == 22, inner: spec_mydata() }, Choice(Cond { cond: tag == 23, inner: spec_mydata() }, Choice(Cond { cond: tag == 24, inner: spec_mydata() }, Choice(Cond { cond: tag == 25, inner: spec_mydata() }, Choice(Cond { cond: tag == 26, inner: spec_mydata() }, Choice(Cond { cond: tag == 27, inner: spec_mydata() }, Choice(Cond { cond: tag == 28, inner: spec_mydata() }, Choice(Cond { cond: tag == 29, inner: spec_mydata() }, Cond { cond: tag == 30, inner: spec_mydata() })))))))))))))))))))))))))))))), mapper: TstMydataMapper })
}

pub fn tst_mydata<'a>(tag: TstTag) -> (o: TstMydataCombinator)
    ensures o@ == spec_tst_mydata(tag@),
{
    TstMydataCombinator(Mapped { inner: TstMydataCombinator30(Choice::new(Cond { cond: tag == 0, inner: mydata() }, TstMydataCombinator29(Choice::new(Cond { cond: tag == 1, inner: mydata() }, TstMydataCombinator28(Choice::new(Cond { cond: tag == 2, inner: mydata() }, TstMydataCombinator27(Choice::new(Cond { cond: tag == 3, inner: mydata() }, TstMydataCombinator26(Choice::new(Cond { cond: tag == 4, inner: mydata() }, TstMydataCombinator25(Choice::new(Cond { cond: tag == 5, inner: mydata() }, TstMydataCombinator24(Choice::new(Cond { cond: tag == 6, inner: mydata() }, TstMydataCombinator23(Choice::new(Cond { cond: tag == 7, inner: mydata() }, TstMydataCombinator22(Choice::new(Cond { cond: tag == 8, inner: mydata() }, TstMydataCombinator21(Choice::new(Cond { cond: tag == 9, inner: mydata() }, TstMydataCombinator20(Choice::new(Cond { cond: tag == 10, inner: mydata() }, TstMydataCombinator19(Choice::new(Cond { cond: tag == 11, inner: mydata() }, TstMydataCombinator18(Choice::new(Cond { cond: tag == 12, inner: mydata() }, TstMydataCombinator17(Choice::new(Cond { cond: tag == 13, inner: mydata() }, TstMydataCombinator16(Choice::new(Cond { cond: tag == 14, inner: mydata() }, TstMydataCombinator15(Choice::new(Cond { cond: tag == 15, inner: mydata() }, TstMydataCombinator14(Choice::new(Cond { cond: tag == 16, inner: mydata() }, TstMydataCombinator13(Choice::new(Cond { cond: tag == 17, inner: mydata() }, TstMydataCombinator12(Choice::new(Cond { cond: tag == 18, inner: mydata() }, TstMydataCombinator11(Choice::new(Cond { cond: tag == 19, inner: mydata() }, TstMydataCombinator10(Choice::new(Cond { cond: tag == 20, inner: mydata() }, TstMydataCombinator9(Choice::new(Cond { cond: tag == 21, inner: mydata() }, TstMydataCombinator8(Choice::new(Cond { cond: tag == 22, inner: mydata() }, TstMydataCombinator7(Choice::new(Cond { cond: tag == 23, inner: mydata() }, TstMydataCombinator6(Choice::new(Cond { cond: tag == 24, inner: mydata() }, TstMydataCombinator5(Choice::new(Cond { cond: tag == 25, inner: mydata() }, TstMydataCombinator4(Choice::new(Cond { cond: tag == 26, inner: mydata() }, TstMydataCombinator3(Choice::new(Cond { cond: tag == 27, inner: mydata() }, TstMydataCombinator2(Choice::new(Cond { cond: tag == 28, inner: mydata() }, TstMydataCombinator1(Choice::new(Cond { cond: tag == 29, inner: mydata() }, Cond { cond: tag == 30, inner: mydata() })))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), mapper: TstMydataMapper })
}

pub type SpecTstTag = u8;
pub type TstTag = u8;
pub type TstTagRef<'a> = &'a u8;


pub struct SpecTstTagCombinator(SpecTstTagCombinatorAlias);

impl SpecCombinator for SpecTstTagCombinator {
    type Type = SpecTstTag;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstTagCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTstTagCombinatorAlias::is_prefix_secure() }
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
pub type SpecTstTagCombinatorAlias = U8;

pub struct TstTagCombinator(TstTagCombinatorAlias);

impl View for TstTagCombinator {
    type V = SpecTstTagCombinator;
    closed spec fn view(&self) -> Self::V { SpecTstTagCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstTagCombinator {
    type Type = TstTag;
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
pub type TstTagCombinatorAlias = U8;


pub closed spec fn spec_tst_tag() -> SpecTstTagCombinator {
    SpecTstTagCombinator(U8)
}

                
pub fn tst_tag() -> (o: TstTagCombinator)
    ensures o@ == spec_tst_tag(),
{
    TstTagCombinator(U8)
}

                

pub struct SpecPairStress {
    pub f1: u8,
    pub f2: u16,
    pub f3: u32,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
    pub f11: u8,
    pub f12: u8,
    pub f13: u8,
    pub f14: u8,
    pub f15: u8,
}

pub type SpecPairStressInner = (u8, (u16, (u32, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))));


impl SpecFrom<SpecPairStress> for SpecPairStressInner {
    open spec fn spec_from(m: SpecPairStress) -> SpecPairStressInner {
        (m.f1, (m.f2, (m.f3, (m.f4, (m.f5, (m.f6, (m.f7, (m.f8, (m.f9, (m.f10, (m.f11, (m.f12, (m.f13, (m.f14, m.f15))))))))))))))
    }
}

impl SpecFrom<SpecPairStressInner> for SpecPairStress {
    open spec fn spec_from(m: SpecPairStressInner) -> SpecPairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, (f10, (f11, (f12, (f13, (f14, f15)))))))))))))) = m;
        SpecPairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15 }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct PairStress {
    pub f1: u8,
    pub f2: u16,
    pub f3: u32,
    pub f4: u8,
    pub f5: u8,
    pub f6: u8,
    pub f7: u8,
    pub f8: u8,
    pub f9: u8,
    pub f10: u8,
    pub f11: u8,
    pub f12: u8,
    pub f13: u8,
    pub f14: u8,
    pub f15: u8,
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
            f11: self.f11@,
            f12: self.f12@,
            f13: self.f13@,
            f14: self.f14@,
            f15: self.f15@,
        }
    }
}
pub type PairStressInner = (u8, (u16, (u32, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, (u8, u8))))))))))))));

pub type PairStressInnerRef<'a> = (&'a u8, (&'a u16, (&'a u32, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, (&'a u8, &'a u8))))))))))))));
impl<'a> From<&'a PairStress> for PairStressInnerRef<'a> {
    fn ex_from(m: &'a PairStress) -> PairStressInnerRef<'a> {
        (&m.f1, (&m.f2, (&m.f3, (&m.f4, (&m.f5, (&m.f6, (&m.f7, (&m.f8, (&m.f9, (&m.f10, (&m.f11, (&m.f12, (&m.f13, (&m.f14, &m.f15))))))))))))))
    }
}

impl From<PairStressInner> for PairStress {
    fn ex_from(m: PairStressInner) -> PairStress {
        let (f1, (f2, (f3, (f4, (f5, (f6, (f7, (f8, (f9, (f10, (f11, (f12, (f13, (f14, f15)))))))))))))) = m;
        PairStress { f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15 }
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
type SpecPairStressCombinatorAlias1 = (U8, U8);
type SpecPairStressCombinatorAlias2 = (U8, SpecPairStressCombinatorAlias1);
type SpecPairStressCombinatorAlias3 = (U8, SpecPairStressCombinatorAlias2);
type SpecPairStressCombinatorAlias4 = (U8, SpecPairStressCombinatorAlias3);
type SpecPairStressCombinatorAlias5 = (U8, SpecPairStressCombinatorAlias4);
type SpecPairStressCombinatorAlias6 = (U8, SpecPairStressCombinatorAlias5);
type SpecPairStressCombinatorAlias7 = (U8, SpecPairStressCombinatorAlias6);
type SpecPairStressCombinatorAlias8 = (U8, SpecPairStressCombinatorAlias7);
type SpecPairStressCombinatorAlias9 = (U8, SpecPairStressCombinatorAlias8);
type SpecPairStressCombinatorAlias10 = (U8, SpecPairStressCombinatorAlias9);
type SpecPairStressCombinatorAlias11 = (U8, SpecPairStressCombinatorAlias10);
type SpecPairStressCombinatorAlias12 = (U32Le, SpecPairStressCombinatorAlias11);
type SpecPairStressCombinatorAlias13 = (U16Le, SpecPairStressCombinatorAlias12);
type SpecPairStressCombinatorAlias14 = (U8, SpecPairStressCombinatorAlias13);
pub struct SpecPairStressCombinator(SpecPairStressCombinatorAlias);

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
    { SpecPairStressCombinatorAlias::is_prefix_secure() }
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
pub type SpecPairStressCombinatorAlias = Mapped<SpecPairStressCombinatorAlias14, PairStressMapper>;
type PairStressCombinatorAlias1 = (U8, U8);
type PairStressCombinatorAlias2 = (U8, PairStressCombinator1);
type PairStressCombinatorAlias3 = (U8, PairStressCombinator2);
type PairStressCombinatorAlias4 = (U8, PairStressCombinator3);
type PairStressCombinatorAlias5 = (U8, PairStressCombinator4);
type PairStressCombinatorAlias6 = (U8, PairStressCombinator5);
type PairStressCombinatorAlias7 = (U8, PairStressCombinator6);
type PairStressCombinatorAlias8 = (U8, PairStressCombinator7);
type PairStressCombinatorAlias9 = (U8, PairStressCombinator8);
type PairStressCombinatorAlias10 = (U8, PairStressCombinator9);
type PairStressCombinatorAlias11 = (U8, PairStressCombinator10);
type PairStressCombinatorAlias12 = (U32Le, PairStressCombinator11);
type PairStressCombinatorAlias13 = (U16Le, PairStressCombinator12);
type PairStressCombinatorAlias14 = (U8, PairStressCombinator13);
struct PairStressCombinator1(PairStressCombinatorAlias1);
impl View for PairStressCombinator1 {
    type V = SpecPairStressCombinatorAlias1;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator1, PairStressCombinatorAlias1);

struct PairStressCombinator2(PairStressCombinatorAlias2);
impl View for PairStressCombinator2 {
    type V = SpecPairStressCombinatorAlias2;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator2, PairStressCombinatorAlias2);

struct PairStressCombinator3(PairStressCombinatorAlias3);
impl View for PairStressCombinator3 {
    type V = SpecPairStressCombinatorAlias3;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator3, PairStressCombinatorAlias3);

struct PairStressCombinator4(PairStressCombinatorAlias4);
impl View for PairStressCombinator4 {
    type V = SpecPairStressCombinatorAlias4;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator4, PairStressCombinatorAlias4);

struct PairStressCombinator5(PairStressCombinatorAlias5);
impl View for PairStressCombinator5 {
    type V = SpecPairStressCombinatorAlias5;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator5, PairStressCombinatorAlias5);

struct PairStressCombinator6(PairStressCombinatorAlias6);
impl View for PairStressCombinator6 {
    type V = SpecPairStressCombinatorAlias6;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator6, PairStressCombinatorAlias6);

struct PairStressCombinator7(PairStressCombinatorAlias7);
impl View for PairStressCombinator7 {
    type V = SpecPairStressCombinatorAlias7;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator7, PairStressCombinatorAlias7);

struct PairStressCombinator8(PairStressCombinatorAlias8);
impl View for PairStressCombinator8 {
    type V = SpecPairStressCombinatorAlias8;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator8, PairStressCombinatorAlias8);

struct PairStressCombinator9(PairStressCombinatorAlias9);
impl View for PairStressCombinator9 {
    type V = SpecPairStressCombinatorAlias9;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator9, PairStressCombinatorAlias9);

struct PairStressCombinator10(PairStressCombinatorAlias10);
impl View for PairStressCombinator10 {
    type V = SpecPairStressCombinatorAlias10;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator10, PairStressCombinatorAlias10);

struct PairStressCombinator11(PairStressCombinatorAlias11);
impl View for PairStressCombinator11 {
    type V = SpecPairStressCombinatorAlias11;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator11, PairStressCombinatorAlias11);

struct PairStressCombinator12(PairStressCombinatorAlias12);
impl View for PairStressCombinator12 {
    type V = SpecPairStressCombinatorAlias12;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator12, PairStressCombinatorAlias12);

struct PairStressCombinator13(PairStressCombinatorAlias13);
impl View for PairStressCombinator13 {
    type V = SpecPairStressCombinatorAlias13;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator13, PairStressCombinatorAlias13);

struct PairStressCombinator14(PairStressCombinatorAlias14);
impl View for PairStressCombinator14 {
    type V = SpecPairStressCombinatorAlias14;
    closed spec fn view(&self) -> Self::V { self.0@ }
}
impl_wrapper_combinator!(PairStressCombinator14, PairStressCombinatorAlias14);

pub struct PairStressCombinator(PairStressCombinatorAlias);

impl View for PairStressCombinator {
    type V = SpecPairStressCombinator;
    closed spec fn view(&self) -> Self::V { SpecPairStressCombinator(self.0@) }
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
pub type PairStressCombinatorAlias = Mapped<PairStressCombinator14, PairStressMapper>;


pub closed spec fn spec_pair_stress() -> SpecPairStressCombinator {
    SpecPairStressCombinator(
    Mapped {
        inner: (U8, (U16Le, (U32Le, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, (U8, U8)))))))))))))),
        mapper: PairStressMapper,
    })
}

                
pub fn pair_stress() -> (o: PairStressCombinator)
    ensures o@ == spec_pair_stress(),
{
    PairStressCombinator(
    Mapped {
        inner: PairStressCombinator14((U8, PairStressCombinator13((U16Le, PairStressCombinator12((U32Le, PairStressCombinator11((U8, PairStressCombinator10((U8, PairStressCombinator9((U8, PairStressCombinator8((U8, PairStressCombinator7((U8, PairStressCombinator6((U8, PairStressCombinator5((U8, PairStressCombinator4((U8, PairStressCombinator3((U8, PairStressCombinator2((U8, PairStressCombinator1((U8, U8)))))))))))))))))))))))))))),
        mapper: PairStressMapper,
    })
}

                

pub struct SpecTst {
    pub tag: SpecTstTag,
    pub mydata: SpecTstMydata,
}

pub type SpecTstInner = (SpecTstTag, SpecTstMydata);


impl SpecFrom<SpecTst> for SpecTstInner {
    open spec fn spec_from(m: SpecTst) -> SpecTstInner {
        (m.tag, m.mydata)
    }
}

impl SpecFrom<SpecTstInner> for SpecTst {
    open spec fn spec_from(m: SpecTstInner) -> SpecTst {
        let (tag, mydata) = m;
        SpecTst { tag, mydata }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]

pub struct Tst<'a> {
    pub tag: TstTag,
    pub mydata: TstMydata<'a>,
}

impl View for Tst<'_> {
    type V = SpecTst;

    open spec fn view(&self) -> Self::V {
        SpecTst {
            tag: self.tag@,
            mydata: self.mydata@,
        }
    }
}
pub type TstInner<'a> = (TstTag, TstMydata<'a>);

pub type TstInnerRef<'a> = (&'a TstTag, &'a TstMydata<'a>);
impl<'a> From<&'a Tst<'a>> for TstInnerRef<'a> {
    fn ex_from(m: &'a Tst) -> TstInnerRef<'a> {
        (&m.tag, &m.mydata)
    }
}

impl<'a> From<TstInner<'a>> for Tst<'a> {
    fn ex_from(m: TstInner) -> Tst {
        let (tag, mydata) = m;
        Tst { tag, mydata }
    }
}

pub struct TstMapper;
impl View for TstMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TstMapper {
    type Src = SpecTstInner;
    type Dst = SpecTst;
}
impl SpecIsoProof for TstMapper {
    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }
    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}
impl<'a> Iso<'a> for TstMapper {
    type Src = TstInner<'a>;
    type Dst = Tst<'a>;
    type RefSrc = TstInnerRef<'a>;
}

pub struct SpecTstCombinator(SpecTstCombinatorAlias);

impl SpecCombinator for SpecTstCombinator {
    type Type = SpecTst;
    closed spec fn requires(&self) -> bool
    { self.0.requires() }
    closed spec fn wf(&self, v: Self::Type) -> bool
    { self.0.wf(v) }
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> 
    { self.0.spec_serialize(v) }
}
impl SecureSpecCombinator for SpecTstCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTstCombinatorAlias::is_prefix_secure() }
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
pub type SpecTstCombinatorAlias = Mapped<SpecPair<SpecTstTagCombinator, SpecTstMydataCombinator>, TstMapper>;

pub struct TstCombinator(TstCombinatorAlias);

impl View for TstCombinator {
    type V = SpecTstCombinator;
    closed spec fn view(&self) -> Self::V { SpecTstCombinator(self.0@) }
}
impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for TstCombinator {
    type Type = Tst<'a>;
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
pub type TstCombinatorAlias = Mapped<Pair<TstTagCombinator, TstMydataCombinator, TstCont0>, TstMapper>;


pub closed spec fn spec_tst() -> SpecTstCombinator {
    SpecTstCombinator(
    Mapped {
        inner: Pair::spec_new(spec_tst_tag(), |deps| spec_tst_cont0(deps)),
        mapper: TstMapper,
    })
}

pub open spec fn spec_tst_cont0(deps: SpecTstTag) -> SpecTstMydataCombinator {
    let tag = deps;
    spec_tst_mydata(tag)
}

impl View for TstCont0 {
    type V = spec_fn(SpecTstTag) -> SpecTstMydataCombinator;

    open spec fn view(&self) -> Self::V {
        |deps: SpecTstTag| {
            spec_tst_cont0(deps)
        }
    }
}

                
pub fn tst() -> (o: TstCombinator)
    ensures o@ == spec_tst(),
{
    TstCombinator(
    Mapped {
        inner: Pair::new(tst_tag(), TstCont0),
        mapper: TstMapper,
    })
}

pub struct TstCont0;
type TstCont0Type<'a, 'b> = &'b TstTag;
type TstCont0SType<'a, 'x> = &'x TstTag;
type TstCont0Input<'a, 'b, 'x> = POrSType<TstCont0Type<'a, 'b>, TstCont0SType<'a, 'x>>;
impl<'a, 'b, 'x> Continuation<TstCont0Input<'a, 'b, 'x>> for TstCont0 {
    type Output = TstMydataCombinator;

    open spec fn requires(&self, deps: TstCont0Input<'a, 'b, 'x>) -> bool { true }

    open spec fn ensures(&self, deps: TstCont0Input<'a, 'b, 'x>, o: Self::Output) -> bool {
        o@ == spec_tst_cont0(deps@)
    }

    fn apply(&self, deps: TstCont0Input<'a, 'b, 'x>) -> Self::Output {
        match deps {
            POrSType::P(deps) => {
                let tag = *deps;
                tst_mydata(tag)
            }
            POrSType::S(deps) => {
                let tag = deps;
                let tag = *tag;
                tst_mydata(tag)
            }
        }
    }
}
                

}
