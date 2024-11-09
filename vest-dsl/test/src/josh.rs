#![allow(unused_imports)]
use vstd::prelude::*;
use vest::properties::*;
use vest::utils::*;
use vest::regular::map::*;
use vest::regular::tag::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::uints::*;
use vest::regular::tail::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::depend::*;
use vest::regular::and_then::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
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
        SpecMydata {
            foo,
            bar,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mydata<'a> {
    pub foo: &'a [u8],
    pub bar: &'a [u8],
}
pub type MydataInner<'a> = (&'a [u8], &'a [u8]);
impl View for Mydata<'_> {
    type V = SpecMydata;
    open spec fn view(&self) -> Self::V {
        SpecMydata {
            foo: self.foo@,
            bar: self.bar@,
        }
    }
}
impl<'a> From<Mydata<'a>> for MydataInner<'a> {
    fn ex_from(m: Mydata<'a>) -> MydataInner<'a> {
        (m.foo, m.bar)
    }
}
impl<'a> From<MydataInner<'a>> for Mydata<'a> {
    fn ex_from(m: MydataInner<'a>) -> Mydata<'a> {
        let (foo, bar) = m;
        Mydata {
            foo,
            bar,
        }
    }
}
pub struct MydataMapper;
impl View for MydataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso<'_> for MydataMapper {
    type Src = SpecMydataInner;
    type Dst = SpecMydata;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for MydataMapper {
    type Src<'a> = MydataInner<'a>;
    type Dst<'a> = Mydata<'a>;
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
impl View for TstMydata<'_> {
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
impl<'a> From<TstMydata<'a>> for TstMydataInner<'a> {
    fn ex_from(m: TstMydata<'a>) -> TstMydataInner<'a> {
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
impl SpecIso<'_> for TstMydataMapper {
    type Src = SpecTstMydataInner;
    type Dst = SpecTstMydata;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for TstMydataMapper {
    type Src<'a> = TstMydataInner<'a>;
    type Dst<'a> = TstMydata<'a>;
}

pub type SpecTstTag = u8;
pub type TstTag = u8;

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
        SpecTst {
            tag,
            mydata,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tst<'a> {
    pub tag: TstTag,
    pub mydata: TstMydata<'a>,
}
pub type TstInner<'a> = (TstTag, TstMydata<'a>);
impl View for Tst<'_> {
    type V = SpecTst;
    open spec fn view(&self) -> Self::V {
        SpecTst {
            tag: self.tag@,
            mydata: self.mydata@,
        }
    }
}
impl<'a> From<Tst<'a>> for TstInner<'a> {
    fn ex_from(m: Tst<'a>) -> TstInner<'a> {
        (m.tag, m.mydata)
    }
}
impl<'a> From<TstInner<'a>> for Tst<'a> {
    fn ex_from(m: TstInner<'a>) -> Tst<'a> {
        let (tag, mydata) = m;
        Tst {
            tag,
            mydata,
        }
    }
}
pub struct TstMapper;
impl View for TstMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso<'_> for TstMapper {
    type Src = SpecTstInner;
    type Dst = SpecTst;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for TstMapper {
    type Src<'a> = TstInner<'a>;
    type Dst<'a> = Tst<'a>;
}


pub type SpecMydataCombinator = Mapped<(BytesN<2>, BytesN<2>), MydataMapper>;

pub type MydataCombinator = Mapped<(BytesN<2>, BytesN<2>), MydataMapper>;































pub type SpecTstMydataCombinator = Mapped<OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>;






























pub type TstMydataCombinator = Mapped<OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, Cond<MydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>;

pub type SpecTstTagCombinator = U8;
pub type TstTagCombinator = U8;


pub type SpecTstCombinator = Mapped<SpecDepend<SpecTstTagCombinator, SpecTstMydataCombinator, SpecTstTag>, TstMapper>;

pub struct TstCont;pub type TstCombinator = Mapped<Depend<TstTagCombinator, TstMydataCombinator, TstTag, TstCont>, TstMapper>;

pub open spec fn spec_mydata() -> SpecMydataCombinator {
Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper }}

pub fn mydata() -> (o: MydataCombinator)
    ensures o@ == spec_mydata(),
{
Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper }}


pub open spec fn spec_tst_mydata(tag: SpecTstTag) -> SpecTstMydataCombinator {
Mapped { inner: OrdChoice(Cond { cond: tag == 0, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 1, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 2, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 3, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 4, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 5, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 6, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 7, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 8, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 9, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 10, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 11, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 12, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 13, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 14, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 15, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 16, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 17, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 18, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 19, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 20, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 21, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 22, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 23, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 24, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 25, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 26, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 27, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 28, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 29, inner: spec_mydata() }, Cond { cond: tag == 30, inner: spec_mydata() })))))))))))))))))))))))))))))), mapper: TstMydataMapper }}






























pub fn tst_mydata<'a>(tag: TstTag) -> (o: TstMydataCombinator)
    ensures o@ == spec_tst_mydata(tag@),
{
Mapped { inner: OrdChoice(Cond { cond: tag == 0, inner: mydata() }, OrdChoice(Cond { cond: tag == 1, inner: mydata() }, OrdChoice(Cond { cond: tag == 2, inner: mydata() }, OrdChoice(Cond { cond: tag == 3, inner: mydata() }, OrdChoice(Cond { cond: tag == 4, inner: mydata() }, OrdChoice(Cond { cond: tag == 5, inner: mydata() }, OrdChoice(Cond { cond: tag == 6, inner: mydata() }, OrdChoice(Cond { cond: tag == 7, inner: mydata() }, OrdChoice(Cond { cond: tag == 8, inner: mydata() }, OrdChoice(Cond { cond: tag == 9, inner: mydata() }, OrdChoice(Cond { cond: tag == 10, inner: mydata() }, OrdChoice(Cond { cond: tag == 11, inner: mydata() }, OrdChoice(Cond { cond: tag == 12, inner: mydata() }, OrdChoice(Cond { cond: tag == 13, inner: mydata() }, OrdChoice(Cond { cond: tag == 14, inner: mydata() }, OrdChoice(Cond { cond: tag == 15, inner: mydata() }, OrdChoice(Cond { cond: tag == 16, inner: mydata() }, OrdChoice(Cond { cond: tag == 17, inner: mydata() }, OrdChoice(Cond { cond: tag == 18, inner: mydata() }, OrdChoice(Cond { cond: tag == 19, inner: mydata() }, OrdChoice(Cond { cond: tag == 20, inner: mydata() }, OrdChoice(Cond { cond: tag == 21, inner: mydata() }, OrdChoice(Cond { cond: tag == 22, inner: mydata() }, OrdChoice(Cond { cond: tag == 23, inner: mydata() }, OrdChoice(Cond { cond: tag == 24, inner: mydata() }, OrdChoice(Cond { cond: tag == 25, inner: mydata() }, OrdChoice(Cond { cond: tag == 26, inner: mydata() }, OrdChoice(Cond { cond: tag == 27, inner: mydata() }, OrdChoice(Cond { cond: tag == 28, inner: mydata() }, OrdChoice(Cond { cond: tag == 29, inner: mydata() }, Cond { cond: tag == 30, inner: mydata() })))))))))))))))))))))))))))))), mapper: TstMydataMapper }}































pub open spec fn spec_tst_tag() -> SpecTstTagCombinator {
U8}
pub fn tst_tag() -> (o: TstTagCombinator)
    ensures o@ == spec_tst_tag(),
{
U8}

pub open spec fn spec_tst() -> SpecTstCombinator {
    let fst = spec_tst_tag();
    let snd = |deps| spec_tst_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: TstMapper }}

pub open spec fn spec_tst_cont(deps: SpecTstTag) -> SpecTstMydataCombinator {
    let tag = deps;
    spec_tst_mydata(tag)
}
                    pub fn tst() -> (o: TstCombinator)
    ensures o@ == spec_tst(),
{
   let fst = tst_tag();
    let snd = TstCont;
    let spec_snd = Ghost(|deps| spec_tst_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: TstMapper }}

impl Continuation<TstTag> for TstCont {
    type Output = TstMydataCombinator;

    open spec fn requires(&self, deps: TstTag) -> bool {
        true
    }

    open spec fn ensures(&self, deps: TstTag, o: Self::Output) -> bool {
        o@ == spec_tst_cont(deps@)
    }

    fn apply(&self, deps: TstTag) -> Self::Output {
        let tag = deps;
        tst_mydata(tag)
    }
}

                    
pub open spec fn parse_spec_mydata(i: Seq<u8>) -> Result<(usize, SpecMydata), ()> {
    spec_mydata().spec_parse(i)
}
pub open spec fn serialize_spec_mydata(msg: SpecMydata) -> Result<Seq<u8>, ()> {
    spec_mydata().spec_serialize(msg)
}
pub fn parse_mydata(i: &[u8]) -> (o: Result<(usize, Mydata<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_mydata(i@) matches Ok(r_) && r@ == r_,
{
    mydata().parse(i)
}

pub fn serialize_mydata(msg: Mydata<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_mydata(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    mydata().serialize(msg, data, pos)
}
pub open spec fn parse_spec_tst_mydata(i: Seq<u8>, tag: SpecTstTag) -> Result<(usize, SpecTstMydata), ()> {
    spec_tst_mydata(tag).spec_parse(i)
}
pub open spec fn serialize_spec_tst_mydata(msg: SpecTstMydata, tag: SpecTstTag) -> Result<Seq<u8>, ()> {
    spec_tst_mydata(tag).spec_serialize(msg)
}
pub fn parse_tst_mydata(i: &[u8], tag: TstTag) -> (o: Result<(usize, TstMydata<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_tst_mydata(i@, tag@) matches Ok(r_) && r@ == r_,
{
    tst_mydata(tag).parse(i)
}

pub fn serialize_tst_mydata(msg: TstMydata<'_>, data: &mut Vec<u8>, pos: usize, tag: TstTag) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst_mydata(msg@, tag@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    tst_mydata(tag).serialize(msg, data, pos)
}
pub open spec fn parse_spec_tst_tag(i: Seq<u8>) -> Result<(usize, SpecTstTag), ()> {
    spec_tst_tag().spec_parse(i)
}
pub open spec fn serialize_spec_tst_tag(msg: SpecTstTag) -> Result<Seq<u8>, ()> {
    spec_tst_tag().spec_serialize(msg)
}
pub fn parse_tst_tag(i: &[u8]) -> (o: Result<(usize, TstTag), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_tst_tag(i@) matches Ok(r_) && r@ == r_,
{
    tst_tag().parse(i)
}

pub fn serialize_tst_tag(msg: TstTag, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst_tag(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    tst_tag().serialize(msg, data, pos)
}
pub open spec fn parse_spec_tst(i: Seq<u8>) -> Result<(usize, SpecTst), ()> {
    spec_tst().spec_parse(i)
}
pub open spec fn serialize_spec_tst(msg: SpecTst) -> Result<Seq<u8>, ()> {
    spec_tst().spec_serialize(msg)
}
pub fn parse_tst(i: &[u8]) -> (o: Result<(usize, Tst<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_tst(i@) matches Ok(r_) && r@ == r_,
{
    tst().parse(i)
}

pub fn serialize_tst(msg: Tst<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    tst().serialize(msg, data, pos)
}

}
