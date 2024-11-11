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
impl SpecIso for MydataMapper {
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
    type SrcOwned = MydataOwnedInner;
    type DstOwned = MydataOwned;
}
pub struct MydataOwned {
    pub foo: Vec<u8>,
    pub bar: Vec<u8>,
}
pub type MydataOwnedInner = (Vec<u8>, Vec<u8>);
impl View for MydataOwned {
    type V = SpecMydata;
    open spec fn view(&self) -> Self::V {
        SpecMydata {
            foo: self.foo@,
            bar: self.bar@,
        }
    }
}
impl From<MydataOwned> for MydataOwnedInner {
    fn ex_from(m: MydataOwned) -> MydataOwnedInner {
        (m.foo, m.bar)
    }
}
impl From<MydataOwnedInner> for MydataOwned {
    fn ex_from(m: MydataOwnedInner) -> MydataOwned {
        let (foo, bar) = m;
        MydataOwned {
            foo,
            bar,
        }
    }
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
impl SpecIso for TstMydataMapper {
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
    type SrcOwned = TstMydataOwnedInner;
    type DstOwned = TstMydataOwned;
}
pub enum TstMydataOwned {
    C0(MydataOwned),
    C1(MydataOwned),
    C2(MydataOwned),
    C3(MydataOwned),
    C4(MydataOwned),
    C5(MydataOwned),
    C6(MydataOwned),
    C7(MydataOwned),
    C8(MydataOwned),
    C9(MydataOwned),
    C10(MydataOwned),
    C11(MydataOwned),
    C12(MydataOwned),
    C13(MydataOwned),
    C14(MydataOwned),
    C15(MydataOwned),
    C16(MydataOwned),
    C17(MydataOwned),
    C18(MydataOwned),
    C19(MydataOwned),
    C20(MydataOwned),
    C21(MydataOwned),
    C22(MydataOwned),
    C23(MydataOwned),
    C24(MydataOwned),
    C25(MydataOwned),
    C26(MydataOwned),
    C27(MydataOwned),
    C28(MydataOwned),
    C29(MydataOwned),
    C30(MydataOwned),
}
pub type TstMydataOwnedInner = Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, Either<MydataOwned, MydataOwned>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for TstMydataOwned {
    type V = SpecTstMydata;
    open spec fn view(&self) -> Self::V {
        match self {
            TstMydataOwned::C0(m) => SpecTstMydata::C0(m@),
            TstMydataOwned::C1(m) => SpecTstMydata::C1(m@),
            TstMydataOwned::C2(m) => SpecTstMydata::C2(m@),
            TstMydataOwned::C3(m) => SpecTstMydata::C3(m@),
            TstMydataOwned::C4(m) => SpecTstMydata::C4(m@),
            TstMydataOwned::C5(m) => SpecTstMydata::C5(m@),
            TstMydataOwned::C6(m) => SpecTstMydata::C6(m@),
            TstMydataOwned::C7(m) => SpecTstMydata::C7(m@),
            TstMydataOwned::C8(m) => SpecTstMydata::C8(m@),
            TstMydataOwned::C9(m) => SpecTstMydata::C9(m@),
            TstMydataOwned::C10(m) => SpecTstMydata::C10(m@),
            TstMydataOwned::C11(m) => SpecTstMydata::C11(m@),
            TstMydataOwned::C12(m) => SpecTstMydata::C12(m@),
            TstMydataOwned::C13(m) => SpecTstMydata::C13(m@),
            TstMydataOwned::C14(m) => SpecTstMydata::C14(m@),
            TstMydataOwned::C15(m) => SpecTstMydata::C15(m@),
            TstMydataOwned::C16(m) => SpecTstMydata::C16(m@),
            TstMydataOwned::C17(m) => SpecTstMydata::C17(m@),
            TstMydataOwned::C18(m) => SpecTstMydata::C18(m@),
            TstMydataOwned::C19(m) => SpecTstMydata::C19(m@),
            TstMydataOwned::C20(m) => SpecTstMydata::C20(m@),
            TstMydataOwned::C21(m) => SpecTstMydata::C21(m@),
            TstMydataOwned::C22(m) => SpecTstMydata::C22(m@),
            TstMydataOwned::C23(m) => SpecTstMydata::C23(m@),
            TstMydataOwned::C24(m) => SpecTstMydata::C24(m@),
            TstMydataOwned::C25(m) => SpecTstMydata::C25(m@),
            TstMydataOwned::C26(m) => SpecTstMydata::C26(m@),
            TstMydataOwned::C27(m) => SpecTstMydata::C27(m@),
            TstMydataOwned::C28(m) => SpecTstMydata::C28(m@),
            TstMydataOwned::C29(m) => SpecTstMydata::C29(m@),
            TstMydataOwned::C30(m) => SpecTstMydata::C30(m@),
        }
    }
}
impl From<TstMydataOwned> for TstMydataOwnedInner {
    fn ex_from(m: TstMydataOwned) -> TstMydataOwnedInner {
        match m {
            TstMydataOwned::C0(m) => Either::Left(m),
            TstMydataOwned::C1(m) => Either::Right(Either::Left(m)),
            TstMydataOwned::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            TstMydataOwned::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            TstMydataOwned::C4(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            TstMydataOwned::C5(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            TstMydataOwned::C6(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            TstMydataOwned::C7(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            TstMydataOwned::C8(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            TstMydataOwned::C9(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            TstMydataOwned::C10(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            TstMydataOwned::C11(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            TstMydataOwned::C12(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            TstMydataOwned::C13(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            TstMydataOwned::C14(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            TstMydataOwned::C15(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            TstMydataOwned::C16(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            TstMydataOwned::C17(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            TstMydataOwned::C18(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            TstMydataOwned::C19(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            TstMydataOwned::C20(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            TstMydataOwned::C21(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            TstMydataOwned::C22(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            TstMydataOwned::C23(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            TstMydataOwned::C24(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            TstMydataOwned::C25(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            TstMydataOwned::C26(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))),
            TstMydataOwned::C27(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))),
            TstMydataOwned::C28(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))),
            TstMydataOwned::C29(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))),
            TstMydataOwned::C30(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))),
        }
    }
}
impl From<TstMydataOwnedInner> for TstMydataOwned {
    fn ex_from(m: TstMydataOwnedInner) -> TstMydataOwned {
        match m {
            Either::Left(m) => TstMydataOwned::C0(m),
            Either::Right(Either::Left(m)) => TstMydataOwned::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => TstMydataOwned::C2(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => TstMydataOwned::C3(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => TstMydataOwned::C4(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => TstMydataOwned::C5(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => TstMydataOwned::C6(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => TstMydataOwned::C7(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => TstMydataOwned::C8(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => TstMydataOwned::C9(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => TstMydataOwned::C10(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => TstMydataOwned::C11(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => TstMydataOwned::C12(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => TstMydataOwned::C13(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => TstMydataOwned::C14(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => TstMydataOwned::C15(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => TstMydataOwned::C16(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => TstMydataOwned::C17(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => TstMydataOwned::C18(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => TstMydataOwned::C19(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => TstMydataOwned::C20(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => TstMydataOwned::C21(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => TstMydataOwned::C22(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => TstMydataOwned::C23(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => TstMydataOwned::C24(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => TstMydataOwned::C25(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))) => TstMydataOwned::C26(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))) => TstMydataOwned::C27(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))))))) => TstMydataOwned::C28(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))))))) => TstMydataOwned::C29(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))))))) => TstMydataOwned::C30(m),
        }
    }
}

pub type SpecTstTag = u8;
pub type TstTag = u8;
pub type TstTagOwned = u8;

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
impl SpecIso for TstMapper {
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
    type SrcOwned = TstOwnedInner;
    type DstOwned = TstOwned;
}
pub struct TstOwned {
    pub tag: TstTagOwned,
    pub mydata: TstMydataOwned,
}
pub type TstOwnedInner = (TstTagOwned, TstMydataOwned);
impl View for TstOwned {
    type V = SpecTst;
    open spec fn view(&self) -> Self::V {
        SpecTst {
            tag: self.tag@,
            mydata: self.mydata@,
        }
    }
}
impl From<TstOwned> for TstOwnedInner {
    fn ex_from(m: TstOwned) -> TstOwnedInner {
        (m.tag, m.mydata)
    }
}
impl From<TstOwnedInner> for TstOwned {
    fn ex_from(m: TstOwnedInner) -> TstOwned {
        let (tag, mydata) = m;
        TstOwned {
            tag,
            mydata,
        }
    }
}



pub struct SpecMydataCombinator(Mapped<(BytesN<2>, BytesN<2>), MydataMapper>);

impl SpecCombinator for SpecMydataCombinator {
    type SpecResult = SpecMydata;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMydataCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMydataCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

                pub type SpecMydataCombinatorAlias = Mapped<(BytesN<2>, BytesN<2>), MydataMapper>;


pub struct MydataCombinator(Mapped<(BytesN<2>, BytesN<2>), MydataMapper>);

impl View for MydataCombinator {
    type V = SpecMydataCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMydataCombinator(self.0@)
    }
}
impl Combinator for MydataCombinator {
    type Result<'a> = Mydata<'a>;

    type Owned = MydataOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {
        self.0.serialize(v, data, pos)
    }

}
                pub type MydataCombinatorAlias = Mapped<(BytesN<2>, BytesN<2>), MydataMapper>;
































pub struct SpecTstMydataCombinator(Mapped<OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>);

impl SpecCombinator for SpecTstMydataCombinator {
    type SpecResult = SpecTstMydata;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTstMydataCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecTstMydataCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

                pub type SpecTstMydataCombinatorAlias = Mapped<OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, OrdChoice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>;































pub struct TstMydataCombinator(Mapped<OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, Cond<MydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>);

impl View for TstMydataCombinator {
    type V = SpecTstMydataCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecTstMydataCombinator(self.0@)
    }
}
impl Combinator for TstMydataCombinator {
    type Result<'a> = TstMydata<'a>;

    type Owned = TstMydataOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {
        self.0.serialize(v, data, pos)
    }

}
                pub type TstMydataCombinatorAlias = Mapped<OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, OrdChoice<Cond<MydataCombinator>, Cond<MydataCombinator>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>, TstMydataMapper>;


pub struct SpecTstTagCombinator(U8);

impl SpecCombinator for SpecTstTagCombinator {
    type SpecResult = SpecTstTag;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTstTagCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecTstTagCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

                pub type SpecTstTagCombinatorAlias = U8;

pub struct TstTagCombinator(U8);

impl View for TstTagCombinator {
    type V = SpecTstTagCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecTstTagCombinator(self.0@)
    }
}
impl Combinator for TstTagCombinator {
    type Result<'a> = TstTag;

    type Owned = TstTagOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {
        self.0.serialize(v, data, pos)
    }

}
                pub type TstTagCombinatorAlias = U8;



pub struct SpecTstCombinator(Mapped<SpecDepend<SpecTstTagCombinator, SpecTstMydataCombinator>, TstMapper>);

impl SpecCombinator for SpecTstCombinator {
    type SpecResult = SpecTst;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTstCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecTstCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

                pub type SpecTstCombinatorAlias = Mapped<SpecDepend<SpecTstTagCombinator, SpecTstMydataCombinator>, TstMapper>;

pub struct TstCont;
pub struct TstCombinator(Mapped<Depend<TstTagCombinator, TstMydataCombinator, TstCont>, TstMapper>);

impl View for TstCombinator {
    type V = SpecTstCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecTstCombinator(self.0@)
    }
}
impl Combinator for TstCombinator {
    type Result<'a> = Tst<'a>;

    type Owned = TstOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    {
        self.0.serialize(v, data, pos)
    }

}
                pub type TstCombinatorAlias = Mapped<Depend<TstTagCombinator, TstMydataCombinator, TstCont>, TstMapper>;


pub closed spec fn spec_mydata() -> SpecMydataCombinator {
    SpecMydataCombinator(Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper })
}



                
pub fn mydata() -> (o: MydataCombinator)
    ensures o@ == spec_mydata(),
{
    MydataCombinator(Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper })
}



                

pub closed spec fn spec_tst_mydata(tag: SpecTstTag) -> SpecTstMydataCombinator {
    SpecTstMydataCombinator(Mapped { inner: OrdChoice(Cond { cond: tag == 0, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 1, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 2, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 3, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 4, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 5, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 6, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 7, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 8, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 9, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 10, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 11, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 12, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 13, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 14, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 15, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 16, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 17, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 18, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 19, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 20, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 21, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 22, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 23, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 24, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 25, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 26, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 27, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 28, inner: spec_mydata() }, OrdChoice(Cond { cond: tag == 29, inner: spec_mydata() }, Cond { cond: tag == 30, inner: spec_mydata() })))))))))))))))))))))))))))))), mapper: TstMydataMapper })
}
































                
pub fn tst_mydata<'a>(tag: TstTag) -> (o: TstMydataCombinator)
    ensures o@ == spec_tst_mydata(tag@),
{
    TstMydataCombinator(Mapped { inner: OrdChoice(Cond { cond: tag == 0, inner: mydata() }, OrdChoice(Cond { cond: tag == 1, inner: mydata() }, OrdChoice(Cond { cond: tag == 2, inner: mydata() }, OrdChoice(Cond { cond: tag == 3, inner: mydata() }, OrdChoice(Cond { cond: tag == 4, inner: mydata() }, OrdChoice(Cond { cond: tag == 5, inner: mydata() }, OrdChoice(Cond { cond: tag == 6, inner: mydata() }, OrdChoice(Cond { cond: tag == 7, inner: mydata() }, OrdChoice(Cond { cond: tag == 8, inner: mydata() }, OrdChoice(Cond { cond: tag == 9, inner: mydata() }, OrdChoice(Cond { cond: tag == 10, inner: mydata() }, OrdChoice(Cond { cond: tag == 11, inner: mydata() }, OrdChoice(Cond { cond: tag == 12, inner: mydata() }, OrdChoice(Cond { cond: tag == 13, inner: mydata() }, OrdChoice(Cond { cond: tag == 14, inner: mydata() }, OrdChoice(Cond { cond: tag == 15, inner: mydata() }, OrdChoice(Cond { cond: tag == 16, inner: mydata() }, OrdChoice(Cond { cond: tag == 17, inner: mydata() }, OrdChoice(Cond { cond: tag == 18, inner: mydata() }, OrdChoice(Cond { cond: tag == 19, inner: mydata() }, OrdChoice(Cond { cond: tag == 20, inner: mydata() }, OrdChoice(Cond { cond: tag == 21, inner: mydata() }, OrdChoice(Cond { cond: tag == 22, inner: mydata() }, OrdChoice(Cond { cond: tag == 23, inner: mydata() }, OrdChoice(Cond { cond: tag == 24, inner: mydata() }, OrdChoice(Cond { cond: tag == 25, inner: mydata() }, OrdChoice(Cond { cond: tag == 26, inner: mydata() }, OrdChoice(Cond { cond: tag == 27, inner: mydata() }, OrdChoice(Cond { cond: tag == 28, inner: mydata() }, OrdChoice(Cond { cond: tag == 29, inner: mydata() }, Cond { cond: tag == 30, inner: mydata() })))))))))))))))))))))))))))))), mapper: TstMydataMapper })
}
































                

pub closed spec fn spec_tst_tag() -> SpecTstTagCombinator {
    SpecTstTagCombinator(U8)
}


                
pub fn tst_tag() -> (o: TstTagCombinator)
    ensures o@ == spec_tst_tag(),
{
    TstTagCombinator(U8)
}


                

pub closed spec fn spec_tst() -> SpecTstCombinator {
    SpecTstCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_tst_tag(),
            snd: |deps| spec_tst_cont(deps),
        },
        mapper: TstMapper,
    }
)
}


pub open spec fn spec_tst_cont(deps: SpecTstTag) -> SpecTstMydataCombinator {
    let tag = deps;
    spec_tst_mydata(tag)
}
                    
                
pub fn tst() -> (o: TstCombinator)
    ensures o@ == spec_tst(),
{
    TstCombinator(
    Mapped {
        inner: Depend {
            fst: tst_tag(),
            snd: TstCont,
            spec_snd: Ghost(|deps| spec_tst_cont(deps)),
        },
        mapper: TstMapper,
    }
)
}


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

                    
                

}
