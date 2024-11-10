#![allow(unused_imports)]
use std::marker::PhantomData;
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

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

pub type MydataInner<'a> = (&'a [u8], &'a [u8]);

impl View for Mydata<'_> {
    type V = SpecMydata;

    open spec fn view(&self) -> Self::V {
        SpecMydata { foo: self.foo@, bar: self.bar@ }
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
        Mydata { foo, bar }
    }
}

pub struct MydataMapper<'a>(PhantomData<&'a ()>);

impl<'a> MydataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MydataMapper(PhantomData)
    }

    pub fn new() -> Self {
        MydataMapper(PhantomData)
    }
}

impl View for MydataMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MydataMapper<'_> {
    type Src = SpecMydataInner;

    type Dst = SpecMydata;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MydataMapper<'a> {
    type Src = MydataInner<'a>;

    type Dst = Mydata<'a>;
}

pub type SpecMydataCombinator = Mapped<(BytesN<2>, BytesN<2>), MydataMapper<'static>>;

pub type MydataCombinator<'a> = Mapped<(BytesN<2>, BytesN<2>), MydataMapper<'a>>;

pub open spec fn spec_mydata() -> SpecMydataCombinator {
    Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper::spec_new() }
}

pub fn mydata<'a>() -> (o: MydataCombinator<'a>)
    ensures
        o@ == spec_mydata(),
{
    Mapped { inner: (BytesN::<2>, BytesN::<2>), mapper: MydataMapper::new() }
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
    let c = mydata();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_mydata(msg: Mydata<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_mydata(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = mydata();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub type SpecTstTag = u8;

pub type TstTag = u8;

pub type SpecTstTagCombinator = U8;

pub type TstTagCombinator = U8;

pub open spec fn spec_tst_tag() -> SpecTstTagCombinator {
    U8
}

pub fn tst_tag() -> (o: TstTagCombinator)
    ensures
        o@ == spec_tst_tag(),
{
    U8
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
    let c = tst_tag();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_tst_tag(msg: TstTag, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst_tag(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = tst_tag();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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
}

pub type SpecTstMydataInner = Either<
    SpecMydata,
    Either<
        SpecMydata,
        Either<
            SpecMydata,
            Either<
                SpecMydata,
                Either<
                    SpecMydata,
                    Either<SpecMydata, Either<SpecMydata, Either<SpecMydata, SpecMydata>>>,
                >,
            >,
        >,
    >,
>;

impl SpecFrom<SpecTstMydata> for SpecTstMydataInner {
    open spec fn spec_from(m: SpecTstMydata) -> SpecTstMydataInner {
        match m {
            SpecTstMydata::C0(m) => Either::Left(m),
            SpecTstMydata::C1(m) => Either::Right(Either::Left(m)),
            SpecTstMydata::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecTstMydata::C3(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecTstMydata::C4(m) => Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ),
            SpecTstMydata::C5(m) => Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ),
            SpecTstMydata::C6(m) => Either::Right(
                Either::Right(
                    Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                ),
            ),
            SpecTstMydata::C7(m) => Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                    ),
                ),
            ),
            SpecTstMydata::C8(m) => Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(
                            Either::Right(Either::Right(Either::Right(Either::Right(m)))),
                        ),
                    ),
                ),
            ),
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
            Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ) => SpecTstMydata::C4(m),
            Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ) => SpecTstMydata::C5(m),
            Either::Right(
                Either::Right(
                    Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                ),
            ) => SpecTstMydata::C6(m),
            Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                    ),
                ),
            ) => SpecTstMydata::C7(m),
            Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(
                            Either::Right(Either::Right(Either::Right(Either::Right(m)))),
                        ),
                    ),
                ),
            ) => SpecTstMydata::C8(m),
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
}

pub type TstMydataInner<'a> = Either<
    Mydata<'a>,
    Either<
        Mydata<'a>,
        Either<
            Mydata<'a>,
            Either<
                Mydata<'a>,
                Either<
                    Mydata<'a>,
                    Either<Mydata<'a>, Either<Mydata<'a>, Either<Mydata<'a>, Mydata<'a>>>>,
                >,
            >,
        >,
    >,
>;

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
            TstMydata::C4(m) => Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ),
            TstMydata::C5(m) => Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ),
            TstMydata::C6(m) => Either::Right(
                Either::Right(
                    Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                ),
            ),
            TstMydata::C7(m) => Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                    ),
                ),
            ),
            TstMydata::C8(m) => Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(
                            Either::Right(Either::Right(Either::Right(Either::Right(m)))),
                        ),
                    ),
                ),
            ),
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
            Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ) => TstMydata::C4(m),
            Either::Right(
                Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ) => TstMydata::C5(m),
            Either::Right(
                Either::Right(
                    Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                ),
            ) => TstMydata::C6(m),
            Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
                    ),
                ),
            ) => TstMydata::C7(m),
            Either::Right(
                Either::Right(
                    Either::Right(
                        Either::Right(
                            Either::Right(Either::Right(Either::Right(Either::Right(m)))),
                        ),
                    ),
                ),
            ) => TstMydata::C8(m),
        }
    }
}

pub struct TstMydataMapper<'a>(PhantomData<&'a ()>);

impl<'a> TstMydataMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TstMydataMapper(PhantomData)
    }

    pub fn new() -> Self {
        TstMydataMapper(PhantomData)
    }
}

impl View for TstMydataMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for TstMydataMapper<'_> {
    type Src = SpecTstMydataInner;

    type Dst = SpecTstMydata;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for TstMydataMapper<'a> {
    type Src = TstMydataInner<'a>;

    type Dst = TstMydata<'a>;
}

pub type SpecTstMydataCombinator = Mapped<
    OrdChoice<
        Cond<SpecMydataCombinator>,
        OrdChoice<
            Cond<SpecMydataCombinator>,
            OrdChoice<
                Cond<SpecMydataCombinator>,
                OrdChoice<
                    Cond<SpecMydataCombinator>,
                    OrdChoice<
                        Cond<SpecMydataCombinator>,
                        OrdChoice<
                            Cond<SpecMydataCombinator>,
                            OrdChoice<
                                Cond<SpecMydataCombinator>,
                                OrdChoice<Cond<SpecMydataCombinator>, Cond<SpecMydataCombinator>>,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
    TstMydataMapper<'static>,
>;

pub type TstMydataCombinator<'a> = Mapped<
    OrdChoice<
        Cond<MydataCombinator<'a>>,
        OrdChoice<
            Cond<MydataCombinator<'a>>,
            OrdChoice<
                Cond<MydataCombinator<'a>>,
                OrdChoice<
                    Cond<MydataCombinator<'a>>,
                    OrdChoice<
                        Cond<MydataCombinator<'a>>,
                        OrdChoice<
                            Cond<MydataCombinator<'a>>,
                            OrdChoice<
                                Cond<MydataCombinator<'a>>,
                                OrdChoice<Cond<MydataCombinator<'a>>, Cond<MydataCombinator<'a>>>,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
    TstMydataMapper<'a>,
>;

pub open spec fn spec_tst_mydata(tag: SpecTstTag) -> SpecTstMydataCombinator {
    Mapped {
        inner: OrdChoice(
            Cond { cond: tag == 0, inner: spec_mydata() },
            OrdChoice(
                Cond { cond: tag == 1, inner: spec_mydata() },
                OrdChoice(
                    Cond { cond: tag == 2, inner: spec_mydata() },
                    OrdChoice(
                        Cond { cond: tag == 3, inner: spec_mydata() },
                        OrdChoice(
                            Cond { cond: tag == 4, inner: spec_mydata() },
                            OrdChoice(
                                Cond { cond: tag == 5, inner: spec_mydata() },
                                OrdChoice(
                                    Cond { cond: tag == 6, inner: spec_mydata() },
                                    OrdChoice(
                                        Cond { cond: tag == 7, inner: spec_mydata() },
                                        Cond { cond: tag == 8, inner: spec_mydata() },
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        mapper: TstMydataMapper::spec_new(),
    }
}

pub fn tst_mydata<'a>(tag: TstTag) -> (o: TstMydataCombinator<'a>)
    ensures
        o@ == spec_tst_mydata(tag@),
{
    Mapped {
        inner: OrdChoice(
            Cond { cond: tag == 0, inner: mydata() },
            OrdChoice(
                Cond { cond: tag == 1, inner: mydata() },
                OrdChoice(
                    Cond { cond: tag == 2, inner: mydata() },
                    OrdChoice(
                        Cond { cond: tag == 3, inner: mydata() },
                        OrdChoice(
                            Cond { cond: tag == 4, inner: mydata() },
                            OrdChoice(
                                Cond { cond: tag == 5, inner: mydata() },
                                OrdChoice(
                                    Cond { cond: tag == 6, inner: mydata() },
                                    OrdChoice(
                                        Cond { cond: tag == 7, inner: mydata() },
                                        Cond { cond: tag == 8, inner: mydata() },
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        mapper: TstMydataMapper::new(),
    }
}

pub open spec fn parse_spec_tst_mydata(i: Seq<u8>, tag: SpecTstTag) -> Result<
    (usize, SpecTstMydata),
    (),
> {
    spec_tst_mydata(tag).spec_parse(i)
}

pub open spec fn serialize_spec_tst_mydata(msg: SpecTstMydata, tag: SpecTstTag) -> Result<
    Seq<u8>,
    (),
> {
    spec_tst_mydata(tag).spec_serialize(msg)
}

pub fn parse_tst_mydata(i: &[u8], tag: TstTag) -> (o: Result<(usize, TstMydata<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_tst_mydata(i@, tag@) matches Ok(r_) && r@ == r_,
{
    let c = tst_mydata(tag);
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_tst_mydata(msg: TstMydata<'_>, data: &mut Vec<u8>, pos: usize, tag: TstTag) -> (o:
    Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst_mydata(msg@, tag@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = tst_mydata(tag);
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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

pub type TstInner<'a> = (TstTag, TstMydata<'a>);

impl View for Tst<'_> {
    type V = SpecTst;

    open spec fn view(&self) -> Self::V {
        SpecTst { tag: self.tag@, mydata: self.mydata@ }
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
        Tst { tag, mydata }
    }
}

pub struct TstMapper<'a>(PhantomData<&'a ()>);

impl<'a> TstMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        TstMapper(PhantomData)
    }

    pub fn new() -> Self {
        TstMapper(PhantomData)
    }
}

impl View for TstMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for TstMapper<'_> {
    type Src = SpecTstInner;

    type Dst = SpecTst;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for TstMapper<'a> {
    type Src = TstInner<'a>;

    type Dst = Tst<'a>;
}

pub type SpecTstCombinator = Mapped<
    SpecDepend<SpecTstTagCombinator, SpecTstMydataCombinator>,
    TstMapper<'static>,
>;

pub type TstCombinator<'a> = Mapped<
    Depend<'a, TstTagCombinator, TstMydataCombinator<'a>, TstCont<'a>>,
    TstMapper<'a>,
>;

pub open spec fn spec_tst() -> SpecTstCombinator {
    let fst = spec_tst_tag();
    let snd = |deps| spec_tst_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: TstMapper::spec_new() }
}

pub open spec fn spec_tst_cont(deps: SpecTstTag) -> SpecTstMydataCombinator {
    let tag = deps;
    spec_tst_mydata(tag)
}

pub fn tst<'a>() -> (o: TstCombinator<'a>)
    ensures
        o@ == spec_tst(),
{
    let fst = tst_tag();
    let snd = TstCont::new();
    let spec_snd = Ghost(|deps| spec_tst_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: TstMapper::new() }
}

pub struct TstCont<'a>(PhantomData<&'a ()>);

impl<'a> TstCont<'a> {
    pub fn new() -> Self {
        TstCont(PhantomData)
    }
}

impl<'a> Continuation<TstTag> for TstCont<'a> {
    type Output = TstMydataCombinator<'a>;

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
    let c = tst();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_tst(msg: Tst<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_tst(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = tst();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

} // verus!
