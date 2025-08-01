#![allow(unused_imports)]

use vest::properties::*;
use vest::regular::bytes;
use vest::regular::modifier::*;
use vest::regular::repetition::*;
use vest::regular::sequence::*;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::regular::variant::*;
use vest::utils::*;
use vstd::prelude::*;

verus! {

pub struct SpecMsgD {
    pub f1: Seq<u8>,
    pub f2: u16,
}

pub type SpecMsgDInner = (Seq<u8>, u16);

impl SpecFrom<SpecMsgD> for SpecMsgDInner {
    open spec fn spec_from(m: SpecMsgD) -> SpecMsgDInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgDInner> for SpecMsgD {
    open spec fn spec_from(m: SpecMsgDInner) -> SpecMsgD {
        let (f1, f2) = m;
        SpecMsgD { f1, f2 }
    }
}

pub struct MsgD<'a> {
    pub f1: &'a [u8],
    pub f2: u16,
}

pub type MsgDInner<'a> = (&'a [u8], u16);

impl View for MsgD<'_> {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgD<'a>> for MsgDInner<'a> {
    fn ex_from(m: MsgD<'a>) -> MsgDInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner<'a>) -> MsgD<'a> {
        let (f1, f2) = m;
        MsgD { f1, f2 }
    }
}

pub struct MsgDMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgDMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for MsgDMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgDMapper<'_> {
    type Src = SpecMsgDInner;

    type Dst = SpecMsgD;
}

impl SpecIsoProof for MsgDMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MsgDMapper<'a> {
    type Src = MsgDInner<'a>;

    type Dst = MsgD<'a>;
}

pub struct SpecMsgB {
    pub f1: SpecMsgD,
}

pub type SpecMsgBInner = SpecMsgD;

impl SpecFrom<SpecMsgB> for SpecMsgBInner {
    open spec fn spec_from(m: SpecMsgB) -> SpecMsgBInner {
        m.f1
    }
}

impl SpecFrom<SpecMsgBInner> for SpecMsgB {
    open spec fn spec_from(m: SpecMsgBInner) -> SpecMsgB {
        let f1 = m;
        SpecMsgB { f1 }
    }
}

pub struct MsgB<'a> {
    pub f1: MsgD<'a>,
}

pub type MsgBInner<'a> = MsgD<'a>;

impl View for MsgB<'_> {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

impl<'a> From<MsgB<'a>> for MsgBInner<'a> {
    fn ex_from(m: MsgB<'a>) -> MsgBInner<'a> {
        m.f1
    }
}

impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner<'a>) -> MsgB<'a> {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgBMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for MsgBMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgBMapper<'_> {
    type Src = SpecMsgBInner;

    type Dst = SpecMsgB;
}

impl SpecIsoProof for MsgBMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MsgBMapper<'a> {
    type Src = MsgBInner<'a>;

    type Dst = MsgB<'a>;
}

pub type SpecContent0 = Seq<u8>;

pub type Content0<'a> = &'a [u8];

pub type SpecContentType = u8;

pub type ContentType = u8;

pub enum SpecMsgCF4 {
    C0(SpecContent0),
    C1(u16),
    C2(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecMsgCF4Inner = Either<SpecContent0, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecMsgCF4> for SpecMsgCF4Inner {
    open spec fn spec_from(m: SpecMsgCF4) -> SpecMsgCF4Inner {
        match m {
            SpecMsgCF4::C0(m) => Either::Left(m),
            SpecMsgCF4::C1(m) => Either::Right(Either::Left(m)),
            SpecMsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl SpecFrom<SpecMsgCF4Inner> for SpecMsgCF4 {
    open spec fn spec_from(m: SpecMsgCF4Inner) -> SpecMsgCF4 {
        match m {
            Either::Left(m) => SpecMsgCF4::C0(m),
            Either::Right(Either::Left(m)) => SpecMsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecMsgCF4::Unrecognized(m),
        }
    }
}

pub enum MsgCF4<'a> {
    C0(Content0<'a>),
    C1(u16),
    C2(u32),
    Unrecognized(&'a [u8]),
}

pub type MsgCF4Inner<'a> = Either<Content0<'a>, Either<u16, Either<u32, &'a [u8]>>>;

impl View for MsgCF4<'_> {
    type V = SpecMsgCF4;

    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}

impl<'a> From<MsgCF4<'a>> for MsgCF4Inner<'a> {
    fn ex_from(m: MsgCF4<'a>) -> MsgCF4Inner<'a> {
        match m {
            MsgCF4::C0(m) => Either::Left(m),
            MsgCF4::C1(m) => Either::Right(Either::Left(m)),
            MsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            MsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl<'a> From<MsgCF4Inner<'a>> for MsgCF4<'a> {
    fn ex_from(m: MsgCF4Inner<'a>) -> MsgCF4<'a> {
        match m {
            Either::Left(m) => MsgCF4::C0(m),
            Either::Right(Either::Left(m)) => MsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => MsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => MsgCF4::Unrecognized(m),
        }
    }
}

pub struct MsgCF4Mapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgCF4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for MsgCF4Mapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCF4Mapper<'_> {
    type Src = SpecMsgCF4Inner;

    type Dst = SpecMsgCF4;
}

impl SpecIsoProof for MsgCF4Mapper<'_> {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MsgCF4Mapper<'a> {
    type Src = MsgCF4Inner<'a>;

    type Dst = MsgCF4<'a>;
}

pub struct SpecMsgC {
    pub f2: SpecContentType,
    pub f3: u24,
    pub f4: SpecMsgCF4,
}

pub type SpecMsgCInner = ((SpecContentType, u24), SpecMsgCF4);

impl SpecFrom<SpecMsgC> for SpecMsgCInner {
    open spec fn spec_from(m: SpecMsgC) -> SpecMsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl SpecFrom<SpecMsgCInner> for SpecMsgC {
    open spec fn spec_from(m: SpecMsgCInner) -> SpecMsgC {
        let ((f2, f3), f4) = m;
        SpecMsgC { f2, f3, f4 }
    }
}

pub struct MsgC<'a> {
    pub f2: ContentType,
    pub f3: u24,
    pub f4: MsgCF4<'a>,
}

pub type MsgCInner<'a> = ((ContentType, u24), MsgCF4<'a>);

impl View for MsgC<'_> {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

impl<'a> From<MsgC<'a>> for MsgCInner<'a> {
    fn ex_from(m: MsgC<'a>) -> MsgCInner<'a> {
        ((m.f2, m.f3), m.f4)
    }
}

impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner<'a>) -> MsgC<'a> {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgCMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for MsgCMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCMapper<'_> {
    type Src = SpecMsgCInner;

    type Dst = SpecMsgC;
}

impl SpecIsoProof for MsgCMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MsgCMapper<'a> {
    type Src = MsgCInner<'a>;

    type Dst = MsgC<'a>;
}

pub struct SpecMsgA {
    pub f1: SpecMsgB,
    pub f2: Seq<u8>,
}

pub type SpecMsgAInner = (SpecMsgB, Seq<u8>);

impl SpecFrom<SpecMsgA> for SpecMsgAInner {
    open spec fn spec_from(m: SpecMsgA) -> SpecMsgAInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgAInner> for SpecMsgA {
    open spec fn spec_from(m: SpecMsgAInner) -> SpecMsgA {
        let (f1, f2) = m;
        SpecMsgA { f1, f2 }
    }
}

pub struct MsgA<'a> {
    pub f1: MsgB<'a>,
    pub f2: &'a [u8],
}

pub type MsgAInner<'a> = (MsgB<'a>, &'a [u8]);

impl View for MsgA<'_> {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgA<'a>> for MsgAInner<'a> {
    fn ex_from(m: MsgA<'a>) -> MsgAInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner<'a>) -> MsgA<'a> {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgAMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for MsgAMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgAMapper<'_> {
    type Src = SpecMsgAInner;

    type Dst = SpecMsgA;
}

impl SpecIsoProof for MsgAMapper<'_> {
    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for MsgAMapper<'a> {
    type Src = MsgAInner<'a>;

    type Dst = MsgA<'a>;
}

pub spec const SPEC_MSGD_F1: Seq<u8> = seq![1; 4];

pub const MSGD_F2: u16 = 4660;

pub type SpecMsgDCombinator = Mapped<
    (
        Refined<bytes::Fixed<4>, BytesPredicate16235736133663645624<'static>>,
        Refined<U16Be, TagPred<u16>>,
    ),
    MsgDMapper<'static>,
>;

pub exec const MSGD_F1: [u8; 4]
    ensures
        MSGD_F1@ == SPEC_MSGD_F1,
{
    let arr: [u8; 4] = [1;4];
    assert(arr@ == SPEC_MSGD_F1);
    arr
}

pub struct BytesPredicate16235736133663645624<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> BytesPredicate16235736133663645624<'a> {
    pub closed spec fn spec_new() -> Self {
        Self(std::marker::PhantomData)
    }

    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl View for BytesPredicate16235736133663645624<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for BytesPredicate16235736133663645624<'_> {
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        i == &SPEC_MSGD_F1
    }
}

impl<'a> Pred for BytesPredicate16235736133663645624<'a> {
    type Input = &'a [u8];

    fn apply(&self, i: &Self::Input) -> bool {
        compare_slice(i, MSGD_F1.as_slice())
    }
}

pub type MsgDCombinator<'a> = Mapped<
    (
        Refined<bytes::Fixed<4>, BytesPredicate16235736133663645624<'a>>,
        Refined<U16Be, TagPred<u16>>,
    ),
    MsgDMapper<'a>,
>;

pub type SpecMsgBCombinator = Mapped<SpecMsgDCombinator, MsgBMapper<'static>>;

pub type MsgBCombinator<'a> = Mapped<MsgDCombinator<'a>, MsgBMapper<'a>>;

pub type SpecContent0Combinator = bytes::Variable;

pub type Content0Combinator = bytes::Variable;

pub type SpecContentTypeCombinator = U8;

pub type ContentTypeCombinator = U8;

pub type SpecMsgCF4Combinator = AndThen<
    bytes::Variable,
    Mapped<
        Choice<
            Cond<SpecContent0Combinator>,
            Choice<Cond<U16Be>, Choice<Cond<U32Be>, Cond<bytes::Tail>>>,
        >,
        MsgCF4Mapper<'static>,
    >,
>;

pub type MsgCF4Combinator<'a> = AndThen<
    bytes::Variable,
    Mapped<
        Choice<
            Cond<Content0Combinator>,
            Choice<Cond<U16Be>, Choice<Cond<U32Be>, Cond<bytes::Tail>>>,
        >,
        MsgCF4Mapper<'a>,
    >,
>;

pub type SpecMsgCCombinator = Mapped<
    SpecPair<(SpecContentTypeCombinator, U24Be), SpecMsgCF4Combinator>,
    MsgCMapper<'static>,
>;

pub struct MsgCCont<'a>(std::marker::PhantomData<&'a ()>);

pub type MsgCCombinator<'a> = Mapped<
    Pair<&'a [u8], Vec<u8>, (ContentTypeCombinator, U24Be), MsgCF4Combinator<'a>, MsgCCont<'a>>,
    MsgCMapper<'a>,
>;

pub type SpecMsgACombinator = Mapped<(SpecMsgBCombinator, bytes::Tail), MsgAMapper<'static>>;

pub type MsgACombinator<'a> = Mapped<(MsgBCombinator<'a>, bytes::Tail), MsgAMapper<'a>>;

pub open spec fn spec_msg_d() -> SpecMsgDCombinator {
    Mapped {
        inner: (
            Refined {
                inner: bytes::Fixed::<4>,
                predicate: BytesPredicate16235736133663645624::spec_new(),
            },
            Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
        ),
        mapper: MsgDMapper::spec_new(),
    }
}

pub fn msg_d<'a>() -> (o: MsgDCombinator<'a>)
    ensures
        o@ == spec_msg_d(),
{
    Mapped {
        inner: (
            Refined {
                inner: bytes::Fixed::<4>,
                predicate: BytesPredicate16235736133663645624::new(),
            },
            Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
        ),
        mapper: MsgDMapper::new(),
    }
}

pub open spec fn spec_msg_b() -> SpecMsgBCombinator {
    Mapped { inner: spec_msg_d(), mapper: MsgBMapper::spec_new() }
}

pub fn msg_b<'a>() -> (o: MsgBCombinator<'a>)
    ensures
        o@ == spec_msg_b(),
{
    Mapped { inner: msg_d(), mapper: MsgBMapper::new() }
}

pub open spec fn spec_content_0(num: u24) -> SpecContent0Combinator {
    bytes::Variable(num.spec_into())
}

pub fn content_0<'a>(num: u24) -> (o: Content0Combinator)
    ensures
        o@ == spec_content_0(num@),
{
    bytes::Variable(num.ex_into())
}

pub open spec fn spec_content_type() -> SpecContentTypeCombinator {
    U8
}

pub fn content_type() -> (o: ContentTypeCombinator)
    ensures
        o@ == spec_content_type(),
{
    U8
}

pub open spec fn spec_msg_c_f4(f2: SpecContentType, f3: u24) -> SpecMsgCF4Combinator {
    AndThen(
        bytes::Variable(f3.spec_into()),
        Mapped {
            inner: Choice(
                Cond { cond: f2 == 0, inner: spec_content_0(f3) },
                Choice(
                    Cond { cond: f2 == 1, inner: U16Be },
                    Choice(
                        Cond { cond: f2 == 2, inner: U32Be },
                        Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: bytes::Tail },
                    ),
                ),
            ),
            mapper: MsgCF4Mapper::spec_new(),
        },
    )
}

pub fn msg_c_f4<'a>(f2: ContentType, f3: u24) -> (o: MsgCF4Combinator<'a>)
    ensures
        o@ == spec_msg_c_f4(f2@, f3@),
{
    AndThen(
        bytes::Variable(f3.ex_into()),
        Mapped {
            inner: Choice(
                Cond { cond: f2 == 0, inner: content_0(f3) },
                Choice(
                    Cond { cond: f2 == 1, inner: U16Be },
                    Choice(
                        Cond { cond: f2 == 2, inner: U32Be },
                        Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: bytes::Tail },
                    ),
                ),
            ),
            mapper: MsgCF4Mapper::new(),
        },
    )
}

pub open spec fn spec_msg_c() -> SpecMsgCCombinator {
    let fst = (spec_content_type(), U24Be);
    let snd = |deps| spec_msg_c_cont(deps);
    Mapped { inner: SpecPair { fst, snd }, mapper: MsgCMapper::spec_new() }
}

pub open spec fn spec_msg_c_cont(deps: (SpecContentType, u24)) -> SpecMsgCF4Combinator {
    let (f2, f3) = deps;
    spec_msg_c_f4(f2, f3)
}

pub fn msg_c<'a>() -> (o: MsgCCombinator<'a>)
    ensures
        o@ == spec_msg_c(),
{
    let fst = (content_type(), U24Be);
    let snd = MsgCCont(std::marker::PhantomData);
    let spec_snd = Ghost(|deps| spec_msg_c_cont(deps));
    Mapped { inner: Pair { fst, snd, spec_snd }, mapper: MsgCMapper::new() }
}

impl<'a> Continuation<&(ContentType, u24)> for MsgCCont<'a> {
    type Output = MsgCF4Combinator<'a>;

    open spec fn requires(&self, deps: &(ContentType, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &(ContentType, u24), o: Self::Output) -> bool {
        o@ == spec_msg_c_cont(deps@)
    }

    fn apply(&self, deps: &(ContentType, u24)) -> Self::Output {
        let (f2, f3) = *deps;
        msg_c_f4(f2, f3)
    }
}

pub open spec fn spec_msg_a() -> SpecMsgACombinator {
    Mapped { inner: (spec_msg_b(), bytes::Tail), mapper: MsgAMapper::spec_new() }
}

pub fn msg_a<'a>() -> (o: MsgACombinator<'a>)
    ensures
        o@ == spec_msg_a(),
{
    Mapped { inner: (msg_b(), bytes::Tail), mapper: MsgAMapper::new() }
}

pub open spec fn parse_spec_msg_d(i: Seq<u8>) -> Result<(usize, SpecMsgD), ()> {
    spec_msg_d().spec_parse(i)
}

pub open spec fn serialize_spec_msg_d(msg: SpecMsgD) -> Result<Seq<u8>, ()> {
    spec_msg_d().spec_serialize(msg)
}

pub fn parse_msg_d(i: &[u8]) -> (o: Result<(usize, MsgD<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_d(i@) matches Ok(r_) && r@ == r_,
{
    // msg_d().parse(i)
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg_d(), i)
}

pub fn serialize_msg_d(msg: MsgD<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_d(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_d().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_b(i: Seq<u8>) -> Result<(usize, SpecMsgB), ()> {
    spec_msg_b().spec_parse(i)
}

pub open spec fn serialize_spec_msg_b(msg: SpecMsgB) -> Result<Seq<u8>, ()> {
    spec_msg_b().spec_serialize(msg)
}

pub fn parse_msg_b(i: &[u8]) -> (o: Result<(usize, MsgB<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_b(i@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg_b(), i)
}

pub fn serialize_msg_b(msg: MsgB<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_b(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_b().serialize(msg, data, pos)
}

pub open spec fn parse_spec_content_0(i: Seq<u8>, num: u24) -> Result<(usize, SpecContent0), ()> {
    spec_content_0(num).spec_parse(i)
}

pub open spec fn serialize_spec_content_0(msg: SpecContent0, num: u24) -> Result<Seq<u8>, ()> {
    spec_content_0(num).spec_serialize(msg)
}

pub fn parse_content_0(i: &[u8], num: u24) -> (o: Result<(usize, Content0<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_content_0(i@, num@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&content_0(num), i)
}

pub fn serialize_content_0(msg: Content0<'_>, data: &mut Vec<u8>, pos: usize, num: u24) -> (o:
    Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_content_0(msg@, num@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    content_0(num).serialize(msg, data, pos)
}

pub open spec fn parse_spec_content_type(i: Seq<u8>) -> Result<(usize, SpecContentType), ()> {
    spec_content_type().spec_parse(i)
}

pub open spec fn serialize_spec_content_type(msg: SpecContentType) -> Result<Seq<u8>, ()> {
    spec_content_type().spec_serialize(msg)
}

pub fn parse_content_type(i: &[u8]) -> (o: Result<(usize, ContentType), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_content_type(i@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&content_type(), i)
}

pub fn serialize_content_type(msg: ContentType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_content_type(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    <_ as Combinator<&[u8], Vec<u8>>>::serialize(&content_type(), msg, data, pos)
}

pub open spec fn parse_spec_msg_c_f4(i: Seq<u8>, f2: SpecContentType, f3: u24) -> Result<
    (usize, SpecMsgCF4),
    (),
> {
    spec_msg_c_f4(f2, f3).spec_parse(i)
}

pub open spec fn serialize_spec_msg_c_f4(msg: SpecMsgCF4, f2: SpecContentType, f3: u24) -> Result<
    Seq<u8>,
    (),
> {
    spec_msg_c_f4(f2, f3).spec_serialize(msg)
}

pub fn parse_msg_c_f4(i: &[u8], f2: ContentType, f3: u24) -> (o: Result<
    (usize, MsgCF4<'_>),
    ParseError,
>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_c_f4(i@, f2@, f3@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg_c_f4(f2, f3), i)
}

pub fn serialize_msg_c_f4(
    msg: MsgCF4<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    f2: ContentType,
    f3: u24,
) -> (o: Result<usize, SerializeError>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_c_f4(msg@, f2@, f3@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_c_f4(f2, f3).serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_c(i: Seq<u8>) -> Result<(usize, SpecMsgC), ()> {
    spec_msg_c().spec_parse(i)
}

pub open spec fn serialize_spec_msg_c(msg: SpecMsgC) -> Result<Seq<u8>, ()> {
    spec_msg_c().spec_serialize(msg)
}

pub fn parse_msg_c(i: &[u8]) -> (o: Result<(usize, MsgC<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_c(i@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg_c(), i)
}

pub fn serialize_msg_c(msg: MsgC<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_c(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_c().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg_a(i: Seq<u8>) -> Result<(usize, SpecMsgA), ()> {
    spec_msg_a().spec_parse(i)
}

pub open spec fn serialize_spec_msg_a(msg: SpecMsgA) -> Result<Seq<u8>, ()> {
    spec_msg_a().spec_serialize(msg)
}

pub fn parse_msg_a(i: &[u8]) -> (o: Result<(usize, MsgA<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg_a(i@) matches Ok(r_) && r@ == r_,
{
    <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg_a(), i)
}

pub fn serialize_msg_a(msg: MsgA<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg_a(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg_a().serialize(msg, data, pos)
}

} // verus!
