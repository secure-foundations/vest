#![allow(warnings)]
#![allow(unused)]
use std::marker::PhantomData;
use vest::bitcoin::varint::{BtcVarint, VarInt};
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
use vest::regular::repeat_n::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgD<'a> {
    pub f1: &'a [u8],
    pub f2: u16,
}

impl View for MsgD<'_> {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

pub type MsgDInner<'a> = (&'a [u8], u16);

impl<'a> From<MsgD<'a>> for MsgDInner<'a> {
    fn ex_from(m: MsgD) -> MsgDInner {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner) -> MsgD {
        let (f1, f2) = m;
        MsgD { f1, f2 }
    }
}

pub struct MsgDMapper<'a>(PhantomData<&'a ()>);

impl<'a> MsgDMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgDMapper(PhantomData)
    }

    pub fn new() -> Self {
        MsgDMapper(PhantomData)
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

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for MsgDMapper<'a> {
    type Src = MsgDInner<'a>;

    type Dst = MsgD<'a>;
}

pub spec const SPEC_MSGD_F1: Seq<u8> = seq![1; 4];

pub const MSGD_F2: u16 = 4660;

pub struct SpecMsgDCombinator(SpecMsgDCombinatorAlias);

impl SpecCombinator for SpecMsgDCombinator {
    type Result = SpecMsgD;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgDCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgDCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgDCombinatorAlias = Mapped<
    (Refined<BytesN<4>, BytesPredicate16235736133663645624<'static>>, Refined<U16Be, TagPred<u16>>),
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

pub struct BytesPredicate16235736133663645624<'a>(PhantomData<&'a ()>);

impl<'a> BytesPredicate16235736133663645624<'a> {
    pub closed spec fn spec_new() -> Self {
        BytesPredicate16235736133663645624(PhantomData)
    }

    pub fn new() -> Self {
        BytesPredicate16235736133663645624(PhantomData)
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

pub struct MsgDCombinator<'a>(MsgDCombinatorAlias<'a>);

impl<'a> View for MsgDCombinator<'a> {
    type V = SpecMsgDCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgDCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgDCombinator<'a> {
    type Result = MsgD<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type MsgDCombinatorAlias<'a> = Mapped<
    (Refined<BytesN<4>, BytesPredicate16235736133663645624<'a>>, Refined<U16Be, TagPred<u16>>),
    MsgDMapper<'a>,
>;

pub closed spec fn spec_msg_d() -> SpecMsgDCombinator {
    SpecMsgDCombinator(
        Mapped {
            inner: (
                Refined {
                    inner: BytesN::<4>,
                    predicate: BytesPredicate16235736133663645624::spec_new(),
                },
                Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
            ),
            mapper: MsgDMapper::spec_new(),
        },
    )
}

pub fn msg_d<'a>() -> (o: MsgDCombinator<'a>)
    ensures
        o@ == spec_msg_d(),
{
    MsgDCombinator(
        Mapped {
            inner: (
                Refined {
                    inner: BytesN::<4>,
                    predicate: BytesPredicate16235736133663645624::new(),
                },
                Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
            ),
            mapper: MsgDMapper::new(),
        },
    )
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgB<'a> {
    pub f1: MsgD<'a>,
}

impl View for MsgB<'_> {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

pub type MsgBInner<'a> = MsgD<'a>;

impl<'a> From<MsgB<'a>> for MsgBInner<'a> {
    fn ex_from(m: MsgB) -> MsgBInner {
        m.f1
    }
}

impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner) -> MsgB {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper<'a>(PhantomData<&'a ()>);

impl<'a> MsgBMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgBMapper(PhantomData)
    }

    pub fn new() -> Self {
        MsgBMapper(PhantomData)
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

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for MsgBMapper<'a> {
    type Src = MsgBInner<'a>;

    type Dst = MsgB<'a>;
}

pub struct SpecMsgBCombinator(SpecMsgBCombinatorAlias);

impl SpecCombinator for SpecMsgBCombinator {
    type Result = SpecMsgB;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgBCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgBCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgBCombinatorAlias = Mapped<SpecMsgDCombinator, MsgBMapper<'static>>;

pub struct MsgBCombinator<'a>(MsgBCombinatorAlias<'a>);

impl<'a> View for MsgBCombinator<'a> {
    type V = SpecMsgBCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgBCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgBCombinator<'a> {
    type Result = MsgB<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type MsgBCombinatorAlias<'a> = Mapped<MsgDCombinator<'a>, MsgBMapper<'a>>;

pub closed spec fn spec_msg_b() -> SpecMsgBCombinator {
    SpecMsgBCombinator(Mapped { inner: spec_msg_d(), mapper: MsgBMapper::spec_new() })
}

pub fn msg_b<'a>() -> (o: MsgBCombinator<'a>)
    ensures
        o@ == spec_msg_b(),
{
    MsgBCombinator(Mapped { inner: msg_d(), mapper: MsgBMapper::new() })
}

pub type SpecContentType = u8;

pub type ContentType = u8;

pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type Result = SpecContentType;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecContentTypeCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecContentTypeCombinatorAlias = U8;

pub struct ContentTypeCombinator(ContentTypeCombinatorAlias);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecContentTypeCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ContentTypeCombinator {
    type Result = ContentType;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ContentTypeCombinatorAlias = U8;

pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(U8)
}

pub fn content_type() -> (o: ContentTypeCombinator)
    ensures
        o@ == spec_content_type(),
{
    ContentTypeCombinator(U8)
}

pub type SpecContent0 = Seq<u8>;

pub type Content0<'a> = &'a [u8];

pub struct SpecContent0Combinator(SpecContent0CombinatorAlias);

impl SpecCombinator for SpecContent0Combinator {
    type Result = SpecContent0;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecContent0Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecContent0CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecContent0CombinatorAlias = Bytes;

pub struct Content0Combinator(Content0CombinatorAlias);

impl View for Content0Combinator {
    type V = SpecContent0Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecContent0Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Content0Combinator {
    type Result = Content0<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Content0CombinatorAlias = Bytes;

pub closed spec fn spec_content_0(num: u24) -> SpecContent0Combinator {
    SpecContent0Combinator(Bytes(num.spec_into()))
}

pub fn content_0<'a>(num: u24) -> (o: Content0Combinator)
    ensures
        o@ == spec_content_0(num@),
{
    Content0Combinator(Bytes(num.ex_into()))
}

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgCF4<'a> {
    C0(Content0<'a>),
    C1(u16),
    C2(u32),
    Unrecognized(&'a [u8]),
}

pub type MsgCF4Inner<'a> = Either<Content0<'a>, Either<u16, Either<u32, &'a [u8]>>>;

impl<'a> View for MsgCF4<'a> {
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

pub struct MsgCF4Mapper<'a>(PhantomData<&'a ()>);

impl<'a> MsgCF4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgCF4Mapper(PhantomData)
    }

    pub fn new() -> Self {
        MsgCF4Mapper(PhantomData)
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

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for MsgCF4Mapper<'a> {
    type Src = MsgCF4Inner<'a>;

    type Dst = MsgCF4<'a>;
}

pub struct SpecMsgCF4Combinator(SpecMsgCF4CombinatorAlias);

impl SpecCombinator for SpecMsgCF4Combinator {
    type Result = SpecMsgCF4;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgCF4Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgCF4CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgCF4CombinatorAlias = AndThen<
    Bytes,
    Mapped<
        OrdChoice<
            Cond<SpecContent0Combinator>,
            OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
        >,
        MsgCF4Mapper<'static>,
    >,
>;

pub struct MsgCF4Combinator<'a>(MsgCF4CombinatorAlias<'a>);

impl<'a> View for MsgCF4Combinator<'a> {
    type V = SpecMsgCF4Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgCF4Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgCF4Combinator<'a> {
    type Result = MsgCF4<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type MsgCF4CombinatorAlias<'a> = AndThen<
    Bytes,
    Mapped<
        OrdChoice<
            Cond<Content0Combinator>,
            OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
        >,
        MsgCF4Mapper<'a>,
    >,
>;

pub closed spec fn spec_msg_c_f4(f2: SpecContentType, f3: u24) -> SpecMsgCF4Combinator {
    SpecMsgCF4Combinator(
        AndThen(
            Bytes(f3.spec_into()),
            Mapped {
                inner: OrdChoice(
                    Cond { cond: f2 == 0, inner: spec_content_0(f3) },
                    OrdChoice(
                        Cond { cond: f2 == 1, inner: U16Be },
                        OrdChoice(
                            Cond { cond: f2 == 2, inner: U32Be },
                            Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
                        ),
                    ),
                ),
                mapper: MsgCF4Mapper::spec_new(),
            },
        ),
    )
}

pub fn msg_c_f4<'a>(f2: ContentType, f3: u24) -> (o: MsgCF4Combinator<'a>)
    ensures
        o@ == spec_msg_c_f4(f2@, f3@),
{
    MsgCF4Combinator(
        AndThen(
            Bytes(f3.ex_into()),
            Mapped {
                inner: OrdChoice::new(
                    Cond { cond: f2 == 0, inner: content_0(f3) },
                    OrdChoice::new(
                        Cond { cond: f2 == 1, inner: U16Be },
                        OrdChoice::new(
                            Cond { cond: f2 == 2, inner: U32Be },
                            Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
                        ),
                    ),
                ),
                mapper: MsgCF4Mapper::new(),
            },
        ),
    )
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgC<'a> {
    pub f2: ContentType,
    pub f3: u24,
    pub f4: MsgCF4<'a>,
}

impl View for MsgC<'_> {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

pub type MsgCInner<'a> = ((ContentType, u24), MsgCF4<'a>);

impl<'a> From<MsgC<'a>> for MsgCInner<'a> {
    fn ex_from(m: MsgC) -> MsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner) -> MsgC {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper<'a>(PhantomData<&'a ()>);

impl<'a> MsgCMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgCMapper(PhantomData)
    }

    pub fn new() -> Self {
        MsgCMapper(PhantomData)
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

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for MsgCMapper<'a> {
    type Src = MsgCInner<'a>;

    type Dst = MsgC<'a>;
}

pub struct SpecMsgCCombinator(SpecMsgCCombinatorAlias);

impl SpecCombinator for SpecMsgCCombinator {
    type Result = SpecMsgC;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgCCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgCCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgCCombinatorAlias = Mapped<
    SpecDepend<SpecDepend<SpecContentTypeCombinator, U24Be>, SpecMsgCF4Combinator>,
    MsgCMapper<'static>,
>;

pub struct MsgCCombinator<'a>(MsgCCombinatorAlias<'a>);

impl<'a> View for MsgCCombinator<'a> {
    type V = SpecMsgCCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgCCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgCCombinator<'a> {
    type Result = MsgC<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type MsgCCombinatorAlias<'a> = Mapped<
    Depend<
        &'a [u8],
        Vec<u8>,
        Depend<&'a [u8], Vec<u8>, ContentTypeCombinator, U24Be, MsgCCont1<'a>>,
        MsgCF4Combinator<'a>,
        MsgCCont0<'a>,
    >,
    MsgCMapper<'a>,
>;

pub closed spec fn spec_msg_c() -> SpecMsgCCombinator {
    SpecMsgCCombinator(
        Mapped {
            inner: SpecDepend {
                fst: SpecDepend { fst: spec_content_type(), snd: |deps| spec_msg_c_cont1(deps) },
                snd: |deps| spec_msg_c_cont0(deps),
            },
            mapper: MsgCMapper::spec_new(),
        },
    )
}

pub open spec fn spec_msg_c_cont1(deps: SpecContentType) -> U24Be {
    let f2 = deps;
    U24Be
}

pub open spec fn spec_msg_c_cont0(deps: (SpecContentType, u24)) -> SpecMsgCF4Combinator {
    let (f2, f3) = deps;
    spec_msg_c_f4(f2, f3)
}

pub fn msg_c<'a>() -> (o: MsgCCombinator<'a>)
    ensures
        o@ == spec_msg_c(),
{
    MsgCCombinator(
        Mapped {
            inner: Depend {
                fst: Depend {
                    fst: content_type(),
                    snd: MsgCCont1::new(),
                    spec_snd: Ghost(|deps| spec_msg_c_cont1(deps)),
                },
                snd: MsgCCont0::new(),
                spec_snd: Ghost(|deps| spec_msg_c_cont0(deps)),
            },
            mapper: MsgCMapper::new(),
        },
    )
}

pub struct MsgCCont1<'a>(PhantomData<&'a ()>);

impl<'a> MsgCCont1<'a> {
    pub fn new() -> Self {
        MsgCCont1(PhantomData)
    }
}

impl<'a> Continuation<&ContentType> for MsgCCont1<'a> {
    type Output = U24Be;

    open spec fn requires(&self, deps: &ContentType) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &ContentType, o: Self::Output) -> bool {
        o@ == spec_msg_c_cont1(deps@)
    }

    fn apply(&self, deps: &ContentType) -> Self::Output {
        let f2 = *deps;
        U24Be
    }
}

pub struct MsgCCont0<'a>(PhantomData<&'a ()>);

impl<'a> MsgCCont0<'a> {
    pub fn new() -> Self {
        MsgCCont0(PhantomData)
    }
}

impl<'a> Continuation<&(ContentType, u24)> for MsgCCont0<'a> {
    type Output = MsgCF4Combinator<'a>;

    open spec fn requires(&self, deps: &(ContentType, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &(ContentType, u24), o: Self::Output) -> bool {
        o@ == spec_msg_c_cont0(deps@)
    }

    fn apply(&self, deps: &(ContentType, u24)) -> Self::Output {
        let (f2, f3) = *deps;
        msg_c_f4(f2, f3)
    }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgA<'a> {
    pub f1: MsgB<'a>,
    pub f2: &'a [u8],
}

impl View for MsgA<'_> {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

pub type MsgAInner<'a> = (MsgB<'a>, &'a [u8]);

impl<'a> From<MsgA<'a>> for MsgAInner<'a> {
    fn ex_from(m: MsgA) -> MsgAInner {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner) -> MsgA {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper<'a>(PhantomData<&'a ()>);

impl<'a> MsgAMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        MsgAMapper(PhantomData)
    }

    pub fn new() -> Self {
        MsgAMapper(PhantomData)
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

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for MsgAMapper<'a> {
    type Src = MsgAInner<'a>;

    type Dst = MsgA<'a>;
}

pub struct SpecMsgACombinator(SpecMsgACombinatorAlias);

impl SpecCombinator for SpecMsgACombinator {
    type Result = SpecMsgA;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgACombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgACombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgACombinatorAlias = Mapped<(SpecMsgBCombinator, Tail), MsgAMapper<'static>>;

pub struct MsgACombinator<'a>(MsgACombinatorAlias<'a>);

impl<'a> View for MsgACombinator<'a> {
    type V = SpecMsgACombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgACombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for MsgACombinator<'a> {
    type Result = MsgA<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Result, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type MsgACombinatorAlias<'a> = Mapped<(MsgBCombinator<'a>, Tail), MsgAMapper<'a>>;

pub closed spec fn spec_msg_a() -> SpecMsgACombinator {
    SpecMsgACombinator(Mapped { inner: (spec_msg_b(), Tail), mapper: MsgAMapper::spec_new() })
}

pub fn msg_a<'a>() -> (o: MsgACombinator<'a>)
    ensures
        o@ == spec_msg_a(),
{
    MsgACombinator(Mapped { inner: (msg_b(), Tail), mapper: MsgAMapper::new() })
}

} // verus!
