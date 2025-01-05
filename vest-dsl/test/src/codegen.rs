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

pub struct SpecMsg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type SpecMsg2Inner = (u8, (u16, u32));

impl SpecFrom<SpecMsg2> for SpecMsg2Inner {
    open spec fn spec_from(m: SpecMsg2) -> SpecMsg2Inner {
        (m.a, (m.b, m.c))
    }
}

impl SpecFrom<SpecMsg2Inner> for SpecMsg2 {
    open spec fn spec_from(m: SpecMsg2Inner) -> SpecMsg2 {
        let (a, (b, c)) = m;
        SpecMsg2 { a, b, c }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

impl View for Msg2 {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

pub type Msg2Inner = (u8, (u16, u32));

impl From<Msg2> for Msg2Inner {
    fn ex_from(m: Msg2) -> Msg2Inner {
        (m.a, (m.b, m.c))
    }
}

impl From<Msg2Inner> for Msg2 {
    fn ex_from(m: Msg2Inner) -> Msg2 {
        let (a, (b, c)) = m;
        Msg2 { a, b, c }
    }
}

pub struct Msg2Mapper;

impl Msg2Mapper {
    pub closed spec fn spec_new() -> Self {
        Msg2Mapper
    }

    pub fn new() -> Self {
        Msg2Mapper
    }
}

impl View for Msg2Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg2Mapper {
    type Src = SpecMsg2Inner;

    type Dst = SpecMsg2;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl Iso for Msg2Mapper {
    type Src = Msg2Inner;

    type Dst = Msg2;
}

pub struct SpecMsg2Combinator(SpecMsg2CombinatorAlias);

impl SpecCombinator for SpecMsg2Combinator {
    type Type = SpecMsg2;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsg2Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsg2CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsg2CombinatorAlias = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub struct Msg2Combinator(Msg2CombinatorAlias);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg2Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg2Combinator {
    type Type = Msg2;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Msg2CombinatorAlias = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub closed spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper::spec_new() })
}

pub fn msg2() -> (o: Msg2Combinator)
    ensures
        o@ == spec_msg2(),
{
    Msg2Combinator(Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper::new() })
}

pub type SpecMsg3 = Seq<u8>;

pub type Msg3<'a> = &'a [u8];

pub struct SpecMsg3Combinator(SpecMsg3CombinatorAlias);

impl SpecCombinator for SpecMsg3Combinator {
    type Type = SpecMsg3;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsg3Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsg3CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsg3CombinatorAlias = BytesN<6>;

pub struct Msg3Combinator(Msg3CombinatorAlias);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg3Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg3Combinator {
    type Type = Msg3<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Msg3CombinatorAlias = BytesN<6>;

pub closed spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(BytesN::<6>)
}

pub fn msg3() -> (o: Msg3Combinator)
    ensures
        o@ == spec_msg3(),
{
    Msg3Combinator(BytesN::<6>)
}

pub struct SpecMsg1 {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
}

pub type SpecMsg1Inner = (u8, (u16, Seq<u8>));

impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(m: SpecMsg1) -> SpecMsg1Inner {
        (m.a, (m.b, m.c))
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(m: SpecMsg1Inner) -> SpecMsg1 {
        let (a, (b, c)) = m;
        SpecMsg1 { a, b, c }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg1<'a> {
    pub a: u8,
    pub b: u16,
    pub c: &'a [u8],
}

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

pub type Msg1Inner<'a> = (u8, (u16, &'a [u8]));

impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
    fn ex_from(m: Msg1) -> Msg1Inner {
        (m.a, (m.b, m.c))
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (a, (b, c)) = m;
        Msg1 { a, b, c }
    }
}

pub struct Msg1Mapper<'a>(PhantomData<&'a ()>);

impl<'a> Msg1Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg1Mapper(PhantomData)
    }

    pub fn new() -> Self {
        Msg1Mapper(PhantomData)
    }
}

impl View for Msg1Mapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg1Mapper<'_> {
    type Src = SpecMsg1Inner;

    type Dst = SpecMsg1;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for Msg1Mapper<'a> {
    type Src = Msg1Inner<'a>;

    type Dst = Msg1<'a>;
}

pub struct SpecMsg1Combinator(SpecMsg1CombinatorAlias);

impl SpecCombinator for SpecMsg1Combinator {
    type Type = SpecMsg1;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsg1Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsg1CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsg1CombinatorAlias = Mapped<
    (Refined<U8, Predicate15164968237706789291>, (U16Le, BytesN<3>)),
    Msg1Mapper<'static>,
>;

pub struct Predicate15164968237706789291;

impl View for Predicate15164968237706789291 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate15164968237706789291 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10) || (i == 32) || (i >= 100)
    }
}

impl SpecPred for Predicate15164968237706789291 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        (i >= 0 && i <= 10) || (i == 32) || (i >= 100)
    }
}

pub struct Msg1Combinator<'a>(Msg1CombinatorAlias<'a>);

impl<'a> View for Msg1Combinator<'a> {
    type V = SpecMsg1Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg1Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg1Combinator<'a> {
    type Type = Msg1<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Msg1CombinatorAlias<'a> = Mapped<
    (Refined<U8, Predicate15164968237706789291>, (U16Le, BytesN<3>)),
    Msg1Mapper<'a>,
>;

pub closed spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
        Mapped {
            inner: (
                Refined { inner: U8, predicate: Predicate15164968237706789291 },
                (U16Le, BytesN::<3>),
            ),
            mapper: Msg1Mapper::spec_new(),
        },
    )
}

pub fn msg1<'a>() -> (o: Msg1Combinator<'a>)
    ensures
        o@ == spec_msg1(),
{
    Msg1Combinator(
        Mapped {
            inner: (
                Refined { inner: U8, predicate: Predicate15164968237706789291 },
                (U16Le, BytesN::<3>),
            ),
            mapper: Msg1Mapper::new(),
        },
    )
}

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AType {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAType = AType;

pub type ATypeInner = u8;

impl View for AType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ATypeInner> for AType {
    type Error = ();

    open spec fn spec_try_from(v: ATypeInner) -> Result<AType, ()> {
        match v {
            0u8 => Ok(AType::A),
            1u8 => Ok(AType::B),
            2u8 => Ok(AType::C),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AType> for ATypeInner {
    type Error = ();

    open spec fn spec_try_from(v: AType) -> Result<ATypeInner, ()> {
        match v {
            AType::A => Ok(0u8),
            AType::B => Ok(1u8),
            AType::C => Ok(2u8),
        }
    }
}

impl TryFrom<ATypeInner> for AType {
    type Error = ();

    fn ex_try_from(v: ATypeInner) -> Result<AType, ()> {
        match v {
            0u8 => Ok(AType::A),
            1u8 => Ok(AType::B),
            2u8 => Ok(AType::C),
            _ => Err(()),
        }
    }
}

impl TryFrom<AType> for ATypeInner {
    type Error = ();

    fn ex_try_from(v: AType) -> Result<ATypeInner, ()> {
        match v {
            AType::A => Ok(0u8),
            AType::B => Ok(1u8),
            AType::C => Ok(2u8),
        }
    }
}

pub struct ATypeMapper;

impl View for ATypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for ATypeMapper {
    type Src = ATypeInner;

    type Dst = AType;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl TryFromInto for ATypeMapper {
    type Src = ATypeInner;

    type Dst = AType;
}

pub struct SpecATypeCombinator(SpecATypeCombinatorAlias);

impl SpecCombinator for SpecATypeCombinator {
    type Type = SpecAType;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecATypeCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecATypeCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecATypeCombinatorAlias = TryMap<U8, ATypeMapper>;

pub struct ATypeCombinator(ATypeCombinatorAlias);

impl View for ATypeCombinator {
    type V = SpecATypeCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecATypeCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for ATypeCombinator {
    type Type = AType;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type ATypeCombinatorAlias = TryMap<U8, ATypeMapper>;

pub closed spec fn spec_a_type() -> SpecATypeCombinator {
    SpecATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper })
}

pub fn a_type() -> (o: ATypeCombinator)
    ensures
        o@ == spec_a_type(),
{
    ATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper })
}

pub enum SpecMsg4V {
    A(SpecMsg1),
    B(SpecMsg2),
    C(SpecMsg3),
}

pub type SpecMsg4VInner = Either<SpecMsg1, Either<SpecMsg2, SpecMsg3>>;

impl SpecFrom<SpecMsg4V> for SpecMsg4VInner {
    open spec fn spec_from(m: SpecMsg4V) -> SpecMsg4VInner {
        match m {
            SpecMsg4V::A(m) => Either::Left(m),
            SpecMsg4V::B(m) => Either::Right(Either::Left(m)),
            SpecMsg4V::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl SpecFrom<SpecMsg4VInner> for SpecMsg4V {
    open spec fn spec_from(m: SpecMsg4VInner) -> SpecMsg4V {
        match m {
            Either::Left(m) => SpecMsg4V::A(m),
            Either::Right(Either::Left(m)) => SpecMsg4V::B(m),
            Either::Right(Either::Right(m)) => SpecMsg4V::C(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Msg4V<'a> {
    A(Msg1<'a>),
    B(Msg2),
    C(Msg3<'a>),
}

pub type Msg4VInner<'a> = Either<Msg1<'a>, Either<Msg2, Msg3<'a>>>;

impl<'a> View for Msg4V<'a> {
    type V = SpecMsg4V;

    open spec fn view(&self) -> Self::V {
        match self {
            Msg4V::A(m) => SpecMsg4V::A(m@),
            Msg4V::B(m) => SpecMsg4V::B(m@),
            Msg4V::C(m) => SpecMsg4V::C(m@),
        }
    }
}

impl<'a> From<Msg4V<'a>> for Msg4VInner<'a> {
    fn ex_from(m: Msg4V<'a>) -> Msg4VInner<'a> {
        match m {
            Msg4V::A(m) => Either::Left(m),
            Msg4V::B(m) => Either::Right(Either::Left(m)),
            Msg4V::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl<'a> From<Msg4VInner<'a>> for Msg4V<'a> {
    fn ex_from(m: Msg4VInner<'a>) -> Msg4V<'a> {
        match m {
            Either::Left(m) => Msg4V::A(m),
            Either::Right(Either::Left(m)) => Msg4V::B(m),
            Either::Right(Either::Right(m)) => Msg4V::C(m),
        }
    }
}

pub struct Msg4VMapper<'a>(PhantomData<&'a ()>);

impl<'a> Msg4VMapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg4VMapper(PhantomData)
    }

    pub fn new() -> Self {
        Msg4VMapper(PhantomData)
    }
}

impl View for Msg4VMapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg4VMapper<'_> {
    type Src = SpecMsg4VInner;

    type Dst = SpecMsg4V;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for Msg4VMapper<'a> {
    type Src = Msg4VInner<'a>;

    type Dst = Msg4V<'a>;
}

pub struct SpecMsg4VCombinator(SpecMsg4VCombinatorAlias);

impl SpecCombinator for SpecMsg4VCombinator {
    type Type = SpecMsg4V;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsg4VCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsg4VCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsg4VCombinatorAlias = Mapped<
    OrdChoice<
        Cond<SpecMsg1Combinator>,
        OrdChoice<Cond<SpecMsg2Combinator>, Cond<SpecMsg3Combinator>>,
    >,
    Msg4VMapper<'static>,
>;

pub struct Msg4VCombinator<'a>(Msg4VCombinatorAlias<'a>);

impl<'a> View for Msg4VCombinator<'a> {
    type V = SpecMsg4VCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg4VCombinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg4VCombinator<'a> {
    type Type = Msg4V<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Msg4VCombinatorAlias<'a> = Mapped<
    OrdChoice<Cond<Msg1Combinator<'a>>, OrdChoice<Cond<Msg2Combinator>, Cond<Msg3Combinator>>>,
    Msg4VMapper<'a>,
>;

pub closed spec fn spec_msg4_v(t: SpecAType) -> SpecMsg4VCombinator {
    SpecMsg4VCombinator(
        Mapped {
            inner: OrdChoice(
                Cond { cond: t == AType::A, inner: spec_msg1() },
                OrdChoice(
                    Cond { cond: t == AType::B, inner: spec_msg2() },
                    Cond { cond: t == AType::C, inner: spec_msg3() },
                ),
            ),
            mapper: Msg4VMapper::spec_new(),
        },
    )
}

pub fn msg4_v<'a>(t: AType) -> (o: Msg4VCombinator<'a>)
    ensures
        o@ == spec_msg4_v(t@),
{
    Msg4VCombinator(
        Mapped {
            inner: OrdChoice::new(
                Cond { cond: t == AType::A, inner: msg1() },
                OrdChoice::new(
                    Cond { cond: t == AType::B, inner: msg2() },
                    Cond { cond: t == AType::C, inner: msg3() },
                ),
            ),
            mapper: Msg4VMapper::new(),
        },
    )
}

pub struct SpecMsg4 {
    pub t: SpecAType,
    pub v: SpecMsg4V,
    pub tail: Seq<u8>,
}

pub type SpecMsg4Inner = (SpecAType, (SpecMsg4V, Seq<u8>));

impl SpecFrom<SpecMsg4> for SpecMsg4Inner {
    open spec fn spec_from(m: SpecMsg4) -> SpecMsg4Inner {
        (m.t, (m.v, m.tail))
    }
}

impl SpecFrom<SpecMsg4Inner> for SpecMsg4 {
    open spec fn spec_from(m: SpecMsg4Inner) -> SpecMsg4 {
        let (t, (v, tail)) = m;
        SpecMsg4 { t, v, tail }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg4<'a> {
    pub t: AType,
    pub v: Msg4V<'a>,
    pub tail: &'a [u8],
}

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 { t: self.t@, v: self.v@, tail: self.tail@ }
    }
}

pub type Msg4Inner<'a> = (AType, (Msg4V<'a>, &'a [u8]));

impl<'a> From<Msg4<'a>> for Msg4Inner<'a> {
    fn ex_from(m: Msg4) -> Msg4Inner {
        (m.t, (m.v, m.tail))
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner) -> Msg4 {
        let (t, (v, tail)) = m;
        Msg4 { t, v, tail }
    }
}

pub struct Msg4Mapper<'a>(PhantomData<&'a ()>);

impl<'a> Msg4Mapper<'a> {
    pub closed spec fn spec_new() -> Self {
        Msg4Mapper(PhantomData)
    }

    pub fn new() -> Self {
        Msg4Mapper(PhantomData)
    }
}

impl View for Msg4Mapper<'_> {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg4Mapper<'_> {
    type Src = SpecMsg4Inner;

    type Dst = SpecMsg4;

    proof fn spec_iso(s: Self::Src) {
        assert(Self::Src::spec_from(Self::Dst::spec_from(s)) == s);
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        assert(Self::Dst::spec_from(Self::Src::spec_from(s)) == s);
    }
}

impl<'a> Iso for Msg4Mapper<'a> {
    type Src = Msg4Inner<'a>;

    type Dst = Msg4<'a>;
}

pub struct SpecMsg4Combinator(SpecMsg4CombinatorAlias);

impl SpecCombinator for SpecMsg4Combinator {
    type Type = SpecMsg4;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsg4Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsg4CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsg4CombinatorAlias = Mapped<
    SpecDepend<SpecATypeCombinator, (SpecMsg4VCombinator, Tail)>,
    Msg4Mapper<'static>,
>;

pub struct Msg4Combinator<'a>(Msg4CombinatorAlias<'a>);

impl<'a> View for Msg4Combinator<'a> {
    type V = SpecMsg4Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg4Combinator(self.0@)
    }
}

impl<'a> Combinator<&'a [u8], Vec<u8>> for Msg4Combinator<'a> {
    type Type = Msg4<'a>;

    closed spec fn spec_length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::spec_length(&self.0)
    }

    fn length(&self) -> Option<usize> {
        <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
    }

    closed spec fn parse_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::parse_requires(&self.0)
    }

    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize_requires(&self.0)
    }

    fn serialize(&self, v: Self::Type, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v, data, pos)
    }
}

pub type Msg4CombinatorAlias<'a> = Mapped<
    Depend<&'a [u8], Vec<u8>, ATypeCombinator, (Msg4VCombinator<'a>, Tail), Msg4Cont0<'a>>,
    Msg4Mapper<'a>,
>;

pub closed spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
        Mapped {
            inner: SpecDepend { fst: spec_a_type(), snd: |deps| spec_msg4_cont0(deps) },
            mapper: Msg4Mapper::spec_new(),
        },
    )
}

pub open spec fn spec_msg4_cont0(deps: SpecAType) -> (SpecMsg4VCombinator, Tail) {
    let t = deps;
    (spec_msg4_v(t), Tail)
}

pub fn msg4<'a>() -> (o: Msg4Combinator<'a>)
    ensures
        o@ == spec_msg4(),
{
    Msg4Combinator(
        Mapped {
            inner: Depend {
                fst: a_type(),
                snd: Msg4Cont0::new(),
                spec_snd: Ghost(|deps| spec_msg4_cont0(deps)),
            },
            mapper: Msg4Mapper::new(),
        },
    )
}

pub struct Msg4Cont0<'a>(PhantomData<&'a ()>);

impl<'a> Msg4Cont0<'a> {
    pub fn new() -> Self {
        Msg4Cont0(PhantomData)
    }
}

impl<'a> Continuation<&AType> for Msg4Cont0<'a> {
    type Output = (Msg4VCombinator<'a>, Tail);

    open spec fn requires(&self, deps: &AType) -> bool {
        true
    }

    open spec fn ensures(&self, deps: &AType, o: Self::Output) -> bool {
        o@ == spec_msg4_cont0(deps@)
    }

    fn apply(&self, deps: &AType) -> Self::Output {
        let t = *deps;
        (msg4_v(t), Tail)
    }
}

} // verus!
