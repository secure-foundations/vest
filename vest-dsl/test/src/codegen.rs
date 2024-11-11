#![allow(unused_imports)]
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

pub type SpecMsg3 = Seq<u8>;

pub type Msg3<'a> = &'a [u8];

pub type Msg3Owned = Vec<u8>;

#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AType {
    A = 0,
    B = 1,
    C = 2,
}

pub type SpecAType = AType;

pub type ATypeOwned = AType;

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
    type Src<'a> = ATypeInner;

    type Dst<'a> = AType;

    type SrcOwned = ATypeInner;

    type DstOwned = AType;
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

pub type Msg1Inner<'a> = (u8, (u16, &'a [u8]));

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
    fn ex_from(m: Msg1<'a>) -> Msg1Inner<'a> {
        (m.a, (m.b, m.c))
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(m: Msg1Inner<'a>) -> Msg1<'a> {
        let (a, (b, c)) = m;
        Msg1 { a, b, c }
    }
}

pub struct Msg1Mapper;

impl View for Msg1Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg1Mapper {
    type Src = SpecMsg1Inner;

    type Dst = SpecMsg1;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for Msg1Mapper {
    type Src<'a> = Msg1Inner<'a>;

    type Dst<'a> = Msg1<'a>;

    type SrcOwned = Msg1OwnedInner;

    type DstOwned = Msg1Owned;
}

pub struct Msg1Owned {
    pub a: u8,
    pub b: u16,
    pub c: Vec<u8>,
}

pub type Msg1OwnedInner = (u8, (u16, Vec<u8>));

impl View for Msg1Owned {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

impl From<Msg1Owned> for Msg1OwnedInner {
    fn ex_from(m: Msg1Owned) -> Msg1OwnedInner {
        (m.a, (m.b, m.c))
    }
}

impl From<Msg1OwnedInner> for Msg1Owned {
    fn ex_from(m: Msg1OwnedInner) -> Msg1Owned {
        let (a, (b, c)) = m;
        Msg1Owned { a, b, c }
    }
}

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

pub type Msg2Inner = (u8, (u16, u32));

impl View for Msg2 {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for Msg2Mapper {
    type Src<'a> = Msg2Inner;

    type Dst<'a> = Msg2;

    type SrcOwned = Msg2OwnedInner;

    type DstOwned = Msg2Owned;
}

pub struct Msg2Owned {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type Msg2OwnedInner = (u8, (u16, u32));

impl View for Msg2Owned {
    type V = SpecMsg2;

    open spec fn view(&self) -> Self::V {
        SpecMsg2 { a: self.a@, b: self.b@, c: self.c@ }
    }
}

impl From<Msg2Owned> for Msg2OwnedInner {
    fn ex_from(m: Msg2Owned) -> Msg2OwnedInner {
        (m.a, (m.b, m.c))
    }
}

impl From<Msg2OwnedInner> for Msg2Owned {
    fn ex_from(m: Msg2OwnedInner) -> Msg2Owned {
        let (a, (b, c)) = m;
        Msg2Owned { a, b, c }
    }
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

impl View for Msg4V<'_> {
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

pub struct Msg4VMapper;

impl View for Msg4VMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg4VMapper {
    type Src = SpecMsg4VInner;

    type Dst = SpecMsg4V;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for Msg4VMapper {
    type Src<'a> = Msg4VInner<'a>;

    type Dst<'a> = Msg4V<'a>;

    type SrcOwned = Msg4VOwnedInner;

    type DstOwned = Msg4VOwned;
}

pub enum Msg4VOwned {
    A(Msg1Owned),
    B(Msg2Owned),
    C(Msg3Owned),
}

pub type Msg4VOwnedInner = Either<Msg1Owned, Either<Msg2Owned, Msg3Owned>>;

impl View for Msg4VOwned {
    type V = SpecMsg4V;

    open spec fn view(&self) -> Self::V {
        match self {
            Msg4VOwned::A(m) => SpecMsg4V::A(m@),
            Msg4VOwned::B(m) => SpecMsg4V::B(m@),
            Msg4VOwned::C(m) => SpecMsg4V::C(m@),
        }
    }
}

impl From<Msg4VOwned> for Msg4VOwnedInner {
    fn ex_from(m: Msg4VOwned) -> Msg4VOwnedInner {
        match m {
            Msg4VOwned::A(m) => Either::Left(m),
            Msg4VOwned::B(m) => Either::Right(Either::Left(m)),
            Msg4VOwned::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl From<Msg4VOwnedInner> for Msg4VOwned {
    fn ex_from(m: Msg4VOwnedInner) -> Msg4VOwned {
        match m {
            Either::Left(m) => Msg4VOwned::A(m),
            Either::Right(Either::Left(m)) => Msg4VOwned::B(m),
            Either::Right(Either::Right(m)) => Msg4VOwned::C(m),
        }
    }
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

pub type Msg4Inner<'a> = (AType, (Msg4V<'a>, &'a [u8]));

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 { t: self.t@, v: self.v@, tail: self.tail@ }
    }
}

impl<'a> From<Msg4<'a>> for Msg4Inner<'a> {
    fn ex_from(m: Msg4<'a>) -> Msg4Inner<'a> {
        (m.t, (m.v, m.tail))
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(m: Msg4Inner<'a>) -> Msg4<'a> {
        let (t, (v, tail)) = m;
        Msg4 { t, v, tail }
    }
}

pub struct Msg4Mapper;

impl View for Msg4Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg4Mapper {
    type Src = SpecMsg4Inner;

    type Dst = SpecMsg4;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for Msg4Mapper {
    type Src<'a> = Msg4Inner<'a>;

    type Dst<'a> = Msg4<'a>;

    type SrcOwned = Msg4OwnedInner;

    type DstOwned = Msg4Owned;
}

pub struct Msg4Owned {
    pub t: ATypeOwned,
    pub v: Msg4VOwned,
    pub tail: Vec<u8>,
}

pub type Msg4OwnedInner = (ATypeOwned, (Msg4VOwned, Vec<u8>));

impl View for Msg4Owned {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        SpecMsg4 { t: self.t@, v: self.v@, tail: self.tail@ }
    }
}

impl From<Msg4Owned> for Msg4OwnedInner {
    fn ex_from(m: Msg4Owned) -> Msg4OwnedInner {
        (m.t, (m.v, m.tail))
    }
}

impl From<Msg4OwnedInner> for Msg4Owned {
    fn ex_from(m: Msg4OwnedInner) -> Msg4Owned {
        let (t, (v, tail)) = m;
        Msg4Owned { t, v, tail }
    }
}

pub struct SpecMsg3Combinator(BytesN<6>);

impl SpecCombinator for SpecMsg3Combinator {
    type SpecResult = SpecMsg3;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct Msg3Combinator(BytesN<6>);

impl View for Msg3Combinator {
    type V = SpecMsg3Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg3Combinator(self.0@)
    }
}

impl Combinator for Msg3Combinator {
    type Result<'a> = Msg3<'a>;

    type Owned = Msg3Owned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Msg3CombinatorAlias = BytesN<6>;

pub struct SpecATypeCombinator(TryMap<U8, ATypeMapper>);

impl SpecCombinator for SpecATypeCombinator {
    type SpecResult = SpecAType;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct ATypeCombinator(TryMap<U8, ATypeMapper>);

impl View for ATypeCombinator {
    type V = SpecATypeCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecATypeCombinator(self.0@)
    }
}

impl Combinator for ATypeCombinator {
    type Result<'a> = AType;

    type Owned = ATypeOwned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ATypeCombinatorAlias = TryMap<U8, ATypeMapper>;

impl SpecPred for Predicate5821512137558126895 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 10) || (i == 32) || (i >= 100) {
            true
        } else {
            false
        }
    }
}

pub struct SpecMsg1Combinator(
    Mapped<(Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)), Msg1Mapper>,
);

impl SpecCombinator for SpecMsg1Combinator {
    type SpecResult = SpecMsg1;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
    (Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)),
    Msg1Mapper,
>;

pub struct Predicate5821512137558126895;

impl View for Predicate5821512137558126895 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate5821512137558126895 {
    type Input<'a> = u8;

    type InputOwned = u8;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 10) || (i == 32) || (i >= 100) {
            true
        } else {
            false
        }
    }
}

pub struct Msg1Combinator(
    Mapped<(Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)), Msg1Mapper>,
);

impl View for Msg1Combinator {
    type V = SpecMsg1Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg1Combinator(self.0@)
    }
}

impl Combinator for Msg1Combinator {
    type Result<'a> = Msg1<'a>;

    type Owned = Msg1Owned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Msg1CombinatorAlias = Mapped<
    (Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)),
    Msg1Mapper,
>;

pub struct SpecMsg2Combinator(Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>);

impl SpecCombinator for SpecMsg2Combinator {
    type SpecResult = SpecMsg2;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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

pub struct Msg2Combinator(Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>);

impl View for Msg2Combinator {
    type V = SpecMsg2Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg2Combinator(self.0@)
    }
}

impl Combinator for Msg2Combinator {
    type Result<'a> = Msg2;

    type Owned = Msg2Owned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Msg2CombinatorAlias = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub struct SpecMsg4VCombinator(
    Mapped<
        OrdChoice<
            Cond<SpecMsg1Combinator>,
            OrdChoice<Cond<SpecMsg2Combinator>, Cond<SpecMsg3Combinator>>,
        >,
        Msg4VMapper,
    >,
);

impl SpecCombinator for SpecMsg4VCombinator {
    type SpecResult = SpecMsg4V;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
    Msg4VMapper,
>;

pub struct Msg4VCombinator(
    Mapped<
        OrdChoice<Cond<Msg1Combinator>, OrdChoice<Cond<Msg2Combinator>, Cond<Msg3Combinator>>>,
        Msg4VMapper,
    >,
);

impl View for Msg4VCombinator {
    type V = SpecMsg4VCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg4VCombinator(self.0@)
    }
}

impl Combinator for Msg4VCombinator {
    type Result<'a> = Msg4V<'a>;

    type Owned = Msg4VOwned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Msg4VCombinatorAlias = Mapped<
    OrdChoice<Cond<Msg1Combinator>, OrdChoice<Cond<Msg2Combinator>, Cond<Msg3Combinator>>>,
    Msg4VMapper,
>;

pub struct SpecMsg4Combinator(
    Mapped<SpecDepend<SpecATypeCombinator, (SpecMsg4VCombinator, Tail)>, Msg4Mapper>,
);

impl SpecCombinator for SpecMsg4Combinator {
    type SpecResult = SpecMsg4;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
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
    Msg4Mapper,
>;

pub struct Msg4Cont;

pub struct Msg4Combinator(
    Mapped<Depend<ATypeCombinator, (Msg4VCombinator, Tail), Msg4Cont>, Msg4Mapper>,
);

impl View for Msg4Combinator {
    type V = SpecMsg4Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsg4Combinator(self.0@)
    }
}

impl Combinator for Msg4Combinator {
    type Result<'a> = Msg4<'a>;

    type Owned = Msg4Owned;

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

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Msg4CombinatorAlias = Mapped<
    Depend<ATypeCombinator, (Msg4VCombinator, Tail), Msg4Cont>,
    Msg4Mapper,
>;

pub closed spec fn spec_msg3() -> SpecMsg3Combinator {
    SpecMsg3Combinator(BytesN::<6>)
}

pub fn msg3() -> (o: Msg3Combinator)
    ensures
        o@ == spec_msg3(),
{
    Msg3Combinator(BytesN::<6>)
}

pub closed spec fn spec_a_type() -> SpecATypeCombinator {
    SpecATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper })
}

pub fn a_type() -> (o: ATypeCombinator)
    ensures
        o@ == spec_a_type(),
{
    ATypeCombinator(TryMap { inner: U8, mapper: ATypeMapper })
}

pub closed spec fn spec_msg1() -> SpecMsg1Combinator {
    SpecMsg1Combinator(
        Mapped {
            inner: (
                Refined { inner: U8, predicate: Predicate5821512137558126895 },
                (U16Le, BytesN::<3>),
            ),
            mapper: Msg1Mapper,
        },
    )
}

pub fn msg1() -> (o: Msg1Combinator)
    ensures
        o@ == spec_msg1(),
{
    Msg1Combinator(
        Mapped {
            inner: (
                Refined { inner: U8, predicate: Predicate5821512137558126895 },
                (U16Le, BytesN::<3>),
            ),
            mapper: Msg1Mapper,
        },
    )
}

pub closed spec fn spec_msg2() -> SpecMsg2Combinator {
    SpecMsg2Combinator(Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper })
}

pub fn msg2() -> (o: Msg2Combinator)
    ensures
        o@ == spec_msg2(),
{
    Msg2Combinator(Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper })
}

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
            mapper: Msg4VMapper,
        },
    )
}

pub fn msg4_v<'a>(t: AType) -> (o: Msg4VCombinator)
    ensures
        o@ == spec_msg4_v(t@),
{
    Msg4VCombinator(
        Mapped {
            inner: OrdChoice(
                Cond { cond: t == AType::A, inner: msg1() },
                OrdChoice(
                    Cond { cond: t == AType::B, inner: msg2() },
                    Cond { cond: t == AType::C, inner: msg3() },
                ),
            ),
            mapper: Msg4VMapper,
        },
    )
}

pub closed spec fn spec_msg4() -> SpecMsg4Combinator {
    SpecMsg4Combinator(
        Mapped {
            inner: SpecDepend { fst: spec_a_type(), snd: |deps| spec_msg4_cont(deps) },
            mapper: Msg4Mapper,
        },
    )
}

pub open spec fn spec_msg4_cont(deps: SpecAType) -> (SpecMsg4VCombinator, Tail) {
    let t = deps;
    (spec_msg4_v(t), Tail)
}

pub fn msg4() -> (o: Msg4Combinator)
    ensures
        o@ == spec_msg4(),
{
    Msg4Combinator(
        Mapped {
            inner: Depend {
                fst: a_type(),
                snd: Msg4Cont,
                spec_snd: Ghost(|deps| spec_msg4_cont(deps)),
            },
            mapper: Msg4Mapper,
        },
    )
}

impl Continuation<AType> for Msg4Cont {
    type Output = (Msg4VCombinator, Tail);

    open spec fn requires(&self, deps: AType) -> bool {
        true
    }

    open spec fn ensures(&self, deps: AType, o: Self::Output) -> bool {
        o@ == spec_msg4_cont(deps@)
    }

    fn apply(&self, deps: AType) -> Self::Output {
        let t = deps;
        (msg4_v(t), Tail)
    }
}

} // verus!
