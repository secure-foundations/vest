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
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

pub type SpecMsg3 = Seq<u8>;

pub type Msg3<'a> = &'a [u8];

pub type Msg3Owned = Vec<u8>;

#[derive(Structural, Copy, Clone, PartialEq, Eq)]
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
}

pub type SpecMsg1Inner = (u8, u16);

impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(m: SpecMsg1) -> SpecMsg1Inner {
        (m.a, m.b)
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(m: SpecMsg1Inner) -> SpecMsg1 {
        let (a, b) = m;
        SpecMsg1 { a, b }
    }
}

pub struct Msg1 {
    pub a: u8,
    pub b: u16,
}

pub type Msg1Inner = (u8, u16);

impl View for Msg1 {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a@, b: self.b@ }
    }
}

impl From<Msg1> for Msg1Inner {
    fn ex_from(m: Msg1) -> Msg1Inner {
        (m.a, m.b)
    }
}

impl From<Msg1Inner> for Msg1 {
    fn ex_from(m: Msg1Inner) -> Msg1 {
        let (a, b) = m;
        Msg1 { a, b }
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
    type Src<'a> = Msg1Inner;

    type Dst<'a> = Msg1;

    type SrcOwned = Msg1OwnedInner;

    type DstOwned = Msg1Owned;
}

pub struct Msg1Owned {
    pub a: u8,
    pub b: u16,
}

pub type Msg1OwnedInner = (u8, u16);

impl View for Msg1Owned {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a@, b: self.b@ }
    }
}

impl From<Msg1Owned> for Msg1OwnedInner {
    fn ex_from(m: Msg1Owned) -> Msg1OwnedInner {
        (m.a, m.b)
    }
}

impl From<Msg1OwnedInner> for Msg1Owned {
    fn ex_from(m: Msg1OwnedInner) -> Msg1Owned {
        let (a, b) = m;
        Msg1Owned { a, b }
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
    C(u64),
}

pub type SpecMsg4VInner = Either<SpecMsg1, Either<SpecMsg2, u64>>;

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

pub enum Msg4V {
    A(Msg1),
    B(Msg2),
    C(u64),
}

pub type Msg4VInner = Either<Msg1, Either<Msg2, u64>>;

impl View for Msg4V {
    type V = SpecMsg4V;

    open spec fn view(&self) -> Self::V {
        match self {
            Msg4V::A(m) => SpecMsg4V::A(m@),
            Msg4V::B(m) => SpecMsg4V::B(m@),
            Msg4V::C(m) => SpecMsg4V::C(m@),
        }
    }
}

impl From<Msg4V> for Msg4VInner {
    fn ex_from(m: Msg4V) -> Msg4VInner {
        match m {
            Msg4V::A(m) => Either::Left(m),
            Msg4V::B(m) => Either::Right(Either::Left(m)),
            Msg4V::C(m) => Either::Right(Either::Right(m)),
        }
    }
}

impl From<Msg4VInner> for Msg4V {
    fn ex_from(m: Msg4VInner) -> Msg4V {
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
    type Src<'a> = Msg4VInner;

    type Dst<'a> = Msg4V;

    type SrcOwned = Msg4VOwnedInner;

    type DstOwned = Msg4VOwned;
}

pub enum Msg4VOwned {
    A(Msg1Owned),
    B(Msg2Owned),
    C(u64),
}

pub type Msg4VOwnedInner = Either<Msg1Owned, Either<Msg2Owned, u64>>;

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

pub struct Msg4<'a> {
    pub t: AType,
    pub v: Msg4V,
    pub tail: &'a [u8],
}

pub type Msg4Inner<'a> = (AType, (Msg4V, &'a [u8]));

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

pub type SpecMsg3Combinator = BytesN<6>;

pub type Msg3Combinator = BytesN<6>;

pub type SpecATypeCombinator = TryMap<U8, ATypeMapper>;

pub type ATypeCombinator = TryMap<U8, ATypeMapper>;

impl SpecPred for Predicate5821512137558126895 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = *i;
        if (i >= 0 && i <= 10) || (i == 32) || (i >= 100) {
            true
        } else {
            false
        }
    }
}

pub type SpecMsg1Combinator = Mapped<
    (Refined<U8, Predicate5821512137558126895>, U16Le),
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
        let i = *i;
        if (i >= 0 && i <= 10) || (i == 32) || (i >= 100) {
            true
        } else {
            false
        }
    }
}

pub type Msg1Combinator = Mapped<(Refined<U8, Predicate5821512137558126895>, U16Le), Msg1Mapper>;

pub type SpecMsg2Combinator = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub type Msg2Combinator = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub type SpecMsg4VCombinator = Mapped<
    OrdChoice<Cond<SpecMsg1Combinator>, OrdChoice<Cond<SpecMsg2Combinator>, Cond<U64Le>>>,
    Msg4VMapper,
>;

pub type Msg4VCombinator = Mapped<
    OrdChoice<Cond<Msg1Combinator>, OrdChoice<Cond<Msg2Combinator>, Cond<U64Le>>>,
    Msg4VMapper,
>;

pub type SpecMsg4Combinator = Mapped<
    SpecDepend<SpecATypeCombinator, (SpecMsg4VCombinator, Tail)>,
    Msg4Mapper,
>;

pub struct Msg4Cont;

pub type Msg4Combinator = Mapped<
    Depend<ATypeCombinator, (Msg4VCombinator, Tail), Msg4Cont>,
    Msg4Mapper,
>;

pub open spec fn spec_msg3() -> SpecMsg3Combinator {
    BytesN::<6>
}

pub fn msg3() -> (o: Msg3Combinator)
    ensures
        o@ == spec_msg3(),
{
    BytesN::<6>
}

pub open spec fn spec_a_type() -> SpecATypeCombinator {
    TryMap { inner: U8, mapper: ATypeMapper }
}

pub fn a_type() -> (o: ATypeCombinator)
    ensures
        o@ == spec_a_type(),
{
    TryMap { inner: U8, mapper: ATypeMapper }
}

pub open spec fn spec_msg1() -> SpecMsg1Combinator {
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate5821512137558126895 }, U16Le),
        mapper: Msg1Mapper,
    }
}

pub fn msg1() -> (o: Msg1Combinator)
    ensures
        o@ == spec_msg1(),
{
    Mapped {
        inner: (Refined { inner: U8, predicate: Predicate5821512137558126895 }, U16Le),
        mapper: Msg1Mapper,
    }
}

pub open spec fn spec_msg2() -> SpecMsg2Combinator {
    Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper }
}

pub fn msg2() -> (o: Msg2Combinator)
    ensures
        o@ == spec_msg2(),
{
    Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper }
}

pub open spec fn spec_msg4_v(t: SpecAType) -> SpecMsg4VCombinator {
    Mapped {
        inner: OrdChoice(
            Cond { cond: t == AType::A, inner: spec_msg1() },
            OrdChoice(
                Cond { cond: t == AType::B, inner: spec_msg2() },
                Cond { cond: t == AType::C, inner: U64Le },
            ),
        ),
        mapper: Msg4VMapper,
    }
}

pub fn msg4_v(t: AType) -> (o: Msg4VCombinator)
    ensures
        o@ == spec_msg4_v(t@),
{
    Mapped {
        inner: OrdChoice(
            Cond { cond: t == AType::A, inner: msg1() },
            OrdChoice(
                Cond { cond: t == AType::B, inner: msg2() },
                Cond { cond: t == AType::C, inner: U64Le },
            ),
        ),
        mapper: Msg4VMapper,
    }
}

pub open spec fn spec_msg4() -> SpecMsg4Combinator {
    let fst = spec_a_type();
    let snd = |deps| spec_msg4_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: Msg4Mapper }
}

pub open spec fn spec_msg4_cont(deps: SpecAType) -> (SpecMsg4VCombinator, Tail) {
    let t = deps;
    (spec_msg4_v(t), Tail)
}

pub fn msg4() -> (o: Msg4Combinator)
    ensures
        o@ == spec_msg4(),
{
    let fst = a_type();
    let snd = Msg4Cont;
    let spec_snd = Ghost(|deps| spec_msg4_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: Msg4Mapper }
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

pub open spec fn parse_spec_msg3(i: Seq<u8>) -> Result<(usize, SpecMsg3), ()> {
    spec_msg3().spec_parse(i)
}

pub open spec fn serialize_spec_msg3(msg: SpecMsg3) -> Result<Seq<u8>, ()> {
    spec_msg3().spec_serialize(msg)
}

pub fn parse_msg3(i: &[u8]) -> (o: Result<(usize, Msg3<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg3(i@) matches Ok(r_) && r@ == r_,
{
    msg3().parse(i)
}

pub fn serialize_msg3(msg: Msg3<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg3(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg3().serialize(msg, data, pos)
}

pub open spec fn parse_spec_a_type(i: Seq<u8>) -> Result<(usize, SpecAType), ()> {
    spec_a_type().spec_parse(i)
}

pub open spec fn serialize_spec_a_type(msg: SpecAType) -> Result<Seq<u8>, ()> {
    spec_a_type().spec_serialize(msg)
}

pub fn parse_a_type(i: &[u8]) -> (o: Result<(usize, AType), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_a_type(i@) matches Ok(r_) && r@ == r_,
{
    a_type().parse(i)
}

pub fn serialize_a_type(msg: AType, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_a_type(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    a_type().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg1(i: Seq<u8>) -> Result<(usize, SpecMsg1), ()> {
    spec_msg1().spec_parse(i)
}

pub open spec fn serialize_spec_msg1(msg: SpecMsg1) -> Result<Seq<u8>, ()> {
    spec_msg1().spec_serialize(msg)
}

pub fn parse_msg1(i: &[u8]) -> (o: Result<(usize, Msg1), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg1(i@) matches Ok(r_) && r@ == r_,
{
    msg1().parse(i)
}

pub fn serialize_msg1(msg: Msg1, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg1(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg1().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg2(i: Seq<u8>) -> Result<(usize, SpecMsg2), ()> {
    spec_msg2().spec_parse(i)
}

pub open spec fn serialize_spec_msg2(msg: SpecMsg2) -> Result<Seq<u8>, ()> {
    spec_msg2().spec_serialize(msg)
}

pub fn parse_msg2(i: &[u8]) -> (o: Result<(usize, Msg2), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg2(i@) matches Ok(r_) && r@ == r_,
{
    msg2().parse(i)
}

pub fn serialize_msg2(msg: Msg2, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg2(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg2().serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg4_v(i: Seq<u8>, t: SpecAType) -> Result<(usize, SpecMsg4V), ()> {
    spec_msg4_v(t).spec_parse(i)
}

pub open spec fn serialize_spec_msg4_v(msg: SpecMsg4V, t: SpecAType) -> Result<Seq<u8>, ()> {
    spec_msg4_v(t).spec_serialize(msg)
}

pub fn parse_msg4_v(i: &[u8], t: AType) -> (o: Result<(usize, Msg4V), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg4_v(i@, t@) matches Ok(r_) && r@ == r_,
{
    msg4_v(t).parse(i)
}

pub fn serialize_msg4_v(msg: Msg4V, data: &mut Vec<u8>, pos: usize, t: AType) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg4_v(msg@, t@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg4_v(t).serialize(msg, data, pos)
}

pub open spec fn parse_spec_msg4(i: Seq<u8>) -> Result<(usize, SpecMsg4), ()> {
    spec_msg4().spec_parse(i)
}

pub open spec fn serialize_spec_msg4(msg: SpecMsg4) -> Result<Seq<u8>, ()> {
    spec_msg4().spec_serialize(msg)
}

pub fn parse_msg4(i: &[u8]) -> (o: Result<(usize, Msg4<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg4(i@) matches Ok(r_) && r@ == r_,
{
    msg4().parse(i)
}

pub fn serialize_msg4(msg: Msg4<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg4(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg4().serialize(msg, data, pos)
}

} // verus!
