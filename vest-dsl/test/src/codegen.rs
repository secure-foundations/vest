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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for Msg1Mapper<'a> {
    type Src = Msg1Inner<'a>;

    type Dst = Msg1<'a>;
}

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

pub type SpecMsg1Combinator = Mapped<
    (Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)),
    Msg1Mapper<'static>,
>;

pub struct Predicate5821512137558126895;

impl View for Predicate5821512137558126895 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl Pred for Predicate5821512137558126895 {
    type Input = u8;

    fn apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 10) || (i == 32) || (i >= 100) {
            true
        } else {
            false
        }
    }
}

pub type Msg1Combinator<'a> = Mapped<
    (Refined<U8, Predicate5821512137558126895>, (U16Le, BytesN<3>)),
    Msg1Mapper<'a>,
>;

pub open spec fn spec_msg1() -> SpecMsg1Combinator {
    Mapped {
        inner: (
            Refined { inner: U8, predicate: Predicate5821512137558126895 },
            (U16Le, BytesN::<3>),
        ),
        mapper: Msg1Mapper::spec_new(),
    }
}

pub fn msg1<'a>() -> (o: Msg1Combinator<'a>)
    ensures
        o@ == spec_msg1(),
{
    Mapped {
        inner: (
            Refined { inner: U8, predicate: Predicate5821512137558126895 },
            (U16Le, BytesN::<3>),
        ),
        mapper: Msg1Mapper::new(),
    }
}

pub open spec fn parse_spec_msg1(i: Seq<u8>) -> Result<(usize, SpecMsg1), ()> {
    spec_msg1().spec_parse(i)
}

pub open spec fn serialize_spec_msg1(msg: SpecMsg1) -> Result<Seq<u8>, ()> {
    spec_msg1().spec_serialize(msg)
}

pub fn parse_msg1(i: &[u8]) -> (o: Result<(usize, Msg1<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg1(i@) matches Ok(r_) && r@ == r_,
{
    let c = msg1();
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_msg1(msg: Msg1<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg1(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = msg1();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for Msg2Mapper {
    type Src = Msg2Inner;

    type Dst = Msg2;
}

pub type SpecMsg2Combinator = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub type Msg2Combinator = Mapped<(U8, (U16Le, U32Le)), Msg2Mapper>;

pub open spec fn spec_msg2() -> SpecMsg2Combinator {
    Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper::spec_new() }
}

pub fn msg2() -> (o: Msg2Combinator)
    ensures
        o@ == spec_msg2(),
{
    Mapped { inner: (U8, (U16Le, U32Le)), mapper: Msg2Mapper::new() }
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
    let c = msg2();
    assert(c.parse_requires());
    c.parse(i)
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
    let c = msg2();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

pub type SpecMsg3 = Seq<u8>;

pub type Msg3<'a> = &'a [u8];

pub type SpecMsg3Combinator = BytesN<6>;

pub type Msg3Combinator<'a> = BytesN<6>;

pub open spec fn spec_msg3() -> SpecMsg3Combinator {
    BytesN::<6>
}

pub fn msg3<'a>() -> (o: Msg3Combinator<'a>)
    ensures
        o@ == spec_msg3(),
{
    BytesN::<6>
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
    let c = msg3();
    assert(c.parse_requires());
    c.parse(i)
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
    let c = msg3();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for Msg4VMapper<'a> {
    type Src = Msg4VInner<'a>;

    type Dst = Msg4V<'a>;
}

pub type SpecMsg4VCombinator = Mapped<
    OrdChoice<
        Cond<SpecMsg1Combinator>,
        OrdChoice<Cond<SpecMsg2Combinator>, Cond<SpecMsg3Combinator>>,
    >,
    Msg4VMapper<'static>,
>;

pub type Msg4VCombinator<'a> = Mapped<
    OrdChoice<Cond<Msg1Combinator<'a>>, OrdChoice<Cond<Msg2Combinator>, Cond<Msg3Combinator<'a>>>>,
    Msg4VMapper<'a>,
>;

pub open spec fn spec_msg4_v(t: SpecAType) -> SpecMsg4VCombinator {
    Mapped {
        inner: OrdChoice(
            Cond { cond: t == AType::A, inner: spec_msg1() },
            OrdChoice(
                Cond { cond: t == AType::B, inner: spec_msg2() },
                Cond { cond: t == AType::C, inner: spec_msg3() },
            ),
        ),
        mapper: Msg4VMapper::spec_new(),
    }
}

pub fn msg4_v<'a>(t: AType) -> (o: Msg4VCombinator<'a>)
    ensures
        o@ == spec_msg4_v(t@),
{
    Mapped {
        inner: OrdChoice(
            Cond { cond: t == AType::A, inner: msg1() },
            OrdChoice(
                Cond { cond: t == AType::B, inner: msg2() },
                Cond { cond: t == AType::C, inner: msg3() },
            ),
        ),
        mapper: Msg4VMapper::new(),
    }
}

pub open spec fn parse_spec_msg4_v(i: Seq<u8>, t: SpecAType) -> Result<(usize, SpecMsg4V), ()> {
    spec_msg4_v(t).spec_parse(i)
}

pub open spec fn serialize_spec_msg4_v(msg: SpecMsg4V, t: SpecAType) -> Result<Seq<u8>, ()> {
    spec_msg4_v(t).spec_serialize(msg)
}

pub fn parse_msg4_v(i: &[u8], t: AType) -> (o: Result<(usize, Msg4V<'_>), ParseError>)
    ensures
        o matches Ok(r) ==> parse_spec_msg4_v(i@, t@) matches Ok(r_) && r@ == r_,
{
    let c = msg4_v(t);
    assert(c.parse_requires());
    c.parse(i)
}

pub fn serialize_msg4_v(msg: Msg4V<'_>, data: &mut Vec<u8>, pos: usize, t: AType) -> (o: Result<
    usize,
    SerializeError,
>)
    ensures
        o matches Ok(n) ==> {
            &&& serialize_spec_msg4_v(msg@, t@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let c = msg4_v(t);
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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

pub type SpecATypeCombinator = TryMap<U8, ATypeMapper>;

pub type ATypeCombinator = TryMap<U8, ATypeMapper>;

pub open spec fn spec_a_type() -> SpecATypeCombinator {
    TryMap { inner: U8, mapper: ATypeMapper }
}

pub fn a_type() -> (o: ATypeCombinator)
    ensures
        o@ == spec_a_type(),
{
    TryMap { inner: U8, mapper: ATypeMapper }
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
    let c = a_type();
    assert(c.parse_requires());
    c.parse(i)
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
    let c = a_type();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
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
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl<'a> Iso for Msg4Mapper<'a> {
    type Src = Msg4Inner<'a>;

    type Dst = Msg4<'a>;
}

pub type SpecMsg4Combinator = Mapped<
    SpecDepend<SpecATypeCombinator, (SpecMsg4VCombinator, Tail)>,
    Msg4Mapper<'static>,
>;

pub type Msg4Combinator<'a> = Mapped<
    Depend<'a, ATypeCombinator, (Msg4VCombinator<'a>, Tail), Msg4Cont<'a>>,
    Msg4Mapper<'a>,
>;

pub open spec fn spec_msg4() -> SpecMsg4Combinator {
    let fst = spec_a_type();
    let snd = |deps| spec_msg4_cont(deps);
    Mapped { inner: SpecDepend { fst, snd }, mapper: Msg4Mapper::spec_new() }
}

pub open spec fn spec_msg4_cont(deps: SpecAType) -> (SpecMsg4VCombinator, Tail) {
    let t = deps;
    (spec_msg4_v(t), Tail)
}

pub fn msg4<'a>() -> (o: Msg4Combinator<'a>)
    ensures
        o@ == spec_msg4(),
{
    let fst = a_type();
    let snd = Msg4Cont::new();
    let spec_snd = Ghost(|deps| spec_msg4_cont(deps));
    Mapped { inner: Depend { fst, snd, spec_snd }, mapper: Msg4Mapper::new() }
}

pub struct Msg4Cont<'a>(PhantomData<&'a ()>);

impl<'a> Msg4Cont<'a> {
    pub fn new() -> Self {
        Msg4Cont(PhantomData)
    }
}

impl<'a> Continuation<AType> for Msg4Cont<'a> {
    type Output = (Msg4VCombinator<'a>, Tail);

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
    let c = msg4();
    assert(c.parse_requires());
    c.parse(i)
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
    let c = msg4();
    assert(c.serialize_requires());
    c.serialize(msg, data, pos)
}

} // verus!
