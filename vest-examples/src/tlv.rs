use vest::properties::*;
use vest::regular::{
    and_then::AndThen,
    bytes::Bytes,
    bytes_n::BytesN,
    choice::{Either, OrdChoice},
    cond::Cond,
    depend::{Depend, SpecDepend},
    map::*,
    tail::Tail,
    uints::{U16, U32, U8},
};
use vstd::prelude::*;

verus! {

/// somewhat more complex TLV example
/// should be generated from the following vest code:
/// ```vest
/// msg1 = {
///   a: u8,
///   b: u16,
///   c: [u8; 3],
///   data: Tail,
/// }
///
/// msg2 = {
///   a: u8,
///   b: u16,
///   c: u32,
/// }
///
/// msg3 = {
///   data: [u8; 6],
/// }
///
/// msg_type = enum {
///   Msg1 = 1,
///   Msg2 = 2,
///   Msg3 = 3,
/// }
///
/// tlv = {
///   @tag: msg_type,
///   @len: u8,
///   content: [u8; @len] >>= choose(@tag) {
///     Msg1 => msg1,
///     Msg2 => msg2,
///     Msg3 => msg3,
///   },
///   rest: Tail,
/// }
/// ```
/// Message type 1
pub struct SpecMsg1 {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
    pub d: Seq<u8>,
}

pub type SpecMsg1Inner = (((u8, u16), Seq<u8>), Seq<u8>);

pub struct Msg1<'a> {
    pub a: u8,
    pub b: u16,
    pub c: &'a [u8],
    pub d: &'a [u8],
}

pub struct Msg1Owned {
    pub a: u8,
    pub b: u16,
    pub c: Vec<u8>,
    pub d: Vec<u8>,
}

pub type Msg1Inner<'a> = (((u8, u16), &'a [u8]), &'a [u8]);

pub type Msg1InnerOwned = (((u8, u16), Vec<u8>), Vec<u8>);

impl View for Msg1<'_> {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a, b: self.b, c: self.c@, d: self.d@ }
    }
}

impl View for Msg1Owned {
    type V = SpecMsg1;

    open spec fn view(&self) -> Self::V {
        SpecMsg1 { a: self.a, b: self.b, c: self.c@, d: self.d@ }
    }
}

impl SpecFrom<SpecMsg1> for SpecMsg1Inner {
    open spec fn spec_from(t: SpecMsg1) -> SpecMsg1Inner {
        (((t.a, t.b), t.c), t.d)
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(e: SpecMsg1Inner) -> SpecMsg1 {
        let (((a, b), c), d) = e;
        SpecMsg1 { a, b, c, d }
    }
}

impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
    fn ex_from(e: Msg1) -> (res: Msg1Inner) {
        (((e.a, e.b), e.c), e.d)
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(e: Msg1Inner) -> (res: Msg1) {
        let (((a, b), c), d) = e;
        Msg1 { a, b, c, d }
    }
}

impl From<Msg1Owned> for Msg1InnerOwned {
    fn ex_from(e: Msg1Owned) -> (res: Msg1InnerOwned) {
        (((e.a, e.b), e.c), e.d)
    }
}

impl From<Msg1InnerOwned> for Msg1Owned {
    fn ex_from(e: Msg1InnerOwned) -> (res: Msg1Owned) {
        let (((a, b), c), d) = e;
        Msg1Owned { a, b, c, d }
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

    proof fn spec_iso(s: SpecMsg1Inner) {
    }

    proof fn spec_iso_rev(s: SpecMsg1) {
    }
}

impl Iso for Msg1Mapper {
    type Src<'a> = Msg1Inner<'a>;

    type Dst<'a> = Msg1<'a>;

    type SrcOwned = Msg1InnerOwned;

    type DstOwned = Msg1Owned;
}

/// Message type 2
pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type Msg2Inner = ((u8, u16), u32);

impl View for Msg2 {
    type V = Msg2;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecFrom<Msg2> for Msg2Inner {
    open spec fn spec_from(t: Msg2) -> Msg2Inner {
        ((t.a, t.b), t.c)
    }
}

impl From<Msg2> for Msg2Inner {
    fn ex_from(e: Msg2) -> (res: Msg2Inner) {
        ((e.a, e.b), e.c)
    }
}

impl SpecFrom<Msg2Inner> for Msg2 {
    open spec fn spec_from(e: Msg2Inner) -> Msg2 {
        let ((a, b), c) = e;
        Msg2 { a, b, c }
    }
}

impl From<Msg2Inner> for Msg2 {
    fn ex_from(e: Msg2Inner) -> (res: Msg2) {
        let ((a, b), c) = e;
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
    type Src = Msg2Inner;

    type Dst = Msg2;

    proof fn spec_iso(s: Msg2Inner) {
    }

    proof fn spec_iso_rev(s: Msg2) {
    }
}

impl Iso for Msg2Mapper {
    type Src<'a> = Msg2Inner;

    type Dst<'a> = Msg2;

    type SrcOwned = Msg2Inner;

    type DstOwned = Msg2;
}

/// Message type 3
pub struct SpecMsg3 {
    pub a: Seq<u8>,
}

pub type SpecMsg3Inner = (Seq<u8>);

pub struct Msg3<'a> {
    pub a: &'a [u8],
}

pub struct Msg3Owned {
    pub a: Vec<u8>,
}

pub type Msg3Inner<'a> = (&'a [u8]);

pub type Msg3InnerOwned = (Vec<u8>);

impl View for Msg3<'_> {
    type V = SpecMsg3;

    open spec fn view(&self) -> Self::V {
        SpecMsg3 { a: self.a@ }
    }
}

impl View for Msg3Owned {
    type V = SpecMsg3;

    open spec fn view(&self) -> Self::V {
        SpecMsg3 { a: self.a@ }
    }
}

impl SpecFrom<SpecMsg3> for SpecMsg3Inner {
    open spec fn spec_from(e: SpecMsg3) -> SpecMsg3Inner {
        e.a
    }
}

impl SpecFrom<SpecMsg3Inner> for SpecMsg3 {
    open spec fn spec_from(e: SpecMsg3Inner) -> SpecMsg3 {
        SpecMsg3 { a: e }
    }
}

impl<'a> From<Msg3<'a>> for Msg3Inner<'a> {
    fn ex_from(e: Msg3) -> (res: Msg3Inner) {
        e.a
    }
}

impl<'a> From<Msg3Inner<'a>> for Msg3<'a> {
    fn ex_from(e: Msg3Inner) -> (res: Msg3) {
        Msg3 { a: e }
    }
}

impl From<Msg3Owned> for Msg3InnerOwned {
    fn ex_from(e: Msg3Owned) -> (res: Msg3InnerOwned) {
        (e.a)
    }
}

impl From<Msg3InnerOwned> for Msg3Owned {
    fn ex_from(e: Msg3InnerOwned) -> (res: Msg3Owned) {
        Msg3Owned { a: e }
    }
}

pub struct Msg3Mapper;

impl View for Msg3Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for Msg3Mapper {
    type Src = SpecMsg3Inner;

    type Dst = SpecMsg3;

    proof fn spec_iso(s: SpecMsg3Inner) {
    }

    proof fn spec_iso_rev(s: SpecMsg3) {
    }
}

impl Iso for Msg3Mapper {
    type Src<'a> = Msg3Inner<'a>;

    type Dst<'a> = Msg3<'a>;

    type SrcOwned = Msg3InnerOwned;

    type DstOwned = Msg3Owned;
}

/// Message type tlv content
pub enum SpecTlvContent {
    M1(SpecMsg1),
    M2(Msg2),
    M3(SpecMsg3),
}

pub type SpecTlvContentInner = Either<Either<SpecMsg1, Msg2>, SpecMsg3>;

pub enum TlvContent<'a> {
    M1(Msg1<'a>),
    M2(Msg2),
    M3(Msg3<'a>),
}

pub enum TlvContentOwned {
    M1(Msg1Owned),
    M2(Msg2),
    M3(Msg3Owned),
}

pub type TlvContentInner<'a> = Either<Either<Msg1<'a>, Msg2>, Msg3<'a>>;

pub type TlvContentOwnedInner = Either<Either<Msg1Owned, Msg2>, Msg3Owned>;

impl View for TlvContent<'_> {
    type V = SpecTlvContent;

    open spec fn view(&self) -> Self::V {
        match self {
            TlvContent::M1(m) => SpecTlvContent::M1(m@),
            TlvContent::M2(m) => SpecTlvContent::M2(m@),
            TlvContent::M3(m) => SpecTlvContent::M3(m@),
        }
    }
}

impl View for TlvContentOwned {
    type V = SpecTlvContent;

    open spec fn view(&self) -> Self::V {
        match self {
            TlvContentOwned::M1(m) => SpecTlvContent::M1(m@),
            TlvContentOwned::M2(m) => SpecTlvContent::M2(m@),
            TlvContentOwned::M3(m) => SpecTlvContent::M3(m@),
        }
    }
}

impl SpecFrom<SpecTlvContent> for SpecTlvContentInner {
    open spec fn spec_from(e: SpecTlvContent) -> SpecTlvContentInner {
        match e {
            SpecTlvContent::M1(m) => Either::Left(Either::Left(m)),
            SpecTlvContent::M2(m) => Either::Left(Either::Right(m)),
            SpecTlvContent::M3(m) => Either::Right(m),
        }
    }
}

impl SpecFrom<SpecTlvContentInner> for SpecTlvContent {
    open spec fn spec_from(e: SpecTlvContentInner) -> SpecTlvContent {
        match e {
            Either::Left(Either::Left(m)) => SpecTlvContent::M1(m),
            Either::Left(Either::Right(m)) => SpecTlvContent::M2(m),
            Either::Right(m) => SpecTlvContent::M3(m),
        }
    }
}

impl<'a> From<TlvContent<'a>> for TlvContentInner<'a> {
    fn ex_from(e: TlvContent) -> (res: TlvContentInner) {
        match e {
            TlvContent::M1(m) => Either::Left(Either::Left(m)),
            TlvContent::M2(m) => Either::Left(Either::Right(m)),
            TlvContent::M3(m) => Either::Right(m),
        }
    }
}

impl<'a> From<TlvContentInner<'a>> for TlvContent<'a> {
    fn ex_from(e: TlvContentInner) -> (res: TlvContent) {
        match e {
            Either::Left(Either::Left(m)) => TlvContent::M1(m),
            Either::Left(Either::Right(m)) => TlvContent::M2(m),
            Either::Right(m) => TlvContent::M3(m),
        }
    }
}

impl From<TlvContentOwned> for TlvContentOwnedInner {
    fn ex_from(e: TlvContentOwned) -> (res: TlvContentOwnedInner) {
        match e {
            TlvContentOwned::M1(m) => Either::Left(Either::Left(m)),
            TlvContentOwned::M2(m) => Either::Left(Either::Right(m)),
            TlvContentOwned::M3(m) => Either::Right(m),
        }
    }
}

impl From<TlvContentOwnedInner> for TlvContentOwned {
    fn ex_from(e: TlvContentOwnedInner) -> (res: TlvContentOwned) {
        match e {
            Either::Left(Either::Left(m)) => TlvContentOwned::M1(m),
            Either::Left(Either::Right(m)) => TlvContentOwned::M2(m),
            Either::Right(m) => TlvContentOwned::M3(m),
        }
    }
}

pub struct TlvContentMapper;

impl View for TlvContentMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for TlvContentMapper {
    type Src = SpecTlvContentInner;

    type Dst = SpecTlvContent;

    proof fn spec_iso(s: SpecTlvContentInner) {
    }

    proof fn spec_iso_rev(s: SpecTlvContent) {
    }
}

impl Iso for TlvContentMapper {
    type Src<'a> = TlvContentInner<'a>;

    type Dst<'a> = TlvContent<'a>;

    type SrcOwned = TlvContentOwnedInner;

    type DstOwned = TlvContentOwned;
}

/// TLV
pub struct SpecTlv {
    pub tag: u8,
    pub len: u8,
    pub content: SpecTlvContent,
    pub rest: Seq<u8>,
}

pub type SpecTlvInner = ((u8, u8), (SpecTlvContent, Seq<u8>));

pub struct Tlv<'a> {
    pub tag: u8,
    pub len: u8,
    pub content: TlvContent<'a>,
    pub rest: &'a [u8],
}

pub type TlvInner<'a> = ((u8, u8), (TlvContent<'a>, &'a [u8]));

pub struct TlvOwned {
    pub tag: u8,
    pub len: u8,
    pub content: TlvContentOwned,
    pub rest: Vec<u8>,
}

pub type TlvInnerOwned = ((u8, u8), (TlvContentOwned, Vec<u8>));

impl View for Tlv<'_> {
    type V = SpecTlv;

    open spec fn view(&self) -> Self::V {
        SpecTlv { tag: self.tag, len: self.len, content: self.content@, rest: self.rest@ }
    }
}

impl View for TlvOwned {
    type V = SpecTlv;

    open spec fn view(&self) -> Self::V {
        SpecTlv { tag: self.tag, len: self.len, content: self.content@, rest: self.rest@ }
    }
}

impl SpecFrom<SpecTlv> for SpecTlvInner {
    open spec fn spec_from(e: SpecTlv) -> SpecTlvInner {
        ((e.tag, e.len), (e.content, e.rest))
    }
}

impl SpecFrom<SpecTlvInner> for SpecTlv {
    open spec fn spec_from(e: SpecTlvInner) -> SpecTlv {
        let ((tag, len), (content, rest)) = e;
        SpecTlv { tag, len, content, rest }
    }
}

impl<'a> From<Tlv<'a>> for TlvInner<'a> {
    fn ex_from(e: Tlv) -> (res: TlvInner) {
        ((e.tag, e.len), (e.content, e.rest))
    }
}

impl<'a> From<TlvInner<'a>> for Tlv<'a> {
    fn ex_from(e: TlvInner) -> (res: Tlv) {
        let ((tag, len), (content, rest)) = e;
        Tlv { tag, len, content, rest }
    }
}

impl From<TlvOwned> for TlvInnerOwned {
    fn ex_from(e: TlvOwned) -> (res: TlvInnerOwned) {
        ((e.tag, e.len), (e.content, e.rest))
    }
}

impl From<TlvInnerOwned> for TlvOwned {
    fn ex_from(e: TlvInnerOwned) -> (res: TlvOwned) {
        let ((tag, len), (content, rest)) = e;
        TlvOwned { tag, len, content, rest }
    }
}

pub struct TlvMapper;

impl View for TlvMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for TlvMapper {
    type Src = SpecTlvInner;

    type Dst = SpecTlv;

    proof fn spec_iso(s: SpecTlvInner) {
    }

    proof fn spec_iso_rev(s: SpecTlv) {
    }
}

impl Iso for TlvMapper {
    type Src<'a> = TlvInner<'a>;

    type Dst<'a> = Tlv<'a>;

    type SrcOwned = TlvInnerOwned;

    type DstOwned = TlvOwned;
}

type Msg1Combinator = Mapped<(((U8, U16), Bytes), Tail), Msg1Mapper>;

type Msg2Combinator = Mapped<((U8, U16), U32), Msg2Mapper>;

type Msg3Combinator = Mapped<BytesN<6>, Msg3Mapper>;

type TlvContentCombinator = AndThen<
    Bytes,
    Mapped<
        OrdChoice<
            OrdChoice<Cond<u8, u8, Msg1Combinator>, Cond<u8, u8, Msg2Combinator>>,
            Cond<u8, u8, Msg3Combinator>,
        >,
        TlvContentMapper,
    >,
>;

type TlvCombinator = Mapped<SpecDepend<(U8, U8), (TlvContentCombinator, Tail)>, TlvMapper>;

// type TlvCombinator = Mapped<Depend<(U8, U8), (TlvContentCombinator, Tail), impl Fn((u8, u8)) -> (TlvContentCombinator, Tail)>, TlvMapper>;
pub open spec fn spec_msg1() -> Msg1Combinator {
    Mapped { inner: (((U8, U16), Bytes(3)), Tail), mapper: Msg1Mapper }
}


pub open spec fn spec_msg2() -> Msg2Combinator {
    Mapped { inner: ((U8, U16), U32), mapper: Msg2Mapper }
}

pub open spec fn spec_msg3() -> Msg3Combinator {
    Mapped { inner: BytesN::<6>, mapper: Msg3Mapper }
}

pub open spec fn spec_tlv_content(tag: u8, len: u8) -> TlvContentCombinator {
    AndThen(
        Bytes(len as usize),
        Mapped {
            inner: OrdChoice(
                OrdChoice(
                    Cond { lhs: tag, rhs: 1, inner: spec_msg1() },
                    Cond { lhs: tag, rhs: 2, inner: spec_msg2() },
                ),
                Cond { lhs: tag, rhs: 3, inner: spec_msg3() },
            ),
            mapper: TlvContentMapper,
        },
    )
}

pub open spec fn spec_tlv() -> TlvCombinator {
    let fst = (U8, U8);
    let snd = |deps|
        {
            let (tag, len) = deps;
            (spec_tlv_content(tag, len), Tail)
        };
    Mapped { inner: SpecDepend { fst, snd }, mapper: TlvMapper }
}

pub fn msg1() -> (o: Msg1Combinator)
    ensures
        o@ == spec_msg1(),
{
    Mapped { inner: (((U8, U16), Bytes(3)), Tail), mapper: Msg1Mapper }
}

pub fn msg2() -> (o: Msg2Combinator)
    ensures
        o@ == spec_msg2(),
{
    Mapped { inner: ((U8, U16), U32), mapper: Msg2Mapper }
}

pub fn msg3() -> (o: Msg3Combinator)
    ensures
        o@ == spec_msg3(),
{
    Mapped { inner: BytesN::<6>, mapper: Msg3Mapper }
}

fn tlv_content(tag: u8, len: u8) -> (o: TlvContentCombinator)
    ensures
        o@ == spec_tlv_content(tag@, len@),
{
    AndThen(
        Bytes(len as usize),
        Mapped {
            inner: OrdChoice(
                OrdChoice(
                    Cond { lhs: tag, rhs: 1, inner: msg1() },
                    Cond { lhs: tag, rhs: 2, inner: msg2() },
                ),
                Cond { lhs: tag, rhs: 3, inner: msg3() },
            ),
            mapper: TlvContentMapper,
        },
    )
}

pub open spec fn spec_msg1_parse(i: Seq<u8>) -> Result<(usize, SpecMsg1), ()> {
    spec_msg1().spec_parse(i)
}

pub open spec fn spec_msg1_serialize(msg: SpecMsg1) -> Result<Seq<u8>, ()> {
    spec_msg1().spec_serialize(msg)
}

pub open spec fn spec_msg2_parse(i: Seq<u8>) -> Result<(usize, Msg2), ()> {
    spec_msg2().spec_parse(i)
}

pub open spec fn spec_msg2_serialize(msg: Msg2) -> Result<Seq<u8>, ()> {
    spec_msg2().spec_serialize(msg)
}

pub open spec fn spec_msg3_parse(i: Seq<u8>) -> Result<(usize, SpecMsg3), ()> {
    spec_msg3().spec_parse(i)
}

pub open spec fn spec_msg3_serialize(msg: SpecMsg3) -> Result<Seq<u8>, ()> {
    spec_msg3().spec_serialize(msg)
}

pub open spec fn spec_tlv_content_parse(i: Seq<u8>, tag: u8, len: u8) -> Result<(usize, SpecTlvContent), ()> {
    spec_tlv_content(tag, len).spec_parse(i)
}

pub open spec fn spec_tlv_content_serialize(msg: SpecTlvContent, tag: u8, len: u8) -> Result<Seq<u8>, ()> {
    spec_tlv_content(tag, len).spec_serialize(msg)
}

pub open spec fn spec_tlv_parse(i: Seq<u8>) -> Result<(usize, SpecTlv), ()> {
    spec_tlv().spec_parse(i)
}

pub open spec fn spec_tlv_serialize(msg: SpecTlv) -> Result<Seq<u8>, ()> {
    spec_tlv().spec_serialize(msg)
}

pub fn msg1_parse(i: &[u8]) -> (o: Result<(usize, Msg1<'_>), ()>)
    ensures
        o matches Ok(r) ==> spec_msg1_parse(i@) matches Ok(r_) && r@ == r_,
{
    msg1().parse(i)
}

pub fn msg1_serialize(msg: Msg1<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& spec_msg1_serialize(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg1().serialize(msg, data, pos)
}

pub fn msg2_parse(i: &[u8]) -> (o: Result<(usize, Msg2), ()>)
    ensures
        o matches Ok(r) ==> spec_msg2_parse(i@) matches Ok(r_) && r@ == r_,
{
    msg2().parse(i)
}

pub fn msg2_serialize(msg: Msg2, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& spec_msg2_serialize(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg2().serialize(msg, data, pos)
}

pub fn msg3_parse(i: &[u8]) -> (o: Result<(usize, Msg3<'_>), ()>)
    ensures
        o matches Ok(r) ==> spec_msg3_parse(i@) matches Ok(r_) && r@ == r_,
{
    msg3().parse(i)
}

pub fn msg3_serialize(msg: Msg3<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& spec_msg3_serialize(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    msg3().serialize(msg, data, pos)
}

fn tlv_content_parse(i: &[u8], tag: u8, len: u8) -> (o: Result<(usize, TlvContent<'_>), ()>)
    ensures
        o matches Ok(r) ==> spec_tlv_content_parse(i@, tag@, len@) matches Ok(r_) && r@ == r_,
{
    tlv_content(tag, len).parse(i)
}

fn tlv_content_serialize(
    msg: TlvContent<'_>,
    data: &mut Vec<u8>,
    pos: usize,
    tag: u8,
    len: u8,
) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& spec_tlv_content_serialize(msg@, tag@, len@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    tlv_content(tag, len).serialize(msg, data, pos)
}

pub fn tlv_parse(i: &[u8]) -> (o: Result<(usize, Tlv<'_>), ()>)
    ensures
        o matches Ok(r) ==> spec_tlv_parse(i@) matches Ok(r_) && r@ == r_,
{
    let ghost spec_snd = |deps|
        {
            let (tag, len) = deps;
            (spec_tlv_content(tag, len), Tail)
        };
    let fst = (U8, U8);
    let snd = |deps: (u8, u8)| -> (o: (TlvContentCombinator, Tail))
        ensures
            o@ == spec_snd(deps@),
        {
            let (tag, len) = deps;
            (tlv_content(tag, len), Tail)
        };
    Mapped { inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) }, mapper: TlvMapper }.parse(
        i,
    )
}

pub fn tlv_serialize(msg: Tlv<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, ()>)
    ensures
        o matches Ok(n) ==> {
            &&& spec_tlv_serialize(msg@) matches Ok(buf)
            &&& n == buf.len() && data@ == seq_splice(old(data)@, pos, buf)
        },
{
    let ghost spec_snd = |deps|
        {
            let (tag, len) = deps;
            (spec_tlv_content(tag, len), Tail)
        };
    let fst = (U8, U8);
    let snd = |deps: (u8, u8)| -> (o: (TlvContentCombinator, Tail))
        ensures
            o@ == spec_snd(deps@),
        {
            let (tag, len) = deps;
            (tlv_content(tag, len), Tail)
        };
    Mapped { inner: Depend { fst, snd, spec_snd: Ghost(spec_snd) }, mapper: TlvMapper }.serialize(
        msg,
        data,
        pos,
    )
}

} // verus!
