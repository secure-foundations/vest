use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::OrdChoice;
use vest::regular::choice::*;
use vest::regular::map::*;
use vest::regular::preceded::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Message type 1
pub struct SpecMsg1 {
    pub a: u8,
    pub b: u16,
    pub c: Seq<u8>,
    pub d: Seq<u8>,
}

pub type SpecMsg1Inner = (u8, (u16, (Seq<u8>, Seq<u8>)));

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

pub type Msg1Inner<'a> = (u8, (u16, (&'a [u8], &'a [u8])));

pub type Msg1InnerOwned = (u8, (u16, (Vec<u8>, Vec<u8>)));

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
        (t.a, (t.b, (t.c, t.d)))
    }
}

impl SpecFrom<SpecMsg1Inner> for SpecMsg1 {
    open spec fn spec_from(e: SpecMsg1Inner) -> SpecMsg1 {
        let (a, (b, (c, d))) = e;
        SpecMsg1 { a, b, c, d }
    }
}

impl<'a> From<Msg1<'a>> for Msg1Inner<'a> {
    fn ex_from(e: Msg1) -> (res: Msg1Inner) {
        (e.a, (e.b, (e.c, e.d)))
    }
}

impl<'a> From<Msg1Inner<'a>> for Msg1<'a> {
    fn ex_from(e: Msg1Inner) -> (res: Msg1) {
        let (a, (b, (c, d))) = e;
        Msg1 { a, b, c, d }
    }
}

impl From<Msg1Owned> for Msg1InnerOwned {
    fn ex_from(e: Msg1Owned) -> (res: Msg1InnerOwned) {
        (e.a, (e.b, (e.c, e.d)))
    }
}

impl From<Msg1InnerOwned> for Msg1Owned {
    fn ex_from(e: Msg1InnerOwned) -> (res: Msg1Owned) {
        let (a, (b, (c, d))) = e;
        Msg1Owned { a, b, c, d }
    }
}

fn test() {
    let bytes1: [u8; 3] = [1, 2, 3];
    let bytes2: [u8; 3] = [4, 5, 6];
    let e = Msg1 { a: 1, b: 2, c: bytes1.as_slice(), d: bytes2.as_slice() };
    let (a, (b, (c, d))) = Msg1Inner::ex_from(e);
    assert(a == 1);
    assert(b == 2);
    assert(c@ == seq![1u8, 2, 3]);
    assert(d@ == seq![4u8, 5, 6]);
    let e2 = Msg1::ex_from((a, (b, (c, d))));
    assert(e2.a == 1);
    assert(e2.b == 2);
    assert(e2.c@ == seq![1u8, 2, 3]);
    assert(e2.d@ == seq![4u8, 5, 6]);
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

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
fn parse_serialize() -> Result<(), ()> {
    let msg_inner = (U8, (U16, (Bytes(3), Tail)));
    let msg = Mapped { inner: msg_inner, mapper: Msg1Mapper };
    let mut data = my_vec![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = msg.parse(data.as_slice())?;
    let len = msg.serialize(val, &mut s, 0)?;
    proof {
        msg.theorem_parse_serialize_roundtrip(data@);
        assert(data@.subrange(0, n as int) == s@.subrange(0, len as int));
        assert(s@.subrange(0, len as int) == seq![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
fn serialize_parse() -> Result<(), ()> {
    let msg_inner = (U8, (U16, (Bytes(3), Tail)));
    let msg = Mapped { inner: msg_inner, mapper: Msg1Mapper };
    let bytes1: [u8; 3] = [0u8, 0u8, 1u8];
    let bytes2: [u8; 3] = [0u8, 0u8, 2u8];
    let val = Msg1 { a: 1, b: 123, c: bytes1.as_slice(), d: bytes2.as_slice() };
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len = msg.serialize(val, &mut s1, 0)?;
    let s_ = slice_subrange(s1.as_slice(), 0, len);
    let (n, val_) = msg.parse(s_)?;
    proof {
        msg.theorem_serialize_parse_roundtrip(val@);
        assert(n == len);
        // assert(val@ == val_@); // rlimit exceeded
        // assert(val_@ == SpecMsg1 { a: 1, b: 123, c: bytes1@, d: bytes2@ });
    }
    Ok(())
}

/// Message type 2
pub struct Msg2 {
    pub a: u8,
    pub b: u16,
    pub c: u32,
}

pub type Msg2Inner = (u8, (u16, u32));

impl View for Msg2 {
    type V = Msg2;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecFrom<Msg2> for Msg2Inner {
    open spec fn spec_from(t: Msg2) -> Msg2Inner {
        (t.a, (t.b, t.c))
    }
}

impl From<Msg2> for Msg2Inner {
    fn ex_from(e: Msg2) -> (res: Msg2Inner) {
        (e.a, (e.b, e.c))
    }
}

impl SpecFrom<Msg2Inner> for Msg2 {
    open spec fn spec_from(e: Msg2Inner) -> Msg2 {
        let (a, (b, c)) = e;
        Msg2 { a, b, c }
    }
}

impl From<Msg2Inner> for Msg2 {
    fn ex_from(e: Msg2Inner) -> (res: Msg2) {
        let (a, (b, c)) = e;
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

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
fn parse_serialize2() -> Result<(), ()> {
    let msg_inner = (U8, (U16, U32));
    let msg = Mapped { inner: msg_inner, mapper: Msg2Mapper };
    let mut data = my_vec![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = msg.parse(data.as_slice())?;
    let len = msg.serialize(val, &mut s, 0)?;
    proof {
        msg.theorem_parse_serialize_roundtrip(data@);
        assert(data@.subrange(0, n as int) == s@.subrange(0, len as int));
        assert(s@.subrange(0, len as int) == seq![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
fn serialize_parse2() -> Result<(), ()> {
    let msg_inner = (U8, (U16, U32));
    let msg = Mapped { inner: msg_inner, mapper: Msg2Mapper };
    let val = Msg2 { a: 1, b: 123, c: 1 };
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len = msg.serialize(val, &mut s1, 0)?;
    let s_ = slice_subrange(s1.as_slice(), 0, len);
    let (n, val_) = msg.parse(s_)?;
    proof {
        msg.theorem_serialize_parse_roundtrip(val@);
        assert(n == len);
        // assert(val@ == val_@); // rlimit exceeded
        // assert(val_@ == Msg2 { a: 1, b: 123, c: 1 });
    }
    Ok(())
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

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
fn parse_serialize3() -> Result<(), ()> {
    let msg_inner = BytesN::<6>;
    let msg = Mapped { inner: msg_inner, mapper: Msg3Mapper };
    let mut data = my_vec![1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = msg.parse(data.as_slice())?;
    let len = msg.serialize(val, &mut s, 0)?;
    proof {
        assert(n == 6);
        msg.theorem_parse_serialize_roundtrip(data@);
        assert(data@.subrange(0, n as int) == s@.subrange(0, len as int));
        assert(s@.subrange(0, len as int) == seq![1u8, 2u8, 3u8, 4u8, 5u8, 6u8]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
fn serialize_parse3() -> Result<(), ()> {
    let msg_inner = BytesN::<6>;
    let msg = Mapped { inner: msg_inner, mapper: Msg3Mapper };
    let bytes: [u8; 6] = [1, 2, 3, 4, 5, 6];
    let val = Msg3 { a: bytes.as_slice() };
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len = msg.serialize(val, &mut s1, 0)?;
    let s_ = slice_subrange(s1.as_slice(), 0, len);
    let (n, val_) = msg.parse(s_)?;
    proof {
        msg.theorem_serialize_parse_roundtrip(val@);
        assert(n == len);
        // assert(val@ == val_@); // rlimit exceeded
        // assert(val_@ == SpecMsg3 { a: bytes@ });
    }
    Ok(())
}

/// Message type 4
pub enum SpecMsg4 {
    M1(SpecMsg1),
    M2(Msg2),
    M3(SpecMsg3),
}

pub type SpecMsg4Inner = Either<Either<SpecMsg1, Msg2>, SpecMsg3>;

pub enum Msg4<'a> {
    M1(Msg1<'a>),
    M2(Msg2),
    M3(Msg3<'a>),
}

pub enum Msg4Owned {
    M1(Msg1Owned),
    M2(Msg2),
    M3(Msg3Owned),
}

pub type Msg4Inner<'a> = Either<Either<Msg1<'a>, Msg2>, Msg3<'a>>;

pub type Msg4InnerOwned = Either<Either<Msg1Owned, Msg2>, Msg3Owned>;

impl View for Msg4<'_> {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        match self {
            Msg4::M1(m) => SpecMsg4::M1(m@),
            Msg4::M2(m) => SpecMsg4::M2(m@),
            Msg4::M3(m) => SpecMsg4::M3(m@),
        }
    }
}

impl View for Msg4Owned {
    type V = SpecMsg4;

    open spec fn view(&self) -> Self::V {
        match self {
            Msg4Owned::M1(m) => SpecMsg4::M1(m@),
            Msg4Owned::M2(m) => SpecMsg4::M2(m@),
            Msg4Owned::M3(m) => SpecMsg4::M3(m@),
        }
    }
}

impl SpecFrom<SpecMsg4> for SpecMsg4Inner {
    open spec fn spec_from(e: SpecMsg4) -> SpecMsg4Inner {
        match e {
            SpecMsg4::M1(m) => Either::Left(Either::Left(m)),
            SpecMsg4::M2(m) => Either::Left(Either::Right(m)),
            SpecMsg4::M3(m) => Either::Right(m),
        }
    }
}

impl SpecFrom<SpecMsg4Inner> for SpecMsg4 {
    open spec fn spec_from(e: SpecMsg4Inner) -> SpecMsg4 {
        match e {
            Either::Left(Either::Left(m)) => SpecMsg4::M1(m),
            Either::Left(Either::Right(m)) => SpecMsg4::M2(m),
            Either::Right(m) => SpecMsg4::M3(m),
        }
    }
}

impl<'a> From<Msg4<'a>> for Msg4Inner<'a> {
    fn ex_from(e: Msg4) -> (res: Msg4Inner) {
        match e {
            Msg4::M1(m) => Either::Left(Either::Left(m)),
            Msg4::M2(m) => Either::Left(Either::Right(m)),
            Msg4::M3(m) => Either::Right(m),
        }
    }
}

impl<'a> From<Msg4Inner<'a>> for Msg4<'a> {
    fn ex_from(e: Msg4Inner) -> (res: Msg4) {
        match e {
            Either::Left(Either::Left(m)) => Msg4::M1(m),
            Either::Left(Either::Right(m)) => Msg4::M2(m),
            Either::Right(m) => Msg4::M3(m),
        }
    }
}

impl From<Msg4Owned> for Msg4InnerOwned {
    fn ex_from(e: Msg4Owned) -> (res: Msg4InnerOwned) {
        match e {
            Msg4Owned::M1(m) => Either::Left(Either::Left(m)),
            Msg4Owned::M2(m) => Either::Left(Either::Right(m)),
            Msg4Owned::M3(m) => Either::Right(m),
        }
    }
}

impl From<Msg4InnerOwned> for Msg4Owned {
    fn ex_from(e: Msg4InnerOwned) -> (res: Msg4Owned) {
        match e {
            Either::Left(Either::Left(m)) => Msg4Owned::M1(m),
            Either::Left(Either::Right(m)) => Msg4Owned::M2(m),
            Either::Right(m) => Msg4Owned::M3(m),
        }
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

    proof fn spec_iso(s: SpecMsg4Inner) {
    }

    proof fn spec_iso_rev(s: SpecMsg4) {
    }
}

impl Iso for Msg4Mapper {
    type Src<'a> = Msg4Inner<'a>;

    type Dst<'a> = Msg4<'a>;

    type SrcOwned = Msg4InnerOwned;

    type DstOwned = Msg4Owned;
}

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
fn parse_serialize4() -> Result<(), ()> {
    let tag1 = Tag::new(U8, 1);
    let tag2 = Tag::new(U8, 2);
    let tag3 = Tag::new(U8, 3);
    let msg1 = Preceded(tag1, Mapped { inner: (U8, (U16, (Bytes(3), Tail))), mapper: Msg1Mapper });
    let msg2 = Preceded(tag2, Mapped { inner: (U8, (U16, U32)), mapper: Msg2Mapper });
    let msg3 = Preceded(tag3, Mapped { inner: BytesN::<6>, mapper: Msg3Mapper });
    let msg_inner = OrdChoice(OrdChoice(msg1, msg2), msg3);
    let msg = Mapped { inner: msg_inner, mapper: Msg4Mapper };
    let mut data = my_vec![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = msg.parse(data.as_slice())?;
    let len = msg.serialize(val, &mut s, 0)?;
    proof {
        msg.theorem_parse_serialize_roundtrip(data@);
        assert(data@.subrange(0, n as int) == s@.subrange(0, len as int));
        assert(s@.subrange(0, len as int) == seq![1u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
    }
    let mut data = my_vec![3u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = msg.parse(data.as_slice())?;
    let len = msg.serialize(val, &mut s, 0)?;
    proof {
        msg.theorem_parse_serialize_roundtrip(data@);
        assert(data@.subrange(0, n as int) == s@.subrange(0, len as int));
        assert(s@.subrange(0, len as int) == seq![3u8, 123u8, 1u8, 0u8, 0u8, 0u8, 0u8]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
fn serialize_parse4() -> Result<(), ()> {
    let tag1 = Tag::new(U8, 1);
    let tag2 = Tag::new(U8, 2);
    let tag3 = Tag::new(U8, 3);
    let msg1 = Preceded(tag1, Mapped { inner: (U8, (U16, (Bytes(3), Tail))), mapper: Msg1Mapper });
    let msg2 = Preceded(tag2, Mapped { inner: (U8, (U16, U32)), mapper: Msg2Mapper });
    let msg3 = Preceded(tag3, Mapped { inner: BytesN::<6>, mapper: Msg3Mapper });
    let msg_inner = OrdChoice(OrdChoice(msg1, msg2), msg3);
    let msg = Mapped { inner: msg_inner, mapper: Msg4Mapper };
    let bytes1: [u8; 3] = [0u8, 0u8, 1u8];
    let bytes2: [u8; 3] = [0u8, 0u8, 2u8];
    let val = Msg4::M1(Msg1 { a: 1, b: 123, c: bytes1.as_slice(), d: bytes2.as_slice() });
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len = msg.serialize(val, &mut s1, 0)?;
    let s_ = slice_subrange(s1.as_slice(), 0, len);
    let (n, val_) = msg.parse(s_)?;
    proof {
        msg@.theorem_serialize_parse_roundtrip(val@);
        assert(n == len);
        // assert(val@ == val_@);
        // assert(val_@ == SpecMsg4::M1(SpecMsg1 { a: 1, b: 123, c: bytes1@, d: bytes2@ }));
    }
    let val = Msg4::M3(Msg3 { a: bytes1.as_slice() });
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0];
    let len = msg.serialize(val, &mut s1, 0)?;
    let s_ = slice_subrange(s1.as_slice(), 0, len);
    let (n, val_) = msg.parse(s_)?;
    proof {
        msg@.theorem_serialize_parse_roundtrip(val@);
        assert(n == len);
        assert(val@ == val_@);
        assert(val_@ == SpecMsg4::M3(SpecMsg3 { a: bytes1@ }));
    }
    Ok(())
}

} // verus!
