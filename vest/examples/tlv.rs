//! ```vest
//! msg1 = [u8; 32]
//! msg2 = {
//!   a: u8,
//!   b: Vec<u32>,
//! }
//!
//! msg = {
//!   @tag: u8,
//!   @len: u16,
//!   val: [u8; @len] >>=
//!     choose (@tag) {
//!       1 => msg1,
//!       2 => msg2,
//!   },
//! }
//! ```
//!
//!
//! ```rust
//! Mapped(Pair(
//!   (U8, U16Le),
//!   |(tag, len)| AndThen(
//!     Variable(len as usize),
//!     Choice(
//!       Cond { cond: tag == 1, inner: Msg1 },
//!       Cond { cond: tag == 2, inner: Msg2 },
//!     )
//!   )
//! ),
//! MsgMapper)
//! ```

use vest_lib::properties::*;
use vest_lib::regular::bytes::{Fixed, Variable};
use vest_lib::regular::modifier::{AndThen, CondEq, FixedLen, Mapped, Mapper};
use vest_lib::regular::repetition::RepeatN;
use vest_lib::regular::sequence::Pair;
use vest_lib::regular::uints::{U16Le, U32Le, U8};
use vest_lib::regular::variant::{Choice, Either};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg2 {
    pub a: u8,
    pub b: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValue<'a> {
    Msg1(&'a [u8]),
    Msg2(Msg2),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValueOwned {
    Msg1(Vec<u8>),
    Msg2(Msg2),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message<'a> {
    pub tag: u8,
    pub len: u16,
    pub val: MsgValue<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessageOwned {
    pub tag: u8,
    pub len: u16,
    pub val: MsgValueOwned,
}

impl From<(u8, Vec<u32>)> for Msg2 {
    fn from((a, b): (u8, Vec<u32>)) -> Self {
        Msg2 { a, b }
    }
}

impl<'s> From<&'s Msg2> for (u8, &'s [u32]) {
    fn from(m: &'s Msg2) -> Self {
        (m.a, &m.b)
    }
}

impl<'a> From<((u8, u16), Either<&'a [u8], Msg2>)> for Message<'a> {
    fn from(((tag, len), val): ((u8, u16), Either<&'a [u8], Msg2>)) -> Self {
        let val = match val {
            Either::Left(bytes) => MsgValue::Msg1(bytes),
            Either::Right(m2) => MsgValue::Msg2(m2),
        };
        Message { tag, len, val }
    }
}

impl<'s, 'a: 's> From<&'s Message<'a>> for ((u8, u16), Either<&'a [u8], &'s Msg2>) {
    fn from(msg: &'s Message<'a>) -> Self {
        let val = match &msg.val {
            MsgValue::Msg1(bytes) => Either::Left(*bytes),
            MsgValue::Msg2(m2) => Either::Right(m2),
        };
        ((msg.tag, msg.len), val)
    }
}

impl From<((u8, u16), Either<Vec<u8>, Msg2>)> for MessageOwned {
    fn from(((tag, len), val): ((u8, u16), Either<Vec<u8>, Msg2>)) -> Self {
        let val = match val {
            Either::Left(bytes) => MsgValueOwned::Msg1(bytes),
            Either::Right(m2) => MsgValueOwned::Msg2(m2),
        };
        MessageOwned { tag, len, val }
    }
}

struct Msg2Mapper;

impl Mapper for Msg2Mapper {
    type Src<'p> = (u8, Vec<u32>);
    type Dst<'p> = Msg2;
    type SrcBorrow<'s> = (u8, &'s [u32]);
    type DstBorrow<'s> = &'s Msg2;
    type SrcOwned = (u8, Vec<u32>);
    type DstOwned = Msg2;
}

struct MsgMapper;

impl Mapper for MsgMapper {
    type Src<'p> = ((u8, u16), Either<&'p [u8], Msg2>);
    type Dst<'p> = Message<'p>;
    type SrcBorrow<'s> = ((u8, u16), Either<&'s [u8], &'s Msg2>);
    type DstBorrow<'s> = &'s Message<'s>;
    type SrcOwned = ((u8, u16), Either<Vec<u8>, Msg2>);
    type DstOwned = MessageOwned;
}

type Msg2Comb = Mapped<(U8, RepeatN<U32Le>), Msg2Mapper>;
type PayloadChoice = Choice<CondEq<u8, Fixed<32>>, CondEq<u8, Msg2Comb>>;
// type PayloadComb = AndThen<Variable, PayloadChoice>;
type PayloadComb = FixedLen<PayloadChoice>;
type TlvComb = Mapped<Pair<(U8, U16Le), PayloadComb, fn((u8, u16)) -> PayloadComb>, MsgMapper>;

fn msg2_combinator() -> Msg2Comb {
    Mapped::new((U8, RepeatN(U32Le, 3)), Msg2Mapper)
}

fn payload_combinator((tag, len): (u8, u16)) -> PayloadComb {
    let choice = Choice(
        CondEq {
            lhs: tag,
            rhs: 1,
            inner: Fixed::<32>,
        },
        CondEq {
            lhs: tag,
            rhs: 2,
            inner: msg2_combinator(),
        },
    );
    // AndThen(Variable(len as usize), choice)
    FixedLen(len as usize, choice)
}

fn tlv_combinator() -> TlvComb {
    Mapped::new(Pair::new((U8, U16Le), payload_combinator), MsgMapper)
}

fn example_msg1() {
    println!("\n=== TLV msg1 (tag=1, len=32) ===");

    let comb = tlv_combinator();
    let msg1_payload: [u8; 32] = *b"0123456789ABCDEF0123456789ABCDEF";
    let msg1_payload: &[u8] = &msg1_payload;
    let msg = Message {
        tag: 1,
        len: 32,
        val: MsgValue::Msg1(msg1_payload),
    };

    let len = <_ as Combinator<_, Vec<u8>>>::length(&comb, &msg);
    let mut buf = vec![0u8; len];
    let written = comb.serialize(&msg, &mut buf, 0).expect("serialize");

    println!("  Serialized bytes ({}): {:02X?}", written, &buf[..written]);
    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&comb, &buf[..written]).expect("parse msg1");
    println!(
        "  Parsed: tag={}, len={}, val={:02X?}",
        parsed.tag, parsed.len, parsed.val
    );

    assert_eq!(consumed, written);
    assert_eq!(parsed.tag, msg.tag);
    assert_eq!(parsed.len, msg.len);
    assert_eq!(parsed.val, msg.val);
    println!("  msg1 roundtrip passed!");
}

fn example_msg2() {
    println!("\n=== TLV msg2 (tag=2, len=13) ===");

    let comb = tlv_combinator();
    let msg2_payload = Msg2 {
        a: 0x42,
        b: vec![0x11223344, 0x55667788, 0x99AABBCC],
    };
    let msg = Message {
        tag: 2,
        len: 13,
        val: MsgValue::Msg2(msg2_payload),
    };

    let len = <_ as Combinator<_, Vec<u8>>>::length(&comb, &msg);
    let mut buf = vec![0u8; len];
    let written = comb.serialize(&msg, &mut buf, 0).expect("serialize");

    println!("  Serialized bytes ({}): {:02X?}", written, &buf[..written]);
    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&comb, &buf[..written]).expect("parse msg2");
    println!(
        "  Parsed: tag={}, len={}, val={:2X?}",
        parsed.tag, parsed.len, parsed.val
    );

    assert_eq!(consumed, written);
    assert_eq!(parsed.tag, msg.tag);
    assert_eq!(parsed.len, msg.len);
    assert_eq!(parsed.val, msg.val);
    println!("  msg2 roundtrip passed!");
}

fn example_msg_generation() {
    println!("\n=== TLV message generation ===");

    let comb = tlv_combinator();
    let mut gen_st = GenSt::new(1);

    let (len, gen_msg) = comb.generate(&mut gen_st).expect("generate message");
    println!(
        "  Generated message (len={}): tag={}, len={}, val={:02X?}",
        len, gen_msg.tag, gen_msg.len, gen_msg.val
    );
}

fn main() {
    example_msg1();
    example_msg2();
    example_msg_generation();
}
