//! ```vest
//! msg1 = [u8; 32]
//! msg2 = {
//!   a: u8,
//!   b: Vec<u32>,
//! }
//! msg3 = {
//!   x: u16,
//!   y: u16,
//! }
//!
//! msg = {
//!   @tag: u8,
//!   @len: u16,
//!   val: [u8; @len] >>=
//!     choose (@tag) {
//!       1 => msg1,
//!       2 => msg2,
//!       3 => msg3,
//!   },
//! }
//! ```
//!
//!
//! ```rust
//! Mapped(Pair(
//!   (U8, U16Le),
//!   |(tag, len)| FixedLen(
//!     len as usize,
//!     Dispatch(
//!       tag,
//!       [
//!         (1, Msg1),
//!         (2, Msg2),
//!         (3, Msg3),
//!       ],
//!     )
//!   )
//! ),
//! MsgMapper)
//! ```

use vest_lib::enum_combinator;
use vest_lib::properties::*;
use vest_lib::regular::bytes::Fixed;
use vest_lib::regular::modifier::{FixedLen, Length, Mapped, Mapper, RuntimeValue};
use vest_lib::regular::repetition::RepeatN;
use vest_lib::regular::sequence::{DepCombinator, Pair};
use vest_lib::regular::uints::{U16Le, U32Le, U8};
use vest_lib::regular::variant::Dispatch;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg2 {
    pub a: u8,
    pub b: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Msg3 {
    pub x: u16,
    pub y: u16,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValue<'a> {
    Msg1(&'a [u8]),
    Msg2(Msg2),
    Msg3(Msg3),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgValueOwned {
    Msg1(Vec<u8>),
    Msg2(Msg2),
    Msg3(Msg3),
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

impl From<(u16, u16)> for Msg3 {
    fn from((x, y): (u16, u16)) -> Self {
        Msg3 { x, y }
    }
}

impl<'s> From<&'s Msg3> for (u16, u16) {
    fn from(m: &'s Msg3) -> Self {
        (m.x, m.y)
    }
}

impl<'a> From<((u8, u16), MsgValue<'a>)> for Message<'a> {
    fn from(((tag, len), val): ((u8, u16), MsgValue<'a>)) -> Self {
        Message { tag, len, val }
    }
}

impl<'s, 'a: 's> From<&'s Message<'a>> for ((u8, u16), &'s MsgValue<'s>) {
    fn from(msg: &'s Message<'a>) -> Self {
        ((msg.tag, msg.len), &msg.val)
    }
}

impl From<((u8, u16), MsgValueOwned)> for MessageOwned {
    fn from(((tag, len), val): ((u8, u16), MsgValueOwned)) -> Self {
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

struct Msg3Mapper;

impl Mapper for Msg3Mapper {
    type Src<'p> = (u16, u16);
    type Dst<'p> = Msg3;
    type SrcBorrow<'s> = (u16, u16);
    type DstBorrow<'s> = &'s Msg3;
    type SrcOwned = (u16, u16);
    type DstOwned = Msg3;
}

struct MsgMapper;

impl Mapper for MsgMapper {
    type Src<'p> = ((u8, u16), MsgValue<'p>);
    type Dst<'p> = Message<'p>;
    type SrcBorrow<'s> = ((u8, u16), &'s MsgValue<'s>);
    type DstBorrow<'s> = &'s Message<'s>;
    type SrcOwned = ((u8, u16), MsgValueOwned);
    type DstOwned = MessageOwned;
}

type Msg2Comb = Mapped<(U8, RepeatN<U32Le>), Msg2Mapper>;
type Msg3Comb = Mapped<(U16Le, U16Le), Msg3Mapper>;
type PayloadComb<'g> = FixedLen<'g, Dispatch<'g, u8, PayloadCases, 3>>;
type TlvComb = Mapped<Pair<(U8, U16Le), PayloadDep>, MsgMapper>;
struct PayloadDep;

enum_combinator! {

enum PayloadCases {
    Msg1(Fixed<32>),
    Msg2(Msg2Comb),
    Msg3(Msg3Comb),
}
impl Combinator<[u8], Vec<u8>> {
    type Type<'p> = MsgValue<'p>;
    type SType<'s> = &'s MsgValue<'s>;
    type GType = MsgValueOwned;
}

}

fn msg2_combinator() -> Msg2Comb {
    Mapped::new((U8, RepeatN(U32Le, 3)), Msg2Mapper)
}

fn msg3_combinator() -> Msg3Comb {
    Mapped::new((U16Le, U16Le), Msg3Mapper)
}

fn payload_combinator<'a>(tag: RuntimeValue<'a, u8>, len: Length<'a>) -> PayloadComb<'a> {
    FixedLen(
        len,
        Dispatch::new(
            tag,
            [
                (1, PayloadCases::Msg1(Fixed::<32>)),
                (2, PayloadCases::Msg2(msg2_combinator())),
                (3, PayloadCases::Msg3(msg3_combinator())),
            ],
        ),
    )
}

fn tlv_combinator() -> TlvComb {
    Mapped::new(Pair::new((U8, U16Le), PayloadDep), MsgMapper)
}

impl DepCombinator<(U8, U16Le), [u8], Vec<u8>> for PayloadDep {
    type Out = PayloadComb<'static>;
    type OutGen<'g> = PayloadComb<'g>;

    fn dep_snd<'s>(&self, fst: (u8, u16)) -> Self::Out {
        payload_combinator(
            RuntimeValue::from_value(fst.0),
            Length::from_value(fst.1.into()),
        )
    }

    fn dep_snd_gen<'g>(&self, fst: &'g mut (u8, u16)) -> Self::OutGen<'g> {
        payload_combinator(
            RuntimeValue::from_mut(&mut fst.0),
            Length::from_u16_mut(&mut fst.1),
        )
    }
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

fn example_msg3() {
    println!("\n=== TLV msg3 (tag=3, len=4) ===");

    let comb = tlv_combinator();
    let msg3_payload = Msg3 {
        x: 0x1234,
        y: 0xABCD,
    };
    let msg = Message {
        tag: 3,
        len: 4,
        val: MsgValue::Msg3(msg3_payload),
    };

    let len = <_ as Combinator<_, Vec<u8>>>::length(&comb, &msg);
    let mut buf = vec![0u8; len];
    let written = comb.serialize(&msg, &mut buf, 0).expect("serialize");

    println!("  Serialized bytes ({}): {:02X?}", written, &buf[..written]);
    let (consumed, parsed) =
        <_ as Combinator<_, Vec<u8>>>::parse(&comb, &buf[..written]).expect("parse msg3");
    println!(
        "  Parsed: tag={}, len={}, val={:02X?}",
        parsed.tag, parsed.len, parsed.val
    );

    assert_eq!(consumed, written);
    assert_eq!(parsed.tag, msg.tag);
    assert_eq!(parsed.len, msg.len);
    assert_eq!(parsed.val, msg.val);
    println!("  msg3 roundtrip passed!");
}

fn example_msg_generation() {
    println!("\n=== TLV message generation ===");

    let mut comb = tlv_combinator();

    for s in 1..30 {
        let mut gen_st = GenSt::new(s);
        let (len, gen_msg) = comb.generate(&mut gen_st).expect("generate message");
        println!(
            "  Generated message (len={}): tag={}, len={}, val={:02X?}",
            len, gen_msg.tag, gen_msg.len, gen_msg.val
        );
    }
}

fn main() {
    example_msg1();
    example_msg2();
    example_msg3();
    example_msg_generation();
}
