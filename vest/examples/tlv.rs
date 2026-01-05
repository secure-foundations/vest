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
use vest_lib::regular::modifier::{AndThen, Cond, Mapped, Mapper};
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

/// A borrowed view of MsgValue for serialization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MsgValueRef<'a, 'b> {
    Msg1(&'a [u8]),
    Msg2(&'b Msg2),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message<'a> {
    pub tag: u8,
    pub len: u16,
    pub val: MsgValue<'a>,
}

/// A borrowed view of Message for serialization
#[derive(Debug, Clone, Copy)]
pub struct MessageRef<'a, 'b> {
    pub tag: u8,
    pub len: u16,
    pub val: MsgValueRef<'a, 'b>,
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

impl<'a, 's> From<MessageRef<'a, 's>> for ((u8, u16), Either<&'a [u8], &'s Msg2>) {
    fn from(msg: MessageRef<'a, 's>) -> Self {
        let val = match msg.val {
            MsgValueRef::Msg1(bytes) => Either::Left(bytes),
            MsgValueRef::Msg2(m2) => Either::Right(m2),
        };
        ((msg.tag, msg.len), val)
    }
}

impl<'a> Message<'a> {
    /// Create a reference view for serialization
    pub fn as_ref<'s>(&'s self) -> MessageRef<'a, 's> {
        let val = match &self.val {
            MsgValue::Msg1(bytes) => MsgValueRef::Msg1(*bytes),
            MsgValue::Msg2(m2) => MsgValueRef::Msg2(m2),
        };
        MessageRef {
            tag: self.tag,
            len: self.len,
            val,
        }
    }
}

struct Msg2Mapper;

impl Mapper for Msg2Mapper {
    type Src = (u8, Vec<u32>);
    type Dst = Msg2;
    type SrcBorrow<'s> = (u8, &'s [u32]);
    type DstBorrow<'s> = &'s Msg2;
}

struct MsgMapper<'a>(std::marker::PhantomData<&'a ()>);

impl<'a> MsgMapper<'a> {
    fn new() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<'a> Mapper for MsgMapper<'a> {
    type Src = ((u8, u16), Either<&'a [u8], Msg2>);
    type Dst = Message<'a>;
    type SrcBorrow<'s> = ((u8, u16), Either<&'a [u8], &'s Msg2>);
    type DstBorrow<'s> = MessageRef<'a, 's>;
    // type DstBorrow<'s> = &'s Message<'a> where 'a: 's;
}

type Msg2Comb = Mapped<(U8, RepeatN<U32Le>), Msg2Mapper>;
type PayloadChoice = Choice<Cond<Fixed<32>>, Cond<Msg2Comb>>;
type PayloadComb = AndThen<Variable, PayloadChoice>;
type TlvComb<'a> =
    Mapped<Pair<(U8, U16Le), PayloadComb, fn((u8, u16)) -> PayloadComb>, MsgMapper<'a>>;

fn msg2_combinator() -> Msg2Comb {
    Mapped::new((U8, RepeatN(U32Le, 3)), Msg2Mapper)
}

fn payload_combinator((tag, len): (u8, u16)) -> PayloadComb {
    let choice = Choice(
        Cond {
            cond: tag == 1,
            inner: Fixed::<32>,
        },
        Cond {
            cond: tag == 2,
            inner: msg2_combinator(),
        },
    );
    AndThen(Variable(len as usize), choice)
}

// fn payload_combinator_fn(input: (u8, u16)) -> PayloadComb {
//     let (tag, len) = input;
//     payload_combinator(tag, len)
// }

fn tlv_combinator<'a>() -> TlvComb<'a> {
    Mapped::new(Pair::new((U8, U16Le), payload_combinator), MsgMapper::new())
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

    let mut buf = vec![0u8; 64];
    // let written = serialize_fn(&comb, &msg, &mut buf, 0).expect("serialize");
    let written = comb
        .serialize(msg.as_ref(), &mut buf, 0)
        .expect("serialize");

    println!("  Serialized bytes ({}): {:02X?}", written, &buf[..written]);
    let (consumed, parsed) = <_ as Combinator<_, Vec<u8>>>::parse(&comb, &buf[..written]).expect("parse msg1");
    println!(
        "  Parsed: tag={}, len={}, val={:02X?}",
        parsed.tag, parsed.len, parsed.val
    );

    assert_eq!(consumed, written);
    assert_eq!(parsed.tag, 1);
    assert_eq!(parsed.len, 32);
    assert_eq!(parsed.val, MsgValue::Msg1(msg1_payload));
    println!("  msg1 roundtrip passed!");
}

fn main() {
    example_msg1();
}
