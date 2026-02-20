//! ```vest
//! msg1 = [u8; 32]
//! msg2 = RefinedPacket
//! msg3 = {
//!   x: u16,
//!   y: u16,
//! }
//!
//! msg = {
//!   @tag: u8,
//!   @len: u16 | 0..8000,
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
//!   (U8, Refined(U16Le, |len| len <= 8000)),
//!   |(tag, len)| FixedLen(
//!     len as usize,
//!     Dispatch(
//!       tag,
//!       [
//!         (1, Msg1),
//!         (2, RefinedPacket),
//!         (3, Msg3),
//!       ],
//!     )
//!   )
//! ),
//! MsgMapper)
//! ```

#[allow(dead_code)]
#[path = "combined.rs"]
mod combined;

use vest_lib::enum_combinator;
use vest_lib::properties::*;
use vest_lib::regular::bytes::Fixed;
use vest_lib::regular::modifier::{FixedLen, Length, Mapped, Mapper, Refined, RuntimeValue};
use vest_lib::regular::sequence::{DepCombinator, Pair};
use vest_lib::regular::uints::{U16Le, U8};
use vest_lib::regular::variant::Dispatch;

type Msg2 = combined::RefinedPacket;

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

type Msg2Comb = combined::RefinedPacketCombinator;
type Msg3Comb = Mapped<(U16Le, U16Le), Msg3Mapper>;
type PayloadComb<'g> = FixedLen<'g, Dispatch<'g, u8, PayloadCases, 3>>;
type OuterLenComb = Refined<U16Le, fn(u16) -> bool>;
type TlvComb = Mapped<Pair<(U8, OuterLenComb), PayloadDep>, MsgMapper>;

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
    combined::refined_packet_combinator()
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
    let refined_len: OuterLenComb = Refined {
        inner: U16Le,
        predicate: |v: u16| v <= 8000,
    };
    Mapped::new(Pair::new((U8, refined_len), PayloadDep), MsgMapper)
}

impl DepCombinator<(U8, OuterLenComb), [u8], Vec<u8>> for PayloadDep {
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

fn summarize_value(val: &MsgValueOwned) -> String {
    match val {
        MsgValueOwned::Msg1(v) => format!("Msg1({} bytes)", v.len()),
        MsgValueOwned::Msg2(pkt) => format!(
            "Msg2(RefinedPacket: ver={}, flags=0x{:02X}, len={}, records={})",
            pkt.header.version,
            pkt.header.flags,
            pkt.len,
            pkt.records.len()
        ),
        MsgValueOwned::Msg3(v) => format!("Msg3(x=0x{:04X}, y=0x{:04X})", v.x, v.y),
    }
}

fn example_msg_generation() {
    println!("\n=== TLV message generation (nested refinements) ===");

    let mut comb = tlv_combinator();
    let mut tag_counts = [0u32; 4];

    for s in 50..=100 {
        let mut gen_st = GenSt::new(s);
        let (_len, gen_msg) = comb.generate(&mut gen_st).expect("generate message");

        let tag = gen_msg.tag as usize;
        if tag < tag_counts.len() {
            tag_counts[tag] += 1;
        }

        let summary = summarize_value(&gen_msg.val);
        println!(
            "  [seed={:>3}] tag={}, len={}, {}",
            s, gen_msg.tag, gen_msg.len, summary
        );
    }

    println!(
        "  Tag distribution over 50 seeds: tag1={}, tag2={}, tag3={}",
        tag_counts[1], tag_counts[2], tag_counts[3]
    );
    println!("  Generation checks passed with nested refinements.");
}

fn main() {
    example_msg_generation();
}
