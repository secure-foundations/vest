//! Paired Vest / hand-written loops, one per format per operation.
//!
//! Both sides of a pair produce the *same* value type — field for field, and
//! with the same size and alignment, which the `layout_parity` test in `lib.rs`
//! checks — and hand the result to `black_box`. That is what makes the
//! comparison meaningful: the two parsers do the same job and build the same
//! structure, so the difference between them is the codec, not the harness.
//!
//! An earlier version folded a few fields into an accumulator instead. That
//! avoids paying to materialise the result, but it only observes the fields it
//! touches, so a baseline could silently skip work the generated parser still
//! performs. Matching the layouts and observing the whole value is the honest
//! comparison; the cost is that `black_box` forces both results to memory,
//! which inflates both sides equally and compresses ratios slightly toward 1.

use std::hint::black_box;

use vest_lib::core::exec::parser::Parser;
use vest_lib::core::exec::serializer::{Prepare, SerializerExt};

use crate::bits::{BitsPacket, BitsPacketFmt};
use crate::flat::{FlatRecord, FlatRecordFmt};
use crate::hand;
use crate::bounded_list::{BoundedList, BoundedListFmt};
use crate::table::{Table, TableFmt};
use crate::tail_list::{TailItem, TailListFmt};
use crate::nest::{Nest8, Nest8Fmt};
use crate::tlv::{TlvMsg, TlvMsgFmt};
use crate::varint::{VarintList, VarintListFmt};

/// Parses every buffer and makes each parsed value observable.
macro_rules! parse_loop {
    ($bufs:expr, $fmt:expr) => {{
        for b in $bufs {
            black_box($fmt.parse(b).unwrap());
        }
    }};
}

macro_rules! hand_parse_loop {
    ($bufs:expr, $parse:path) => {{
        for b in $bufs {
            black_box($parse(b).unwrap());
        }
    }};
}

/// Computes the exact length, sizes the buffer, writes, and observes the bytes.
macro_rules! ser_loop {
    ($vs:expr, $buf:expr, $fmt:expr) => {{
        for v in $vs {
            let n = $fmt.prepare(v).unwrap();
            $buf.resize(n, 0);
            $fmt.serialize(v, &mut $buf[..n]);
            black_box(&$buf);
        }
    }};
}

macro_rules! hand_ser_loop {
    ($vs:expr, $buf:expr, $size:path, $write:path) => {{
        for v in $vs {
            let n = $size(v).unwrap();
            $buf.resize(n, 0);
            $write(v, &mut $buf[..n]);
            black_box(&$buf);
        }
    }};
}

// ---------------------------------------------------------------- flat

pub fn parse_flat_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, FlatRecordFmt)
}

pub fn parse_flat_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_flat)
}

pub fn ser_flat_vest(vs: &[FlatRecord<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, FlatRecordFmt)
}

pub fn ser_flat_hand(vs: &[hand::FlatRef<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_flat, hand::write_flat)
}

// --------------------------------------------------------------- table

pub fn parse_table_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, TableFmt)
}

pub fn parse_table_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_table)
}

pub fn ser_table_vest(vs: &[Table<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, TableFmt)
}

pub fn ser_table_hand(vs: &[hand::TableRef<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_table, hand::write_table)
}

// ---------------------------------------------------------------- nest

pub fn parse_nest_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, Nest8Fmt)
}

pub fn parse_nest_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_nest)
}

pub fn ser_nest_vest(vs: &[Nest8<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, Nest8Fmt)
}

pub fn ser_nest_hand(vs: &[hand::HNest8<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_nest, hand::write_nest)
}

// ----------------------------------------------------------------- tlv

pub fn parse_tlv_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, TlvMsgFmt)
}

pub fn parse_tlv_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_tlv)
}

pub fn ser_tlv_vest(vs: &[TlvMsg<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, TlvMsgFmt)
}

pub fn ser_tlv_hand(vs: &[hand::HTlvMsg<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_tlv, hand::write_tlv)
}

// -------------------------------------------------------------- varint

pub fn parse_varint_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, VarintListFmt)
}

pub fn parse_varint_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_varint_list)
}

pub fn ser_varint_vest(vs: &[VarintList<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, VarintListFmt)
}

pub fn ser_varint_hand(vs: &[hand::VarintListRef<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_varint_list, hand::write_varint_list)
}

// ---------------------------------------------------------------- bits

pub fn parse_bits_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, BitsPacketFmt)
}

pub fn parse_bits_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_bits)
}

pub fn ser_bits_vest(vs: &[BitsPacket<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, BitsPacketFmt)
}

pub fn ser_bits_hand(vs: &[hand::HBitsPacket<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_bits, hand::write_bits)
}

// ---------------------------------------------------------- list formats

pub fn parse_bounded_list_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, BoundedListFmt)
}

pub fn parse_bounded_list_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_bounded_list)
}

pub fn ser_bounded_list_vest(vs: &[BoundedList<'_>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, BoundedListFmt)
}

pub fn ser_bounded_list_hand(vs: &[hand::BoundedListRef<'_>], buf: &mut Vec<u8>) {
    hand_ser_loop!(vs, buf, hand::size_bounded_list, hand::write_bounded_list)
}

pub fn parse_tail_list_vest(bufs: &[&[u8]]) {
    parse_loop!(bufs, TailListFmt)
}

pub fn parse_tail_list_hand(bufs: &[&[u8]]) {
    hand_parse_loop!(bufs, hand::parse_tail_list)
}

pub fn ser_tail_list_vest(vs: &[Vec<TailItem<'_>>], buf: &mut Vec<u8>) {
    ser_loop!(vs, buf, TailListFmt)
}

pub fn ser_tail_list_hand(vs: &[Vec<hand::ItemRef<'_>>], buf: &mut Vec<u8>) {
    for v in vs {
        let n = hand::size_tail_list(v).unwrap();
        buf.resize(n, 0);
        hand::write_tail_list(v, &mut buf[..n]);
        black_box(&buf);
    }
}
