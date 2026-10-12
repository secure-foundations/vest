//! Paired microformat serialization passes, including validation and sizing.
//!
//! Both sides use equivalent field layouts and reusable initialized output slices.
//! The Criterion harness controls input lifetimes and excludes decoded-value drops.

use std::hint::black_box;

use vest_lib::core::exec::serializer::{Prepare, SerializerExt};

use super::baseline as hand;
use crate::bits::{BitsPacket, BitsPacketFmt};
use crate::bounded_list::{BoundedList, BoundedListFmt};
use crate::flat::{FlatRecord, FlatRecordFmt};
use crate::nest::{Nest8, Nest8Fmt};
use crate::table::{Table, TableFmt};
use crate::tail_list::{TailItem, TailListFmt};
use crate::tlv::{TlvMsg, TlvMsgFmt};
use crate::varint::{VarintList, VarintListFmt};

/// Computes the exact length, writes into an already initialized buffer, and observes the bytes.
macro_rules! ser_loop {
    ($vs:expr, $buf:expr, $fmt:expr) => {{
        for v in $vs {
            let n = $fmt.prepare(black_box(v)).unwrap();
            $fmt.serialize(v, &mut $buf[..n]);
            black_box(&$buf);
        }
    }};
}

macro_rules! hand_ser_loop {
    ($vs:expr, $buf:expr, $size:path, $write:path) => {{
        for v in $vs {
            let n = $size(black_box(v)).unwrap();
            $write(v, &mut $buf[..n]);
            black_box(&$buf);
        }
    }};
}

// ---------------------------------------------------------------- flat

pub fn flat_vest(vs: &[FlatRecord<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, FlatRecordFmt)
}

pub fn flat_hand(vs: &[hand::FlatRef<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_flat, hand::write_flat)
}

// --------------------------------------------------------------- table

pub fn table_vest(vs: &[Table<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, TableFmt)
}

pub fn table_hand(vs: &[hand::TableRef<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_table, hand::write_table)
}

// ---------------------------------------------------------------- nest

pub fn nest_vest(vs: &[Nest8<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, Nest8Fmt)
}

pub fn nest_hand(vs: &[hand::HNest8<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_nest, hand::write_nest)
}

// ----------------------------------------------------------------- tlv

pub fn tlv_vest(vs: &[TlvMsg<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, TlvMsgFmt)
}

pub fn tlv_hand(vs: &[hand::HTlvMsg<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_tlv, hand::write_tlv)
}

// -------------------------------------------------------------- varint

pub fn varint_vest(vs: &[VarintList<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, VarintListFmt)
}

pub fn varint_hand(vs: &[hand::VarintListRef<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_varint_list, hand::write_varint_list)
}

// ---------------------------------------------------------------- bits

pub fn bits_vest(vs: &[BitsPacket<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, BitsPacketFmt)
}

pub fn bits_hand(vs: &[hand::HBitsPacket<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_bits, hand::write_bits)
}

// ---------------------------------------------------------- list formats

pub fn bounded_list_vest(vs: &[BoundedList<'_>], buf: &mut [u8]) {
    ser_loop!(vs, buf, BoundedListFmt)
}

pub fn bounded_list_hand(vs: &[hand::BoundedListRef<'_>], buf: &mut [u8]) {
    hand_ser_loop!(vs, buf, hand::size_bounded_list, hand::write_bounded_list)
}

pub fn tail_list_vest(vs: &[Vec<TailItem<'_>>], buf: &mut [u8]) {
    ser_loop!(vs, buf, TailListFmt)
}

pub fn tail_list_hand(vs: &[Vec<hand::ItemRef<'_>>], buf: &mut [u8]) {
    for v in vs {
        let n = hand::size_tail_list(black_box(v)).unwrap();
        hand::write_tail_list(v, &mut buf[..n]);
        black_box(&buf);
    }
}
