//! Performance comparison between Vest-generated codecs and hand-written ones.

// Generated from formats/*.vest by `make generate`; do not edit by hand.
#[rustfmt::skip]
pub mod bits;
#[rustfmt::skip]
pub mod bounded_list;
#[rustfmt::skip]
pub mod flat;
#[rustfmt::skip]
pub mod nest;
#[rustfmt::skip]
pub mod table;
#[rustfmt::skip]
pub mod tail_list;
#[rustfmt::skip]
pub mod tlv;
#[rustfmt::skip]
pub mod varint;

pub mod corpus;
pub mod hand;
pub mod runners;

use vest_lib::core::exec::serializer::{Prepare, SerializerExt};

/// Encodes one value with its generated serializer.
///
/// The Vest encoder is the ground truth for the corpus: the wire-compatibility
/// tests then check that the hand-written codec agrees with it byte for byte.
pub fn encode<F, T>(fmt: F, v: &T) -> Vec<u8>
where
    F: Prepare<T> + SerializerExt<T> + vest_lib::core::exec::serializer::Serializer<Vec<u8>, T>,
    T: vstd::prelude::DeepView + ?Sized,
{
    let mut out = Vec::new();
    fmt.serialize_with_vec(v, &mut out);
    out
}

/// The benchmark is only fair if each hand-written value type is the same shape
/// as the generated one.
#[cfg(test)]
mod layout_parity {
    use super::*;
    use core::mem::{align_of, size_of};

    macro_rules! same_layout {
        ($name:ident, $vest:ty, $hand:ty) => {
            #[test]
            fn $name() {
                assert_eq!(
                    size_of::<$vest>(),
                    size_of::<$hand>(),
                    "{} and {} differ in size",
                    stringify!($vest),
                    stringify!($hand)
                );
                assert_eq!(
                    align_of::<$vest>(),
                    align_of::<$hand>(),
                    "{} and {} differ in alignment",
                    stringify!($vest),
                    stringify!($hand)
                );
            }
        };
    }

    same_layout!(flat, flat::FlatRecord<'static>, hand::FlatRef<'static>);
    same_layout!(entry, table::TableEntry<'static>, hand::EntryRef<'static>);
    same_layout!(table, table::Table<'static>, hand::TableRef<'static>);
    same_layout!(nest, nest::Nest8<'static>, hand::HNest8<'static>);
    same_layout!(tlv, tlv::TlvMsg<'static>, hand::HTlvMsg<'static>);
    same_layout!(
        varint_item,
        varint::VarintItem<'static>,
        hand::VarintItemRef<'static>
    );
    same_layout!(
        varint_list,
        varint::VarintList<'static>,
        hand::VarintListRef<'static>
    );
    same_layout!(bits, bits::BitsPacket<'static>, hand::HBitsPacket<'static>);
    same_layout!(
        bounded_item,
        bounded_list::BoundedItem<'static>,
        hand::ItemRef<'static>
    );
    same_layout!(
        tail_item,
        tail_list::TailItem<'static>,
        hand::ItemRef<'static>
    );
    same_layout!(
        bounded_list,
        bounded_list::BoundedList<'static>,
        hand::BoundedListRef<'static>
    );
}

#[cfg(test)]
mod wire_compat {
    use super::corpus::Corpus;
    use super::*;
    use vest_lib::core::exec::parser::Parser;

    /// Every format: the generated encoder and the hand-written encoder must
    /// agree byte for byte, and each parser must accept the other's output.
    macro_rules! check {
        ($name:ident, $fmt:expr, $values:expr, $hand_parse:path, $hand_size:path, $hand_write:path) => {
            #[test]
            fn $name() {
                let corpus = Corpus::new();
                let values = $values(&corpus);
                assert!(!values.is_empty());
                for v in &values {
                    let vest_bytes = encode($fmt, v);

                    // The generated parser round-trips its own output.
                    let (n, _) = $fmt.parse(&&vest_bytes[..]).expect("vest parse failed");
                    assert_eq!(n, vest_bytes.len(), "vest did not consume its own output");

                    // The hand-written parser accepts it and re-encodes identically.
                    let (hn, hv) = $hand_parse(&vest_bytes[..]).expect("hand parse failed");
                    assert_eq!(hn, vest_bytes.len(), "hand did not consume vest's output");
                    let hand_len = $hand_size(&hv).expect("hand prepare rejected a valid value");
                    assert_eq!(hand_len, vest_bytes.len(), "length disagreement");
                    let mut hand_bytes = vec![0u8; hand_len];
                    $hand_write(&hv, &mut hand_bytes);
                    assert_eq!(hand_bytes, vest_bytes, "encoding disagreement");
                }
            }
        };
    }

    check!(
        flat,
        flat::FlatRecordFmt,
        Corpus::flat_values,
        hand::parse_flat,
        hand::size_flat,
        hand::write_flat
    );
    check!(
        table,
        table::TableFmt,
        Corpus::table_values,
        hand::parse_table,
        hand::size_table,
        hand::write_table
    );
    check!(
        nest,
        nest::Nest8Fmt,
        Corpus::nest_values,
        hand::parse_nest,
        hand::size_nest,
        hand::write_nest
    );
    check!(
        tlv,
        tlv::TlvMsgFmt,
        Corpus::tlv_values,
        hand::parse_tlv,
        hand::size_tlv,
        hand::write_tlv
    );
    check!(
        varint,
        varint::VarintListFmt,
        Corpus::varint_values,
        hand::parse_varint_list,
        hand::size_varint_list,
        hand::write_varint_list
    );
    check!(
        bits,
        bits::BitsPacketFmt,
        Corpus::bits_values,
        hand::parse_bits,
        hand::size_bits,
        hand::write_bits
    );
    check!(
        bounded_list,
        bounded_list::BoundedListFmt,
        Corpus::bounded_list_values,
        hand::parse_bounded_list,
        hand::size_bounded_list,
        hand::write_bounded_list
    );

    /// `Tail >>= Vec<item>` has a slice-shaped value, so it does not fit the
    /// macro above.
    #[test]
    fn tail_list() {
        let corpus = Corpus::new();
        for v in &corpus.tail_list_values() {
            let mut vest_bytes = Vec::new();
            tail_list::TailListFmt.serialize_with_vec(v, &mut vest_bytes);

            let (n, _) = tail_list::TailListFmt
                .parse(&&vest_bytes[..])
                .expect("vest parse failed");
            assert_eq!(n, vest_bytes.len());

            let (hn, hv) = hand::parse_tail_list(&vest_bytes[..]).expect("hand parse failed");
            assert_eq!(hn, vest_bytes.len());
            let hand_len = hand::size_tail_list(&hv).expect("hand prepare rejected a valid value");
            assert_eq!(hand_len, vest_bytes.len());
            let mut hand_bytes = vec![0u8; hand_len];
            hand::write_tail_list(&hv, &mut hand_bytes);
            assert_eq!(hand_bytes, vest_bytes);
        }
    }
}
