//! Vest vs hand-written, one group per format.
//!
//! Each group holds exactly two functions, `vest` and `hand`, driving loops that
//! do the same work and produce equivalent value layouts. Criterion's ratio between
//! them is the abstraction overhead for that format.

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::hint::black_box;
use vest_lib::core::exec::Parser;

#[path = "shared/timing.rs"]
mod harness;

use vest_bench::micro::corpus::Corpus;
use vest_bench::{
    encode,
    micro::{baseline as hand, serialize},
    tail_list,
};
use vest_lib::core::exec::serializer::SerializerExt;

/// A corpus pass with untimed result disposal on both sides.
macro_rules! parse_pair {
    ($c:expr, $name:literal, $inputs:expr, $fmt:expr, $hand:path) => {{
        let inputs = $inputs;
        for input in inputs {
            assert_eq!($fmt.parse(input).unwrap().0, input.len());
            assert_eq!($hand(input).unwrap().0, input.len());
        }
        let mut g = $c.benchmark_group(concat!($name, "/parse"));
        harness::corpus_metadata(
            concat!($name, "/parse"),
            inputs.len(),
            inputs.iter().map(|b| b.len() as u64).sum(),
        );
        g.throughput(Throughput::Bytes(
            inputs.iter().map(|b| b.len() as u64).sum(),
        ));
        g.bench_function("vest", |b| {
            harness::retained(b, inputs.len(), |i| {
                $fmt.parse(black_box(&inputs[i])).unwrap()
            })
        });
        g.bench_function("hand", |b| {
            harness::retained(b, inputs.len(), |i| $hand(black_box(inputs[i])).unwrap())
        });
        g.finish();
    }};
}

/// Both encoders calculate their exact length inside timing; initialization is untimed.
macro_rules! serialize_pair {
    ($c:expr, $name:literal, $inputs:expr, $vest:expr, $hand:expr) => {{
        let inputs = $inputs;
        let mut buf = vec![0; inputs.iter().map(|b| b.len()).max().unwrap()];
        let mut g = $c.benchmark_group(concat!($name, "/serialize"));
        harness::corpus_metadata(
            concat!($name, "/serialize"),
            inputs.len(),
            inputs.iter().map(|b| b.len() as u64).sum(),
        );
        g.throughput(Throughput::Bytes(
            inputs.iter().map(|b| b.len() as u64).sum(),
        ));
        g.bench_function("vest", |b| harness::reused(b, || $vest(&mut buf[..])));
        g.bench_function("hand", |b| harness::reused(b, || $hand(&mut buf[..])));
        g.finish();
    }};
}

fn refs(v: &[Vec<u8>]) -> Vec<&[u8]> {
    v.iter().map(|b| b.as_slice()).collect()
}

fn bench(c: &mut Criterion) {
    let corpus = Corpus::new();

    // Values, the same values encoded, and the encoding parsed back by the
    // hand-written codec so both sides serialize equivalent inputs.
    let flat_v = corpus.flat_values();
    let flat_b: Vec<Vec<u8>> = flat_v
        .iter()
        .map(|v| encode(vest_bench::flat::FlatRecordFmt, v))
        .collect();
    let flat_r = refs(&flat_b);
    let flat_h: Vec<_> = flat_b
        .iter()
        .map(|b| hand::parse_flat(b).unwrap().1)
        .collect();

    let table_v = corpus.table_values();
    let table_b: Vec<Vec<u8>> = table_v
        .iter()
        .map(|v| encode(vest_bench::table::TableFmt, v))
        .collect();
    let table_r = refs(&table_b);
    let table_h: Vec<_> = table_b
        .iter()
        .map(|b| hand::parse_table(b).unwrap().1)
        .collect();

    let nest_v = corpus.nest_values();
    let nest_b: Vec<Vec<u8>> = nest_v
        .iter()
        .map(|v| encode(vest_bench::nest::Nest8Fmt, v))
        .collect();
    let nest_r = refs(&nest_b);
    let nest_h: Vec<_> = nest_b
        .iter()
        .map(|b| hand::parse_nest(b).unwrap().1)
        .collect();

    let tlv_v = corpus.tlv_values();
    let tlv_b: Vec<Vec<u8>> = tlv_v
        .iter()
        .map(|v| encode(vest_bench::tlv::TlvMsgFmt, v))
        .collect();
    let tlv_r = refs(&tlv_b);
    let tlv_h: Vec<_> = tlv_b
        .iter()
        .map(|b| hand::parse_tlv(b).unwrap().1)
        .collect();

    let varint_v = corpus.varint_values();
    let varint_b: Vec<Vec<u8>> = varint_v
        .iter()
        .map(|v| encode(vest_bench::varint::VarintListFmt, v))
        .collect();
    let varint_r = refs(&varint_b);
    let varint_h: Vec<_> = varint_b
        .iter()
        .map(|b| hand::parse_varint_list(b).unwrap().1)
        .collect();

    let bits_v = corpus.bits_values();
    let bits_b: Vec<Vec<u8>> = bits_v
        .iter()
        .map(|v| encode(vest_bench::bits::BitsPacketFmt, v))
        .collect();
    let bits_r = refs(&bits_b);
    let bits_h: Vec<_> = bits_b
        .iter()
        .map(|b| hand::parse_bits(b).unwrap().1)
        .collect();

    let bounded_v = corpus.bounded_list_values();
    let bounded_b: Vec<Vec<u8>> = bounded_v
        .iter()
        .map(|v| encode(vest_bench::bounded_list::BoundedListFmt, v))
        .collect();
    let bounded_r = refs(&bounded_b);
    let bounded_h: Vec<_> = bounded_b
        .iter()
        .map(|b| hand::parse_bounded_list(b).unwrap().1)
        .collect();

    // `Tail >>= Vec<item>` has a slice-shaped value, so it is encoded directly.
    let tail_v = corpus.tail_list_values();
    let tail_b: Vec<Vec<u8>> = tail_v
        .iter()
        .map(|v| {
            let mut out = Vec::new();
            tail_list::TailListFmt.serialize_with_vec(v, &mut out);
            out
        })
        .collect();
    let tail_r = refs(&tail_b);
    let tail_h: Vec<_> = tail_b
        .iter()
        .map(|b| hand::parse_tail_list(b).unwrap().1)
        .collect();

    // ---- parse ----
    parse_pair!(
        c,
        "flat",
        &flat_r,
        vest_bench::flat::FlatRecordFmt,
        hand::parse_flat
    );
    parse_pair!(
        c,
        "table",
        &table_r,
        vest_bench::table::TableFmt,
        hand::parse_table
    );
    parse_pair!(
        c,
        "nest",
        &nest_r,
        vest_bench::nest::Nest8Fmt,
        hand::parse_nest
    );
    parse_pair!(
        c,
        "tlv",
        &tlv_r,
        vest_bench::tlv::TlvMsgFmt,
        hand::parse_tlv
    );
    parse_pair!(
        c,
        "varint",
        &varint_r,
        vest_bench::varint::VarintListFmt,
        hand::parse_varint_list
    );
    parse_pair!(
        c,
        "bits",
        &bits_r,
        vest_bench::bits::BitsPacketFmt,
        hand::parse_bits
    );
    parse_pair!(
        c,
        "bounded_list",
        &bounded_r,
        vest_bench::bounded_list::BoundedListFmt,
        hand::parse_bounded_list
    );
    parse_pair!(
        c,
        "tail_list",
        &tail_r,
        vest_bench::tail_list::TailListFmt,
        hand::parse_tail_list
    );

    // ---- serialize ----
    serialize_pair!(
        c,
        "flat",
        &flat_b,
        |buf| serialize::flat_vest(&flat_v, buf),
        |buf| serialize::flat_hand(&flat_h, buf)
    );
    serialize_pair!(
        c,
        "table",
        &table_b,
        |buf| serialize::table_vest(&table_v, buf),
        |buf| serialize::table_hand(&table_h, buf)
    );
    serialize_pair!(
        c,
        "nest",
        &nest_b,
        |buf| serialize::nest_vest(&nest_v, buf),
        |buf| serialize::nest_hand(&nest_h, buf)
    );
    serialize_pair!(
        c,
        "tlv",
        &tlv_b,
        |buf| serialize::tlv_vest(&tlv_v, buf),
        |buf| serialize::tlv_hand(&tlv_h, buf)
    );
    serialize_pair!(
        c,
        "varint",
        &varint_b,
        |buf| serialize::varint_vest(&varint_v, buf),
        |buf| serialize::varint_hand(&varint_h, buf)
    );
    serialize_pair!(
        c,
        "bits",
        &bits_b,
        |buf| serialize::bits_vest(&bits_v, buf),
        |buf| serialize::bits_hand(&bits_h, buf)
    );
    serialize_pair!(
        c,
        "bounded_list",
        &bounded_b,
        |buf| serialize::bounded_list_vest(&bounded_v, buf),
        |buf| serialize::bounded_list_hand(&bounded_h, buf)
    );
    serialize_pair!(
        c,
        "tail_list",
        &tail_b,
        |buf| serialize::tail_list_vest(&tail_v, buf),
        |buf| serialize::tail_list_hand(&tail_h, buf)
    );
}

criterion_group! { name = benches; config = harness::configuration(); targets = bench }
criterion_main!(benches);
