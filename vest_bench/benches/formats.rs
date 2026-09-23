//! Vest vs hand-written, one group per format.
//!
//! Each group holds exactly two functions, `vest` and `hand`, driving loops that
//! do the same work and produce the same value type. Criterion's ratio between
//! them is the abstraction overhead for that format.

use criterion::{criterion_group, criterion_main, Criterion, Throughput};

use vest_bench::corpus::Corpus;
use vest_bench::{encode, hand, runners, tail_list};
use vest_lib::core::exec::serializer::SerializerExt;

/// Runs one `vest` / `hand` pair as a criterion group.
macro_rules! pair {
    ($c:expr, $name:literal, $n:expr, $vest:expr, $hand:expr) => {{
        let mut g = $c.benchmark_group($name);
        g.throughput(Throughput::Elements($n as u64));
        g.bench_function("vest", |b| b.iter(|| $vest));
        g.bench_function("hand", |b| b.iter(|| $hand));
        g.finish();
    }};
}

fn refs(v: &[Vec<u8>]) -> Vec<&[u8]> {
    v.iter().map(|b| b.as_slice()).collect()
}

fn bench(c: &mut Criterion) {
    let corpus = Corpus::new();
    let mut buf = Vec::new();

    // Values, the same values encoded, and the encoding parsed back by the
    // hand-written codec so both sides serialize equivalent inputs.
    let flat_v = corpus.flat_values();
    let flat_b: Vec<Vec<u8>> =
        flat_v.iter().map(|v| encode(vest_bench::flat::FlatRecordFmt, v)).collect();
    let flat_r = refs(&flat_b);
    let flat_h: Vec<_> = flat_b.iter().map(|b| hand::parse_flat(b).unwrap().1).collect();

    let table_v = corpus.table_values();
    let table_b: Vec<Vec<u8>> =
        table_v.iter().map(|v| encode(vest_bench::table::TableFmt, v)).collect();
    let table_r = refs(&table_b);
    let table_h: Vec<_> = table_b.iter().map(|b| hand::parse_table(b).unwrap().1).collect();

    let nest_v = corpus.nest_values();
    let nest_b: Vec<Vec<u8>> =
        nest_v.iter().map(|v| encode(vest_bench::nest::Nest8Fmt, v)).collect();
    let nest_r = refs(&nest_b);
    let nest_h: Vec<_> = nest_b.iter().map(|b| hand::parse_nest(b).unwrap().1).collect();

    let tlv_v = corpus.tlv_values();
    let tlv_b: Vec<Vec<u8>> = tlv_v.iter().map(|v| encode(vest_bench::tlv::TlvMsgFmt, v)).collect();
    let tlv_r = refs(&tlv_b);
    let tlv_h: Vec<_> = tlv_b.iter().map(|b| hand::parse_tlv(b).unwrap().1).collect();

    let varint_v = corpus.varint_values();
    let varint_b: Vec<Vec<u8>> =
        varint_v.iter().map(|v| encode(vest_bench::varint::VarintListFmt, v)).collect();
    let varint_r = refs(&varint_b);
    let varint_h: Vec<_> =
        varint_b.iter().map(|b| hand::parse_varint_list(b).unwrap().1).collect();

    let bits_v = corpus.bits_values();
    let bits_b: Vec<Vec<u8>> =
        bits_v.iter().map(|v| encode(vest_bench::bits::BitsPacketFmt, v)).collect();
    let bits_r = refs(&bits_b);
    let bits_h: Vec<_> = bits_b.iter().map(|b| hand::parse_bits(b).unwrap().1).collect();

    let bounded_v = corpus.bounded_list_values();
    let bounded_b: Vec<Vec<u8>> = bounded_v
        .iter()
        .map(|v| encode(vest_bench::bounded_list::BoundedListFmt, v))
        .collect();
    let bounded_r = refs(&bounded_b);
    let bounded_h: Vec<_> =
        bounded_b.iter().map(|b| hand::parse_bounded_list(b).unwrap().1).collect();

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
    let tail_h: Vec<_> = tail_b.iter().map(|b| hand::parse_tail_list(b).unwrap().1).collect();

    // ---- parse ----
    pair!(c, "flat/parse", flat_r.len(),
        runners::parse_flat_vest(&flat_r), runners::parse_flat_hand(&flat_r));
    pair!(c, "table/parse", table_r.len(),
        runners::parse_table_vest(&table_r), runners::parse_table_hand(&table_r));
    pair!(c, "nest/parse", nest_r.len(),
        runners::parse_nest_vest(&nest_r), runners::parse_nest_hand(&nest_r));
    pair!(c, "tlv/parse", tlv_r.len(),
        runners::parse_tlv_vest(&tlv_r), runners::parse_tlv_hand(&tlv_r));
    pair!(c, "varint/parse", varint_r.len(),
        runners::parse_varint_vest(&varint_r), runners::parse_varint_hand(&varint_r));
    pair!(c, "bits/parse", bits_r.len(),
        runners::parse_bits_vest(&bits_r), runners::parse_bits_hand(&bits_r));
    pair!(c, "bounded_list/parse", bounded_r.len(),
        runners::parse_bounded_list_vest(&bounded_r), runners::parse_bounded_list_hand(&bounded_r));
    pair!(c, "tail_list/parse", tail_r.len(),
        runners::parse_tail_list_vest(&tail_r), runners::parse_tail_list_hand(&tail_r));

    // ---- serialize ----
    pair!(c, "flat/serialize", flat_v.len(),
        runners::ser_flat_vest(&flat_v, &mut buf), runners::ser_flat_hand(&flat_h, &mut buf));
    pair!(c, "table/serialize", table_v.len(),
        runners::ser_table_vest(&table_v, &mut buf), runners::ser_table_hand(&table_h, &mut buf));
    pair!(c, "nest/serialize", nest_v.len(),
        runners::ser_nest_vest(&nest_v, &mut buf), runners::ser_nest_hand(&nest_h, &mut buf));
    pair!(c, "tlv/serialize", tlv_v.len(),
        runners::ser_tlv_vest(&tlv_v, &mut buf), runners::ser_tlv_hand(&tlv_h, &mut buf));
    pair!(c, "varint/serialize", varint_v.len(),
        runners::ser_varint_vest(&varint_v, &mut buf), runners::ser_varint_hand(&varint_h, &mut buf));
    pair!(c, "bits/serialize", bits_v.len(),
        runners::ser_bits_vest(&bits_v, &mut buf), runners::ser_bits_hand(&bits_h, &mut buf));
    pair!(c, "bounded_list/serialize", bounded_v.len(),
        runners::ser_bounded_list_vest(&bounded_v, &mut buf),
        runners::ser_bounded_list_hand(&bounded_h, &mut buf));
    pair!(c, "tail_list/serialize", tail_v.len(),
        runners::ser_tail_list_vest(&tail_v, &mut buf),
        runners::ser_tail_list_hand(&tail_h, &mut buf));
}

criterion_group!(benches, bench);
criterion_main!(benches);
