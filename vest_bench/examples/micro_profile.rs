//! Continuous microformat loops for sampling. Unlike Criterion, parsing includes
//! result destruction. Use `make bench-formats` for comparable elapsed times.

use std::hint::black_box;

use vest_bench::micro::{baseline, corpus::Corpus, serialize};
use vest_bench::{encode, *};
use vest_lib::core::exec::Parser;

macro_rules! spin {
    ($body:expr) => {
        loop {
            $body;
        }
    };
}

macro_rules! profile_format {
    ($corpus:expr, $op:expr, $side:expr, $values:ident, $fmt:expr, $parse:path, $vest_write:path, $hand_write:path) => {{
        let values = $corpus.$values();
        let inputs: Vec<_> = values.iter().map(|v| encode($fmt, v)).collect();
        match ($op, $side) {
            ("parse", "vest") => spin!({
                for b in &inputs {
                    black_box($fmt.parse(black_box(&b.as_slice())).unwrap());
                }
            }),
            ("parse", "hand") => spin!({
                for b in &inputs {
                    black_box($parse(black_box(b)).unwrap());
                }
            }),
            ("serialize", side) => {
                let baseline: Vec<_> = inputs.iter().map(|b| $parse(b).unwrap().1).collect();
                let mut output = vec![0; inputs.iter().map(Vec::len).max().unwrap()];
                if side == "vest" {
                    spin!($vest_write(&values, &mut output));
                } else {
                    spin!($hand_write(&baseline, &mut output));
                }
            }
            _ => unreachable!(),
        }
    }};
}

fn main() {
    assert!(
        !vest_lib::ERROR_TRACE_ENABLED,
        "disable vest_lib/error-trace for profiling"
    );
    let selector = std::env::args().nth(1).unwrap_or_default();
    let parts: Vec<_> = selector.split('/').collect();
    if !(2..=3).contains(&parts.len())
        || !matches!(parts[1], "parse" | "serialize")
        || parts.get(2).is_some_and(|s| !matches!(*s, "vest" | "hand"))
    {
        eprintln!("usage: micro_profile <format>/<parse|serialize>[/<vest|hand>]");
        std::process::exit(2);
    }
    let side = parts.get(2).copied().unwrap_or("vest");
    let corpus = Corpus::new();
    macro_rules! select {
        ($values:ident, $fmt:expr, $parse:path, $vest:path, $hand:path) => {
            profile_format!(corpus, parts[1], side, $values, $fmt, $parse, $vest, $hand)
        };
    }
    match parts[0] {
        "flat" => select!(
            flat_values,
            flat::FlatRecordFmt,
            baseline::parse_flat,
            serialize::flat_vest,
            serialize::flat_hand
        ),
        "table" => select!(
            table_values,
            table::TableFmt,
            baseline::parse_table,
            serialize::table_vest,
            serialize::table_hand
        ),
        "nest" => select!(
            nest_values,
            nest::Nest8Fmt,
            baseline::parse_nest,
            serialize::nest_vest,
            serialize::nest_hand
        ),
        "tlv" => select!(
            tlv_values,
            tlv::TlvMsgFmt,
            baseline::parse_tlv,
            serialize::tlv_vest,
            serialize::tlv_hand
        ),
        "varint" => select!(
            varint_values,
            varint::VarintListFmt,
            baseline::parse_varint_list,
            serialize::varint_vest,
            serialize::varint_hand
        ),
        "bits" => select!(
            bits_values,
            bits::BitsPacketFmt,
            baseline::parse_bits,
            serialize::bits_vest,
            serialize::bits_hand
        ),
        "bounded_list" => select!(
            bounded_list_values,
            bounded_list::BoundedListFmt,
            baseline::parse_bounded_list,
            serialize::bounded_list_vest,
            serialize::bounded_list_hand
        ),
        "tail_list" => select!(
            tail_list_values,
            tail_list::TailListFmt,
            baseline::parse_tail_list,
            serialize::tail_list_vest,
            serialize::tail_list_hand
        ),
        _ => {
            eprintln!("unknown format: {}", parts[0]);
            std::process::exit(2);
        }
    }
}
