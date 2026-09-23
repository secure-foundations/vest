//! Runs one format's loop repeatedly so a sampling profiler has something to
//! attribute.
//!
//! ```sh
//! cargo build --release --example profile
//! ../target/release/examples/profile table/serialize &
//! sample $! 5 -file /tmp/table-serialize.txt
//! ```
//!
//! Pass `<format>/<op>/<side>`, e.g. `table/serialize/vest` (the side defaults
//! to `vest`). Use the `hand` side to see what the baseline spends its time on.

use vest_bench::corpus::Corpus;
use vest_bench::{encode, hand, runners};

fn refs(v: &[Vec<u8>]) -> Vec<&[u8]> {
    v.iter().map(|b| b.as_slice()).collect()
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: profile <format>/<parse|serialize>[/<vest|hand>]");
        std::process::exit(2);
    });
    let mut parts = arg.split('/');
    let format = parts.next().unwrap_or("");
    let op = parts.next().unwrap_or("");
    let side = parts.next().unwrap_or("vest");

    let corpus = Corpus::new();
    let mut buf = Vec::new();

    // Repeat until interrupted, so the profiler sees a steady state.
    macro_rules! spin {
        ($body:expr) => {{
            loop {
                for _ in 0..200 {
                    $body;
                }
                std::hint::black_box(&buf);
            }
        }};
    }

    match (format, op, side) {
        ("flat", "parse", s) => {
            let v = corpus.flat_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::flat::FlatRecordFmt, x)).collect();
            let r = refs(&b);
            if s == "hand" { spin!(runners::parse_flat_hand(&r)) } else { spin!(runners::parse_flat_vest(&r)) }
        }
        ("flat", "serialize", s) => {
            let v = corpus.flat_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::flat::FlatRecordFmt, x)).collect();
            let h: Vec<_> = b.iter().map(|x| hand::parse_flat(x).unwrap().1).collect();
            if s == "hand" { spin!(runners::ser_flat_hand(&h, &mut buf)) } else { spin!(runners::ser_flat_vest(&v, &mut buf)) }
        }
        ("table", "parse", s) => {
            let v = corpus.table_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::table::TableFmt, x)).collect();
            let r = refs(&b);
            if s == "hand" { spin!(runners::parse_table_hand(&r)) } else { spin!(runners::parse_table_vest(&r)) }
        }
        ("table", "serialize", s) => {
            let v = corpus.table_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::table::TableFmt, x)).collect();
            let h: Vec<_> = b.iter().map(|x| hand::parse_table(x).unwrap().1).collect();
            if s == "hand" { spin!(runners::ser_table_hand(&h, &mut buf)) } else { spin!(runners::ser_table_vest(&v, &mut buf)) }
        }
        ("nest", "serialize", s) => {
            let v = corpus.nest_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::nest::Nest8Fmt, x)).collect();
            let h: Vec<_> = b.iter().map(|x| hand::parse_nest(x).unwrap().1).collect();
            if s == "hand" { spin!(runners::ser_nest_hand(&h, &mut buf)) } else { spin!(runners::ser_nest_vest(&v, &mut buf)) }
        }
        ("bits", "parse", s) => {
            let v = corpus.bits_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::bits::BitsPacketFmt, x)).collect();
            let r = refs(&b);
            if s == "hand" { spin!(runners::parse_bits_hand(&r)) } else { spin!(runners::parse_bits_vest(&r)) }
        }
        ("tlv", "parse", s) => {
            let v = corpus.tlv_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::tlv::TlvMsgFmt, x)).collect();
            let r = refs(&b);
            if s == "hand" { spin!(runners::parse_tlv_hand(&r)) } else { spin!(runners::parse_tlv_vest(&r)) }
        }
        ("bounded_list", "parse", s) => {
            let v = corpus.bounded_list_values();
            let b: Vec<Vec<u8>> = v.iter().map(|x| encode(vest_bench::bounded_list::BoundedListFmt, x)).collect();
            let r = refs(&b);
            if s == "hand" { spin!(runners::parse_bounded_list_hand(&r)) } else { spin!(runners::parse_bounded_list_vest(&r)) }
        }
        _ => {
            eprintln!("unknown selector: {arg}");
            std::process::exit(2);
        }
    }
}
