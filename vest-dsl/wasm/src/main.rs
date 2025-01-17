pub mod vest_wasm;
// pub mod wasm_data;

use vest::{
    properties::*,
    regular::{
        choice::{Either, OrdChoice},
        depend::Continuation,
        disjoint::DisjointFrom,
        refined::Refined,
        repeat::{Repeat, RepeatResult},
        star::Star,
        tag::TagPred,
        uints::U8,
    },
};
use vest_wasm::*;
// use wasm_data::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // parse_vestbtc_tx()?;
    // parse_rustbtc_tx()?;
    // serialize_vestbtc_tx()?;
    // serialize_rustbtc_tx()?;
    // bench_fn(parse_rustbtc_tx)?;
    // bench_fn(parse_vestbtc_tx)?;
    // bench_fn(serialize_rustbtc_tx)?;
    // bench_fn(serialize_vestbtc_tx)?;
    // test();

    // for hex in wasm_data() {
    //     println!("{:?}", hex_to_bytes(hex));
    // }

    Ok(())
}

fn bench_fn(
    f: impl Fn() -> Result<(), Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    for _ in 0..1000000 {
        f()?;
    }
    println!("Time elapsed: {} ms", start.elapsed().as_millis());

    Ok(())
}
