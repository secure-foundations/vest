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
