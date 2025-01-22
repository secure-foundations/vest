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

pub const POLYBENCH_C_TESTS: &[(&str, &[u8])] = &[
    (
        "2mm",
        include_bytes!("../benches/data/polybench-c/2mm.wasm.rewritten"),
    ),
    (
        "3mm",
        include_bytes!("../benches/data/polybench-c/3mm.wasm.rewritten"),
    ),
    (
        "adi",
        include_bytes!("../benches/data/polybench-c/adi.wasm.rewritten"),
    ),
    (
        "atax",
        include_bytes!("../benches/data/polybench-c/atax.wasm.rewritten"),
    ),
    (
        "bicg",
        include_bytes!("../benches/data/polybench-c/bicg.wasm.rewritten"),
    ),
    (
        "cholesky",
        include_bytes!("../benches/data/polybench-c/cholesky.wasm.rewritten"),
    ),
    (
        "correlation",
        include_bytes!("../benches/data/polybench-c/correlation.wasm.rewritten"),
    ),
    (
        "covariance",
        include_bytes!("../benches/data/polybench-c/covariance.wasm.rewritten"),
    ),
    (
        "doitgen",
        include_bytes!("../benches/data/polybench-c/doitgen.wasm.rewritten"),
    ),
    (
        "durbin",
        include_bytes!("../benches/data/polybench-c/durbin.wasm.rewritten"),
    ),
    (
        "dynprog",
        include_bytes!("../benches/data/polybench-c/dynprog.wasm.rewritten"),
    ),
    (
        "fdtd-2d",
        include_bytes!("../benches/data/polybench-c/fdtd-2d.wasm.rewritten"),
    ),
    (
        "fdtd-apml",
        include_bytes!("../benches/data/polybench-c/fdtd-apml.wasm.rewritten"),
    ),
    (
        "floyd-warshall",
        include_bytes!("../benches/data/polybench-c/floyd-warshall.wasm.rewritten"),
    ),
    (
        "gemm",
        include_bytes!("../benches/data/polybench-c/gemm.wasm.rewritten"),
    ),
    (
        "gemver",
        include_bytes!("../benches/data/polybench-c/gemver.wasm.rewritten"),
    ),
    (
        "gesummv",
        include_bytes!("../benches/data/polybench-c/gesummv.wasm.rewritten"),
    ),
    (
        "gramschmidt",
        include_bytes!("../benches/data/polybench-c/gramschmidt.wasm.rewritten"),
    ),
    (
        "jacobi-1d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-1d-imper.wasm.rewritten"),
    ),
    (
        "jacobi-2d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-2d-imper.wasm.rewritten"),
    ),
    (
        "lu",
        include_bytes!("../benches/data/polybench-c/lu.wasm.rewritten"),
    ),
    (
        "ludcmp",
        include_bytes!("../benches/data/polybench-c/ludcmp.wasm.rewritten"),
    ),
    (
        "mvt",
        include_bytes!("../benches/data/polybench-c/mvt.wasm.rewritten"),
    ),
    (
        "reg_detect",
        include_bytes!("../benches/data/polybench-c/reg_detect.wasm.rewritten"),
    ),
    (
        "seidel-2d",
        include_bytes!("../benches/data/polybench-c/seidel-2d.wasm.rewritten"),
    ),
    (
        "symm",
        include_bytes!("../benches/data/polybench-c/symm.wasm.rewritten"),
    ),
    (
        "syr2k",
        include_bytes!("../benches/data/polybench-c/syr2k.wasm.rewritten"),
    ),
    (
        "syrk",
        include_bytes!("../benches/data/polybench-c/syrk.wasm.rewritten"),
    ),
    (
        "trisolv",
        include_bytes!("../benches/data/polybench-c/trisolv.wasm.rewritten"),
    ),
    (
        "trmm",
        include_bytes!("../benches/data/polybench-c/trmm.wasm.rewritten"),
    ),
];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for (_, bytes) in POLYBENCH_C_TESTS {
        println!("{} ", bytes.len());
        // println!("{} {:?}", bytes.len(), module().parse(bytes).unwrap());
        // println!("{:?}", rwasm::parser::parse(bytes).unwrap());
    }

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
