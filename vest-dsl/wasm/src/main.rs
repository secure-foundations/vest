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
    ("2mm", include_bytes!("../benches/data/polybench-c/2mm.wasm")),
    ("3mm", include_bytes!("../benches/data/polybench-c/3mm.wasm")),
    ("adi", include_bytes!("../benches/data/polybench-c/adi.wasm")),
    ("atax", include_bytes!("../benches/data/polybench-c/atax.wasm")),
    ("bicg", include_bytes!("../benches/data/polybench-c/bicg.wasm")),
    ("cholesky", include_bytes!("../benches/data/polybench-c/cholesky.wasm")),
    ("correlation", include_bytes!("../benches/data/polybench-c/correlation.wasm")),
    ("covariance", include_bytes!("../benches/data/polybench-c/covariance.wasm")),
    ("doitgen", include_bytes!("../benches/data/polybench-c/doitgen.wasm")),
    ("durbin", include_bytes!("../benches/data/polybench-c/durbin.wasm")),
    ("dynprog", include_bytes!("../benches/data/polybench-c/dynprog.wasm")),
    ("fdtd-2d", include_bytes!("../benches/data/polybench-c/fdtd-2d.wasm")),
    ("fdtd-apml", include_bytes!("../benches/data/polybench-c/fdtd-apml.wasm")),
    ("floyd-warshall", include_bytes!("../benches/data/polybench-c/floyd-warshall.wasm")),
    ("gemm", include_bytes!("../benches/data/polybench-c/gemm.wasm")),
    ("gemver", include_bytes!("../benches/data/polybench-c/gemver.wasm")),
    ("gesummv", include_bytes!("../benches/data/polybench-c/gesummv.wasm")),
    ("gramschmidt", include_bytes!("../benches/data/polybench-c/gramschmidt.wasm")),
    ("jacobi-1d-imper", include_bytes!("../benches/data/polybench-c/jacobi-1d-imper.wasm")),
    ("jacobi-2d-imper", include_bytes!("../benches/data/polybench-c/jacobi-2d-imper.wasm")),
    ("lu", include_bytes!("../benches/data/polybench-c/lu.wasm")),
    ("ludcmp", include_bytes!("../benches/data/polybench-c/ludcmp.wasm")),
    ("mvt", include_bytes!("../benches/data/polybench-c/mvt.wasm")),
    ("reg_detect", include_bytes!("../benches/data/polybench-c/reg_detect.wasm")),
    ("seidel-2d", include_bytes!("../benches/data/polybench-c/seidel-2d.wasm")),
    ("symm", include_bytes!("../benches/data/polybench-c/symm.wasm")),
    ("syr2k", include_bytes!("../benches/data/polybench-c/syr2k.wasm")),
    ("syrk", include_bytes!("../benches/data/polybench-c/syrk.wasm")),
    ("trisolv", include_bytes!("../benches/data/polybench-c/trisolv.wasm")),
    ("trmm", include_bytes!("../benches/data/polybench-c/trmm.wasm")),
];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for (_, bytes) in POLYBENCH_C_TESTS {
        println!("{:?}", module().parse(bytes).unwrap());
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
