pub mod vest_wasm;
// pub mod wasm_data;

use vest::regular::modifier::*;
use vest::regular::bytes;
use vest::regular::variant::*;
use vest::regular::sequence::*;
use vest::regular::repetition::*;
use vest::regular::disjoint::DisjointFrom;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::utils::*;
use vest::properties::*;
use vest_wasm::*;
// use wasm_data::*;

pub const POLYBENCH_C_TESTS: &[(&str, &[u8])] = &[
    (
        "2mm",
        include_bytes!("../benches/data/polybench-c/2mm.wasm.rewritten-2"),
    ),
    (
        "3mm",
        include_bytes!("../benches/data/polybench-c/3mm.wasm.rewritten-2"),
    ),
    (
        "adi",
        include_bytes!("../benches/data/polybench-c/adi.wasm.rewritten-2"),
    ),
    (
        "atax",
        include_bytes!("../benches/data/polybench-c/atax.wasm.rewritten-2"),
    ),
    (
        "bicg",
        include_bytes!("../benches/data/polybench-c/bicg.wasm.rewritten-2"),
    ),
    (
        "cholesky",
        include_bytes!("../benches/data/polybench-c/cholesky.wasm.rewritten-2"),
    ),
    (
        "correlation",
        include_bytes!("../benches/data/polybench-c/correlation.wasm.rewritten-2"),
    ),
    (
        "covariance",
        include_bytes!("../benches/data/polybench-c/covariance.wasm.rewritten-2"),
    ),
    (
        "doitgen",
        include_bytes!("../benches/data/polybench-c/doitgen.wasm.rewritten-2"),
    ),
    (
        "durbin",
        include_bytes!("../benches/data/polybench-c/durbin.wasm.rewritten-2"),
    ),
    (
        "dynprog",
        include_bytes!("../benches/data/polybench-c/dynprog.wasm.rewritten-2"),
    ),
    (
        "fdtd-2d",
        include_bytes!("../benches/data/polybench-c/fdtd-2d.wasm.rewritten-2"),
    ),
    (
        "fdtd-apml",
        include_bytes!("../benches/data/polybench-c/fdtd-apml.wasm.rewritten-2"),
    ),
    (
        "floyd-warshall",
        include_bytes!("../benches/data/polybench-c/floyd-warshall.wasm.rewritten-2"),
    ),
    (
        "gemm",
        include_bytes!("../benches/data/polybench-c/gemm.wasm.rewritten-2"),
    ),
    (
        "gemver",
        include_bytes!("../benches/data/polybench-c/gemver.wasm.rewritten-2"),
    ),
    (
        "gesummv",
        include_bytes!("../benches/data/polybench-c/gesummv.wasm.rewritten-2"),
    ),
    (
        "gramschmidt",
        include_bytes!("../benches/data/polybench-c/gramschmidt.wasm.rewritten-2"),
    ),
    (
        "jacobi-1d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-1d-imper.wasm.rewritten-2"),
    ),
    (
        "jacobi-2d-imper",
        include_bytes!("../benches/data/polybench-c/jacobi-2d-imper.wasm.rewritten-2"),
    ),
    (
        "lu",
        include_bytes!("../benches/data/polybench-c/lu.wasm.rewritten-2"),
    ),
    (
        "ludcmp",
        include_bytes!("../benches/data/polybench-c/ludcmp.wasm.rewritten-2"),
    ),
    (
        "mvt",
        include_bytes!("../benches/data/polybench-c/mvt.wasm.rewritten-2"),
    ),
    (
        "reg_detect",
        include_bytes!("../benches/data/polybench-c/reg_detect.wasm.rewritten-2"),
    ),
    (
        "seidel-2d",
        include_bytes!("../benches/data/polybench-c/seidel-2d.wasm.rewritten-2"),
    ),
    (
        "symm",
        include_bytes!("../benches/data/polybench-c/symm.wasm.rewritten-2"),
    ),
    (
        "syr2k",
        include_bytes!("../benches/data/polybench-c/syr2k.wasm.rewritten-2"),
    ),
    (
        "syrk",
        include_bytes!("../benches/data/polybench-c/syrk.wasm.rewritten-2"),
    ),
    (
        "trisolv",
        include_bytes!("../benches/data/polybench-c/trisolv.wasm.rewritten-2"),
    ),
    (
        "trmm",
        include_bytes!("../benches/data/polybench-c/trmm.wasm.rewritten-2"),
    ),
];

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for _ in 0..100 {
        for (_, bytes) in POLYBENCH_C_TESTS {
            let (consumed, _) = module().parse(bytes)?;
            println!("Consumed: {}/{}", consumed, bytes.len());
            // println!("{:?}", module().parse(bytes).unwrap());
            // println!("{} {:?}", bytes.len(), module().parse(bytes).unwrap());
            // println!("{:?}", rwasm::parser::parse(bytes).unwrap());
        }
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
